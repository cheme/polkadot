// Copyright 2017-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Proving state machine backend.

use std::cell::RefCell;
use codec::{Decode, Codec};
use log::debug;
use hash_db::{Hasher, HashDBRef, EMPTY_PREFIX, Prefix};
use sp_trie::{
	MemoryDB, empty_child_trie_root, read_trie_value_with, read_child_trie_value_with,
	record_all_keys, StorageProofKind, StorageProof, ProofInputKind, ProofInput,
	RecordMapTrieNodes,
};
pub use sp_trie::{Recorder, ChildrenProofMap};
pub use sp_trie::trie_types::{Layout, TrieError};
use crate::trie_backend::TrieBackend;
use crate::trie_backend_essence::{Ephemeral, TrieBackendEssence, TrieBackendStorage};
use crate::{Error, ExecutionError, Backend};
use crate::DBValue;
use sp_core::storage::{ChildInfo, ChildInfoProof, ChildrenMap};

/// Patricia trie-based backend specialized in get value proofs.
pub struct ProvingBackendRecorder<'a, S: 'a + TrieBackendStorage<H>, H: 'a + Hasher> {
	pub(crate) backend: &'a TrieBackendEssence<S, H>,
	pub(crate) proof_recorder: &'a mut Recorder<H::Out>,
}

impl<'a, S, H> ProvingBackendRecorder<'a, S, H>
	where
		S: TrieBackendStorage<H>,
		H: Hasher,
		H::Out: Codec,
{
	/// Produce proof for a key query.
	pub fn storage(&mut self, key: &[u8]) -> Result<Option<Vec<u8>>, String> {
		let mut read_overlay = S::Overlay::default();
		let eph = Ephemeral::new(
			self.backend.backend_storage(),
			&mut read_overlay,
			None,
		);

		let map_e = |e| format!("Trie lookup error: {}", e);

		read_trie_value_with::<Layout<H>, _, Ephemeral<S, H>>(
			&eph,
			self.backend.root(),
			key,
			&mut *self.proof_recorder,
		).map_err(map_e)
	}

	/// Produce proof for a child key query.
	pub fn child_storage(
		&mut self,
		child_info: &ChildInfo,
		key: &[u8]
	) -> Result<Option<Vec<u8>>, String> {
		let storage_key = child_info.storage_key();
		let root = self.storage(storage_key)?
			.and_then(|r| Decode::decode(&mut &r[..]).ok())
			.unwrap_or(empty_child_trie_root::<Layout<H>>());

		let mut read_overlay = S::Overlay::default();
		let eph = Ephemeral::new(
			self.backend.backend_storage(),
			&mut read_overlay,
			Some(child_info),
		);

		let map_e = |e| format!("Trie lookup error: {}", e);

		read_child_trie_value_with::<Layout<H>, _, _>(
			child_info.keyspace(),
			&eph,
			&root.as_ref(),
			key,
			&mut *self.proof_recorder
		).map_err(map_e)
	}

	/// Produce proof for the whole backend.
	pub fn record_all_keys(&mut self) {
		let mut read_overlay = S::Overlay::default();
		let eph = Ephemeral::new(
			self.backend.backend_storage(),
			&mut read_overlay,
			None,
		);

		let mut iter = move || -> Result<(), Box<TrieError<H::Out>>> {
			let root = self.backend.root();
			record_all_keys::<Layout<H>, _>(&eph, root, &mut *self.proof_recorder)
		};

		if let Err(e) = iter() {
			debug!(target: "trie", "Error while recording all keys: {}", e);
		}
	}
}

/// Global proof recorder, act as a layer over a hash db for recording queried
/// data.
pub enum ProofRecorder<H: Hasher> {
	// root of each child is added to be able to pack.
	/// Proof keep a separation between child trie content, this is usually useless,
	/// but when we use proof compression we want this separation.
	Full(RefCell<ChildrenMap<RecordMapTrieNodes<H>>>),
	/// Single level of storage for all recoded nodes.
	Flat(RefCell<RecordMapTrieNodes<H>>),
}

impl<H: Hasher> Default for ProofRecorder<H> {
	fn default() -> Self {
		// Default to flat proof.
		ProofRecorder::Flat(Default::default())
	}
}
/*
impl<H: Hasher> Clone for ProofRecorder<H>
	where
		H::Out: Clone,
{
	fn clone(&self) -> Self {
		match self {
			ProofRecorder::Full(a) => ProofRecorder::Full(RefCell::new((*a.borrow()).clone())),
			ProofRecorder::Flat(a) => ProofRecorder::Flat(RefCell::new(a.borrow().clone())),
		}
	}
}
*/
/// Patricia trie-based backend which also tracks all touched storage trie values.
/// These can be sent to remote node and used as a proof of execution.
pub struct ProvingBackend<'a, S: 'a + TrieBackendStorage<H>, H: 'a + Hasher> {
	trie_backend: TrieBackend<ProofRecorderBackend<'a, S, H>, H>,
	previous_input: ProofInput, // TODO consider &'a mut previous_input
	proof_kind: StorageProofKind,
}

/// Trie backend storage with its proof recorder.
pub struct ProofRecorderBackend<'a, S: 'a + TrieBackendStorage<H>, H: 'a + Hasher> {
	backend: &'a S,
	proof_recorder: ProofRecorder<H>, // TODO if removing rwlock, consider &'a mut
}

impl<'a, S: 'a + TrieBackendStorage<H>, H: 'a + Hasher> ProvingBackend<'a, S, H>
	where H::Out: Codec
{
	/// Create new proving backend.
	pub fn new(backend: &'a TrieBackend<S, H>, kind: StorageProofKind) -> Self {
		let proof_recorder = if kind.need_register_full() {
			ProofRecorder::Full(Default::default())
		} else {
			ProofRecorder::Flat(Default::default())
		};
		Self::new_with_recorder(backend, proof_recorder, kind, ProofInput::None)
	}

	/// Create new proving backend with the given recorder.
	pub fn new_with_recorder(
		backend: &'a TrieBackend<S, H>,
		proof_recorder: ProofRecorder<H>,
		proof_kind: StorageProofKind,
		previous_input: ProofInput,
	) -> Self {
		let essence = backend.essence();
		let root = essence.root().clone();
		let recorder = ProofRecorderBackend {
			backend: essence.backend_storage(),
			proof_recorder,
		};
		let trie_backend = if let ProofInputKind::ChildTrieRoots = proof_kind.processing_input_kind() {
			TrieBackend::new_with_roots(recorder, root)
		} else {
			TrieBackend::new(recorder, root)
		};
		ProvingBackend {
			trie_backend,
			previous_input,
			proof_kind,
		}
	}

	/// Extracting the gathered unordered proof.
	/// TODO remove or make it consiming: here it is doable to get
	/// intermediate proof, not sure if of any use.
	pub fn extract_proof(&mut self) -> Result<StorageProof, String> {
		self.update_input()?;
		self.trie_backend.essence().backend_storage().proof_recorder
			.extract_proof(self.proof_kind, self.previous_input.clone())
	}

	fn update_input(&mut self) -> Result<(), String> {
		let input = match self.proof_kind.processing_input_kind() {
			ProofInputKind::ChildTrieRoots => {
				self.trie_backend.extract_registered_roots()
			},
			_ => ProofInput::None,
		};
		if !self.previous_input.consolidate(input) {
			Err("Incompatible inputs".to_string())
		} else {
			Ok(())
		}
	}

	/// Drop the backend, but keep the state to use it again afterward
	pub fn recording_state(mut self) -> Result<(ProofRecorder<H>, ProofInput), String> {
		self.update_input()?;
		let proof_recorder = self.trie_backend
			.into_essence()
			.into_storage()
			.proof_recorder;
		Ok((proof_recorder, self.previous_input))
	}
}

impl<H: Hasher> ProofRecorder<H>
	where
		H::Out: Codec,
{
	/// Extracts the gathered unordered proof.
	pub fn extract_proof(
		&self,
		kind: StorageProofKind,
		input: ProofInput,
	) -> Result<StorageProof, String> {
		Ok(match self {
			ProofRecorder::Flat(rec) => StorageProof::extract_proof_from_flat(
				&*rec.borrow(),
				kind,
				&input,
			).map_err(|e| format!("{}", e))?,
			ProofRecorder::Full(rec) => StorageProof::extract_proof(
				&*rec.borrow(),
				kind,
				&input,
			).map_err(|e| format!("{}", e))?,
		})
	}
}

impl<'a, S: 'a + TrieBackendStorage<H>, H: 'a + Hasher> TrieBackendStorage<H>
	for ProofRecorderBackend<'a, S, H>
{
	type Overlay = S::Overlay;

	fn get(&self, child_info: &ChildInfo, key: &H::Out, prefix: Prefix) -> Result<Option<DBValue>, String> {
		match &self.proof_recorder {
			ProofRecorder::Flat(rec) => {
				if let Some(v) = (**rec.borrow()).get(key) {
					return Ok(v.clone());
				}
				let backend_value = self.backend.get(child_info, key, prefix)?;
				rec.borrow_mut().insert(key.clone(), backend_value.clone());
				Ok(backend_value)
			},
			ProofRecorder::Full(rec) => {
				if let Some(v) = rec.borrow().get(child_info).and_then(|s| (**s).get(key)) {
					return Ok(v.clone());
				}
				let backend_value = self.backend.get(child_info, key, prefix)?;
				rec.borrow_mut().entry(child_info.clone())
					.or_default()
					.insert(key.clone(), backend_value.clone());
				Ok(backend_value)
			},
		}
	}
}

impl<'a, S: 'a + TrieBackendStorage<H>, H: 'a + Hasher> std::fmt::Debug
	for ProvingBackend<'a, S, H>
{
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "ProvingBackend")
	}
}

impl<'a, S, H> Backend<H> for ProvingBackend<'a, S, H>
	where
		S: 'a + TrieBackendStorage<H>,
		H: 'a + Hasher,
		H::Out: Ord + Codec,
{
	type Error = String;
	type Transaction = S::Overlay;
	type TrieBackendStorage = S;

	fn storage(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		self.trie_backend.storage(key)
	}

	fn child_storage(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<Vec<u8>>, Self::Error> {
		self.trie_backend.child_storage(child_info, key)
	}

	fn for_keys_in_child_storage<F: FnMut(&[u8])>(
		&self,
		child_info: &ChildInfo,
		f: F,
	) {
		self.trie_backend.for_keys_in_child_storage(child_info, f)
	}

	fn next_storage_key(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		self.trie_backend.next_storage_key(key)
	}

	fn next_child_storage_key(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<Vec<u8>>, Self::Error> {
		self.trie_backend.next_child_storage_key(child_info, key)
	}

	fn for_keys_with_prefix<F: FnMut(&[u8])>(&self, prefix: &[u8], f: F) {
		self.trie_backend.for_keys_with_prefix(prefix, f)
	}

	fn for_key_values_with_prefix<F: FnMut(&[u8], &[u8])>(&self, prefix: &[u8], f: F) {
		self.trie_backend.for_key_values_with_prefix(prefix, f)
	}

	fn for_child_keys_with_prefix<F: FnMut(&[u8])>(
		&self,
		child_info: &ChildInfo,
		prefix: &[u8],
		f: F,
	) {
		self.trie_backend.for_child_keys_with_prefix( child_info, prefix, f)
	}

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		self.trie_backend.pairs()
	}

	fn keys(&self, prefix: &[u8]) -> Vec<Vec<u8>> {
		self.trie_backend.keys(prefix)
	}

	fn child_keys(
		&self,
		child_info: &ChildInfo,
		prefix: &[u8],
	) -> Vec<Vec<u8>> {
		self.trie_backend.child_keys(child_info, prefix)
	}

	fn storage_root<I>(&self, delta: I) -> (H::Out, Self::Transaction)
		where I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>
	{
		self.trie_backend.storage_root(delta)
	}

	fn child_storage_root<I>(
		&self,
		child_info: &ChildInfo,
		delta: I,
	) -> (H::Out, bool, Self::Transaction)
	where
		I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>,
		H::Out: Ord
	{
		self.trie_backend.child_storage_root(child_info, delta)
	}

	fn register_overlay_stats(&mut self, _stats: &crate::stats::StateMachineStats) { }

	fn usage_info(&self) -> crate::stats::UsageInfo {
		self.trie_backend.usage_info()
	}
}

/// Create flat proof check backend.
pub fn create_flat_proof_check_backend<H>(
	root: H::Out,
	proof: StorageProof,
) -> Result<TrieBackend<MemoryDB<H>, H>, Box<dyn Error>>
where
	H: Hasher,
	H::Out: Codec,
{
	let db = proof.as_partial_flat_db()
		.map_err(|e| Box::new(format!("{}", e)) as Box<dyn Error>)?;
	if db.contains(&root, EMPTY_PREFIX) {
		Ok(TrieBackend::new(db, root))
	} else {
		Err(Box::new(ExecutionError::InvalidProof))
	}
}

/// Create proof check backend.
pub fn create_proof_check_backend<H>(
	root: H::Out,
	proof: StorageProof,
) -> Result<TrieBackend<ChildrenProofMap<MemoryDB<H>>, H>, Box<dyn Error>>
where
	H: Hasher,
	H::Out: Codec,
{
	use std::ops::Deref;
	let db = proof.as_partial_db()
		.map_err(|e| Box::new(format!("{}", e)) as Box<dyn Error>)?;
	if db.deref().get(&ChildInfoProof::top_trie())
		.map(|db| db.contains(&root, EMPTY_PREFIX))
		.unwrap_or(false) {
		Ok(TrieBackend::new(db, root))
	} else {
		Err(Box::new(ExecutionError::InvalidProof))
	}
}

#[cfg(test)]
mod tests {
	use crate::InMemoryBackend;
	use crate::trie_backend::tests::test_trie;
	use super::*;
	use crate::proving_backend::create_proof_check_backend;
	use sp_trie::PrefixedMemoryDB;
	use sp_runtime::traits::BlakeTwo256;

	fn test_proving<'a>(
		trie_backend: &'a TrieBackend<PrefixedMemoryDB<BlakeTwo256>, BlakeTwo256>,
		kind: StorageProofKind,
	) -> ProvingBackend<'a, PrefixedMemoryDB<BlakeTwo256>, BlakeTwo256> {
		ProvingBackend::new(trie_backend, kind)
	}

	#[test]
	fn proof_is_empty_until_value_is_read() {
		let trie_backend = test_trie();
		let kind = StorageProofKind::Flatten;
		assert!(test_proving(&trie_backend, kind).extract_proof().unwrap().is_empty());
		let kind = StorageProofKind::Full;
		assert!(test_proving(&trie_backend, kind).extract_proof().unwrap().is_empty());
		let kind = StorageProofKind::TrieSkipHashesFull;
		assert!(test_proving(&trie_backend, kind).extract_proof().unwrap().is_empty());
		let kind = StorageProofKind::TrieSkipHashes;
		assert!(test_proving(&trie_backend, kind).extract_proof().unwrap().is_empty());
	}

	#[test]
	fn proof_is_non_empty_after_value_is_read() {
		let trie_backend = test_trie();
		let kind = StorageProofKind::Flatten;
		let mut backend = test_proving(&trie_backend, kind);
		assert_eq!(backend.storage(b"key").unwrap(), Some(b"value".to_vec()));
		assert!(!backend.extract_proof().unwrap().is_empty());
		let kind = StorageProofKind::Full;
		let mut backend = test_proving(&trie_backend, kind);
		assert_eq!(backend.storage(b"key").unwrap(), Some(b"value".to_vec()));
		assert!(!backend.extract_proof().unwrap().is_empty());
	}

	#[test]
	fn proof_is_invalid_when_does_not_contains_root() {
		use sp_core::H256;
		let result = create_proof_check_backend::<BlakeTwo256>(
			H256::from_low_u64_be(1),
			StorageProof::empty()
		);
		assert!(result.is_err());
	}

	#[test]
	fn passes_through_backend_calls() {
		let test = |proof_kind| {
			let trie_backend = test_trie();
			let proving_backend = test_proving(&trie_backend, proof_kind);
			assert_eq!(trie_backend.storage(b"key").unwrap(), proving_backend.storage(b"key").unwrap());
			assert_eq!(trie_backend.pairs(), proving_backend.pairs());

			let (trie_root, mut trie_mdb) = trie_backend.storage_root(::std::iter::empty());
			let (proving_root, mut proving_mdb) = proving_backend.storage_root(::std::iter::empty());
			assert_eq!(trie_root, proving_root);
			assert_eq!(trie_mdb.drain(), proving_mdb.drain());
		};
		test(StorageProofKind::Flatten);
		test(StorageProofKind::Full);
	}

	#[test]
	fn proof_recorded_and_checked() {
		let contents = (0..64).map(|i| (vec![i], Some(vec![i]))).collect::<Vec<_>>();
		let in_memory = InMemoryBackend::<BlakeTwo256>::default();
		let mut in_memory = in_memory.update(vec![(None, contents)]);
		let in_memory_root = in_memory.storage_root(::std::iter::empty()).0;
		(0..64).for_each(|i| assert_eq!(in_memory.storage(&[i]).unwrap().unwrap(), vec![i]));

		let trie = in_memory.as_trie_backend().unwrap();
		let trie_root = trie.storage_root(::std::iter::empty()).0;
		assert_eq!(in_memory_root, trie_root);
		(0..64).for_each(|i| assert_eq!(trie.storage(&[i]).unwrap().unwrap(), vec![i]));

		let test = |kind: StorageProofKind| {
			let mut proving = ProvingBackend::new(trie, kind);
			assert_eq!(proving.storage(&[42]).unwrap().unwrap(), vec![42]);

			let proof = proving.extract_proof().unwrap();

			let proof_check = create_proof_check_backend::<BlakeTwo256>(in_memory_root.into(), proof).unwrap();
			assert_eq!(proof_check.storage(&[42]).unwrap().unwrap(), vec![42]);
		};
		test(StorageProofKind::Flatten);
		test(StorageProofKind::Full);
		test(StorageProofKind::TrieSkipHashesFull);
		test(StorageProofKind::TrieSkipHashes);
	}

	#[test]
	fn proof_recorded_and_checked_with_child() {
		let child_info_1 = ChildInfo::new_default(b"sub1");
		let child_info_2 = ChildInfo::new_default(b"sub2");
		let child_info_1 = &child_info_1;
		let child_info_2 = &child_info_2;
		let contents = vec![
			(None, (0..64).map(|i| (vec![i], Some(vec![i]))).collect()),
			(Some(child_info_1.clone()),
				(28..65).map(|i| (vec![i], Some(vec![i]))).collect()),
			(Some(child_info_2.clone()),
				(10..15).map(|i| (vec![i], Some(vec![i]))).collect()),
		];
		let in_memory = InMemoryBackend::<BlakeTwo256>::default();
		let mut in_memory = in_memory.update(contents);
		let in_memory_root = in_memory.full_storage_root::<_, Vec<_>, _>(
			::std::iter::empty(),
			in_memory.child_storage_infos().map(|k|(k.to_owned(), Vec::new()))
		).0;
		(0..64).for_each(|i| assert_eq!(
			in_memory.storage(&[i]).unwrap().unwrap(),
			vec![i]
		));
		(28..65).for_each(|i| assert_eq!(
			in_memory.child_storage(child_info_1, &[i]).unwrap().unwrap(),
			vec![i]
		));
		(10..15).for_each(|i| assert_eq!(
			in_memory.child_storage(child_info_2, &[i]).unwrap().unwrap(),
			vec![i]
		));

		let trie = in_memory.as_trie_backend().unwrap();
		let trie_root = trie.storage_root(::std::iter::empty()).0;
		assert_eq!(in_memory_root, trie_root);
		(0..64).for_each(|i| assert_eq!(
			trie.storage(&[i]).unwrap().unwrap(),
			vec![i]
		));

		let test = |kind: StorageProofKind| {
			let mut proving = ProvingBackend::new(trie, kind);
			assert_eq!(proving.storage(&[42]).unwrap().unwrap(), vec![42]);

			let proof = proving.extract_proof().unwrap();

			let proof_check = create_proof_check_backend::<BlakeTwo256>(
				in_memory_root.into(),
				proof
			).unwrap();
			assert!(proof_check.storage(&[0]).is_err());
			assert_eq!(proof_check.storage(&[42]).unwrap().unwrap(), vec![42]);
			// note that it is include in root because proof close
			assert_eq!(proof_check.storage(&[41]).unwrap().unwrap(), vec![41]);
			assert_eq!(proof_check.storage(&[64]).unwrap(), None);

			let mut proving = ProvingBackend::new(trie, kind);
			assert_eq!(proving.child_storage(child_info_1, &[64]), Ok(Some(vec![64])));

			let proof = proving.extract_proof().unwrap();
			if kind.use_full_partial_db().unwrap() {
				let proof_check = create_proof_check_backend::<BlakeTwo256>(
					in_memory_root.into(),
					proof
				).unwrap();

				assert_eq!(
					proof_check.child_storage(&child_info_1, &[64]).unwrap().unwrap(),
					vec![64]
				);
			} else {
				let proof_check = create_flat_proof_check_backend::<BlakeTwo256>(
					in_memory_root.into(),
					proof
				).unwrap();

				assert_eq!(
					proof_check.child_storage(&child_info_1, &[64]).unwrap().unwrap(),
					vec![64]
				);
			}
		};
		test(StorageProofKind::Flatten);
		test(StorageProofKind::Full);
		test(StorageProofKind::TrieSkipHashesFull);
		test(StorageProofKind::TrieSkipHashes);
	}
}

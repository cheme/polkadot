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

use std::sync::Arc;
use parking_lot::RwLock;
use codec::{Encode, Decode, Codec};
use log::debug;
use hash_db::{Hasher, HashDB, EMPTY_PREFIX, Prefix};
use sp_trie::{
	MemoryDB, empty_child_trie_root, read_trie_value_with, read_child_trie_value_with,
	record_all_keys,
};
pub use sp_trie::Recorder;
pub use sp_trie::trie_types::{Layout, TrieError};
use crate::trie_backend::TrieBackend;
use crate::trie_backend_essence::{Ephemeral, TrieBackendEssence, TrieBackendStorage};
use crate::{Error, ExecutionError, Backend};
use std::collections::{HashMap, HashSet};
use crate::DBValue;
use sp_core::storage::{ChildInfo, ChildInfoProof, ChildType, ChildrenMap, ChildrenProofMap};

/// Patricia trie-based backend specialized in get value proofs.
pub struct ProvingBackendRecorder<'a, S: 'a + TrieBackendStorage<H>, H: 'a + Hasher> {
	pub(crate) backend: &'a TrieBackendEssence<S, H>,
	pub(crate) proof_recorder: &'a mut Recorder<H::Out>,
}

/// Different kind of proof representation are allowed.
/// This definition is used as input parameter when producing
/// a storage proof.
#[repr(u32)]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum StorageProofKind {
	/// The proof can be build by multiple child trie only when
	/// their query can be done on a single memory backend,
	/// all encoded node can be stored in the same container.
	Flatten,
	/// Proofs split by child trie.
	Full,
	/// Compact form of proofs split by child trie.
	FullCompact,
}

impl StorageProofKind {
	/// Is proof stored in a unique structure or
	/// different structure depending on child trie.
	pub fn is_flatten(&self) -> bool {
		match self {
			StorageProofKind::Flatten => true,
			StorageProofKind::Full | StorageProofKind::FullCompact =>  false
		}
	}

	/// Is the proof compacted. Compaction requires
	/// using state root of every child trie.
	pub fn is_compact(&self) -> bool {
		match self {
			StorageProofKind::FullCompact => true,
			StorageProofKind::Full | StorageProofKind::Flatten =>  false
		}
	}
}

/// The possible compactions for proofs.
#[repr(u32)]
#[derive(Debug, PartialEq, Eq, Clone, Encode, Decode)]
pub enum CompactScheme {
	/// This skip encoding of hashes that are
	/// calculated when reading the structue
	/// of the trie.
	TrieSkipHashes = 1,
/*	/// Skip encoding of hashes and values,
	/// we need to know them when when unpacking.
	KnownQueryPlanAndValues = 2,
	/// Skip encoding of hashes, this need knowing
	/// the queried keys when unpacking, can be faster
	/// than `TrieSkipHashes` but with similar packing
	/// gain.
	KnownQueryPlan = 3,*/
}

type ProofNodes = Vec<Vec<u8>>;
type ProofCompacted = (CompactScheme, Vec<Vec<u8>>);

/// A proof that some set of key-value pairs are included in the storage trie. The proof contains
/// the storage values so that the partial storage backend can be reconstructed by a verifier that
/// does not already have access to the key-value pairs.
///
/// For default trie, the proof component consists of the set of serialized nodes in the storage trie
/// accessed when looking up the keys covered by the proof. Verifying the proof requires constructing
/// the partial trie from the serialized nodes and performing the key lookups.
#[derive(Debug, PartialEq, Eq, Clone, Encode, Decode)]
pub enum StorageProof {
	/// Single flattened proof component, all default child trie are flattened over a same
	/// container, no child trie information is provided, this works only for proof accessing
	/// the same kind of child trie.
	Flatten(ProofNodes),
/* TODO EMCH implement as it will be default for trie skip hashes	/// Proof can address multiple child trie, but results in a single flatten
	/// db backend.
	FlattenCompact(Vec<ProofCompacted>),*/
	///	Fully descriBed proof, it includes the child trie individual descriptions.
	///	Currently Full variant are not of any use as we have only child trie that can use the same
	///	memory db backend.
	///	TODO EMCH consider removal: could be put back when needed, and probably
	///	with a new StorageProof key that is the same for a flattenable kind.
	Full(ChildrenProofMap<ProofNodes>),
	///	Fully descriped proof, compact encoded.
	FullCompact(ChildrenProofMap<ProofCompacted>),
}

impl StorageProof {
	/// Returns a new empty proof.
	///
	/// An empty proof is capable of only proving trivial statements (ie. that an empty set of
	/// key-value pairs exist in storage).
	pub fn empty() -> Self {
		// we default to full as it can be reduce to flatten when reducing
		// flatten to full is not possible without making asumption over the content.
		Self::empty_for(StorageProofKind::Full)
	}

	/// Returns a new empty proof of a given kind.
	pub fn empty_for(kind: StorageProofKind) -> Self {
		match kind {
			StorageProofKind::Flatten => StorageProof::Flatten(Default::default()),
			StorageProofKind::Full => StorageProof::Full(ChildrenProofMap::default()),
			StorageProofKind::FullCompact => StorageProof::FullCompact(ChildrenProofMap::default()),
		}
	}

	/// Returns whether this is an empty proof.
	pub fn is_empty(&self) -> bool {
		match self {
			StorageProof::Flatten(data) => data.is_empty(),
			StorageProof::Full(data) => data.is_empty(),
			StorageProof::FullCompact(data) => data.is_empty(),
		}
	}

	/// Create an iterator over trie nodes constructed from the proof. The nodes are not guaranteed
	/// to be traversed in any particular order.
	/// This iterator is only for `Flatten` proofs, other kind of proof will return an iterator with
	/// no content.
	pub fn iter_nodes_flatten(self) -> StorageProofNodeIterator {
		StorageProofNodeIterator::new(self)
	}

	/// This unpacks `FullCompact` to `Full` or do nothing.
	/// TODO EMCH document and use case for with_roots to true?? (probably unpack -> merge -> pack
	/// but no code for it here)
	pub fn unpack<H: Hasher>(
		self,
		with_roots: bool,
	) -> Result<(Self, Option<ChildrenProofMap<Vec<u8>>>), String>
		where H::Out: Codec,
	{
		let map_e = |e| format!("Trie unpack error: {}", e);
		if let StorageProof::FullCompact(children) = self {
			let mut result = ChildrenProofMap::default();
			let mut roots = if with_roots {
				Some(ChildrenProofMap::default())
			} else {
				None
			};
			for (child_info, (compact_scheme, proof)) in children {
				match child_info.child_type() {
					ChildType::ParentKeyId => {
						match compact_scheme {
							CompactScheme::TrieSkipHashes => {
								// Note that we could check the proof from the unpacking.
								let (root, unpacked_proof) = sp_trie::unpack_proof::<Layout<H>>(proof.as_slice())
									.map_err(map_e)?;
								roots.as_mut().map(|roots| roots.insert(child_info.clone(), root.encode()));
								result.insert(child_info, unpacked_proof);
							},
						}
					}
				}
			}
			Ok((StorageProof::Full(result), roots))
		} else {
			Ok((self, None))
		}
	}

	/// This packs `Full` to `FullCompact`, using needed roots.
	pub fn pack<H: Hasher>(self, roots: &ChildrenProofMap<Vec<u8>>) -> Result<Self, String>
		where H::Out: Codec,
	{
		let map_e = |e| format!("Trie pack error: {}", e);

		if let StorageProof::Full(children) = self {
			let mut result = ChildrenProofMap::default();
			for (child_info, proof) in children {
				match child_info.child_type() {
					ChildType::ParentKeyId => {
						let root = roots.get(&child_info)
							.and_then(|r| Decode::decode(&mut &r[..]).ok())
							.ok_or_else(|| "Missing root for packing".to_string())?;
						let trie_nodes = sp_trie::pack_proof::<Layout<H>>(&root, &proof[..]).map_err(map_e)?;
						result.insert(child_info.clone(), (CompactScheme::TrieSkipHashes, trie_nodes));
					}
				}
			}
			Ok(StorageProof::FullCompact(result))
		} else {
			Ok(self)
		}
	}

	/// This flatten `Full` to `Flatten`.
	/// Note that if for some reason child proof were not
	/// attached to the top trie, they will be lost.
	/// Generally usage of Flatten kind or this function
	/// when using child trie is not recommended.
	pub fn flatten(self) -> Self {
		if let StorageProof::Full(children) = self {
			let mut result = Vec::new();
			children.into_iter().for_each(|(child_info, proof)| {
				match child_info.child_type() {
					ChildType::ParentKeyId => {
						// this can get merged with top, since it is proof we do not use prefix
						result.extend(proof);
					}
				}
			});
			StorageProof::Flatten(result)
		} else {
			self
		}
	}
}

/// An iterator over trie nodes constructed from a storage proof. The nodes are not guaranteed to
/// be traversed in any particular order.
pub struct StorageProofNodeIterator {
	inner: <Vec<Vec<u8>> as IntoIterator>::IntoIter,
}

impl StorageProofNodeIterator {
	fn new(proof: StorageProof) -> Self {
		match proof {
			StorageProof::Flatten(data) => StorageProofNodeIterator {
				inner: data.into_iter(),
			},
			_ => StorageProofNodeIterator {
				inner: Vec::new().into_iter(),
			},
		}
	}
}

impl Iterator for StorageProofNodeIterator {
	type Item = Vec<u8>;

	fn next(&mut self) -> Option<Self::Item> {
		self.inner.next()
	}
}

/// Merges multiple storage proofs covering potentially different sets of keys into one proof
/// covering all keys. The merged proof output may be smaller than the aggregate size of the input
/// proofs due to deduplication of trie nodes.
/// Merge to `Flatten` if any item is flatten (we cannot unflatten), if not `Flatten` we output to
/// non compact form.
/// TODO EMCH on master this has moved to a StorageProof function: do it (same for the other merge
/// function)
pub fn merge_storage_proofs<H, I>(proofs: I) -> Result<StorageProof, String>
	where
		I: IntoIterator<Item=StorageProof>,
		H: Hasher,
		H::Out: Codec,
{
	let mut do_flatten = false;
	let mut child_sets = ChildrenProofMap::<HashSet<Vec<u8>>>::default();
	let mut unique_set = HashSet::<Vec<u8>>::default();
	// lookup for best encoding
	for mut proof in proofs {
		if let &StorageProof::FullCompact(..) = &proof {
			// TODO EMCH pack back so set to true.
			proof = proof.unpack::<H>(false)?.0;
		}
		let proof = proof;
		match proof {
			StorageProof::Flatten(proof) => {
				if !do_flatten {
					do_flatten = true;
					for (_, set) in std::mem::replace(&mut child_sets, Default::default()).into_iter() {
						unique_set.extend(set);
					}
				}
				unique_set.extend(proof);
			},
			StorageProof::Full(children) => {
				for (child_info, child) in children.into_iter() {
					if do_flatten {
						unique_set.extend(child);
					} else {
						let set = child_sets.entry(child_info).or_default();
						set.extend(child);
					}
				}
			},
			StorageProof::FullCompact(_children) => unreachable!("unpacked when entering function"),
		}
	}
	Ok(if do_flatten {
		StorageProof::Flatten(unique_set.into_iter().collect())
	} else {
		let mut result = ChildrenProofMap::default();
		for (child_info, set) in child_sets.into_iter() {
			result.insert(child_info, set.into_iter().collect());
		}
		StorageProof::Full(result)
	})
}

/// Merge over flatten proof, return `None` if one of the proofs is not
/// a flatten proof.
pub fn merge_flatten_storage_proofs<I>(proofs: I) -> Option<StorageProof>
	where
		I: IntoIterator<Item=StorageProof>,
{
	let mut unique_set = HashSet::<Vec<u8>>::default();
	// lookup for best encoding
	for proof in proofs {
		if let StorageProof::Flatten(set) = proof {
			unique_set.extend(set);
		} else {
			return None;
		}
	}
	Some(StorageProof::Flatten(unique_set.into_iter().collect()))
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
	Full(Arc<RwLock<ChildrenMap<HashMap<<H as Hasher>::Out, Option<DBValue>>>>>),
	/// Single level of storage for all recoded nodes.
	Flat(Arc<RwLock<HashMap<<H as Hasher>::Out, Option<DBValue>>>>),
}

impl<H: Hasher> Default for ProofRecorder<H> {
	fn default() -> Self {
		// Default to flat proof.
		ProofRecorder::Flat(Default::default())
	}
}

impl<H: Hasher> Clone for ProofRecorder<H> {
	fn clone(&self) -> Self {
		match self {
			ProofRecorder::Full(a) => ProofRecorder::Full(a.clone()),
			ProofRecorder::Flat(a) => ProofRecorder::Flat(a.clone()),
		}
	}
}

/// Patricia trie-based backend which also tracks all touched storage trie values.
/// These can be sent to remote node and used as a proof of execution.
pub struct ProvingBackend<'a, S: 'a + TrieBackendStorage<H>, H: 'a + Hasher> (
	TrieBackend<ProofRecorderBackend<'a, S, H>, H>,
);

/// Trie backend storage with its proof recorder.
pub struct ProofRecorderBackend<'a, S: 'a + TrieBackendStorage<H>, H: 'a + Hasher> {
	backend: &'a S,
	proof_recorder: ProofRecorder<H>,
}

impl<'a, S: 'a + TrieBackendStorage<H>, H: 'a + Hasher> ProvingBackend<'a, S, H>
	where H::Out: Codec
{
	/// Create new proving backend.
	pub fn new(backend: &'a TrieBackend<S, H>, flatten: bool) -> Self {
		let proof_recorder = if flatten {
			ProofRecorder::Flat(Default::default())
		} else {
			ProofRecorder::Full(Default::default())
		};
		Self::new_with_recorder(backend, proof_recorder)
	}

	/// Create new proving backend with the given recorder.
	pub fn new_with_recorder(
		backend: &'a TrieBackend<S, H>,
		proof_recorder: ProofRecorder<H>,
	) -> Self {
		let essence = backend.essence();
		let root = essence.root().clone();
		let recorder = ProofRecorderBackend {
			backend: essence.backend_storage(),
			proof_recorder,
		};
		ProvingBackend(TrieBackend::new_with_roots(recorder, root))
	}

	/// Extracting the gathered unordered proof.
	pub fn extract_proof(&self) -> Result<StorageProof, String> {
		self.0.essence().backend_storage().proof_recorder.extract_proof()
	}
}

impl<H: Hasher> ProofRecorder<H> {
	/// Extracting the gathered unordered proof.
	pub fn extract_proof(&self) -> Result<StorageProof, String> {
		Ok(match self {
			ProofRecorder::Flat(rec) => {
				let trie_nodes = rec
					.read()
					.iter()
					.filter_map(|(_k, v)| v.as_ref().map(|v| v.to_vec()))
					.collect();
				StorageProof::Flatten(trie_nodes)
			},
			ProofRecorder::Full(rec) => {
				let mut children = ChildrenProofMap::default();
				for (child_info, set) in rec.read().iter() {
					let trie_nodes: Vec<Vec<u8>> = set
						.iter()
						.filter_map(|(_k, v)| v.as_ref().map(|v| v.to_vec()))
						.collect();
					children.insert(child_info.proof_info(), trie_nodes);
				}
				StorageProof::Full(children)
			},
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
				if let Some(v) = rec.read().get(key) {
					return Ok(v.clone());
				}
				let backend_value = self.backend.get(child_info, key, prefix)?;
				rec.write().insert(key.clone(), backend_value.clone());
				Ok(backend_value)
			},
			ProofRecorder::Full(rec) => {
				if let Some(v) = rec.read().get(child_info).and_then(|s| s.get(key)) {
					return Ok(v.clone());
				}
				let backend_value = self.backend.get(child_info, key, prefix)?;
				rec.write().entry(child_info.clone())
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
		self.0.storage(key)
	}

	fn child_storage(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<Vec<u8>>, Self::Error> {
		self.0.child_storage(child_info, key)
	}

	fn for_keys_in_child_storage<F: FnMut(&[u8])>(
		&self,
		child_info: &ChildInfo,
		f: F,
	) {
		self.0.for_keys_in_child_storage(child_info, f)
	}

	fn next_storage_key(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		self.0.next_storage_key(key)
	}

	fn next_child_storage_key(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<Vec<u8>>, Self::Error> {
		self.0.next_child_storage_key(child_info, key)
	}

	fn for_keys_with_prefix<F: FnMut(&[u8])>(&self, prefix: &[u8], f: F) {
		self.0.for_keys_with_prefix(prefix, f)
	}

	fn for_key_values_with_prefix<F: FnMut(&[u8], &[u8])>(&self, prefix: &[u8], f: F) {
		self.0.for_key_values_with_prefix(prefix, f)
	}

	fn for_child_keys_with_prefix<F: FnMut(&[u8])>(
		&self,
		child_info: &ChildInfo,
		prefix: &[u8],
		f: F,
	) {
		self.0.for_child_keys_with_prefix( child_info, prefix, f)
	}

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		self.0.pairs()
	}

	fn keys(&self, prefix: &[u8]) -> Vec<Vec<u8>> {
		self.0.keys(prefix)
	}

	fn child_keys(
		&self,
		child_info: &ChildInfo,
		prefix: &[u8],
	) -> Vec<Vec<u8>> {
		self.0.child_keys(child_info, prefix)
	}

	fn storage_root<I>(&self, delta: I) -> (H::Out, Self::Transaction)
		where I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>
	{
		self.0.storage_root(delta)
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
		self.0.child_storage_root(child_info, delta)
	}

	fn register_overlay_stats(&mut self, _stats: &crate::stats::StateMachineStats) { }

	fn usage_info(&self) -> crate::stats::UsageInfo {
		self.0.usage_info()
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
	let db = create_flat_proof_check_backend_storage(proof)
		.map_err(|e| Box::new(e) as Box<dyn Error>)?;
	if db.contains(&root, EMPTY_PREFIX) {
		Ok(TrieBackend::new_with_roots(db, root))
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
	let db = create_proof_check_backend_storage(proof)
		.map_err(|e| Box::new(e) as Box<dyn Error>)?;
	if db.deref().get(&ChildInfoProof::top_trie())
		.map(|db| db.contains(&root, EMPTY_PREFIX))
		.unwrap_or(false) {
		Ok(TrieBackend::new_with_roots(db, root))
	} else {
		Err(Box::new(ExecutionError::InvalidProof))
	}
}

/// Create in-memory storage of proof check backend.
/// Currently child trie are all with same backend
/// implementation, therefore using
/// `create_flat_proof_check_backend_storage` is prefered.
/// TODO flat proof check is enough for now, do we want to
/// maintain the full variant?
pub fn create_proof_check_backend_storage<H>(
	proof: StorageProof,
) -> Result<ChildrenProofMap<MemoryDB<H>>, String>
where
	H: Hasher,
{
	let map_e = |e| format!("Trie unpack error: {}", e);
	let mut result = ChildrenProofMap::default();
	match proof {
		s@StorageProof::Flatten(..) => {
			let mut db = MemoryDB::default();
			for item in s.iter_nodes_flatten() {
				db.insert(EMPTY_PREFIX, &item);
			}
			result.insert(ChildInfoProof::top_trie(), db);
		},
		StorageProof::Full(children) => {
			for (child_info, proof) in children.into_iter() {
				let mut db = MemoryDB::default();
				for item in proof.into_iter() {
					db.insert(EMPTY_PREFIX, &item);
				}
				result.insert(child_info, db);
			}
		},
		StorageProof::FullCompact(children) => {
			for (child_info, (compact_scheme, proof)) in children.into_iter() {
				match compact_scheme {
					CompactScheme::TrieSkipHashes => {
						// Note that this does check all hashes so using a trie backend
						// for further check is not really good (could use a direct value backend).
						let (_root, db) = sp_trie::unpack_proof_to_memdb::<Layout<H>>(proof.as_slice())
								.map_err(map_e)?;
						result.insert(child_info, db);
					},
				}
			}
		},
	}
	Ok(result)
}

/// Create in-memory storage of proof check backend.
pub fn create_flat_proof_check_backend_storage<H>(
	proof: StorageProof,
) -> Result<MemoryDB<H>, String>
where
	H: Hasher,
{
	let map_e = |e| format!("Trie unpack error: {}", e);
	let mut db = MemoryDB::default();
	match proof {
		s@StorageProof::Flatten(..) => {
			for item in s.iter_nodes_flatten() {
				db.insert(EMPTY_PREFIX, &item);
			}
		},
		StorageProof::Full(children) => {
			for (_child_info, proof) in children.into_iter() {
				for item in proof.into_iter() {
					db.insert(EMPTY_PREFIX, &item);
				}
			}
		},
		StorageProof::FullCompact(children) => {
			for (_child_info, (compact_scheme, proof)) in children.into_iter() {
				match compact_scheme {
					CompactScheme::TrieSkipHashes => {
						// Note that this does check all hashes so using a trie backend
						// for further check is not really good (could use a direct value backend).
						let (_root, child_db) = sp_trie::unpack_proof_to_memdb::<Layout<H>>(proof.as_slice())
								.map_err(map_e)?;
						db.consolidate(child_db);
					},
				}
			}
		},
	}
	Ok(db)
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
		flat: bool,
	) -> ProvingBackend<'a, PrefixedMemoryDB<BlakeTwo256>, BlakeTwo256> {
		ProvingBackend::new(trie_backend, flat)
	}


	#[test]
	fn proof_is_empty_until_value_is_read() {
		let trie_backend = test_trie();
		assert!(test_proving(&trie_backend, true).extract_proof().unwrap().is_empty());
		assert!(test_proving(&trie_backend, false).extract_proof().unwrap().is_empty());
	}

	#[test]
	fn proof_is_non_empty_after_value_is_read() {
		let trie_backend = test_trie();
		let backend = test_proving(&trie_backend, true);
		assert_eq!(backend.storage(b"key").unwrap(), Some(b"value".to_vec()));
		assert!(!backend.extract_proof().unwrap().is_empty());
		let backend = test_proving(&trie_backend, false);
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
		let test = |flat| {
			let trie_backend = test_trie();
			let proving_backend = test_proving(&trie_backend, flat);
			assert_eq!(trie_backend.storage(b"key").unwrap(), proving_backend.storage(b"key").unwrap());
			assert_eq!(trie_backend.pairs(), proving_backend.pairs());

			let (trie_root, mut trie_mdb) = trie_backend.storage_root(::std::iter::empty());
			let (proving_root, mut proving_mdb) = proving_backend.storage_root(::std::iter::empty());
			assert_eq!(trie_root, proving_root);
			assert_eq!(trie_mdb.drain(), proving_mdb.drain());
		};
		test(true);
		test(false);
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

		let test = |flat| {
			let proving = ProvingBackend::new(trie, flat);
			assert_eq!(proving.storage(&[42]).unwrap().unwrap(), vec![42]);

			let proof = proving.extract_proof().unwrap();

			let proof_check = create_proof_check_backend::<BlakeTwo256>(in_memory_root.into(), proof).unwrap();
			assert_eq!(proof_check.storage(&[42]).unwrap().unwrap(), vec![42]);
		};
		test(true);
		test(false);
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

		let test = |flat| {
			let proving = ProvingBackend::new(trie, flat);
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

			let proving = ProvingBackend::new(trie, flat);
			assert_eq!(proving.child_storage(child_info_1, &[64]), Ok(Some(vec![64])));

			let proof = proving.extract_proof().unwrap();
			if flat {
				let proof_check = create_flat_proof_check_backend::<BlakeTwo256>(
					in_memory_root.into(),
					proof
				).unwrap();

				assert_eq!(
					proof_check.child_storage(&child_info_1, &[64]).unwrap().unwrap(),
					vec![64]
				);
			} else {
				let proof_check = create_proof_check_backend::<BlakeTwo256>(
					in_memory_root.into(),
					proof
				).unwrap();

				assert_eq!(
					proof_check.child_storage(&child_info_1, &[64]).unwrap().unwrap(),
					vec![64]
				);
			}
		};
		test(true);
		test(false);
	}
}

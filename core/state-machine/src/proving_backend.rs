// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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
use log::debug;
use hash_db::Hasher;
use heapsize::HeapSizeOf;
use hash_db::HashDB;
use trie::{Recorder, MemoryDB, TrieError, read_child_trie_value, record_all_keys, read_trie_value_with};
use crate::trie_backend::TrieBackend;
use crate::trie_backend_essence::{Ephemeral, TrieBackendEssence, TrieBackendStorage};
use crate::{Error, ExecutionError, Backend};
use primitives::{KeySpace, SubTrie};
use std::collections::BTreeMap;

/// Patricia trie-based backend essence which also tracks all touched storage trie values.
/// These can be sent to remote node and used as a proof of execution.
pub struct ProvingBackendEssence<'a, S: 'a + TrieBackendStorage<H>, H: 'a + Hasher> {
	pub(crate) backend: &'a TrieBackendEssence<S, H>,
	pub(crate) proof_recorder: &'a mut Recorder<H::Out>,
}

impl<'a, S, H> ProvingBackendEssence<'a, S, H>
	where
		S: TrieBackendStorage<H>,
		H: Hasher,
		H::Out: HeapSizeOf,
{
	pub fn storage(&mut self, key: &[u8]) -> Result<Option<Vec<u8>>, String> {
		let mut read_overlay = MemoryDB::default();
		let eph = Ephemeral::new(
			self.backend.backend_storage(),
			&mut read_overlay,
		);

		let map_e = |e| format!("Trie lookup error: {}", e);

		read_trie_value_with::<H, _, Ephemeral<S, H>>(&eph, self.backend.root(), key, &mut *self.proof_recorder).map_err(map_e)
	}

	pub fn child_storage(&mut self, subtrie: &SubTrie, key: &[u8]) -> Result<Option<Vec<u8>>, String> {
/*    // use default value if no storage (proof does not change if incorrect keyspace).
  	let o_subtrie: Option<SubTrie> = self.storage(storage_key)?
			.map(std::io::Cursor::new).as_mut()
			.and_then(parity_codec::Decode::decode);

    if let Some(subtrie) = o_subtrie {*/
      let mut read_overlay = MemoryDB::default();
      let eph = Ephemeral::new(
        self.backend.backend_storage(),
        &mut read_overlay,
      );

      let map_e = |e| format!("Trie lookup error: {}", e);

      read_child_trie_value(subtrie, &eph, key).map_err(map_e)
/*    } else {
      // No subtrie same as no value
      Ok(None)
    }*/
	}

	pub fn record_all_keys(&mut self) {
		let mut read_overlay = MemoryDB::default();
		let eph = Ephemeral::new(
			self.backend.backend_storage(),
			&mut read_overlay,
		);

		let mut iter = move || -> Result<(), Box<TrieError<H::Out>>> {
			let root = self.backend.root();
			record_all_keys::<H, _>(&eph, root, &mut *self.proof_recorder)
		};

		if let Err(e) = iter() {
			debug!(target: "trie", "Error while recording all keys: {}", e);
		}
	}
}

/// Patricia trie-based backend which also tracks all touched storage trie values.
/// These can be sent to remote node and used as a proof of execution.
pub struct ProvingBackend<'a, S: 'a + TrieBackendStorage<H>, H: 'a + Hasher> {
	backend: &'a TrieBackend<S, H>,
	proof_recorder: RefCell<Recorder<H::Out>>,
}

impl<'a, S: 'a + TrieBackendStorage<H>, H: 'a + Hasher> ProvingBackend<'a, S, H> {
	/// Create new proving backend.
	pub fn new(backend: &'a TrieBackend<S, H>) -> Self {
		ProvingBackend {
			backend,
			proof_recorder: RefCell::new(Recorder::new()),
		}
	}

	/// Consume the backend, extracting the gathered proof in lexicographical order
	/// by value.
	pub fn extract_proof(self) -> Vec<Vec<u8>> {
		self.proof_recorder.into_inner().drain()
			.into_iter()
			.map(|n| n.data.to_vec())
			.collect()
	}
}

impl<'a, S, H> Backend<H> for ProvingBackend<'a, S, H>
	where
		S: 'a + TrieBackendStorage<H>,
		H: 'a + Hasher,
		H::Out: Ord + HeapSizeOf,
{
	type Error = String;
	type Transaction = BTreeMap<KeySpace, MemoryDB<H>>;
	type TrieBackendStorage = MemoryDB<H>;

	fn storage(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		ProvingBackendEssence {
			backend: self.backend.essence(),
			proof_recorder: &mut *self.proof_recorder.try_borrow_mut()
				.expect("only fails when already borrowed; storage() is non-reentrant; qed"),
		}.storage(key)
	}

	fn child_storage(&self, subtrie: &SubTrie, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		ProvingBackendEssence {
			backend: self.backend.essence(),
			proof_recorder: &mut *self.proof_recorder.try_borrow_mut()
				.expect("only fails when already borrowed; child_storage() is non-reentrant; qed"),
		}.child_storage(subtrie, key)
	}

	fn for_keys_in_child_storage<F: FnMut(&[u8])>(&self, subtrie: &SubTrie, f: F) {
		self.backend.for_keys_in_child_storage(subtrie, f)
	}

	fn for_keys_with_prefix<F: FnMut(&[u8])>(&self, prefix: &[u8], f: F) {
		self.backend.for_keys_with_prefix(prefix, f)
	}

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		self.backend.pairs()
	}

	fn keys(&self, prefix: &Vec<u8>) -> Vec<Vec<u8>> {
		self.backend.keys(prefix)
	}

	fn storage_root<I>(&self, delta: I) -> (H::Out, BTreeMap<KeySpace, MemoryDB<H>>)
		where I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>
	{
		self.backend.storage_root(delta)
	}

	fn child_storage_root<I>(&self, subtrie: &SubTrie, delta: I) -> (Vec<u8>, bool, Self::Transaction)
	where
		I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>,
		H::Out: Ord
	{
		self.backend.child_storage_root(subtrie, delta)
	}

	fn try_into_trie_backend(self) -> Option<TrieBackend<Self::TrieBackendStorage, H>> {
		None
	}
}

/// Create proof check backend.
pub fn create_proof_check_backend<H>(
	root: H::Out,
	proof: Vec<Vec<u8>>
) -> Result<TrieBackend<MemoryDB<H>, H>, Box<Error>>
where
	H: Hasher,
	H::Out: HeapSizeOf,
{
	let db = create_proof_check_backend_storage(proof);

	if !db.contains(&root) {
		return Err(Box::new(ExecutionError::InvalidProof) as Box<Error>);
	}

	Ok(TrieBackend::new(db, root))
}

/// Create in-memory storage of proof check backend.
pub fn create_proof_check_backend_storage<H>(
	proof: Vec<Vec<u8>>
) -> MemoryDB<H>
where
	H: Hasher,
	H::Out: HeapSizeOf,
{
	let mut db = MemoryDB::default();
	for item in proof {
		db.insert(&item);
	}
	db
}

#[cfg(test)]
mod tests {
	use crate::backend::{InMemory};
	use crate::trie_backend::tests::test_trie;
	use super::*;
	use primitives::{Blake2Hasher};

	fn test_proving<'a>(trie_backend: &'a TrieBackend<MemoryDB<Blake2Hasher>, Blake2Hasher>) -> ProvingBackend<'a, MemoryDB<Blake2Hasher>, Blake2Hasher> {
		ProvingBackend::new(trie_backend)
	}

	#[test]
	fn proof_is_empty_until_value_is_read() {
		let trie_backend = test_trie();
		assert!(test_proving(&trie_backend).extract_proof().is_empty());
	}

	#[test]
	fn proof_is_non_empty_after_value_is_read() {
		let trie_backend = test_trie();
		let backend = test_proving(&trie_backend);
		assert_eq!(backend.storage(b"key").unwrap(), Some(b"value".to_vec()));
		assert!(!backend.extract_proof().is_empty());
	}

	#[test]
	fn proof_is_invalid_when_does_not_contains_root() {
		use primitives::H256;
		assert!(create_proof_check_backend::<Blake2Hasher>(H256::from_low_u64_be(1), vec![]).is_err());
	}

	#[test]
	fn passes_throgh_backend_calls() {
		let trie_backend = test_trie();
		let proving_backend = test_proving(&trie_backend);
		assert_eq!(trie_backend.storage(b"key").unwrap(), proving_backend.storage(b"key").unwrap());
		assert_eq!(trie_backend.pairs(), proving_backend.pairs());

		let (trie_root, trie_mdb) = trie_backend.storage_root(::std::iter::empty());
		let (proving_root, proving_mdb) = proving_backend.storage_root(::std::iter::empty());
		assert_eq!(trie_root, proving_root);
		assert_eq!(trie_mdb.len(), proving_mdb.len());
		for ((k1,mut v1), (k2,mut v2)) in trie_mdb.into_iter().zip(proving_mdb.into_iter()) {
			assert_eq!(k1, k2);
			assert_eq!(v1.drain(), v2.drain());
		}
	}

	#[test]
	fn proof_recorded_and_checked() {
		let contents = (0..64).map(|i| (Vec::new(), vec![i], Some(vec![i]))).collect::<Vec<_>>();
		let in_memory = InMemory::<Blake2Hasher>::default();
		let in_memory = in_memory.update(contents);
		let in_memory_root = in_memory.storage_root(::std::iter::empty()).0;
		(0..64).for_each(|i| assert_eq!(in_memory.storage(&[i]).unwrap().unwrap(), vec![i]));

		let trie = in_memory.try_into_trie_backend().unwrap();
		let trie_root = trie.storage_root(::std::iter::empty()).0;
		assert_eq!(in_memory_root, trie_root);
		(0..64).for_each(|i| assert_eq!(trie.storage(&[i]).unwrap().unwrap(), vec![i]));

		let proving = ProvingBackend::new(&trie);
		assert_eq!(proving.storage(&[42]).unwrap().unwrap(), vec![42]);

		let proof = proving.extract_proof();

		let proof_check = create_proof_check_backend::<Blake2Hasher>(in_memory_root.into(), proof).unwrap();
		assert_eq!(proof_check.storage(&[42]).unwrap().unwrap(), vec![42]);
	}
}

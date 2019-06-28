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

//! State machine backends. These manage the code and storage of contracts.

use std::{error, fmt};
use std::cmp::Ord;
use std::collections::HashMap;
use std::marker::PhantomData;
use log::warn;
use hash_db::Hasher;
use crate::trie_backend::TrieBackend;
use crate::trie_backend_essence::TrieBackendStorage;
use trie::{TrieDBMut, TrieMut, MemoryDB, trie_root, child_trie_root, default_child_trie_root,	KeySpacedDBMut};
use primitives::child_trie::{KeySpace, ChildTrie, ChildTrieReadRef};

// see FIXME #2740 related to performance.
/// Type alias over a in memory change cache, with support for child trie.
/// This need to allow efficient access to value based on keys.
/// First field is top map, second field is existing child trie map,
/// third field is to be created child trie map.
pub type MapTransaction = (
	(HashMap<Vec<u8>, Vec<u8>>),
	HashMap<KeySpace, (HashMap<Vec<u8>, Vec<u8>>, ChildTrie)>,
);

// see FIXME #2740 related to performance.
/// Type alias over a list of memory change cache, with support for child trie.
/// This only need to contain an iterable set of values.
pub type VecTransaction = Vec<(Option<ChildTrie>, Vec<u8>, Option<Vec<u8>>)>;


/// A state backend is used to read state data and can have changes committed
/// to it.
///
/// The clone operation (if implemented) should be cheap.
pub trait Backend<H: Hasher> {
	/// An error type when fetching data is not possible.
	type Error: super::Error;

	/// Storage changes to be applied if committing.
	type Transaction: Consolidate + Default;

	/// Type of trie backend storage.
	type TrieBackendStorage: TrieBackendStorage<H>;

	/// Get keyed storage or None if there is nothing associated.
	fn storage(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error>;

	/// Get keyed storage value hash or None if there is nothing associated.
	fn storage_hash(&self, key: &[u8]) -> Result<Option<H::Out>, Self::Error> {
		self.storage(key).map(|v| v.map(|v| H::hash(&v)))
	}

	/// Get ChildTrie information or `None` if no child trie is defined for this key.
	fn child_trie(&self, storage_key: &[u8]) -> Result<Option<ChildTrie>, Self::Error> {
		let prefixed_key = ChildTrie::prefix_parent_key(storage_key);
		Ok(self.storage(&prefixed_key[..])?
			.and_then(|n| ChildTrie::decode_node_with_parent(&n[..], prefixed_key)))
	}

	/// Get keyed child storage or None if there is nothing associated.
	fn child_storage(&self, child_trie: ChildTrieReadRef, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error>;

	/// Get child keyed storage value hash or None if there is nothing associated.
	fn child_storage_hash(&self, child_trie: ChildTrieReadRef, key: &[u8]) -> Result<Option<H::Out>, Self::Error> {
		self.child_storage(child_trie, key).map(|v| v.map(|v| H::hash(&v)))
	}

	/// true if a key exists in storage.
	fn exists_storage(&self, key: &[u8]) -> Result<bool, Self::Error> {
		Ok(self.storage(key)?.is_some())
	}

	/// true if a key exists in child storage.
	fn exists_child_storage(&self, child_trie: ChildTrieReadRef, key: &[u8]) -> Result<bool, Self::Error> {
		Ok(self.child_storage(child_trie, key)?.is_some())
	}

	/// Retrieve all entries keys of child storage and call `f` for each of those keys.
	fn for_keys_in_child_storage<F: FnMut(&[u8])>(&self, child_trie: ChildTrieReadRef, f: F);

	/// Retrieve all entries keys of which start with the given prefix and
	/// call `f` for each of those keys.
	fn for_keys_with_prefix<F: FnMut(&[u8])>(&self, prefix: &[u8], f: F);

	/// Calculate the storage root, with given delta over what is already stored in
	/// the backend, and produce a "transaction" that can be used to commit.
	/// Does not include child storage updates.
	fn storage_root<I>(&self, delta: I) -> (H::Out, Self::Transaction)
	where
		I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>,
		H::Out: Ord;

	/// Calculate the child storage root, with given delta over what is already stored in
	/// the backend, and produce a "transaction" that can be used to commit. The second argument
	/// is true if child storage root equals default storage root.
	fn child_storage_root<I>(&self, child_trie: &ChildTrie, delta: I) -> (Vec<u8>, bool, Self::Transaction)
	where
		I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>,
		H::Out: Ord;

	/// Get all key/value pairs into a Vec.
	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)>;

	/// Get all keys with given prefix
	fn keys(&self, prefix: &[u8]) -> Vec<Vec<u8>> {
		let mut all = Vec::new();
		self.for_keys_with_prefix(prefix, |k| all.push(k.to_vec()));
		all
	}

	/// Get all keys of child storage with given prefix
	fn child_keys(&self, child_trie: ChildTrieReadRef, prefix: &[u8]) -> Vec<Vec<u8>> {
		let mut all = Vec::new();
		self.for_keys_in_child_storage(child_trie, |k| {
			if k.starts_with(prefix) {
				all.push(k.to_vec());
			}
		});
		all
	}

	/// Try convert into trie backend.
	fn as_trie_backend(&mut self) -> Option<&TrieBackend<Self::TrieBackendStorage, H>>;

	/// Calculate the storage root, with given delta over what is already stored
	/// in the backend, and produce a "transaction" that can be used to commit.
	/// Does include child storage updates.
	fn full_storage_root<I1, I2i, I2, TR>(
		&self,
		delta: I1,
		child_deltas: I2)
	-> (H::Out, Self::Transaction)
	where
		I1: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>,
		I2i: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>,
		TR: AsRef<ChildTrie>,
		I2: IntoIterator<Item=(TR, I2i)>,
		<H as Hasher>::Out: Ord,
	{
		let mut txs: Self::Transaction = Default::default();
		let mut child_roots: Vec<_> = Default::default();
		// child first
		for (child_trie, child_delta) in child_deltas {
			let (child_root, empty, child_txs) =
				self.child_storage_root(child_trie.as_ref(), child_delta);
			txs.consolidate(child_txs);
			if empty {
				child_roots.push((child_trie.as_ref().parent_trie().to_vec(), None));
			} else {
				child_roots.push(
					(child_trie.as_ref().parent_trie().to_vec(),
					Some(child_trie.as_ref().encoded_with_root(&child_root[..])))
				);
			}
		}
		let (root, parent_txs) = self.storage_root(
			delta.into_iter().chain(child_roots.into_iter())
		);
		txs.consolidate(parent_txs);
		(root, txs)
	}

}

/// Trait that allows consolidate two transactions together.
pub trait Consolidate {
	/// Consolidate two transactions into one.
	fn consolidate(&mut self, other: Self);
}

impl Consolidate for () {
	fn consolidate(&mut self, _: Self) {
		()
	}
}

impl Consolidate for VecTransaction {
	fn consolidate(&mut self, mut other: Self) {
		self.append(&mut other);
	}
}

impl<H: Hasher, KF: trie::KeyFunction<H>> Consolidate for trie::GenericMemoryDB<H, KF> {
	fn consolidate(&mut self, other: Self) {
		trie::GenericMemoryDB::consolidate(self, other)
	}
}

/// Error impossible.
// FIXME: use `!` type when stabilized. https://github.com/rust-lang/rust/issues/35121
#[derive(Debug)]
pub enum Void {}

impl fmt::Display for Void {
	fn fmt(&self, _: &mut fmt::Formatter) -> fmt::Result {
		match *self {}
	}
}

impl error::Error for Void {
	fn description(&self) -> &str { "unreachable error" }
}

/// In-memory backend. Fully recomputes tries on each commit but useful for
/// tests.
pub struct InMemory<H: Hasher> {
	inner: MapTransaction,
	trie: Option<TrieBackend<MemoryDB<H>, H>>,
	_hasher: PhantomData<H>,
}

impl<H: Hasher> Default for InMemory<H> {
	fn default() -> Self {
		InMemory {
			inner: Default::default(),
			trie: None,
			_hasher: PhantomData,
		}
	}
}

impl<H: Hasher> Clone for InMemory<H> {
	fn clone(&self) -> Self {
		InMemory {
			inner: self.inner.clone(),
			trie: None,
			_hasher: PhantomData,
		}
	}
}

impl<H: Hasher> PartialEq for InMemory<H> {
	fn eq(&self, other: &Self) -> bool {
		self.inner.eq(&other.inner)
	}
}

impl<H: Hasher> InMemory<H> {
	/// Copy the state, with applied updates
	pub fn update(&self, changes: <Self as Backend<H>>::Transaction) -> Self {
		// costy clone
		let mut inner = self.inner.clone();

		for (child_trie, key, val) in changes {
			if let Some(child_trie) = child_trie {
				let mut entry = inner.1.entry(child_trie.keyspace().clone())
						.or_insert_with(|| (Default::default(), child_trie.clone()));
				match val {
					Some(v) => {
						entry.0.insert(key, v);
						// very costy clone here for update of value: could be change
						entry.1 = child_trie;
					},
					None => {
						entry.0.remove(&key);
					},
				}
			} else {
				match val {
					Some(v) => { let _ = inner.0.insert(key, v); },
					None => { let _ = inner.0.remove(&key); },
				}
			}

		}

		inner.into()
	}

}

impl<H: Hasher> From<MapTransaction> for InMemory<H> {
	fn from(inner: MapTransaction) -> Self {
		InMemory {
			inner: inner,
			trie: None,
			_hasher: PhantomData,
		}
	}
}

impl<H: Hasher> From<HashMap<Vec<u8>, Vec<u8>>> for InMemory<H> {
	fn from(inner: HashMap<Vec<u8>, Vec<u8>>) -> Self {
		InMemory {
			inner: (inner, Default::default()),
			trie: None,
			_hasher: PhantomData,
		}
	}
}

impl<H: Hasher> From<VecTransaction> for InMemory<H> {
	fn from(inner: VecTransaction) -> Self {
		let mut expanded: MapTransaction = Default::default();
		for (child_key, key, value) in inner {
			if let Some(value) = value {
				if let Some(child_trie) = child_key {
					let mut entry = expanded.1.entry(child_trie.keyspace().clone())
							.or_insert_with(|| (Default::default(), child_trie.clone()));
					entry.0.insert(key, value);
					entry.1 = child_trie;
				} else {
					expanded.0.insert(key, value);
				}
			}
		}
		expanded.into()
	}
}

impl super::Error for Void {}

#[cfg(test)]
impl<H: Hasher> InMemory<H> {
	/// Child trie in memory content iterator.
	pub fn child_storage_child_trie(&self) -> impl Iterator<Item=&ChildTrie> {
		self.inner.1.iter().map(|item| &(item.1).1)
	}
}

impl<H: Hasher> Backend<H> for InMemory<H> {
	type Error = Void;
	type Transaction = VecTransaction;
	type TrieBackendStorage = MemoryDB<H>;

	fn storage(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		Ok(self.inner.0.get(key).map(Clone::clone))
	}

	fn child_storage(&self, child_trie: ChildTrieReadRef, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		Ok(self.inner.1.get(child_trie.keyspace()).and_then(|map| map.0.get(key).map(Clone::clone)))
	}

	fn exists_storage(&self, key: &[u8]) -> Result<bool, Self::Error> {
		Ok(self.storage(key)?.is_some())
	}

	fn for_keys_with_prefix<F: FnMut(&[u8])>(&self, prefix: &[u8], f: F) {
		self.inner.0.keys().filter(|key| key.starts_with(prefix)).map(|k| &**k).for_each(f);
	}

	fn for_keys_in_child_storage<F: FnMut(&[u8])>(&self, child_trie: ChildTrieReadRef, mut f: F) {
		self.inner.1.get(child_trie.keyspace()).map(|m| m.0.keys().for_each(|k| f(&k)));
	}

	fn storage_root<I>(&self, delta: I) -> (H::Out, Self::Transaction)
	where
		I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>,
		<H as Hasher>::Out: Ord,
	{
		let existing_pairs = self.inner.0.iter().map(|(k, v)| (k.clone(), Some(v.clone())));

		let transaction: Vec<_> = delta.into_iter().collect();
		let map_input = existing_pairs.chain(transaction.iter().cloned())
			.collect::<HashMap<_, _>>();

		let root = trie_root::<H, _, _, _>(map_input
			.into_iter()
			.filter_map(|(k, maybe_val)| maybe_val.map(|val| (k, val)))
		);

		let full_transaction = transaction.into_iter().map(|(k, v)| (None, k, v)).collect();

		(root, full_transaction)
	}

	fn child_storage_root<I>(&self, child_trie: &ChildTrie, delta: I) -> (Vec<u8>, bool, Self::Transaction)
	where
		I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>,
		H::Out: Ord
	{
		let transaction: Vec<_> = delta.into_iter().collect();
		// all content is clone with this method, avoiding it would require changing
		// the prototype (having a function for calculating root on reference and
		// one for getting transaction while dropping value.
		let existing_pairs = self.inner.1.get(
			child_trie.keyspace()
		).into_iter().flat_map(|map| map.0.iter().map(|(k, v)| (k.clone(), Some(v.clone()))));
		let root = child_trie_root::<H, _, _, _>(
			existing_pairs.chain(transaction.iter().cloned())
				.collect::<HashMap<_, _>>()
				.into_iter()
				.filter_map(|(k, maybe_val)| maybe_val.map(|val| (k, val)))
		);

		// note that the child trie is from parameter, this is allowed because update of child
		// trie should be done by the same child trie instance; can prove problematic?
		let full_transaction = transaction.into_iter().map(|(k, v)| (Some(child_trie.clone()), k, v)).collect();

		let is_default = root == default_child_trie_root::<H>();

		(root, is_default, full_transaction)
	}

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		self.inner.0.iter().map(|(k, v)| (k.clone(), v.clone())).collect()
	}

	fn keys(&self, prefix: &[u8]) -> Vec<Vec<u8>> {
		self.inner.0.keys().filter(|k| k.starts_with(prefix)).cloned().collect()
	}

	fn as_trie_backend(&mut self)-> Option<&TrieBackend<Self::TrieBackendStorage, H>> {
		// Warning tihs do not use keyspace for child trie, that is not an issue unless
		// the memorydb gets incorectly use to fead keyvalue database.
		let mut mdb = MemoryDB::default();
		let mut new_child_roots = Vec::new();
		let (root_map, child_map) = std::mem::replace(&mut self.inner, Default::default());

		for (_k, (map, child_trie)) in child_map.into_iter() {
			let ch = insert_into_memory_db::<H, _>(
				&mut mdb,
				map.into_iter(),
				Some(child_trie.node_ref()),
			)?;
			new_child_roots.push((
				child_trie.parent_trie().to_vec(),
				child_trie.encoded_with_root(ch.as_ref())));
		}
		// root handling
		let root = insert_into_memory_db::<H, _>(
			&mut mdb,
			root_map.into_iter().chain(new_child_roots.into_iter()),
			None,
		)?;
		self.trie = Some(TrieBackend::new(mdb, root));
		self.trie.as_ref()
	}
}

/// Insert input pairs into memory db.
pub(crate) fn insert_into_memory_db<H, I>(
	mdb: &mut MemoryDB<H>,
	input: I,
	child_trie: Option<ChildTrieReadRef>
) -> Option<H::Out>
	where
		H: Hasher,
		I: IntoIterator<Item=(Vec<u8>, Vec<u8>)>,
{
	let mut root = <H as Hasher>::Out::default();
	{
		if let Some(child_trie) = child_trie.as_ref() {
			let mut mdb = KeySpacedDBMut::new(&mut *mdb, child_trie.keyspace());
			let mut trie = TrieDBMut::<H>::new(&mut mdb, &mut root);
			for (key, value) in input {
				if let Err(e) = trie.insert(&key, &value) {
					warn!(target: "trie", "Failed to write to trie: {}", e);
					return None;
				}
			}
		} else {
			let mut trie = TrieDBMut::<H>::new(mdb, &mut root);
			for (key, value) in input {
				if let Err(e) = trie.insert(&key, &value) {
					warn!(target: "trie", "Failed to write to trie: {}", e);
					return None;
				}
			}
		}
	}

	Some(root)
}

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

//! State machine in memory backend.

use crate::{
	StorageKey, StorageValue, StorageCollection,
	trie_backend::TrieBackend,
};
use std::{collections::{BTreeMap, HashMap}};
use hash_db::HasherHybrid as Hasher;
use sp_trie::{
	MemoryDB, TrieMut,
	trie_types::TrieDBMut,
	TrieConfiguration, TrieHash,
};
use codec::Codec;
use sp_core::storage::{ChildInfo, Storage};

/// Insert input pairs into memory db.
fn insert_into_memory_db<H, I>(mut root: H::Out, mdb: &mut MemoryDB<H>, input: I) -> H::Out
where
	H: Hasher,
	I: IntoIterator<Item=(StorageKey, Option<StorageValue>)>,
{
	{
		let mut trie = if root == Default::default() {
			TrieDBMut::<H>::new(mdb, &mut root)
		} else {
			TrieDBMut::<H>::from_existing(mdb, &mut root).unwrap()
		};
		for (key, value) in input {
			if let Err(e) = match value {
				Some(value) => {
					trie.insert(&key, &value)
				},
				None => {
					trie.remove(&key)
				},
			}  {
				panic!("Failed to write to trie: {}", e);
			}
		}
		trie.commit();
	}
	root
}

/// Create a new empty instance of in-memory backend.
pub fn new_in_mem<T: TrieConfiguration>() -> TrieBackend<MemoryDB<T::Hash>, T>
where
	TrieHash<T>: Codec + Ord,
{
	let db = MemoryDB::default();
	let mut backend = TrieBackend::new(db, Default::default());
	backend.insert(std::iter::empty());
	backend
}

impl<T> TrieBackend<MemoryDB<T::Hash>, T>
where
	T: TrieConfiguration,
	TrieHash<T>: Codec + Ord,
{
	/// Copy the state, with applied updates
	pub fn update<
		I: IntoIterator<Item = (Option<ChildInfo>, StorageCollection)>
	>(
		&self,
		changes: I,
	) -> Self {
		let mut clone = self.clone();
		clone.insert(changes);
		clone
	}

	/// Insert values into backend trie.
	pub fn insert<
		I: IntoIterator<Item = (Option<ChildInfo>, StorageCollection)>
	>(
		&mut self,
		changes: I,
	) {
		let mut new_child_roots = Vec::new();
		let mut root_map = None;
		let root = self.root().clone();
		for (child_info, map) in changes {
			if let Some(child_info) = child_info.as_ref() {
				let prefix_storage_key = child_info.prefixed_storage_key();
				let ch = insert_into_memory_db::<T::Hash, _>(root, self.backend_storage_mut(), map.clone().into_iter());
				new_child_roots.push((prefix_storage_key.into_inner(), Some(ch.as_ref().into())));
			} else {
				root_map = Some(map);
			}
		}

		let root = match root_map {
			Some(map) => insert_into_memory_db::<T::Hash, _>(
				root,
				self.backend_storage_mut(),
				map.clone().into_iter().chain(new_child_roots.into_iter()),
			),
			None => insert_into_memory_db::<T::Hash, _>(
				root,
				self.backend_storage_mut(),
				new_child_roots.into_iter(),
			),
		};
		self.essence.set_root(root);
	}

	/// Merge trie nodes into this backend.
	pub fn update_backend(&self, root: TrieHash<T>, changes: MemoryDB<T::Hash>) -> Self {
		let mut clone = self.backend_storage().clone();
		clone.consolidate(changes);
		Self::new(clone, root)
	}

	/// Compare with another in-memory backend.
	pub fn eq(&self, other: &Self) -> bool {
		self.root() == other.root()
	}
}

impl<T> Clone for TrieBackend<MemoryDB<T::Hash>, T>
where
	T: TrieConfiguration,
	TrieHash<T>: Codec + Ord,
{
	fn clone(&self) -> Self {
		TrieBackend::new(self.backend_storage().clone(), self.root().clone())
	}
}

impl<T> Default for TrieBackend<MemoryDB<T::Hash>, T>
where
	T: TrieConfiguration,
	TrieHash<T>: Codec + Ord,
{
	fn default() -> Self {
		new_in_mem()
	}
}

impl<T> From<HashMap<Option<ChildInfo>, BTreeMap<StorageKey, StorageValue>>>
	for TrieBackend<MemoryDB<T::Hash>, T>
where
	T: TrieConfiguration,
	TrieHash<T>: Codec + Ord,
{
	fn from(inner: HashMap<Option<ChildInfo>, BTreeMap<StorageKey, StorageValue>>) -> Self {
		let mut backend = new_in_mem();
		backend.insert(inner.into_iter().map(|(k, m)| (k, m.into_iter().map(|(k, v)| (k, Some(v))).collect())));
		backend
	}
}

impl<T> From<Storage> for TrieBackend<MemoryDB<T::Hash>, T>
where
	T: TrieConfiguration,
	TrieHash<T>: Codec + Ord,
{
	fn from(inners: Storage) -> Self {
		let mut inner: HashMap<Option<ChildInfo>, BTreeMap<StorageKey, StorageValue>>
			= inners.children_default.into_iter().map(|(_k, c)| (Some(c.child_info), c.data)).collect();
		inner.insert(None, inners.top);
		inner.into()
	}
}

impl<T> From<BTreeMap<StorageKey, StorageValue>> for TrieBackend<MemoryDB<T::Hash>, T>
where
	T: TrieConfiguration,
	TrieHash<T>: Codec + Ord,
{
	fn from(inner: BTreeMap<StorageKey, StorageValue>) -> Self {
		let mut expanded = HashMap::new();
		expanded.insert(None, inner);
		expanded.into()
	}
}

impl<T> From<Vec<(Option<ChildInfo>, StorageCollection)>>
	for TrieBackend<MemoryDB<T::Hash>, T>
where
	T: TrieConfiguration,
	TrieHash<T>: Codec + Ord,
{
	fn from(
		inner: Vec<(Option<ChildInfo>, StorageCollection)>,
	) -> Self {
		let mut expanded: HashMap<Option<ChildInfo>, BTreeMap<StorageKey, StorageValue>>
			= HashMap::new();
		for (child_info, key_values) in inner {
			let entry = expanded.entry(child_info).or_default();
			for (key, value) in key_values {
				if let Some(value) = value {
					entry.insert(key, value);
				}
			}
		}
		expanded.into()
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_trie::Layout;
	use crate::backend::Backend;

	type BlakeTwo256 = crate::RefHasher<sp_core::Blake2Hasher>;

	/// Assert in memory backend with only child trie keys works as trie backend.
	#[test]
	fn in_memory_with_child_trie_only() {
		let storage = new_in_mem::<Layout<BlakeTwo256>>();
		let child_info = ChildInfo::new_default(b"1");
		let child_info = &child_info;
		let storage = storage.update(
			vec![(
				Some(child_info.clone()),
				vec![(b"2".to_vec(), Some(b"3".to_vec()))]
			)]
		);
		let trie_backend = &storage;
		assert_eq!(trie_backend.child_storage(child_info, b"2").unwrap(),
			Some(b"3".to_vec()));
		let storage_key = child_info.prefixed_storage_key();
		assert!(trie_backend.storage(storage_key.as_slice()).unwrap().is_some());
	}
}

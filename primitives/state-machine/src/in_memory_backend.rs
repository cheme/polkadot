// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! State machine in memory backend.

use crate::{
	StorageKey, StorageValue, StorageCollection, trie_backend::TrieBackend, backend::Backend,
};
use sp_std::collections::btree_map::BTreeMap;
#[cfg(feature = "std")]
use std::collections::HashMap;
use hash_db::Hasher;
use sp_trie::{MemoryDB, empty_trie_root, Layout};
use codec::Codec;
use sp_core::storage::ChildInfo;
#[cfg(feature = "std")]
use sp_core::storage::Storage;
use sp_std::vec::Vec;

/// Base collection for key values backend.
///
/// This does not support child collection.
/// TODO consider inner trait without child.
#[derive(Default, Clone, Debug, Eq, PartialEq)]
pub struct KVInMemCollection(pub BTreeMap<Vec<u8>, Vec<u8>>);

impl crate::kv_backend::KVBackend for KVInMemCollection {
	fn storage(
		&self,
		child: Option<&ChildInfo>,
		key: &[u8],
	) -> Result<Option<Vec<u8>>, crate::DefaultError> {
		assert!(child.is_none());
		Ok(self.0.get(key).cloned())
	}

	fn next_storage(
		&self,
		child: Option<&ChildInfo>,
		key: &[u8],
	) -> Result<Option<(Vec<u8>, Vec<u8>)>, crate::DefaultError> {
		assert!(child.is_none());
		use sp_std::ops::Bound;
		let range = (Bound::Excluded(key), Bound::Unbounded);
		Ok(self.0.range::<[u8], _>(range).next().map(|(k, v)| (k.clone(), v.clone())))
	}
}

/// Base collection for key values backend.
///
/// This does not support child collection.
///
/// A boolean is paired with value to indicate if next value is in collection.
/// (false for a missing value)
#[derive(Default, Clone, Debug, Eq, PartialEq)]
pub struct PartialKVInMemCollection(pub BTreeMap<Vec<u8>, (Vec<u8>, bool)>);

impl crate::kv_backend::KVBackend for PartialKVInMemCollection {
	fn storage(
		&self,
		child: Option<&ChildInfo>,
		key: &[u8],
	) -> Result<Option<Vec<u8>>, crate::DefaultError> {
		assert!(child.is_none());
		Ok(self.0.get(key).map(|value_next| value_next.0.clone()))
	}

	fn next_storage(
		&self,
		child: Option<&ChildInfo>,
		key: &[u8],
	) -> Result<Option<(Vec<u8>, Vec<u8>)>, crate::DefaultError> {
		assert!(child.is_none());
		use sp_std::ops::Bound;
		let range = (Bound::Excluded(key), Bound::Unbounded);
		let next = self.0.range::<[u8], _>(range).next();
		if let Some((_, (_, false))) = next {
			return Err(crate::default_error("Incomplete base data."));
		}
		Ok(next.map(|(k, (v, _))| (k.clone(), v.clone())))
	}
}

/// In memory alternative key value backend to use
/// instead of a trie backend when operation do not need
/// trie usage.
pub type KVInMem = KVInMemWithChildren<KVInMemCollection>;

/// In memory alternative key value backend to use
/// instead of a trie backend when operation do not need
/// trie usage.
/// This allows collection with only a subset of the key
/// existing keys (proof support).
pub type PartialKVInMem = KVInMemWithChildren<PartialKVInMemCollection>;

/// Struct dispatching `KVBackend` into multiple children
/// implementation.
#[derive(Default, Clone, Debug, Eq, PartialEq)]
pub struct KVInMemWithChildren<B> {
	pub top: B,
	pub children: BTreeMap<ChildInfo, B>,
}

impl<B: crate::kv_backend::KVBackend> crate::kv_backend::KVBackend for KVInMemWithChildren<B> {
	fn storage(
		&self,
		child: Option<&ChildInfo>,
		key: &[u8],
	) -> Result<Option<Vec<u8>>, crate::DefaultError> {
		Ok(if let Some(child) = child {
			if let Some(child) = self.children.get(child) {
				child.storage(None, key)?
			} else {
				None
			}
		} else {
			self.top.storage(None, key)?
		})
	}

	fn next_storage(
		&self,
		child: Option<&ChildInfo>,
		key: &[u8],
	) -> Result<Option<(Vec<u8>, Vec<u8>)>, crate::DefaultError> {
		Ok(if let Some(child) = child {
			if let Some(child) = self.children.get(child) {
				child.next_storage(None, key)?
			} else {
				None
			}
		} else {
			self.top.next_storage(None, key)?
		})
	}
}

/// Create a new empty instance of in-memory backend.
pub fn new_in_mem<H: Hasher>() -> TrieBackend<MemoryDB<H>, H>
where
	H::Out: Codec + Ord,
{
	let db = MemoryDB::default();
	let mut backend = TrieBackend::new(
		db,
		empty_trie_root::<Layout<H>>(),
		None,
	);
	backend.insert(sp_std::iter::empty());
	backend
}

impl<H: Hasher> TrieBackend<MemoryDB<H>, H>
where
	H::Out: Codec + Ord,
{
	/// Copy the state, with applied updates
	pub fn update<
		T: IntoIterator<Item = (Option<ChildInfo>, StorageCollection)>
	>(
		&self,
		changes: T,
	) -> Self {
		let mut clone = self.clone();
		clone.insert(changes);
		clone
	}

	/// Insert values into backend trie.
	pub fn insert<
		T: IntoIterator<Item = (Option<ChildInfo>, StorageCollection)>
	>(
		&mut self,
		changes: T,
	) {
		let (top, child) = changes.into_iter().partition::<Vec<_>, _>(|v| v.0.is_none());
		let (root, transaction) = self.full_storage_root(
			top.iter().map(|(_, v)| v).flatten().map(|(k, v)| (&k[..], v.as_deref())),
			child.iter()
				.filter_map(|v|
					v.0.as_ref().map(|c| (c, v.1.iter().map(|(k, v)| (&k[..], v.as_deref()))))
				),
		);

		self.apply_transaction(root, transaction);
	}

	/// Merge trie nodes into this backend.
	pub fn update_backend(&self, root: H::Out, changes: MemoryDB<H>) -> Self {
		let mut clone = self.backend_storage().clone();
		clone.consolidate(changes);
		Self::new(
			clone,
			root,
			self.alternative.clone(),
		)
	}

	/// Apply the given transaction to this backend and set the root to the given value.
	pub fn apply_transaction(&mut self, root: H::Out, transaction: MemoryDB<H>) {
		self.backend_storage_mut().consolidate(transaction);
		self.essence.set_root(root);
	}

	/// Compare with another in-memory backend.
	pub fn eq(&self, other: &Self) -> bool {
		self.root() == other.root()
	}
}

impl<H: Hasher> Clone for TrieBackend<MemoryDB<H>, H>
where
	H::Out: Codec + Ord,
{
	fn clone(&self) -> Self {
		TrieBackend::new(
			self.backend_storage().clone(),
			self.root().clone(),
			self.alternative.clone(),
		)
	}
}

impl<H: Hasher> Default for TrieBackend<MemoryDB<H>, H>
where
	H::Out: Codec + Ord,
{
	fn default() -> Self {
		new_in_mem()
	}
}

#[cfg(feature = "std")]
impl<H: Hasher> From<HashMap<Option<ChildInfo>, BTreeMap<StorageKey, StorageValue>>>
	for TrieBackend<MemoryDB<H>, H>
where
	H::Out: Codec + Ord,
{
	fn from(inner: HashMap<Option<ChildInfo>, BTreeMap<StorageKey, StorageValue>>) -> Self {
		let mut backend = new_in_mem();
		backend.insert(
			inner.into_iter().map(|(k, m)| (k, m.into_iter().map(|(k, v)| (k, Some(v))).collect())),
		);
		backend
	}
}

#[cfg(feature = "std")]
impl<H: Hasher> From<Storage> for TrieBackend<MemoryDB<H>, H>
where
	H::Out: Codec + Ord,
{
	fn from(inners: Storage) -> Self {
		let mut inner: HashMap<Option<ChildInfo>, BTreeMap<StorageKey, StorageValue>>
			= inners.children_default.into_iter().map(|(_k, c)| (Some(c.child_info), c.data)).collect();
		inner.insert(None, inners.top);
		inner.into()
	}
}

#[cfg(feature = "std")]
impl<H: Hasher> From<BTreeMap<StorageKey, StorageValue>> for TrieBackend<MemoryDB<H>, H>
where
	H::Out: Codec + Ord,
{
	fn from(inner: BTreeMap<StorageKey, StorageValue>) -> Self {
		let mut expanded = HashMap::new();
		expanded.insert(None, inner);
		expanded.into()
	}
}

#[cfg(feature = "std")]
impl<H: Hasher> From<Vec<(Option<ChildInfo>, StorageCollection)>>
	for TrieBackend<MemoryDB<H>, H>
where
	H::Out: Codec + Ord,
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
	use sp_runtime::traits::BlakeTwo256;
	use crate::backend::Backend;

	/// Assert in memory backend with only child trie keys works as trie backend.
	#[test]
	fn in_memory_with_child_trie_only() {
		let storage = new_in_mem::<BlakeTwo256>();
		let child_info = ChildInfo::new_default(b"1");
		let child_info = &child_info;
		let mut storage = storage.update(
			vec![(
				Some(child_info.clone()),
				vec![(b"2".to_vec(), Some(b"3".to_vec()))]
			)]
		);
		let trie_backend = storage.as_trie_backend().unwrap();
		assert_eq!(trie_backend.child_storage(child_info, b"2").unwrap(),
			Some(b"3".to_vec()));
		let storage_key = child_info.prefixed_storage_key();
		assert!(trie_backend.storage(storage_key.as_slice()).unwrap().is_some());
	}

	#[test]
	fn insert_multiple_times_child_data_works() {
		let mut storage = new_in_mem::<BlakeTwo256>();
		let child_info = ChildInfo::new_default(b"1");

		storage.insert(vec![(Some(child_info.clone()), vec![(b"2".to_vec(), Some(b"3".to_vec()))])]);
		storage.insert(vec![(Some(child_info.clone()), vec![(b"1".to_vec(), Some(b"3".to_vec()))])]);

		assert_eq!(storage.child_storage(&child_info, &b"2"[..]), Ok(Some(b"3".to_vec())));
		assert_eq!(storage.child_storage(&child_info, &b"1"[..]), Ok(Some(b"3".to_vec())));
	}
}

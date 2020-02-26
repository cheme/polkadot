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

//! Basic implementation for Externalities.

use std::{
	collections::BTreeMap, any::{TypeId, Any}, iter::FromIterator, ops::Bound
};
use crate::{Backend, InMemoryBackend, StorageKey, StorageValue};
use hash_db::Hasher;
use sp_trie::{TrieConfiguration, empty_child_trie_root};
use sp_trie::trie_types::Layout;
use sp_core::{
	storage::{
		well_known_keys::is_child_storage_key, Storage,
		ChildInfo, StorageChild,
	},
	traits::Externalities, Blake2Hasher,
};
use log::warn;
use codec::Encode;

/// Simple Map-based Externalities impl.
#[derive(Debug)]
pub struct BasicExternalities {
	inner: Storage,
}

impl BasicExternalities {
	/// Create a new instance of `BasicExternalities`
	pub fn new(inner: Storage) -> Self {
		BasicExternalities { inner }
	}

	/// Insert key/value
	pub fn insert(&mut self, k: StorageKey, v: StorageValue) -> Option<StorageValue> {
		self.inner.top.insert(k, v)
	}

	/// Consume self and returns inner storages
	pub fn into_storages(self) -> Storage {
		self.inner
	}

	/// Execute the given closure `f` with the externalities set and initialized with `storage`.
	///
	/// Returns the result of the closure and updates `storage` with all changes.
	pub fn execute_with_storage<R>(
		storage: &mut sp_core::storage::Storage,
		f: impl FnOnce() -> R,
	) -> R {
		let mut ext = Self { inner: Storage {
			top: std::mem::replace(&mut storage.top, Default::default()),
			children_default: std::mem::replace(&mut storage.children_default, Default::default()),
		}};

		let r = ext.execute_with(f);

		*storage = ext.into_storages();

		r
	}

	/// Execute the given closure while `self` is set as externalities.
	///
	/// Returns the result of the given closure.
	pub fn execute_with<R>(&mut self, f: impl FnOnce() -> R) -> R {
		sp_externalities::set_and_run_with_externalities(self, f)
	}
}

impl PartialEq for BasicExternalities {
	fn eq(&self, other: &BasicExternalities) -> bool {
		self.inner.top.eq(&other.inner.top)
			&& self.inner.children_default.eq(&other.inner.children_default)
	}
}

impl FromIterator<(StorageKey, StorageValue)> for BasicExternalities {
	fn from_iter<I: IntoIterator<Item=(StorageKey, StorageValue)>>(iter: I) -> Self {
		let mut t = Self::default();
		t.inner.top.extend(iter);
		t
	}
}

impl Default for BasicExternalities {
	fn default() -> Self { Self::new(Default::default()) }
}

impl From<BTreeMap<StorageKey, StorageValue>> for BasicExternalities {
	fn from(hashmap: BTreeMap<StorageKey, StorageValue>) -> Self {
		BasicExternalities { inner: Storage {
			top: hashmap,
			children_default: Default::default(),
		}}
	}
}

impl Externalities for BasicExternalities {
	fn storage(&self, key: &[u8]) -> Option<StorageValue> {
		self.inner.top.get(key).cloned()
	}

	fn storage_hash(&self, key: &[u8]) -> Option<Vec<u8>> {
		self.storage(key).map(|v| Blake2Hasher::hash(&v).encode())
	}

	fn original_storage(&self, key: &[u8]) -> Option<StorageValue> {
		self.storage(key)
	}

	fn original_storage_hash(&self, key: &[u8]) -> Option<Vec<u8>> {
		self.storage_hash(key)
	}

	fn child_storage(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Option<StorageValue> {
		self.inner.children_default.get(child_info.storage_key())
			.and_then(|child| child.data.get(key)).cloned()
	}

	fn child_storage_hash(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Option<Vec<u8>> {
		self.child_storage(child_info, key).map(|v| Blake2Hasher::hash(&v).encode())
	}

	fn original_child_storage_hash(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Option<Vec<u8>> {
		self.child_storage_hash(child_info, key)
	}

	fn original_child_storage(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Option<StorageValue> {
		Externalities::child_storage(self, child_info, key)
	}

	fn next_storage_key(&self, key: &[u8]) -> Option<StorageKey> {
		let range = (Bound::Excluded(key), Bound::Unbounded);
		self.inner.top.range::<[u8], _>(range).next().map(|(k, _)| k).cloned()
	}

	fn next_child_storage_key(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Option<StorageKey> {
		let range = (Bound::Excluded(key), Bound::Unbounded);
		self.inner.children_default.get(child_info.storage_key())
			.and_then(|child| child.data.range::<[u8], _>(range).next().map(|(k, _)| k).cloned())
	}

	fn place_storage(&mut self, key: StorageKey, maybe_value: Option<StorageValue>) {
		if is_child_storage_key(&key) {
			warn!(target: "trie", "Refuse to set child storage key via main storage");
			return;
		}

		match maybe_value {
			Some(value) => { self.inner.top.insert(key, value); }
			None => { self.inner.top.remove(&key); }
		}
	}

	fn place_child_storage(
		&mut self,
		child_info: &ChildInfo,
		key: StorageKey,
		value: Option<StorageValue>,
	) {
		let child_map = self.inner.children_default.entry(child_info.storage_key().to_vec())
			.or_insert_with(|| StorageChild {
				data: Default::default(),
				child_info: child_info.to_owned(),
			});
		if let Some(value) = value {
			child_map.data.insert(key, value);
		} else {
			child_map.data.remove(&key);
		}
	}

	fn kill_child_storage(
		&mut self,
		child_info: &ChildInfo,
	) {
		self.inner.children_default.remove(child_info.storage_key());
	}

	fn clear_prefix(&mut self, prefix: &[u8]) {
		if is_child_storage_key(prefix) {
			warn!(
				target: "trie",
				"Refuse to clear prefix that is part of child storage key via main storage"
			);
			return;
		}

		let to_remove = self.inner.top.range::<[u8], _>((Bound::Included(prefix), Bound::Unbounded))
			.map(|(k, _)| k)
			.take_while(|k| k.starts_with(prefix))
			.cloned()
			.collect::<Vec<_>>();

		for key in to_remove {
			self.inner.top.remove(&key);
		}
	}

	fn clear_child_prefix(
		&mut self,
		child_info: &ChildInfo,
		prefix: &[u8],
	) {
		if let Some(child) = self.inner.children_default.get_mut(child_info.storage_key()) {
			let to_remove = child.data.range::<[u8], _>((Bound::Included(prefix), Bound::Unbounded))
				.map(|(k, _)| k)
				.take_while(|k| k.starts_with(prefix))
				.cloned()
				.collect::<Vec<_>>();

			for key in to_remove {
				child.data.remove(&key);
			}
		}
	}

	fn chain_id(&self) -> u64 { 42 }

	fn storage_root(&mut self) -> Vec<u8> {
		let mut top = self.inner.top.clone();
		let prefixed_keys: Vec<_> = self.inner.children_default.iter().map(|(_k, v)| {
			(v.child_info.prefixed_storage_key(), v.child_info.clone())
		}).collect();
		// Single child trie implementation currently allows using the same child
		// empty root for all child trie. Using null storage key until multiple
		// type of child trie support.
		let empty_hash = empty_child_trie_root::<Layout<Blake2Hasher>>();
		for (prefixed_storage_key, child_info) in prefixed_keys {
			let child_root = self.child_storage_root(&child_info);
			if &empty_hash[..] == &child_root[..] {
				top.remove(prefixed_storage_key.as_slice());
			} else {
				top.insert(prefixed_storage_key, child_root);
			}
		}

		Layout::<Blake2Hasher>::trie_root(self.inner.top.clone()).as_ref().into()
	}

	fn child_storage_root(
		&mut self,
		child_info: &ChildInfo,
	) -> Vec<u8> {
		if let Some(child) = self.inner.children_default.get(child_info.storage_key()) {
			let delta = child.data.clone().into_iter().map(|(k, v)| (k, Some(v)));

			InMemoryBackend::<Blake2Hasher>::default()
				.child_storage_root(&child.child_info, delta).0
		} else {
			empty_child_trie_root::<Layout<Blake2Hasher>>()
		}.encode()
	}

	fn storage_changes_root(&mut self, _parent: &[u8]) -> Result<Option<Vec<u8>>, ()> {
		Ok(None)
	}

	fn wipe(&mut self) {}

	fn commit(&mut self) {}
}

impl sp_externalities::ExtensionStore for BasicExternalities {
	fn extension_by_type_id(&mut self, _: TypeId) -> Option<&mut dyn Any> {
		warn!("Extensions are not supported by `BasicExternalities`.");
		None
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_core::map;
	use sp_core::storage::{Storage, StorageChild};
	use sp_core::storage::well_known_keys::CODE;
	use hex_literal::hex;

	#[test]
	fn commit_should_work() {
		let mut ext = BasicExternalities::default();
		ext.set_storage(b"doe".to_vec(), b"reindeer".to_vec());
		ext.set_storage(b"dog".to_vec(), b"puppy".to_vec());
		ext.set_storage(b"dogglesworth".to_vec(), b"cat".to_vec());
		const ROOT: [u8; 32] = hex!("39245109cef3758c2eed2ccba8d9b370a917850af3824bc8348d505df2c298fa");

		assert_eq!(&ext.storage_root()[..], &ROOT);
	}

	#[test]
	fn set_and_retrieve_code() {
		let mut ext = BasicExternalities::default();

		let code = vec![1, 2, 3];
		ext.set_storage(CODE.to_vec(), code.clone());

		assert_eq!(&ext.storage(CODE).unwrap(), &code);
	}

	#[test]
	fn children_works() {
		let child_info = ChildInfo::new_default(b"storage_key");
		let child_info = &child_info;
		let mut ext = BasicExternalities::new(Storage {
			top: Default::default(),
			children_default: map![
				child_info.storage_key().to_vec() => StorageChild {
					data: map![	b"doe".to_vec() => b"reindeer".to_vec()	],
					child_info: child_info.clone(),
				}
			]
		});

		assert_eq!(ext.child_storage(child_info, b"doe"), Some(b"reindeer".to_vec()));

		ext.set_child_storage(child_info, b"dog".to_vec(), b"puppy".to_vec());
		assert_eq!(ext.child_storage(child_info, b"dog"), Some(b"puppy".to_vec()));

		ext.clear_child_storage(child_info, b"dog");
		assert_eq!(ext.child_storage(child_info, b"dog"), None);

		ext.kill_child_storage(child_info);
		assert_eq!(ext.child_storage(child_info, b"doe"), None);
	}

	#[test]
	fn basic_externalities_is_empty() {
		// Make sure no values are set by default in `BasicExternalities`.
		let storage = BasicExternalities::new(Default::default()).into_storages();
		assert!(storage.top.is_empty());
		assert!(storage.children_default.is_empty());
	}
}

// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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

//! Test implementation for Externalities.

use std::any::{Any, TypeId};
use codec::Decode;
use sp_trie::{TrieConfiguration, TrieHash};
use crate::{
	backend::Backend, OverlayedChanges, StorageTransactionCache, ext::Ext, InMemoryBackend,
	StorageKey, StorageValue,
	changes_trie::{
		Configuration as ChangesTrieConfiguration,
		InMemoryStorage as ChangesTrieInMemoryStorage,
		BlockNumber as ChangesTrieBlockNumber,
		State as ChangesTrieState,
	},
};
use sp_core::{
	offchain::storage::OffchainOverlayedChanges,
	storage::{
		well_known_keys::{CHANGES_TRIE_CONFIG, CODE, HEAP_PAGES, is_child_storage_key},
		Storage,
	},
};
use codec::Encode;
use sp_externalities::{Extensions, Extension};

/// Simple HashMap-based Externalities impl.
pub struct TestExternalities<T, N = u64>
where
	N: ChangesTrieBlockNumber,
	T: TrieConfiguration,
	TrieHash<T>: codec::Codec + Ord,
{
	overlay: OverlayedChanges,
	offchain_overlay: OffchainOverlayedChanges,
	storage_transaction_cache: StorageTransactionCache<
		<InMemoryBackend<T> as Backend<T::Hash>>::Transaction, T::Hash, N
	>,
	backend: InMemoryBackend<T>,
	changes_trie_config: Option<ChangesTrieConfiguration>,
	changes_trie_storage: ChangesTrieInMemoryStorage<T::Hash, N>,
	extensions: Extensions,
}

impl<T, N> TestExternalities<T, N>
	where
		N: ChangesTrieBlockNumber,
		T: TrieConfiguration,
		TrieHash<T>: Ord + 'static + codec::Codec,
{
	/// Get externalities implementation.
	pub fn ext(&mut self) -> Ext<T::Hash, N, InMemoryBackend<T>> {
		Ext::new(
			&mut self.overlay,
			&mut self.offchain_overlay,
			&mut self.storage_transaction_cache,
			&self.backend,
			match self.changes_trie_config.clone() {
				Some(config) => Some(ChangesTrieState {
					config,
					zero: 0.into(),
					storage: &self.changes_trie_storage,
				}),
				None => None,
			},
			Some(&mut self.extensions),
		)
	}

	/// Create a new instance of `TestExternalities` with storage.
	pub fn new(storage: Storage) -> Self {
		Self::new_with_code(&[], storage)
	}

	/// New empty test externalities.
	pub fn new_empty() -> Self {
		Self::new_with_code(&[], Storage::default())
	}

	/// Create a new instance of `TestExternalities` with code and storage.
	pub fn new_with_code(code: &[u8], mut storage: Storage) -> Self {
		let mut overlay = OverlayedChanges::default();
		let changes_trie_config = storage.top.get(CHANGES_TRIE_CONFIG)
			.and_then(|v| Decode::decode(&mut &v[..]).ok());
		overlay.set_collect_extrinsics(changes_trie_config.is_some());

		assert!(storage.top.keys().all(|key| !is_child_storage_key(key)));
		assert!(storage.children_default.keys().all(|key| is_child_storage_key(key)));

		storage.top.insert(HEAP_PAGES.to_vec(), 8u64.encode());
		storage.top.insert(CODE.to_vec(), code.to_vec());

		let offchain_overlay = OffchainOverlayedChanges::enabled();

		let mut extensions = Extensions::default();
		extensions.register(sp_core::traits::TaskExecutorExt(sp_core::tasks::executor()));


		TestExternalities {
			overlay,
			offchain_overlay,
			changes_trie_config,
			extensions,
			changes_trie_storage: ChangesTrieInMemoryStorage::new(),
			backend: storage.into(),
			storage_transaction_cache: Default::default(),
		}
	}

	/// Insert key/value into backend
	pub fn insert(&mut self, k: StorageKey, v: StorageValue) {
		self.backend.insert(vec![(None, vec![(k, Some(v))])]);
	}

	/// Registers the given extension for this instance.
	pub fn register_extension<E: Any + Extension>(&mut self, ext: E) {
		self.extensions.register(ext);
	}

	/// Get mutable reference to changes trie storage.
	pub fn changes_trie_storage(&mut self) -> &mut ChangesTrieInMemoryStorage<T::Hash, N> {
		&mut self.changes_trie_storage
	}

	/// Return a new backend with all pending value.
	pub fn commit_all(&self) -> InMemoryBackend<T> {
		let top: Vec<_> = self.overlay.changes(None)
			.map(|(k, v)| (k.clone(), v.value().cloned()))
			.collect();
		let mut transaction = vec![(None, top)];

		for child_info in self.overlay.child_infos() {
			transaction.push((
				Some(child_info.clone()),
				self.overlay.changes(Some(child_info))
					.map(|(k, v)| (k.clone(), v.value().cloned()))
					.collect(),
			))
		}

		self.backend.update(transaction)
	}

	/// Execute the given closure while `self` is set as externalities.
	///
	/// Returns the result of the given closure.
	pub fn execute_with<R>(&mut self, execute: impl FnOnce() -> R) -> R {
		let mut ext = self.ext();
		sp_externalities::set_and_run_with_externalities(&mut ext, execute)
	}
}

impl<T, N> std::fmt::Debug for TestExternalities<T, N>
	where
		N: ChangesTrieBlockNumber,
		T: TrieConfiguration,
		TrieHash<T>: Ord + codec::Codec,
{
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		write!(f, "overlay: {:?}\nbackend: {:?}", self.overlay, self.backend.pairs())
	}
}

impl<T, N> PartialEq for TestExternalities<T, N>
	where
		N: ChangesTrieBlockNumber,
		T: TrieConfiguration,
		TrieHash<T>: Ord + 'static + codec::Codec
{
	/// This doesn't test if they are in the same state, only if they contains the
	/// same data at this state
	fn eq(&self, other: &TestExternalities<T, N>) -> bool {
		self.commit_all().eq(&other.commit_all())
	}
}

impl<T, N> Default for TestExternalities<T, N>
	where
		N: ChangesTrieBlockNumber,
		T: TrieConfiguration,
		TrieHash<T>: Ord + 'static + codec::Codec,
{
	fn default() -> Self { Self::new(Default::default()) }
}

impl<T, N> From<Storage> for TestExternalities<T, N>
	where
		N: ChangesTrieBlockNumber,
		T: TrieConfiguration,
		TrieHash<T>: Ord + 'static + codec::Codec,
{
	fn from(storage: Storage) -> Self {
		Self::new(storage)
	}
}

impl<T, N> sp_externalities::ExtensionStore for TestExternalities<T, N>
	where
		N: ChangesTrieBlockNumber,
		T: TrieConfiguration,
		TrieHash<T>: Ord + codec::Codec,
{
	fn extension_by_type_id(&mut self, type_id: TypeId) -> Option<&mut dyn Any> {
		self.extensions.get_mut(type_id)
	}

	fn register_extension_with_type_id(
		&mut self,
		type_id: TypeId,
		extension: Box<dyn Extension>,
	) -> Result<(), sp_externalities::Error> {
		self.extensions.register_with_type_id(type_id, extension)
	}

	fn deregister_extension_by_type_id(&mut self, type_id: TypeId) -> Result<(), sp_externalities::Error> {
		self.extensions
			.deregister(type_id)
			.expect("There should be an extension we try to remove in TestExternalities");
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_core::traits::Externalities;
	use sp_trie::Layout;
	use hex_literal::hex;

	type BlakeTwo256 = crate::RefHasher<sp_core::Blake2Hasher>;

	#[test]
	fn commit_should_work() {
		let mut ext = TestExternalities::<Layout<BlakeTwo256>, u64>::default();
		let mut ext = ext.ext();
		ext.set_storage(b"doe".to_vec(), b"reindeer".to_vec());
		ext.set_storage(b"dog".to_vec(), b"puppy".to_vec());
		ext.set_storage(b"dogglesworth".to_vec(), b"cat".to_vec());
		const ROOT: [u8; 32] = hex!("555d4777b52e9196e3f6373c556cc661e79cd463f881ab9e921e70fc30144bf4");
		assert_eq!(&ext.storage_root()[..], &ROOT);
	}

	#[test]
	fn set_and_retrieve_code() {
		let mut ext = TestExternalities::<Layout<BlakeTwo256>, u64>::default();
		let mut ext = ext.ext();

		let code = vec![1, 2, 3];
		ext.set_storage(CODE.to_vec(), code.clone());

		assert_eq!(&ext.storage(CODE).unwrap(), &code);
	}

	#[test]
	fn check_send() {
		fn assert_send<T: Send>() {}
		assert_send::<TestExternalities::<Layout<BlakeTwo256>, u64>>();
	}
}

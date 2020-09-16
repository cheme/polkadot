// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! RocksDB-based offchain workers local storage.

use std::{
	collections::HashMap,
	sync::Arc,
};

use crate::{columns, Database, DbHash, Transaction};
use parking_lot::{Mutex, RwLock};
use historied_db::{Latest, Management, ManagementRef, UpdateResult,
	management::tree::{TreeManagementStorage, ForkPlan},
	historied::tree::Tree};
use codec::{Decode, Encode, Codec};
use sp_core::offchain::storage::HValue;
use log::error;

/// Offchain local storage
#[derive(Clone)]
pub struct LocalStorage {
	db: Arc<dyn Database<DbHash>>,
	locks: Arc<Mutex<HashMap<Vec<u8>, Arc<Mutex<()>>>>>,
}

/// Offchain local storage with blockchain historied storage.
#[derive(Clone)]
pub struct BlockChainLocalStorage<H: Ord, S: TreeManagementStorage> {
	historied_management: Arc<RwLock<crate::TreeManagement<H, S>>>,
	db: Arc<dyn Database<DbHash>>,
	locks: Arc<Mutex<HashMap<Vec<u8>, Arc<Mutex<()>>>>>,
}

/// Offchain local storage for a given block.
#[derive(Clone)]
pub struct BlockChainLocalAt {
	db: Arc<dyn Database<DbHash>>,
	at_read: ForkPlan<u32, u32>,
	at_write: Option<Latest<(u32, u32)>>,
	locks: Arc<Mutex<HashMap<Vec<u8>, Arc<Mutex<()>>>>>,
}

/// Offchain local storage for a given block,
/// and for new state (without concurrency handling).
#[derive(Clone)]
pub struct BlockChainLocalAtNew(BlockChainLocalAt);

impl std::fmt::Debug for LocalStorage {
	fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
		fmt.debug_struct("LocalStorage")
			.finish()
	}
}

impl<H: Ord, S: TreeManagementStorage> std::fmt::Debug for BlockChainLocalStorage<H, S> {
	fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
		fmt.debug_struct("BlockChainLocalStorage")
			.finish()
	}
}

impl LocalStorage {
	/// Create new offchain storage for tests (backed by memorydb)
	#[cfg(any(test, feature = "test-helpers"))]
	pub fn new_test() -> Self {
		let db = kvdb_memorydb::create(crate::utils::NUM_COLUMNS);
		let db = sp_database::as_database(db);
		Self::new(db as _)
	}

	/// Create offchain local storage with given `KeyValueDB` backend.
	pub fn new(db: Arc<dyn Database<DbHash>>) -> Self {
		Self {
			db,
			locks: Default::default(),
		}
	}
}

impl<H: Ord, S: TreeManagementStorage> BlockChainLocalStorage<H, S> {
	/// Create offchain local storage with given `KeyValueDB` backend.
	pub fn new(
		db: Arc<dyn Database<DbHash>>,
		historied_management: Arc<RwLock<crate::TreeManagement<H, S>>>,
	) -> Self {
		Self {
			historied_management,
			db,
			locks: Default::default(),
		}
	}

}

impl<H: Ord> BlockChainLocalStorage<H, ()> {
	/// Create new offchain storage for tests (backed by memorydb)
	#[cfg(any(test, feature = "test-helpers"))]
	pub fn new_test() -> Self {
		let db = kvdb_memorydb::create(crate::utils::NUM_COLUMNS);
		let db = sp_database::as_database(db);
		let historied_management = Arc::new(RwLock::new(crate::TreeManagement::default()));
		Self::new(db as _, historied_management)
	}
}

impl sp_core::offchain::OffchainStorage for LocalStorage {
	fn set(&mut self, prefix: &[u8], key: &[u8], value: &[u8]) {
		let key: Vec<u8> = prefix.iter().chain(key).cloned().collect();
		let mut tx = Transaction::new();
		tx.set(columns::OFFCHAIN, &key, value);

		if let Err(err) = self.db.commit(tx) {
			error!("Error setting on local storage: {}", err)
		}
	}

	fn remove(&mut self, prefix: &[u8], key: &[u8]) {
		let key: Vec<u8> = prefix.iter().chain(key).cloned().collect();
		let mut tx = Transaction::new();
		tx.remove(columns::OFFCHAIN, &key);

		if let Err(err) = self.db.commit(tx) {
			error!("Error removing on local storage: {}", err)
		}
	}

	fn get(&self, prefix: &[u8], key: &[u8]) -> Option<Vec<u8>> {
		let key: Vec<u8> = prefix.iter().chain(key).cloned().collect();
		self.db.get(columns::OFFCHAIN, &key)
	}

	fn compare_and_set(
		&mut self,
		prefix: &[u8],
		item_key: &[u8],
		old_value: Option<&[u8]>,
		new_value: &[u8],
	) -> bool {
		let key: Vec<u8> = prefix.iter().chain(item_key).cloned().collect();
		let key_lock = {
			let mut locks = self.locks.lock();
			locks.entry(key.clone()).or_default().clone()
		};

		let is_set;
		{
			let _key_guard = key_lock.lock();
			let val = self.db.get(columns::OFFCHAIN, &key);
			is_set = val.as_ref().map(|x| &**x) == old_value;

			if is_set {
				self.set(prefix, item_key, new_value)
			}
		}

		// clean the lock map if we're the only entry
		let mut locks = self.locks.lock();
		{
			drop(key_lock);
			let key_lock = locks.get_mut(&key);
			if let Some(_) = key_lock.and_then(Arc::get_mut) {
				locks.remove(&key);
			}
		}
		is_set
	}
}

impl<H, S> sp_core::offchain::BlockChainOffchainStorage for BlockChainLocalStorage<H, S>
	where
		H: Send + Sync + Ord + Clone + Codec,
		S: TreeManagementStorage + Send + Sync + Clone,
{
	type BlockId = H;
	type OffchainStorage = BlockChainLocalAt;
	type OffchainStorageNew = BlockChainLocalAtNew;

	fn at(&self, id: Self::BlockId) -> Option<Self::OffchainStorage> {
		if let Some(at_read) = self.historied_management.write().get_db_state(&id) {
			let at_write = self.historied_management.write().get_db_state_mut(&id);
			Some(BlockChainLocalAt {
				db: self.db.clone(),
				at_read,
				at_write,
				locks: self.locks.clone(),
			})
		} else {
			None
		}
	}
	fn at_new(&self, id: Self::BlockId) -> Option<Self::OffchainStorageNew> {
		self.at(id).map(|at| BlockChainLocalAtNew(at))
	}
	fn latest(&self) -> Option<Self::BlockId> {
		None // TODO put tree mgmt in its inner struct with cache and reference to latest insert.
	}
}

impl BlockChainLocalAt {
	/// Under current design, the local update is only doable when we
	/// are at a latest block, this function tells if we can use
	/// function that modify state.
	/// TODO EMCH this is probably racy offchain storage do not flush on new block,
	/// but at the same time we need to do them sequentially...
	/// Can probably save processed head of fork (would need a method to also indicate
	/// if it may become updatable later, and produce mut state from fork state casted to latest).
	pub fn can_update(&self) -> bool {
		self.at_write.is_some()
	}
}

impl sp_core::offchain::OffchainStorage for BlockChainLocalAt {
	fn set(&mut self, prefix: &[u8], key: &[u8], value: &[u8]) {
		// TODO have a Tree implementation that can write at non terminal state
		// to avoid locks??
		let test: Option<fn(Option<&[u8]>) -> bool> = None;
		self.modify(
			prefix,
			key,
			test,
			Some(value),
			false,
		);
	}

	fn remove(&mut self, prefix: &[u8], key: &[u8]) {
		let test: Option<fn(Option<&[u8]>) -> bool> = None;
		self.modify(
			prefix,
			key,
			test,
			None,
			false,
		);
	}

	fn get(&self, prefix: &[u8], key: &[u8]) -> Option<Vec<u8>> {
		// TODO consider using types for a totally encoded items.
		let key: Vec<u8> = prefix.iter().chain(key).cloned().collect();
		self.db.get(columns::OFFCHAIN, &key)
			.and_then(|v| {
				let v: Option<HValue> = Decode::decode(&mut &v[..]).ok();
				v
			}.and_then(|h| {
				use historied_db::historied::ValueRef;
				h.get(&self.at_read).flatten()
				/*v.and_then(|mut v| {
					match v.pop() {
						Some(0u8) => None,
						Some(1u8) => Some(v),
						None | Some(_) => panic!("inconsistent value, DB corrupted"),
					}
				})*/
			}))
	}

	fn compare_and_set(
		&mut self,
		prefix: &[u8],
		item_key: &[u8],
		old_value: Option<&[u8]>,
		new_value: &[u8],
	) -> bool {
		let test = |v: Option<&[u8]>| old_value == v;
		self.modify(
			prefix,
			item_key,
			Some(test),
			Some(new_value),
			false,
		)
	}
}

impl sp_core::offchain::OffchainStorage for BlockChainLocalAtNew {
	fn set(&mut self, prefix: &[u8], key: &[u8], value: &[u8]) {
		let test: Option<fn(Option<&[u8]>) -> bool> = None;
		self.0.modify(
			prefix,
			key,
			test,
			Some(value),
			true,
		);
	}

	fn remove(&mut self, prefix: &[u8], key: &[u8]) {
		let test: Option<fn(Option<&[u8]>) -> bool> = None;
		self.0.modify(
			prefix,
			key,
			test,
			None,
			true,
		);
	}

	fn get(&self, prefix: &[u8], key: &[u8]) -> Option<Vec<u8>> {
		self.0.get(prefix, key)
	}

	fn compare_and_set(
		&mut self,
		prefix: &[u8],
		item_key: &[u8],
		old_value: Option<&[u8]>,
		new_value: &[u8],
	) -> bool {
		let test = |v: Option<&[u8]>| old_value == v;
		self.0.modify(
			prefix,
			item_key,
			Some(test),
			Some(new_value),
			true,
		)
	}
}

impl BlockChainLocalAt {
	fn modify(
		&mut self,
		prefix: &[u8],
		item_key: &[u8],
		condition: Option<impl Fn(Option<&[u8]>) -> bool>,
		new_value: Option<&[u8]>,
		is_new: bool,
	) -> bool {
		if self.at_write.is_none() {
			panic!("Incoherent state for offchain writing");
		}
		let key: Vec<u8> = prefix.iter().chain(item_key).cloned().collect();
		let key_lock = {
			let mut locks = self.locks.lock();
			locks.entry(key.clone()).or_default().clone()
		};

		let is_set;
		{
			let _key_guard = key_lock.lock();
			let histo = self.db.get(columns::OFFCHAIN, &key)
				.and_then(|v| {
					let v: Option<HValue> = Decode::decode(&mut &v[..]).ok();
					v
				});
			let val = histo.as_ref().and_then(|h| {
				use historied_db::historied::ValueRef;
				h.get(&self.at_read).flatten()
				/*v.and_then(|mut v| {
					match v.pop() {
						Some(0u8) => None,
						Some(1u8) => Some(v),
						None | Some(_) => panic!("inconsistent value, DB corrupted"),
					}
				})*/
			});

			is_set = condition.map(|c| c(val.as_ref().map(|v| v.as_slice()))).unwrap_or(true);

			if is_set {
				use historied_db::historied::Value;
				let is_insert = new_value.is_some();
				/*let new_value = if let Some(new_value) = new_value {
					let mut new_value = new_value.to_vec();
					new_value.push(1u8);
					new_value
				} else {
					//vec![0]
					None
				};*/
				let new_value = new_value.map(|v| v.to_vec());
				let (new_value, update_result) = if let Some(mut histo) = histo {
					let update_result = if is_new {
						histo.set(new_value, self.at_write.as_ref().expect("Synch at start"))
					} else {
						use historied_db::historied::ConditionalValueMut;
						use historied_db::historied::StateIndex;
						histo.set_if_possible_no_overwrite(
							new_value,
							self.at_write.as_ref().expect("Synch at start").index_ref(),
						).expect("Concurrency failure for sequential write of offchain storage")
					};
					if let &UpdateResult::Unchanged = &update_result {
						(Vec::new(), update_result)
					} else {
						(histo.encode(), update_result)
					}
				} else {
					if is_insert {
						(HValue::new(new_value, self.at_write.as_ref().expect("Synch at start"), ((), ())).encode(), UpdateResult::Changed(()))
					} else {
						// nothing to delete
						(Default::default(), UpdateResult::Unchanged)
					}
				};
				match update_result {
					UpdateResult::Changed(()) => {
						let mut tx = Transaction::new();
						tx.set(columns::OFFCHAIN, &key, new_value.as_slice());

						self.db.commit(tx);
					},
					UpdateResult::Cleared(()) => {
						let mut tx = Transaction::new();
						tx.remove(columns::OFFCHAIN, &key);

						self.db.commit(tx);
					},
					UpdateResult::Unchanged => (),
				}
			}
		}

		// clean the lock map if we're the only entry
		let mut locks = self.locks.lock();
		{
			drop(key_lock);
			let key_lock = locks.get_mut(&key);
			if let Some(_) = key_lock.and_then(Arc::get_mut) {
				locks.remove(&key);
			}
		}
		is_set
	}
	
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_core::offchain::OffchainStorage;

	#[test]
	fn should_compare_and_set_and_clear_the_locks_map() {
		let mut storage = LocalStorage::new_test();
		let prefix = b"prefix";
		let key = b"key";
		let value = b"value";

		storage.set(prefix, key, value);
		assert_eq!(storage.get(prefix, key), Some(value.to_vec()));

		assert_eq!(storage.compare_and_set(prefix, key, Some(value), b"asd"), true);
		assert_eq!(storage.get(prefix, key), Some(b"asd".to_vec()));
		assert!(storage.locks.lock().is_empty(), "Locks map should be empty!");
	}

	#[test]
	fn should_compare_and_set_on_empty_field() {
		let mut storage = LocalStorage::new_test();
		let prefix = b"prefix";
		let key = b"key";

		assert_eq!(storage.compare_and_set(prefix, key, None, b"asd"), true);
		assert_eq!(storage.get(prefix, key), Some(b"asd".to_vec()));
		assert!(storage.locks.lock().is_empty(), "Locks map should be empty!");
	}

}

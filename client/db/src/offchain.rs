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
use parking_lot::Mutex;
use log::error;
use codec::{Encode, Decode, Codec};
use sp_runtime::traits::{NumberFor, Block as BlockT, SaturatedConversion};

/// Offchain local storage
#[derive(Clone)]
pub struct LocalStorage {
	db: Arc<dyn Database<DbHash>>,
	locks: Arc<Mutex<HashMap<Vec<u8>, Arc<Mutex<()>>>>>,
}

impl std::fmt::Debug for LocalStorage {
	fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
		fmt.debug_struct("LocalStorage")
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

/// Current state of journaling changes.
#[derive(Encode, Decode)]
pub(crate) struct CanonicalDefferedUpdate {
	first_non_canonical: u64,
	next_fork_index: std::collections::VecDeque<u64>,
	#[codec(skip)]
	revert: Option<(u64, std::collections::VecDeque<u64>)>,
}

/// When using `Local` api, indexing changes
/// are only committed on block canonicalization.
/// Until then, the changes are stored in serialized
/// journal structue (one per block).
#[derive(Encode, Decode)]
struct JournalRecord<BlockHash> {
	hash: BlockHash,
	inserted: Vec<(Vec<u8>, Vec<u8>)>,
	deleted: Vec<Vec<u8>>,
}

fn to_meta_key<S: Codec>(suffix: &[u8], data: &S) -> Vec<u8> {
	let mut buffer = data.encode();
	buffer.extend(suffix);
	buffer
}

const OFFCHAIN_LOCAL_JOURNAL: &[u8] = b"offchain_journal";
const OFFCHAIN_JOURNALS_PENDING: &[u8] = b"offchain_journal_pending";

fn to_journal_key(block: u64, index: u64) -> Vec<u8> {
	to_meta_key(OFFCHAIN_LOCAL_JOURNAL, &(block, index))
}

impl CanonicalDefferedUpdate {
	/// Add a change set to a transaction.
	pub fn new(db: &dyn Database<DbHash>) -> sp_blockchain::Result<Self> {
		Ok(if let Some(encoded) = db.get(columns::OFFCHAIN, OFFCHAIN_JOURNALS_PENDING) {
			CanonicalDefferedUpdate::decode(&mut encoded.as_slice())
				.map_err(|e| sp_blockchain::Error::from(format!("Invalid offchain journal counter: {:?}", e)))?
		} else {
			// init
			CanonicalDefferedUpdate {
				first_non_canonical: 1,
				next_fork_index: Default::default(),
				revert: Default::default(),
			}
		})
	}

	pub fn write(&self, transaction: &mut Transaction<DbHash>) {
		transaction.set_from_vec(columns::OFFCHAIN, OFFCHAIN_JOURNALS_PENDING, self.encode());
	}

	/// Add a change set to a transaction.
	pub fn new_block<Block: BlockT>(
		&mut self,
		hash: Block::Hash,
		number: NumberFor<Block>,
		changes: super::CanonicalOffchainChanges,
		transaction: &mut Transaction<DbHash>,
	) {
		let number_u64 = number.saturated_into::<u64>();
		if number_u64 == 0 {
			return self.genesis_new_block(changes, transaction);
		}
		let index = (number_u64 - self.first_non_canonical) as usize;
		// pending change is an actual update
		while self.next_fork_index.len() <= index {
			self.next_fork_index.push_back(0);
		}
		let fork_index = self.next_fork_index[index];
		let key = to_journal_key(number_u64, fork_index);
		self.next_fork_index[index] = fork_index + 1;
		let record = JournalRecord::<Block::Hash> {
			hash,
			inserted: changes.inserted,
			deleted: changes.deleted,
		};
		transaction.set_from_vec(columns::OFFCHAIN, &key, record.encode());
		self.write(transaction);
	}

	/// For genesis we do not wait for finalization to commit changes.
	fn genesis_new_block(
		&mut self,
		changes: super::CanonicalOffchainChanges,
		transaction: &mut Transaction<DbHash>,
	) {
		for (key, value) in changes.inserted {
			transaction.set_from_vec(columns::OFFCHAIN, &key, value);
		}
		for key in changes.deleted {
			transaction.remove(columns::OFFCHAIN, &key);
		}
	}

	/// Store a copy of  state before modification.
	pub fn start_pending(&mut self) {
		// If not we got a concurrency issue
		assert!(self.revert.is_none());
		self.revert = Some((self.first_non_canonical, self.next_fork_index.clone()));
	}

	/// Reverts index change in case we did not commit some transactional
	/// changes.
	pub fn revert_pending(&mut self) {
		if let Some(revert) = self.revert.take() {
			self.first_non_canonical = revert.0;
			self.next_fork_index = revert.1;
		}
	}

	/// Changes are applied (internally the revert value is dropped).
	pub fn apply_pending(&mut self) {
		self.revert = None;
	}

	/// Number of block that where skipped on finalization.
	pub fn skipped_finalize<Block: BlockT>(
		&self,
		number: NumberFor<Block>,
	) -> usize {
		let number_u64 = number.saturated_into::<u64>();
		number_u64.saturating_sub(self.first_non_canonical) as usize
	}
	
	pub fn finalize<Block: BlockT>(
		&mut self,
		hash: Block::Hash,
		number: NumberFor<Block>,
		transaction: &mut Transaction<DbHash>,
		db: &dyn Database<DbHash>,
	) {
		let number_u64 = number.saturated_into::<u64>();
		// finalize need to be done without skipping blocks.
		assert!(number_u64 == self.first_non_canonical);
		if let Some(nb) = self.next_fork_index.pop_front() {
			let mut found = false;
			for fork_index in 0..nb {
				let key = to_journal_key(number_u64, fork_index);
				if !found {
					// hash could be split in another key value to avoid decoding cost
					if let Some(journal) = db.get(columns::OFFCHAIN, &key)
						.and_then(|v| JournalRecord::<Block::Hash>::decode(&mut v.as_slice()).ok()) {
						if journal.hash == hash {
							for (key, value) in journal.inserted {
								transaction.set_from_vec(columns::OFFCHAIN, &key, value);
							}
							for key in journal.deleted {
								transaction.remove(columns::OFFCHAIN, &key);
							}
							found = true;
							continue;
						}
					}
				}
				// Note that we do not delete invalid fork branch in depth.
				// We only remove journal for this finalized height,
				// there will be orphan consecutive journal that will be removed
				// later when their height will be finalized.
				// This is not optimal but makes code simplier.
				transaction.remove(columns::OFFCHAIN, &key);
			}
		}
		self.first_non_canonical += 1;
		self.write(transaction);
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

// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

use std::{collections::HashMap, sync::Arc};

use crate::{columns, Database, DbHash, Transaction};
use parking_lot::{Mutex, MutexGuard, RwLock};
use historied_db::{Latest, UpdateResult,
	management::{Management, ManagementMut},
	management::tree::{TreeManagementStorage, ForkPlan},
	historied::tree::Tree,
	backend::nodes::{NodesMeta, NodeStorage, NodeStorageMut, Node, ContextHead},
};
use codec::{Decode, Encode, Codec};
use log::error;

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
	#[cfg(any(feature = "test-helpers", test))]
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
		let mut tx = Transaction::new();
		tx.set(columns::OFFCHAIN, &concatenate_prefix_and_key(prefix, key), value);

		if let Err(err) = self.db.commit(tx) {
			error!("Error setting on local storage: {}", err)
		}
	}

	fn remove(&mut self, prefix: &[u8], key: &[u8]) {
		let mut tx = Transaction::new();
		tx.remove(columns::OFFCHAIN, &concatenate_prefix_and_key(prefix, key));

		if let Err(err) = self.db.commit(tx) {
			error!("Error removing on local storage: {}", err)
		}
	}

	fn get(&self, prefix: &[u8], key: &[u8]) -> Option<Vec<u8>> {
		self.db.get(columns::OFFCHAIN, &concatenate_prefix_and_key(prefix, key))
	}

	fn compare_and_set(
		&mut self,
		prefix: &[u8],
		item_key: &[u8],
		old_value: Option<&[u8]>,
		new_value: &[u8],
	) -> bool {
		let key = concatenate_prefix_and_key(prefix, item_key);
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

/// Concatenate the prefix and key to create an offchain key in the db.
pub(crate) fn concatenate_prefix_and_key(prefix: &[u8], key: &[u8]) -> Vec<u8> {
	prefix
		.iter()
		.chain(key.into_iter())
		.cloned()
		.collect()
}

/// Multiple node splitting strategy based on content
/// size.
#[derive(Clone, Copy)]
pub struct MetaBranches;

/// Multiple node splitting strategy based on content
/// size.
#[derive(Clone, Copy)]
pub struct MetaBlocks;

impl NodesMeta for MetaBranches {
	const APPLY_SIZE_LIMIT: bool = true;
	const MAX_NODE_LEN: usize = 2048; // This should be benched.
	const MAX_NODE_ITEMS: usize = 8;
	const STORAGE_PREFIX: &'static [u8] = b"tree_mgmt/branch_nodes";
}

impl NodesMeta for MetaBlocks {
	const APPLY_SIZE_LIMIT: bool = true;
	// This needs to be less than for `MetaBranches`, the point is to
	// be able to store multiple branche in the immediate storage and
	// avoid having a single branch occupy the whole item.
	const MAX_NODE_LEN: usize = 512;
	const MAX_NODE_ITEMS: usize = 4;
	const STORAGE_PREFIX: &'static [u8] = b"tree_mgmt/block_nodes";
}

/// Node backend for historied value that need to be
/// split in backend database.
///
/// This is transactional and `apply_transaction` need
/// to be call to extract changes into an actual db transaction.
#[derive(Clone)]
pub struct BlockNodes(DatabasePending);

/// Branch backend for historied value that need to be
/// split in backend database.
///
/// This is transactional and `apply_transaction` need
/// to be call to extract changes into an actual db transaction.
#[derive(Clone)]
pub struct BranchNodes(DatabasePending);

#[derive(Clone)]
struct DatabasePending {
	pending: Arc<RwLock<HashMap<Vec<u8>, Option<Vec<u8>>>>>,
	database: Arc<dyn Database<DbHash>>,
}

impl DatabasePending {
	fn clear_and_extract_changes(&self) -> HashMap<Vec<u8>, Option<Vec<u8>>> {
		std::mem::replace(&mut self.pending.write(), HashMap::new())
	}

	fn apply_transaction(
		&self,
		col: sp_database::ColumnId,
		transaction: &mut Transaction<DbHash>,
	) {
		let pending = self.clear_and_extract_changes();
		for (key, change) in pending {
			if let Some(value) = change {
				transaction.set_from_vec(col, &key, value);
			} else {
				transaction.remove(col, &key);
			}
		}
	}

	fn read(&self, col: sp_database::ColumnId, key: &[u8]) -> Option<Vec<u8>> {
		if let Some(pending) = self.pending.read().get(key).cloned() {
			pending
		} else {
			self.database.get(col, key)
		}
	}

	fn write(&self, key: Vec<u8>, value: Vec<u8>) {
		self.pending.write().insert(key, Some(value));
	}

	fn remove(&self, key: Vec<u8>) {
		self.pending.write().insert(key, None);
	}
}

impl BlockNodes {
	/// Initialize from clonable pointer to backend database.
	pub fn new(database: Arc<dyn Database<DbHash>>) -> Self {
		BlockNodes(DatabasePending {
			pending: Arc::new(RwLock::new(HashMap::new())),
			database,
		})
	}

	/// Flush pending changes into a database transaction.
	pub fn apply_transaction(&self, transaction: &mut Transaction<DbHash>) {
		self.0.apply_transaction(crate::columns::AUX, transaction)
	}
}

impl BranchNodes {
	/// Initialize from clonable pointer to backend database.
	pub fn new(database: Arc<dyn Database<DbHash>>) -> Self {
		BranchNodes(DatabasePending {
			pending: Arc::new(RwLock::new(HashMap::new())),
			database,
		})
	}

	/// Flush pending changes into a database transaction.
	pub fn apply_transaction(&self, transaction: &mut Transaction<DbHash>) {
		self.0.apply_transaction(crate::columns::AUX, transaction)
	}
}

impl NodeStorage<Option<Vec<u8>>, u64, LinearBackendInner, MetaBlocks> for BlockNodes {
	fn get_node(
		&self,
		reference_key: &[u8],
		parent_encoded_indexes: &[u8],
		relative_index: u64,
	) -> Option<LinearNode> {
		let key = Self::vec_address(reference_key, parent_encoded_indexes, relative_index);
		self.0.read(crate::columns::AUX, &key).and_then(|value| {
			// use encoded len as size (this is bigger than the call to estimate size
			// but not really an issue, otherwhise could adjust).
			let reference_len = value.len();

			let input = &mut value.as_slice();
			LinearBackendInner::decode(input).ok().map(|data| Node::new(
				data,
				reference_len,
			))
		})
	}
}

impl NodeStorageMut<Option<Vec<u8>>, u64, LinearBackendInner, MetaBlocks> for BlockNodes {
	fn set_node(
		&mut self,
		reference_key: &[u8],
		parent_encoded_indexes: &[u8],
		relative_index: u64,
		node: &LinearNode,
	) {
		let key = Self::vec_address(reference_key, parent_encoded_indexes, relative_index);
		let encoded = node.inner().encode();
		self.0.write(key, encoded);
	}
	fn remove_node(
		&mut self,
		reference_key: &[u8],
		parent_encoded_indexes: &[u8],
		relative_index: u64,
	) {
		let key = Self::vec_address(reference_key, parent_encoded_indexes, relative_index);
		self.0.remove(key);
	}
}

impl NodeStorage<BranchLinear, u32, TreeBackendInner, MetaBranches> for BranchNodes {
	fn get_node(
		&self,
		reference_key: &[u8],
		parent_encoded_indexes: &[u8],
		relative_index: u64,
	) -> Option<TreeNode> {
		use historied_db::DecodeWithContext;
		let key = Self::vec_address(reference_key, parent_encoded_indexes, relative_index);
		self.0.read(crate::columns::AUX, &key).and_then(|value| {
			// use encoded len as size (this is bigger than the call to estimate size
			// but not an issue, otherwhise could adjust).
			let reference_len = value.len();

			let block_nodes = BlockNodes(self.0.clone());
			let input = &mut value.as_slice();
			TreeBackendInner::decode_with_context(
				input,
				&ContextHead {
					key: reference_key.to_vec(),
					backend: block_nodes,
					encoded_indexes: parent_encoded_indexes.to_vec(),
					node_init_from: (),
				},
			).map(|data| Node::new (
				data,
				reference_len,
			))
		})
	}
}

impl NodeStorageMut<BranchLinear, u32, TreeBackendInner, MetaBranches> for BranchNodes {
	fn set_node(
		&mut self,
		reference_key: &[u8],
		parent_encoded_indexes: &[u8],
		relative_index: u64,
		node: &TreeNode,
	) {
		let key = Self::vec_address(reference_key, parent_encoded_indexes, relative_index);
		let encoded = node.inner().encode();
		self.0.write(key, encoded);
	}
	fn remove_node(
		&mut self,
		reference_key: &[u8],
		parent_encoded_indexes: &[u8],
		relative_index: u64,
	) {
		let key = Self::vec_address(reference_key, parent_encoded_indexes, relative_index);
		self.0.remove(key);
	}
}

// Values are stored in memory in Vec like structure
type LinearBackendInner = historied_db::backend::in_memory::MemoryOnly<
	Option<Vec<u8>>,
	u64,
>;

// A multiple nodes wraps multiple vec like structure
type LinearBackend = historied_db::backend::nodes::Head<
	Option<Vec<u8>>,
	u64,
	LinearBackendInner,
	MetaBlocks,
	BlockNodes,
	(),
>;

// Nodes storing these
type LinearNode = historied_db::backend::nodes::Node<
	Option<Vec<u8>>,
	u64,
	LinearBackendInner,
	MetaBlocks,
>;

// Branch
type BranchLinear = historied_db::historied::linear::Linear<Option<Vec<u8>>, u64, LinearBackend>;

// Branch are stored in memory
type TreeBackendInner = historied_db::backend::in_memory::MemoryOnly<
	BranchLinear,
	u32,
>;

// Head of branches
type TreeBackend = historied_db::backend::nodes::Head<
	BranchLinear,
	u32,
	TreeBackendInner,
	MetaBranches,
	BranchNodes,
	ContextHead<BlockNodes, ()>
>;

// Node with branches
type TreeNode = historied_db::backend::nodes::Node<
	BranchLinear,
	u32,
	TreeBackendInner,
	MetaBranches,
>;

/// Historied value with multiple branches.
///
/// Indexed by u32 for both branches and value into branches.
/// Value are in memory but serialized as splitted node.
/// Each node contains multiple values or multiple branch head of nodes.
pub type HValue = Tree<u32, u64, Option<Vec<u8>>, TreeBackend, LinearBackend>;

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

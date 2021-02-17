// This file is part of Substrate.

// Copyright (C) 2021-2021 Parity Technologies (UK) Ltd.
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

//! Blockchain fork tree management.
//!
//! Main purpose is to maintain a mapping between block hash
//! and an internal indexing to store historic of value.

use sp_core::Hasher;
use std::collections::BTreeMap;
use historied_db::{
	DecodeWithContext,
	management::{ManagementMut, ForkableManagement, Management},
	historied::{DataMut, DataRef, aggregate::Sum as _},
	mapped_db::{TransactionalMappedDB, MappedDBDyn},
	db_traits::{StateDB, StateDBRef, StateDBMut}, // TODO check it is use or remove the feature
	Latest, UpdateResult,
	historied::tree::{Tree, aggregate::Sum as TreeSum},
	management::tree::{Tree as TreeMgmt, ForkPlan, TreeManagementStorage},
	backend::nodes::ContextHead,
	historied::aggregate::xdelta::{BytesDelta, BytesDiff},
};
use sp_arithmetic::traits::Saturating;
use sp_runtime::traits::{
	Block as BlockT, Header as HeaderT, NumberFor, Zero, One, SaturatedConversion, HashFor,
};
use std::sync::Arc;
use parking_lot::{Mutex, RwLock};
use sp_database::{Transaction, RadixTreeDatabase};
use crate::DbHash;
use log::{trace, debug, warn};
use sp_blockchain::{Result as ClientResult, Error as ClientError};
use sp_database::{Database, OrderedDatabase};

/// Avoid finalizing at every block.
const HISTORIED_FINALIZATION_WINDOWS: u8 = 101;

/// Historied db state tree management for substrate.
///
/// Branch indexes are `u32`, block indexes `u64`,
/// and values ar encoded as `Vec<u8>`.
pub type TreeManagement<H, S> = historied_db::management::tree::TreeManagement<
	H,
	u32,
	u64,
	S,
>;

/// Registered historied db state consumer.
///
/// Mainly a way to trigger migration over all component using the state.
pub type RegisteredConsumer<H, S> = historied_db::management::tree::RegisteredConsumer<
	H,
	u32,
	u64,
	S,
>;

/// Definition of mappings used by `TreeManagementPersistence`.
pub mod historied_tree_bindings {
	// Mapping block hash with internal indexes.
	static_instance!(Mapping, b"\x08\x00\x00\x00tree_mgmt/mapping");
	// Mapping fork index with branch state data.
	static_instance!(TreeState, b"\x08\x00\x00\x00tree_mgmt/state");
	// Mapping fork index with change range, to know touched state.
	static_instance!(JournalDelete, b"\x08\x00\x00\x00tree_mgmt/journal_delete");
	// Journals of key with change for modified blocks.
	static_instance!(LocalKeyChangeJournal, b"\x08\x00\x00\x00tree_mgmt/key_changes");
	const CST: &'static[u8] = &[8u8, 0, 0, 0]; // AUX collection
	static_instance_variable!(TouchedGC, CST, b"tree_mgmt/touched_gc", false);
	static_instance_variable!(CurrentGC, CST, b"tree_mgmt/current_gc", false);
	// Last added block reference.
	static_instance_variable!(LastIndex, CST, b"tree_mgmt/last_index", false);
	// TODO seems unused upstream: remove upstream
	static_instance_variable!(NeutralElt,CST, b"tree_mgmt/neutral_elt", false);
	// Serialized tree metadata.
	static_instance_variable!(TreeMeta, CST, b"tree_mgmt/tree_meta", true);
}

#[derive(Clone)]
/// Database backed tree management.
///
/// Definitions for storage of historied
/// db tree state (maps block hashes to internal
/// history index).
pub struct TreeManagementPersistence;

impl TreeManagementStorage for TreeManagementPersistence {
	// In theory we do not need to journal in some case, but disabling it
	// is not worth the complexity.
	const JOURNAL_CHANGES: bool = true;
	// Use pointer to serialize db with a transactional layer.
	type Storage = TransactionalMappedDB<MappedDBDyn>;
	type Mapping = historied_tree_bindings::Mapping;
	type JournalDelete = historied_tree_bindings::JournalDelete;
	type LastIndex = historied_tree_bindings::LastIndex;
	type NeutralElt = historied_tree_bindings::NeutralElt;
	type TreeMeta = historied_tree_bindings::TreeMeta;
	type TreeState = historied_tree_bindings::TreeState;
}

#[cfg(any(feature = "with-kvdb-rocksdb", test))]
impl TreeManagementStorage for TreeManagementPersistenceNoTx {
	const JOURNAL_CHANGES: bool = true;
	type Storage = crate::RocksdbStorage; // TOOD MappedDBDyn instead??
	type Mapping = historied_tree_bindings::Mapping;
	type JournalDelete = historied_tree_bindings::JournalDelete;
	type LastIndex = historied_tree_bindings::LastIndex;
	type NeutralElt = historied_tree_bindings::NeutralElt;
	type TreeMeta = historied_tree_bindings::TreeMeta;
	type TreeState = historied_tree_bindings::TreeState;
}

#[cfg(any(feature = "with-kvdb-rocksdb", test))]
#[derive(Clone)]
/// Database backed tree management, no transaction.
pub struct TreeManagementPersistenceNoTx;



/// Tree management shareable sync instance.
#[derive(Clone)]
pub struct TreeManagementSync<Block: BlockT, S: TreeManagementStorage + 'static> {
	///  TODO remove pub
	/// Mutable shared state.
	pub inner: Arc<RwLock<TreeManagementInner<Block, S>>>,
	/// Pruning window.
	pub pruning_window: Option<NumberFor<Block>>,
}

// TODO remove pub
pub struct TreeManagementInner<Block: BlockT, S: TreeManagementStorage + 'static> {
	// TODO rem pub
	pub instance: TreeManagement<
		<HashFor<Block> as Hasher>::Out,
		S,
	>,
	// TODO rem pub
	pub consumer: RegisteredConsumer<
		<HashFor<Block> as Hasher>::Out,
		S,
	>,
	// TODO rem pub
	pub consumer_transaction: Transaction<DbHash>,
	/// Next block to apply migrate.
	pub next_migrate: Option<NumberFor<Block>>,
}

// TODO move in dep
type PendingChanges = BTreeMap<&'static [u8], (BTreeMap<Vec<u8>, Option<Vec<u8>>>, bool)>;

impl<Block, S> TreeManagementSync<Block, S>
	where
		Block: BlockT,
		S: TreeManagementStorage<Storage = TransactionalMappedDB<MappedDBDyn>>,
{
	/// Initiate from persistence storage.
	pub fn from_persistence(persistence: S::Storage) -> Self {
		TreeManagementSync {
			inner: Arc::new(RwLock::new(TreeManagementInner {
				instance: TreeManagement::from_ser(persistence),
				consumer: Default::default(),
				consumer_transaction: Default::default(),
				next_migrate: None,
			})),
			pruning_window: None, // This get set by consumer.
		}
	}

	/// Write management state changes to transaction container.
	/// TODO rename?
	pub fn apply_historied_management_changes(
		historied_management: &mut TreeManagement<
			<HashFor<Block> as Hasher>::Out,
			S,
		>,
		transaction: &mut Transaction<DbHash>,
	) {
		let pending = std::mem::replace(&mut historied_management.ser().pending, Default::default());
		for (col, (mut changes, dropped)) in pending {
			if dropped {
				use historied_db::mapped_db::MappedDB;
				for (key, _v) in historied_management.ser_ref().iter(col) {
					changes.insert(key, None);
				}
			}
			if let Some((col, p)) = crate::resolve_collection(col) {
				for (key, change) in changes {
					subcollection_prefixed_key!(p, key);
					match change {
						Some(value) => transaction.set_from_vec(col, key, value),
						None => transaction.remove(col, key),
					}
				}
			} else {
				warn!("Unknown collection for tree management pending transaction {:?}", col);
			}
		}
	}

	pub fn extract_changes(&self) -> PendingChanges {
		std::mem::replace(&mut self.inner.write().instance.ser().pending, Default::default())
	}

	pub fn register_new_block(
		&self,
		parent_hash: &Block::Hash,
		hash: &Block::Hash,
	) -> ClientResult<(ForkPlan<u32, u64>, Latest<(u32, u64)>)> {
		// lock does notinclude update of value as we do not have concurrent block creation
		let mut lock = self.inner.write();
		let mut management = &mut lock.instance;
		if let Some(state) = Some(management.get_db_state_for_fork(parent_hash)
			.unwrap_or_else(|| {
				// allow this to start from existing state TODO add a stored boolean to only allow
				// that once in genesis or in tests
				warn!("state not found for parent hash, appending to latest");
				management.latest_state_fork()
			}))
		{
			// TODO could use result as update plan (need to check if true)
			let _ = management.append_external_state(hash.clone(), &state)
				.ok_or(ClientError::StateDatabase("correct state resolution".into()))?;
			// TODO could make sense to use previous query plan since it
			// should mainly be use to read previous value.
			let query_plan = management.get_db_state(&hash)
				.ok_or(ClientError::StateDatabase("correct state resolution".into()))?;
			let update_plan = management.get_db_state_mut(&hash)
				// TODO could have a ClientError::StateManagement error.
				.ok_or(ClientError::StateDatabase("correct state resolution".into()))?;
			Ok((query_plan, update_plan))
		} else {
			Err(ClientError::StateDatabase("missing update plan".into()))
		}
	}

	pub fn init_new_management(
		&self,
		hash: &Block::Hash,
		db: &Arc<dyn OrderedDatabase<DbHash>>,
	) -> ClientResult<(ForkPlan<u32, u64>, Latest<(u32, u64)>)> {
		let mut lock = self.inner.write();
		let mut management = &mut lock.instance;
		let state = management.latest_state_fork();
		management.append_external_state(hash.clone(), &state);

		let mut transaction = Default::default();
		TreeManagementSync::<Block, _>::apply_historied_management_changes(management, &mut transaction);

		db.commit(transaction)?;

		let query_plan = management.get_db_state(&hash)
			.ok_or(ClientError::StateDatabase("correct state resolution".into()))?;
		let update_plan = management.get_db_state_mut(&hash)
			.ok_or(ClientError::StateDatabase("correct state resolution".into()))?;

		Ok((query_plan, update_plan))
	}

	pub fn migrate(
		&self,
		hash: &Block::Hash,
		number: NumberFor<Block>,
		db: &Arc<dyn Database<DbHash>>,
	) -> ClientResult<()> {

		// lazy init, not that this can lead to no finalization
		// if the node get close to often, with current windows
		// size, this is fine, otherwhise this value will need
		// to persist.
		if self.pruning_window.is_none() {
			return Ok(());
		}

		let prune_index = self.pruning_window.map(|nb| {
			number.saturating_sub(nb).saturated_into::<u64>()
		});

		// This lock can be rather long, so we really need to migrate occasionally.
		// TODO this is bad design, migrate requires this lock, but the actual
		// pruning does not require it that much: we should be able to run
		// a migration without attaching the historied_management to it.
		// This is due to the fact that transaction is use, and we can apply thing
		// rather atomically.
		// TODO create TransactionalMigration that do not require locking?
		// Maybe some api like AssertUnwindSafe : AssertTransactionalMigrate.
		let mut historied_management = self.inner.write();

		let TreeManagementInner {
			instance,
			consumer,
			consumer_transaction,
			next_migrate,
		} = &mut *historied_management;

		if next_migrate.is_none() {
			*next_migrate = Some(number + HISTORIED_FINALIZATION_WINDOWS.into());
			return Ok(());
		}

		let do_finalize = &number > &next_migrate.as_ref()
			.unwrap_or(&0u16.into());
		if !do_finalize {
			return Ok(())
		}

		// Ensure pending layer is clean: TODO call outside ??
		let _ = std::mem::replace(&mut instance.ser().pending, Default::default());

		let switch_index = instance.get_db_state_for_fork(hash);
		let path = {
			instance.get_db_state(hash)
		};

		if let (Some(switch_index), Some(path)) = (switch_index, path) {
			instance.canonicalize(path, switch_index, prune_index);
			// do migrate data
			consumer.migrate(instance);
		} else {
			return Err(ClientError::UnknownBlock("Missing in historied management".to_string()));
		}

		// flush historied management changes
		let mut transaction = std::mem::replace(consumer_transaction, Default::default());
		TreeManagementSync::<Block, _>::apply_historied_management_changes(instance, &mut transaction);

		db.commit(transaction)?;
		*next_migrate = Some(number + HISTORIED_FINALIZATION_WINDOWS.into());
		Ok(())
	}

	/// Delete all tree management information.
	pub fn clear(db: &Arc<dyn OrderedDatabase<DbHash>>) -> ClientResult<()> {
		db.clear_prefix(crate::columns::AUX, b"tree_mgmt/");
		Ok(())
	}
}

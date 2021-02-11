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

//! Key value snapshot db with history.

use super::HistoriedDB;
use sp_database::{SnapshotDb as SnapshotDbT, SnapshotDbError};
use crate::tree_management::{TreeManagementSync, TreeManagementPersistence};
use historied_db::{
	DecodeWithContext,
	management::{ManagementMut, ForkableManagement, Management},
	historied::{DataMut, DataRef, aggregate::Sum as _},
	mapped_db::{TransactionalMappedDB, MappedDBDyn},
	db_traits::{StateDB, StateDBRef, StateDBMut}, // TODO check it is use or remove the feature
	Latest, UpdateResult,
	historied::tree::{Tree, aggregate::Sum as TreeSum},
	management::tree::{Tree as TreeMgmt, ForkPlan},
	backend::nodes::ContextHead,
	historied::aggregate::xdelta::{BytesDelta, BytesDiff},
};
use sp_runtime::traits::{
	Block as BlockT, Header as HeaderT, NumberFor, Zero, One, SaturatedConversion, HashFor,
};
use std::marker::PhantomData;
use std::sync::Arc;
use parking_lot::{Mutex, RwLock};
use sp_database::{Transaction, RadixTreeDatabase};
use crate::DbHash;
use log::{trace, debug, warn};
use sp_blockchain::{Result as ClientResult, Error as ClientError};
use sp_database::{Database, OrderedDatabase};
use sp_state_machine::kv_backend::KVBackend;

/// Definition of mappings used by `TreeManagementPersistence`.
pub mod snapshot_db_conf {
	pub use sp_database::{SnapshotDbConf, SnapshotDBMode};

	const CST: &'static[u8] = &[8u8, 0, 0, 0]; // AUX collection

	/// Serialized configuration for snapshot.
	static_instance_variable!(SnapConfSer, CST, b"snapshot_db/config", false);

	/// Mapping to store journal of change keys
	static_instance!(JournalChanges, b"\x08\x00\x00\x00snapshot_db/journal_changes");

	/// Get initial conf from chain_spec
	pub fn from_chain_spec(properties: &sp_chain_spec::Properties) -> SnapshotDbConf {
		let mut conf = SnapshotDbConf::default();
		if Some(Some(true)) != properties.get("snapshotEnabled").map(|v| v.as_bool()) {
			return conf;
		}
		conf.enabled = true;
		if Some(Some(true)) == properties.get("snapshotPrimary").map(|v| v.as_bool()) {
			conf.primary_source = true;
		}
		if Some(Some(true)) == properties.get("snapshotNoNodeBackend").map(|v| v.as_bool()) {
			conf.no_node_backend = true;
		}
		if Some(Some(true)) == properties.get("snapshotJournalPruning").map(|v| v.as_bool()) {
			conf.journal_pruning = true;
		}
		if Some(Some(true)) == properties.get("snapshotDebugAssert").map(|v| v.as_bool()) {
			conf.debug_assert = true;
		}
		if Some(Some("xdelta3")) == properties.get("snapshotDebugAssert").map(|v| v.as_str()) {
			conf.diff_mode = SnapshotDBMode::Xdelta3Diff;
		}
		if let Some(Some(window_size)) = properties.get("snapshotLazyPruning").map(|v| v.as_u64()) {
			conf.lazy_pruning = Some(window_size as u32);
		}
		conf
	}

	/// Initiate conf from client command.
	pub fn from_cmd() -> SnapshotDbConf {
		unimplemented!()
	}

	/// Initiate conf from client command.
	pub fn initiate(
		db: (),
		from_chain_spec: SnapshotDbConf,
		from_cmd: SnapshotDbConf,
		new: bool,
	) -> SnapshotDbConf {
		unimplemented!()
		// TODO query db to see if genesis: simply if undefined it is genesis, otherwhise we always
		// got a conf (with enabled false possibly).
		// TODO maybe on genesis fail, remove the entry.

		// if genesis, use all chainspec and consider new.

		// if new use all from_cmd field to override from_chainspec
	}
}

/// Snapshot db implementation.
#[derive(Clone)]
pub struct SnapshotDb<Block: BlockT> {
	// TODO rem pub
	/// Historied management use by snapshot db.
	/// Currently snapshot db is single consumer, so init and clear
	/// operation also act on `historied_management`.
	pub historied_management: TreeManagementSync<Block, TreeManagementPersistence>,
	/// Database with historied items.
	pub ordered_db: Arc<dyn OrderedDatabase<DbHash>>,
	// TODO config from db !!!
	pub _ph: PhantomData<Block>,
}

impl<Block: BlockT> SnapshotDbT for SnapshotDb<Block> {
	fn clear_snapshot_db(&self) -> sp_database::error::Result<()> {
		unimplemented!();
	}

	fn update_running_conf(
		&self,
		_use_as_primary: Option<bool>,
		_debug_assert: Option<bool>,
		_lazy_pruning_window: Option<u32>,
	) -> sp_database::error::Result<()> {
		unimplemented!();
	}
}

impl<Block: BlockT> SnapshotDb<Block> {
	pub fn get_historied_db(
		&self,
		at: Option<&Block::Hash>,
	) -> ClientResult<Option<HistoriedDB>> {
		// TODO if enabled && (primary_source || assert_db)... else None 
		let do_assert: bool = true;
		let mut management = self.historied_management.0.write();
		let current_state = if let Some(hash) = at {
			management.instance.get_db_state(&hash)
				.ok_or_else(|| ClientError::StateDatabase(
					format!("Snapshot db missing state for hash {:?}", hash)
				))?
		} else {
			// genesis
			let state = management.instance.latest_state_fork();
			// starting a new state at default hash is not strictly necessary,
			// but we lack a historied db primitive to get default query state
			// on (0, 0).
			let h = Default::default();
			management.instance.get_db_state(&h)
				.or_else(|| management.instance.append_external_state(h.clone(), &state)
					.and_then(|_| management.instance.get_db_state(&h))
				).ok_or_else(|| ClientError::StateDatabase("Historied management error".into()))?
		};
		Ok(Some(HistoriedDB {
			current_state,
			db: self.ordered_db.clone(),
			do_assert,
		}))
	}

	pub fn get_kvbackend(
		&self,
		at: Option<&Block::Hash>,
	) -> ClientResult<Option<Arc<dyn KVBackend>>> {
		if let Some(db) = self.get_historied_db(at)? {
			let db = Arc::new(db);
			Ok(Some(db))
		} else {
			Ok(None)
		}
	}
	
}

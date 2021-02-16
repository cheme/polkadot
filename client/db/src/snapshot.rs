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
use sp_core::storage::{ChildInfo, ChildType, PrefixedStorageKey, well_known_keys};
use std::marker::PhantomData;
use std::sync::Arc;
use parking_lot::{Mutex, RwLock};
use sp_database::{Transaction, RadixTreeDatabase};
use crate::DbHash;
use log::{trace, debug, warn};
use sp_blockchain::{Result as ClientResult, Error as ClientError};
use sp_database::{Database, OrderedDatabase};
use sp_state_machine::kv_backend::KVBackend;
use codec::{Decode, Encode};
use sp_database::{SnapshotDbConf, SnapshotDBMode};
use sp_database::error::DatabaseError;
pub use sc_state_db::PruningMode;

/// Definition of mappings used by `TreeManagementPersistence`.
pub mod snapshot_db_conf {
	use sp_database::{SnapshotDbConf, SnapshotDBMode};
	use sp_blockchain::{Result as ClientResult, Error as ClientError};
	use historied_db::mapped_db::MappedDBDyn;

	const CST: &'static[u8] = &[8u8, 0, 0, 0]; // AUX collection

	/// Serialized configuration for snapshot.
	static_instance_variable!(SnapConfSer, CST, b"snapshot_db/config", false);

	/// Mapping to store journal of change keys
	static_instance!(JournalChanges, b"\x08\x00\x00\x00snapshot_db/journal_changes");

	/// Get initial conf from chain_spec.
	/// TODO not public
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

	/// Lazy initialization of snapshot db configuration from chain spec.
	pub fn update_db_conf(
		db: &mut MappedDBDyn,
		mut f: impl FnMut(&mut SnapshotDbConf) -> sp_blockchain::Result<()>,
	) -> sp_blockchain::Result<()> {
		let mut conf = historied_db::mapped_db::Variable::<SnapshotDbConf, _, SnapConfSer>::from_ser(db);
		let mut conf_mapping = conf.mapping(db);
		let mut conf = conf_mapping.get().clone();
		let res = f(&mut conf);
		if res.is_ok() {
			conf_mapping.set(conf);
		}
		res
	}

	/// Lazy initialization of snapshot db configuration from chain spec.
	pub fn lazy_init_from_chain_spec(
		db: &mut MappedDBDyn,
		genesis_conf: &SnapshotDbConf,
	) -> sp_blockchain::Result<()> {
		let mut conf = historied_db::mapped_db::Variable::<SnapshotDbConf, _, SnapConfSer>::from_ser(db);
		if !conf.get().lazy_set {
			let mut conf_mapping = conf.mapping(db);
			let mut genesis_conf = genesis_conf.clone();
			genesis_conf.lazy_set = true;
			conf_mapping.set(genesis_conf);
		}
		Ok(())
	}

	/// Get snapshot db configuration from chain spec.
	pub fn fetch_config(
		db: &MappedDBDyn,
	) -> ClientResult<SnapshotDbConf> {
		let conf = historied_db::mapped_db::Variable::<SnapshotDbConf, _, SnapConfSer>::from_ser(db);
		Ok(conf.get().clone())
	}
}

/// Snapshot db implementation.
#[derive(Clone)]
pub struct SnapshotDb<Block: BlockT> {
	// TODO rem pub
	/// Historied management use by snapshot db.
	/// Currently snapshot db is single consumer, so init and clear
	/// operation also act on `historied_management`.
	/// This use a transactional layer in storage.
	pub historied_management: TreeManagementSync<Block, TreeManagementPersistence>,
	/// Database with historied items. Warning, this is non transactional.
	pub ordered_db: Arc<dyn OrderedDatabase<DbHash>>,
	/// Configuration for this db.
	config: SnapshotDbConf,
	/// Historied value variant.
	hvalue_type: HValueType,
	// TODO config from db !!!
	pub _ph: PhantomData<Block>,
}

fn child_prefixed_key(child_info: Option<&ChildInfo>, key: &[u8]) -> Vec<u8> {
	if let Some(child_info) = child_info {
		child_prefixed_key_inner_default(child_info.storage_key(), key)
	} else {
		child_prefixed_key_inner_top(key)
	}
}

fn child_prefixed_key_inner_top(key: &[u8]) -> Vec<u8> {
	let mut prefixed_key = Vec::with_capacity(1 + key.len());
	prefixed_key.push(0);
	prefixed_key.extend_from_slice(key);
	prefixed_key
}


fn child_prefixed_key_inner_default(prefix: &[u8], key: &[u8]) -> Vec<u8> {
	let mut prefixed_key = Vec::with_capacity(1 + prefix.size_hint() + key.len());
	prefixed_key.push(1);
	prefix.encode_to(&mut prefixed_key);
	prefixed_key.extend_from_slice(key);
	prefixed_key
}

impl<Block: BlockT> SnapshotDbT<Block::Hash> for SnapshotDb<Block> {
	fn clear_snapshot_db(&self) -> sp_database::error::Result<()> {
		let mut management = self.historied_management.inner.write();
		TreeManagementSync::<Block, TreeManagementPersistence>::clear(&self.ordered_db)
			.map_err(|e| DatabaseError(Box::new(e)))?;
		// get non transactional mappeddb.
		let db = &mut management.instance.ser().db;
		snapshot_db_conf::update_db_conf(db, |mut genesis_conf| {
			*genesis_conf = Default::default();
			Ok(())
		}).map_err(|e| DatabaseError(Box::new(e)))?;

		self.ordered_db.clear_prefix(crate::columns::AUX, b"snapshot_db/");
		self.ordered_db.clear_prefix(crate::columns::STATE_SNAPSHOT, b"");

		Ok(())
	}

	fn update_running_conf(
		&self,
		use_as_primary: Option<bool>,
		debug_assert: Option<bool>,
		pruning_window: Option<Option<u32>>,
		lazy_pruning_window: Option<u32>,
	) -> sp_database::error::Result<()> {
		let mut management = self.historied_management.inner.write();
		let db = &mut management.instance.ser().db;
		snapshot_db_conf::update_db_conf(db, |mut genesis_conf| {
			if !genesis_conf.enabled {
				return Err(ClientError::StateDatabase(
					"Disabled snapshot db need to be created first".into(),
				));
			}
			if let Some(primary) = use_as_primary {
				genesis_conf.primary_source = primary;
			}
			if let Some(debug) = debug_assert {
				genesis_conf.debug_assert = debug;
			}
			if let Some(window) = pruning_window {
				genesis_conf.pruning = Some(window);
			}
			if let Some(window) = lazy_pruning_window {
				genesis_conf.lazy_pruning = Some(window);
			}
			Ok(())
		}).map_err(|e| DatabaseError(Box::new(e)))
	}

	fn re_init(
		&self,
		mut config: SnapshotDbConf,
		best_block: Block::Hash,
		state_visit: impl sc_client_api::StateVisitor,
	) -> sp_database::error::Result<()> {
		self.clear_snapshot_db()?;

		config.lazy_set = true;

		{
			let mut management = self.historied_management.inner.write();
			let db = &mut management.instance.ser().db;
			snapshot_db_conf::update_db_conf(db, |mut genesis_conf| {
				*genesis_conf = config.clone();
				Ok(())
			}).map_err(|e| DatabaseError(Box::new(e)))?;
		}

		let (query_plan, update_plan) = self.historied_management.init_new_management(
			&best_block,
			&self.ordered_db,
		).map_err(|e| DatabaseError(Box::new(e)))?;
		let mut historied_db = HistoriedDBMut {
			current_state: update_plan,
			current_state_read: query_plan,
			db: self.ordered_db.clone(),
			config,
		};

		let mut tx = Default::default();
		let mut count_tx = 0;
		let tx = &mut tx;
		let count_tx = &mut count_tx;
		let mut child_storage_key = PrefixedStorageKey::new(Vec::new());
		let child_storage_key = &mut child_storage_key;
		let mut last_child: Option<Vec<u8>> = None;
		let last_child = &mut last_child;
		state_visit.state_visit(|child, key, value| {
			let key = if let Some(child) = child {
				if Some(child) != last_child.as_ref().map(Vec::as_slice) {
					*child_storage_key = PrefixedStorageKey::new(child.to_vec());
					*last_child = Some(child.to_vec());
				}
				match ChildType::from_prefixed_key(&child_storage_key) {
					Some((ChildType::ParentKeyId, storage_key)) => {
						child_prefixed_key_inner_default(
							storage_key,
							key.as_slice(),
						)
					},
					_ => {
						let e = ClientError::StateDatabase("Unknown child trie type in state".into());
						return Err(DatabaseError(Box::new(e)));
					},
				}
			} else {
				child_prefixed_key_inner_top(key.as_slice())
			};
			historied_db.unchecked_new_single_inner(key.as_slice(), value, tx, crate::columns::STATE_SNAPSHOT);
			*count_tx = *count_tx + 1;
			if *count_tx == 1000 {
				//count += 1;
				//warn!("write a thousand {} {:?}", count, &k[..20]);
				let to_commit = std::mem::take(tx);
				self.ordered_db.commit(to_commit)?;
				*count_tx = 0;
			}
			Ok(())
		})?;
		let to_commit = std::mem::take(tx);
		self.ordered_db.commit(to_commit)?;

		Ok(())
	}
}

impl<Block: BlockT> SnapshotDb<Block> {
	pub fn new(
		mut historied_management: TreeManagementSync<Block, TreeManagementPersistence>,
		ordered_db: Arc<dyn OrderedDatabase<DbHash>>,
	) -> ClientResult<Self> {
		let config = {
			let management = historied_management.inner.read();
			let db = &management.instance.ser_ref().db;
			snapshot_db_conf::fetch_config(db)?
		};
		historied_management.pruning_window = config.pruning.clone()
			.flatten().map(|nb| nb.into());
		let hvalue_type = HValueType::resolve(&config)
			.ok_or_else(|| ClientError::StateDatabase(
				format!("Invalid snapshot config {:?}", config)
			))?;
		Ok(SnapshotDb {
			historied_management,
			ordered_db,
			config,
			hvalue_type,
			_ph: Default::default(),
		})
	}

	// TODO rename (it does add state)
	pub fn get_historied_db_mut(
		&self,
		parent: &Block::Hash,
		at: &Block::Hash,
	) -> ClientResult<Option<HistoriedDBMut<Arc<dyn OrderedDatabase<DbHash>>>>> {
		if !self.config.enabled {
			return Ok(None);
		}
		let (query_plan, update_plan) = self.historied_management.register_new_block(&parent, &at)?;
		Ok(Some(HistoriedDBMut {
			current_state: update_plan,
			current_state_read: query_plan,
			db: self.ordered_db.clone(),
			config: self.config.clone(),
		}))
	}

	pub fn get_historied_db(
		&self,
		at: Option<&Block::Hash>,
	) -> ClientResult<Option<HistoriedDB>> {
		if !self.config.enabled || !(self.config.primary_source || self.config.debug_assert) {
			return Ok(None);
		}

		let mut management = self.historied_management.inner.write();
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
			config: self.config.clone(),
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


/// Key value db at a given block for an historied DB.
pub struct HistoriedDB {
	// TODO rem pub as upgrade is cleaned
	pub current_state: ForkPlan<u32, u64>,
	// TODO rem pub as upgrade is cleaned
	pub db: Arc<dyn OrderedDatabase<DbHash>>,
	/// Configuration for this db.
	pub config: SnapshotDbConf,
}

/*
mod SingleNodeEncodedNoDiff {
	type LinearBackend<'a> = historied_db::backend::encoded_array::EncodedArray<
		'a,
		Vec<u8>,
		historied_db::backend::encoded_array::NoVersion,
	>;
	type TreeBackend<'a> = historied_db::historied::encoded_array::EncodedArray<
		'a,
		historied_db::historied::linear::Linear<Vec<u8>, u64, LinearBackend<'a>>,
		historied_db::historied::encoded_array::NoVersion,
	>;
	// Warning we use Vec<u8> instead of Some(Vec<u8>) to be able to use encoded_array.
	// None is &[0] when Some are postfixed with a 1. TODO use a custom type instead.
	pub type HValue<'a> = Tree<u32, u64, Vec<u8>, TreeBackend<'a>, LinearBackend<'a>>;
}
*/

mod single_node_xdelta {
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

	type LinearBackend = historied_db::backend::in_memory::MemoryOnly8<
		Vec<u8>,
		u64,
	>;

	type TreeBackend = historied_db::backend::in_memory::MemoryOnly4<
		historied_db::historied::linear::Linear<BytesDiff, u64, LinearBackend>,
		u32,
	>;

	/// HValue variant alias for `HValueType::SingleNodeXDelta`.
	pub type HValue = Tree<u32, u64, BytesDiff, TreeBackend, LinearBackend>;

	/// Access current value.
	pub fn value(v: &HValue, current_state: &ForkPlan<u32, u64>) -> Result<Option<Vec<u8>>, String> {
		let v = TreeSum::<_, _, BytesDelta, _, _>(&v);
		let v = v.get_sum(current_state);
		Ok(v.map(|v| v.into()).flatten())
	}
}

/// Historied value with multiple parallel branches.
/// Support multiple implementation from config.
pub enum HValue {
	SingleNodeXDelta(single_node_xdelta::HValue),
}

/// Compact resolved type from snapshot config.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum HValueType {
	SingleNodeXDelta,
}

impl HValueType {
	fn resolve(config: &SnapshotDbConf) -> Option<Self> {
		Some(match (&config.diff_mode, &config.no_node_backend) {
			(SnapshotDBMode::Xdelta3Diff, true) => HValueType::SingleNodeXDelta,
			(SnapshotDBMode::Xdelta3Diff, false) => unimplemented!(),
			(SnapshotDBMode::NoDiff, true) => unimplemented!(),
			(SnapshotDBMode::NoDiff, false) => unimplemented!(),
			_ => return None,
		})
	}
}
impl HValue {
	/// Instantiate new value.
	pub fn new(value_at: Vec<u8>, state: &Latest<(u32, u64)>) -> Self {
		unimplemented!();
		//BytesDiff::Value(v)
	}
	/// Decode existing value.
	pub fn decode_with_context(encoded: &[u8]) -> Option<Self> {
		unimplemented!();
	}

	/// Access existing value.
	fn value(&self, current_state: &ForkPlan<u32, u64>) -> Result<Option<Vec<u8>>, String> {
		Ok(match self {
			HValue::SingleNodeXDelta(inner) => single_node_xdelta::value(inner, current_state)?, 
		})
	}

	fn set_change(
		&mut self,
		change: Option<Vec<u8>>,
		current_state: &Latest<(u32, u64)>,
		current_state_read: &ForkPlan<u32, u64>,
	) -> Result<UpdateResult<()>, String> {
		Ok(match self {
			HValue::SingleNodeXDelta(inner) => {
				if let Some(v) = change {
					if let Some(previous) = {
						// we should use previous state, but since we know this
						// is a first write for this state (write only once per keys)
						// current state will always return previous state
						// TODO this assumption may not stand (see cumulus issue with storage cache).
						let h = TreeSum::<_, _, BytesDelta, _, _>(inner);
						h.get_sum(current_state_read)
					} {
						let target_value = Some(v).into();
						let v_diff = historied_db::historied::aggregate::xdelta::substract(&previous, &target_value).into();
						inner.set(v_diff, current_state)
					} else {
						inner.set(BytesDiff::Value(v), current_state)
					}
				} else {
					inner.set(BytesDiff::None, current_state)
				}
			},
		})
	}

	// TODO consider no error returned (check with node how it behave).
	fn encode(&self) -> Result<Vec<u8>, String> {
		Ok(match self {
			HValue::SingleNodeXDelta(inner) => inner.encode(),
		})
	}
}

impl HistoriedDB {
	fn storage_inner(
		&self,
		child_info: Option<&ChildInfo>,
		key: &[u8],
		column: u32,
	) -> Result<Option<Vec<u8>>, String> {
		let key = child_prefixed_key(child_info, key);
		if let Some(v) = self.db.get(column, key.as_slice()) {
			HistoriedDB::decode_inner(key.as_slice(), v.as_slice(), &self.current_state)
		} else {
			Ok(None)
		}
	}

	fn decode_inner(
		key: &[u8],
		encoded: &[u8],
		current_state: &ForkPlan<u32, u64>,
	) -> Result<Option<Vec<u8>>, String> {
		let h_value = HValue::decode_with_context(&mut &encoded[..])
			.ok_or_else(|| format!("KVDatabase decode error for k {:?}, v {:?}", key, encoded))?;
		Ok(h_value.value(current_state)?)
	}
}

impl KVBackend for HistoriedDB {
	fn use_as_primary(&self) -> bool {
		self.config.primary_source
	}

	fn assert_value(&self) -> bool {
		self.config.debug_assert
	}

	fn storage(
		&self,
		child: Option<&ChildInfo>,
		key: &[u8],
	) -> Result<Option<Vec<u8>>, String> {
		self.storage_inner(child, key, crate::columns::STATE_SNAPSHOT)
	}

	fn next_storage(
		&self,
		child: Option<&ChildInfo>,
		key: &[u8],
	) -> Result<Option<(Vec<u8>, Vec<u8>)>, String> {
		let trie_prefix = child_prefixed_key(child, &[]);
		let start = child_prefixed_key(child, key);

		let mut iter = self.db.iter_from(crate::columns::STATE_SNAPSHOT, start.as_slice());
		while let Some((key, value)) = iter.next() {
			if !key.starts_with(trie_prefix.as_slice()) {
				return Ok(None);
			}
			if key == start {
				continue;
			}
			if let Some(value) = HistoriedDB::decode_inner(
				key.as_slice(),
				value.as_slice(),
				&self.current_state,
			)? {
				return Ok(Some((key, value)));
			}
		}
		Ok(None)
	}

}

impl HistoriedDB {
	/// Iterator on key values. 
	pub fn iter<'a>(&'a self, column: u32) -> impl Iterator<Item = (Vec<u8>, Vec<u8>)> + 'a {
		self.db.iter(column).filter_map(move |(k, v)| {
			let v = HValue::decode_with_context(&mut &v[..])
				.or_else(|| {
					warn!("Invalid historied value k {:?}, v {:?}", k, v);
					None
				})
				.expect("Invalid encoded historied value, DB corrupted");
			let v = v.value(&self.current_state)
				.expect("Invalid encoded historied value, DB corrupted");
			v.map(|v| (k, v))
		})
	}

	/// Iterator on key values, starting at a given position. TODO is it use???
	pub fn iter_from<'a>(&'a self, start: &[u8], column: u32) -> impl Iterator<Item = (Vec<u8>, Vec<u8>)> + 'a {
		self.db.iter_from(column, start).filter_map(move |(k, v)| {
			let v = HValue::decode_with_context(&mut &v[..])
				.or_else(|| {
					warn!("decoding fail for k {:?}, v {:?}", k, v);
					None
				})
				.expect("Invalid encoded historied value, DB corrupted");
			let v = v.value(&self.current_state)
				.expect("Invalid encoded historied value, DB corrupted");
			v.map(|v| (k, v))
		})
	}
}

/// Key value db change for at a given block of an historied DB.
/// TODO should we remove DB for the pr?
pub struct HistoriedDBMut<DB> {
	/// Branch head indexes to change values of a latest block.
	pub current_state: Latest<(u32, u64)>,
	/// Branch head indexes to change values of a latest block.
	/// TODO is it of any use?? (remove)
	pub current_state_read: ForkPlan<u32, u64>,
	/// Inner database to modify historied values.
	pub db: DB,
	/// Configuration for this db.
	pub config: SnapshotDbConf,
}

impl<DB: Database<DbHash>> HistoriedDBMut<DB> {
	/// Create a transaction for this historied db.
	pub fn transaction(&self) -> Transaction<DbHash> {
		Transaction::new()
	}

	/// write a single value in change set.
	/// TODO use branch and block nodes backend as in offchain-storage
	pub fn update_single(
		&mut self,
		child_info: Option<&ChildInfo>,
		k: &[u8],
		change: Option<Vec<u8>>,
		change_set: &mut Transaction<DbHash>,
	) {
		let key = child_prefixed_key(child_info, k);
		self.update_single_inner(key.as_slice(), change, change_set, crate::columns::STATE_SNAPSHOT)
	}

	/// write a single value in change set.
	pub fn update_single_inner(
		&mut self,
		k: &[u8],
		change: Option<Vec<u8>>,
		change_set: &mut Transaction<DbHash>,
		column: u32,
	) {
		let histo = if let Some(histo) = self.db.get(column, k) {
			Some(HValue::decode_with_context(&mut &histo[..]).expect("Bad encoded value in db, closing"))
		} else {
			if change.is_none() {
				return;
			}
			None
		};
		match if let Some(mut histo) = histo {
			let update = histo.set_change(change, &self.current_state, &self.current_state_read)
				.expect("Could not write change in snapshot db, DB corrupted");
			(histo, update)
		} else {
			if let Some(v) = change {
				let value = HValue::new(v, &self.current_state);
				(value, UpdateResult::Changed(()))
			} else {
				return;
			}
		} {
			(value, UpdateResult::Changed(())) => {
				change_set.set_from_vec(column, k, value.encode()
					.expect("Could not encode."));
			},
			(_value, UpdateResult::Cleared(())) => {
				change_set.remove(column, k);
			},
			(_value, UpdateResult::Unchanged) => (),
		}
	}

	/// write a single value, without checking current state,
	/// please only use on new empty db.
	pub fn unchecked_new_single(
		&mut self,
		child_info: Option<&ChildInfo>,
		k: &[u8],
		v: Vec<u8>,
		change_set: &mut Transaction<DbHash>,
	) {
		let key = child_prefixed_key(child_info, k);
		self.unchecked_new_single_inner(key.as_slice(), v, change_set, crate::columns::STATE_SNAPSHOT)
	}

	fn unchecked_new_single_inner(&mut self, k: &[u8], v: Vec<u8>, change_set: &mut Transaction<DbHash>, column: u32) {
		let value = HValue::new(v, &self.current_state);
		let value = value.encode()
			.expect("Could not encode.");
		change_set.set_from_vec(column, k, value);
		// no need for no value set
	}
}

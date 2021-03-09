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

use crate::error;
use crate::params::{GenericNumber, DatabaseParams, PruningParams, SharedParams, BlockNumberOrHash};
use crate::CliConfiguration;
use log::info;
use sc_service::config::DatabaseConfig;
use sc_client_api::{SnapshotDb, StateBackend, StateVisitor, DatabaseError};
use sp_blockchain::HeaderBackend;
use sp_runtime::traits::{Block as BlockT, Header as HeaderT};
use sp_runtime::generic::BlockId;
use std::fmt::Debug;
use std::marker::PhantomData;
use std::path::PathBuf;
use std::str::FromStr;
use std::sync::Arc;
use structopt::StructOpt;
use structopt::clap::arg_enum;
use sp_runtime::codec::Encode;
use std::io::Write;

// TODO current cache does worsen perf,
// when fix restore a non null default value
// const DEFAULT_CACHE_SIZE: u32 = 1000;
const DEFAULT_CACHE_SIZE: u32 = 0;

arg_enum! {
	/// Mode for the snapshot
	/// storage.
	#[allow(missing_docs)]
	#[derive(Debug, Copy, Clone, PartialEq, Eq)]
	pub enum SnapshotMode {
		// No specific delta applied.
		Default,
		// Uses xdelta 3 library to store diffs.
		Xdelta3,
	}
}

/// Parameters to define the snapshot db pruning mode
#[derive(Debug, StructOpt, Clone)]
pub struct SnapshotPruningParams {
	/// Specify the state pruning mode, a number of blocks to keep or 'archive'.
	///
	/// Default is to keep all block states if the node is running as a
	/// validator (i.e. 'archive'), otherwise state is only kept for the last
	/// 256 blocks.
	#[structopt(long = "snapshot_pruning", value_name = "PRUNING_MODE")]
	pub snapshot_pruning: Option<String>,
}


/// Snapshot configuration.
#[derive(Debug, Clone, StructOpt)]
pub struct SnapshotConf {
	/// Snapshot db is used as primary key value backend.
	#[structopt(long)]
	pub use_as_primary: Option<bool>,

	/// Snapshot db checked against trie state for debugging.
	#[structopt(long)]
	pub debug_assert: Option<bool>,

	/// Snapshot lru cache and size.
	///
	/// Defaults to a 1000 elements cache.
	#[structopt(long)]
	pub snapshot_cache: Option<u32>,

	#[structopt(long)]
	/// Db pruning uses key change journals.
	/// Can be use on archive state db to prune manually.
	///
	/// Default is true for non archive mode and false if archive pruning.
	/// Note that it fails on existing configuration.
	pub with_journals: bool,

	#[structopt(long, value_name = "COUNT")]
	/// Experimental, apply pruning lazilly on update.
	/// This uses a window so we do only prune at pruning
	/// keep_blocks - lazy_pruning_window for this window
	/// of updates.
	/// Require to change keep_blocks value accordingly.
	/// TODO unimplemented for now, just to keep in mind
	/// it is doable.
	pub lazy_pruning_window: Option<u32>,

	/// Pruning behavior to set or apply on the snapshot db.
	#[structopt(flatten)]
	pub snapshot_pruning_params: SnapshotPruningParams,

	#[structopt(long)]
	/// Db history is split in multiple nodes.
	/// This allows using a single node for the whole history,
	/// for setup with aggressive pruning.
	///
	/// Default is false.
	pub no_node_backend: bool,

	/// Specify DB mode.
	/// Only for initialization.
	#[structopt(
		long,
		value_name = "MODE",
		possible_values = &SnapshotMode::variants(),
		case_insensitive = true,
		default_value = "Default"
	)]
	pub db_mode: SnapshotMode,
}

fn pruning_conf(params: &SnapshotPruningParams) -> Option<Option<u32>> {
	match &params.snapshot_pruning {
		Some(ref s) if s == "archive" => Some(None),
		None => None,
		Some(s) => {
			let s = s.parse().expect("Invalid snapshot pruning mode specified");
			Some(Some(s))
		}
	}
}

impl Into<sc_client_api::SnapshotDbConf> for SnapshotConf {
	fn into(self) -> sc_client_api::SnapshotDbConf {
		sc_client_api::SnapshotDbConf {
			enabled: true,
			lazy_set: true,
			start_block: None,
			primary_source: self.use_as_primary.unwrap_or(false),
			debug_assert: self.debug_assert.unwrap_or(false),
			lazy_pruning: self.lazy_pruning_window,
			no_node_backend: self.no_node_backend,
			pruning: pruning_conf(&self.snapshot_pruning_params),
			journal_pruning: self.with_journals,
			diff_mode: match self.db_mode {
				SnapshotMode::Default => sc_client_api::SnapshotDBMode::NoDiff,
				SnapshotMode::Xdelta3 => sc_client_api::SnapshotDBMode::Xdelta3Diff,
			},
			cache_size: self.snapshot_cache.unwrap_or(DEFAULT_CACHE_SIZE),
		}
	}
}

/// The `snapshot` command used to manage snapshot db.
#[derive(Debug, StructOpt)]
pub struct SnapshotManageCmd {
	/// Apply pruning on the snapshot.
	/// Can be use on archive state db to prune manually.
	#[structopt(long)]
	pub do_prune: bool,

	/// Do clear the snapshot db.
	#[structopt(long)]
	pub do_clear: bool,

	/// Do init a fresh snapshot db at the current head
	/// with no history with given pruning configuration params.
	///
	/// Existing db is cleared.
	#[structopt(long)]
	pub do_init: bool,

	/// Update configuration in parameter, some parameter do not
	/// support update.
	///
	/// Only support 'use_as_primary', 'debug_assert' and 'lazy_pruning_window'.
	#[structopt(long)]
	pub do_update_conf: bool,

	/// Experimental, same as do init, but also revert state at the given
	/// block number.
	/// TODO can be implemented later (revert), as clear and later init
	/// is a ok initial strategy. (but if maintaining full history
	/// it is not).
	#[structopt(long, value_name = "HASH or NUMBER")]
	pub init_at: Option<BlockNumberOrHash>,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub database_params: DatabaseParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub pruning_params: PruningParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub snapshot_conf: SnapshotConf,
}

/// The `snapshot` command used to export snapshot.
#[derive(Debug, StructOpt)]
pub struct SnapshotExportCmd {
	/// Output file name or stdout if unspecified.
	#[structopt(parse(from_os_str))]
	pub output: Option<PathBuf>,

	/// Specify starting block number.
	///
	/// Default is genesis.
	/// Do not apply with `flat` format.
	#[structopt(long = "from", value_name = "BLOCK")]
	pub from: Option<GenericNumber>,

	/// Specify last block number.
	///
	/// Default is best block.
	#[structopt(long = "to", value_name = "BLOCK")]
	pub to: Option<GenericNumber>,

	/// Export only a single state in a flat format.
	///
	/// Default is non flat.
	#[structopt(long)]
	pub flat: bool,

	/// Export only state.
	#[structopt(long)]
	pub state_only: bool,

	/// Specify DB mode.
	#[structopt(
		long,
		value_name = "MODE",
		possible_values = &SnapshotMode::variants(),
		case_insensitive = true,
		default_value = "Default"
	)]
	pub db_mode: SnapshotMode,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub database_params: DatabaseParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub pruning_params: PruningParams,
}

/// The `snapshot` command used to import snapshot.
/// TODO shared param with manage cmd
#[derive(Debug, StructOpt)]
pub struct SnapshotImportCmd {
	/// Input file or stdin if unspecified.
	#[structopt(parse(from_os_str))]
	pub input: Option<PathBuf>,

	/// Do we keep snapshot db after import.
	#[structopt(long)]
	pub without_snapshot: bool,

	#[structopt(long, value_name = "COUNT")]
	/// Limit the number of trie states that get build
	/// from this snapshot, starting from  latest state.
	pub limit_state_building: Option<u32>,

	/// Experimental, this do revert state to snapshot latest block
	/// and do not clear state.
	/// TODO can be implemented later (revert), as clear and later init
	/// is a ok initial strategy. (but if maintaining full history
	/// it is not).
	#[structopt(long, value_name = "HASH or NUMBER")]
	pub init_at: Option<BlockNumberOrHash>,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub database_params: DatabaseParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub pruning_params: PruningParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub snapshot_conf: SnapshotConf,
}

impl SnapshotManageCmd {
	/// Run the export-snapshot command
	pub async fn run<B, BA>(
		&self,
		backend: Arc<BA>,
		database_config: DatabaseConfig,
	) -> error::Result<()>
	where
		B: BlockT,
		BA: sc_client_api::backend::Backend<B>,
		B::Hash: FromStr,
		<B::Hash as FromStr>::Err: Debug,
		<<B::Header as HeaderT>::Number as FromStr>::Err: Debug,
	{
		if let DatabaseConfig::RocksDb { ref path, .. } = database_config {
			info!("DB path: {}", path.display());
		}

		match (self.do_prune, self.do_clear, self.do_init, self.do_update_conf) {
			(true, false, false, false) => self.do_prune(backend),
			(false, true, false, false) => self.do_clear(backend),
			(false, false, true, false) => self.do_init(backend),
			(false, false, false, true) => self.do_update_conf(backend),
			_ => {
				let error = "Need one and only one of 'do_prune', 'do_clear', 'do_init' \
										 or 'do_update_conf' argument";
				eprintln!("{}", error);
				Err(error.into())
			},
		}
	}
}

const UNSUPPORTED: &str = "Unsupported snapshot.";

impl SnapshotManageCmd {
	fn do_prune<B, BA>(
		&self,
		_backend: Arc<BA>,
	) -> error::Result<()>
	where
		B: BlockT,
		BA: sc_client_api::backend::Backend<B>,
		B::Hash: FromStr,
		<B::Hash as FromStr>::Err: Debug,
		<<B::Header as HeaderT>::Number as FromStr>::Err: Debug,
	{
		unimplemented!()
	}

	fn do_clear<B, BA>(
		&self,
		backend: Arc<BA>,
	) -> error::Result<()>
	where
		B: BlockT,
		BA: sc_client_api::backend::Backend<B>,
		B::Hash: FromStr,
		<B::Hash as FromStr>::Err: Debug,
		<<B::Header as HeaderT>::Number as FromStr>::Err: Debug,
	{
		let db = backend.snapshot_db().expect(UNSUPPORTED);
		// No specific parameters.
		db.clear_snapshot_db()?;
		Ok(())
	}

	fn do_init<B, BA>(
		&self,
		backend: Arc<BA>,
	) -> error::Result<()>
	where
		B: BlockT,
		BA: sc_client_api::backend::Backend<B>,
		B::Hash: FromStr,
		<B::Hash as FromStr>::Err: Debug,
		<<B::Header as HeaderT>::Number as FromStr>::Err: Debug,
	{
		let db = backend.snapshot_db().expect(UNSUPPORTED);

		let chain_info = backend.blockchain().info();

		if self.init_at.is_some() {
			unimplemented!("Unimplemented TODO revert chain & then same call");
		}

		let mut config: sc_client_api::SnapshotDbConf = self.snapshot_conf.clone().into();
		config.start_block = Some(chain_info.best_number.encode());
		let state_visitor = StateVisitorImpl(&backend, &chain_info.best_hash);
		db.re_init(
			config,
			chain_info.best_hash,
			state_visitor,
		)?;
		Ok(())
	}

	fn do_update_conf<B, BA>(
		&self,
		backend: Arc<BA>,
	) -> error::Result<()>
	where
		B: BlockT,
		BA: sc_client_api::backend::Backend<B>,
		B::Hash: FromStr,
		<B::Hash as FromStr>::Err: Debug,
		<<B::Header as HeaderT>::Number as FromStr>::Err: Debug,
	{
		let db = backend.snapshot_db().expect(UNSUPPORTED);
		db.update_running_conf(
			self.snapshot_conf.use_as_primary,
			self.snapshot_conf.debug_assert,
			pruning_conf(&self.snapshot_conf.snapshot_pruning_params),
			self.snapshot_conf.lazy_pruning_window,
			self.snapshot_conf.snapshot_cache,
		)?;
		Ok(())
	}
}

struct StateVisitorImpl<'a, B: BlockT, BA>(&'a Arc<BA>, &'a B::Hash);

impl<'a, B, BA> StateVisitor for StateVisitorImpl<'a, B, BA>
	where
		B: BlockT,
		BA: sc_client_api::backend::Backend<B>,
{
	fn state_visit(
		&self,
		mut visitor: impl FnMut(Option<&[u8]>, Vec<u8>, Vec<u8>) -> std::result::Result<(), DatabaseError>,
	) -> std::result::Result<(), DatabaseError> {
		let mut state = self.0.state_at(BlockId::Hash(self.1.clone()))
			.map_err(|e| DatabaseError(Box::new(e)))?;
		let trie_state = state.as_trie_backend().expect("Snapshot runing on a trie backend.");

		let mut prev_child = None;
		let prev_child = &mut prev_child;
		let mut prefixed_storage_key = None;
		let prefixed_storage_key = &mut prefixed_storage_key;
		trie_state.for_key_values(|child, key, value| {
			if child != prev_child.as_ref() {
				println!("TOUCHED CHILD");
				*prefixed_storage_key = child.map(|ci| ci.prefixed_storage_key().into_inner());
				*prev_child = child.cloned();
			}
			println!("kr: {:?} {:?}", key, value);
			visitor(
				prefixed_storage_key.as_ref().map(Vec::as_slice),
				key,
				value,
			).expect("Failure adding value to snapshot db.");
		}).map_err(|e| {
			let error: error::Error = e.into();
			DatabaseError(Box::new(error))
		})?;
		Ok(())
	}
}

#[repr(u8)]
enum StateOnly {
	Yes = 0,
	No = 1,
}

impl SnapshotImportCmd {
	/// Run the import-snapshot command
	pub async fn run<B, BA>(
		&self,
		backend: Arc<BA>,
		database_config: DatabaseConfig,
	) -> error::Result<()>
	where
		B: BlockT,
		BA: sc_client_api::backend::Backend<B>,
		B::Hash: FromStr,
		<B::Hash as FromStr>::Err: Debug,
		<<B::Header as HeaderT>::Number as FromStr>::Err: Debug,
	{
		if let DatabaseConfig::RocksDb { ref path, .. } = database_config {
			info!("DB path: {}", path.display());
		}

		// TODO no real need for dyn here.
		let mut file: Box<dyn crate::commands::import_blocks_cmd::ReadPlusSeek + Send> = match &self.input {
			Some(filename) => Box::new(std::fs::File::open(filename)?),
			None => {
				use std::io::Read;
				let mut buffer = Vec::new();
				// TODO use an actual read
				std::io::stdin().read_to_end(&mut buffer)?;
				Box::new(std::io::Cursor::new(buffer))
			}
		};

		let db = backend.snapshot_db().expect(UNSUPPORTED);
		let dest_config: sc_client_api::SnapshotDbConf = self.snapshot_conf.clone().into();
		let mut config = dest_config.clone();
		// import default values will be reverted: tod can move to import_snapshot_db function
		// (revert too)
		config.enabled = true;
		config.pruning = None;
		config.lazy_pruning = None;
		config.primary_source = true; // needed to access historied-db
		config.debug_assert = false; // not really useful

		let reader = &mut file;
		let mut buf = [0];
		reader.read_exact(&mut buf[..1])?;
		match buf[0] {
			b if b == StateOnly::No as u8 => backend.snapshot_sync().import_sync_meta(reader)?,
			b if b == StateOnly::Yes as u8 => (),
			_ => panic!("Invalid first byte for snapshot"),
		}

		// TODO read_import def seems rather useless, and all logic afterwards should be move to
		// snapshot.rs
		let snapshot_def = db.read_import_def(reader, &config)?;
		if snapshot_def.is_flat {
			let (finalized_hash, finalized_number) = if let Some(start_block) = dest_config.start_block.as_ref() {
				unimplemented!("TODO fetch");
			} else {
				// injected with 'import_sync_meta'.
				let chain_info = backend.blockchain().info();
				(chain_info.finalized_hash, chain_info.finalized_number)
			};

			// init snapshot db
			db.import_snapshot_db(reader, &config, &snapshot_def, &finalized_hash)?;

			println!("finalized: {:?} {:?}", finalized_number, finalized_hash);
			let header = backend.blockchain().header(BlockId::Hash(finalized_hash.clone()))?
				.expect("Missing header");
			let expected_root = header.state_root().clone();
			println!("finalized root: {:?}", expected_root);
			let mut op = backend.begin_operation()
				.map_err(|e| DatabaseError(Box::new(e)))?;
			backend.begin_state_operation(&mut op, BlockId::Hash(Default::default()))
				.map_err(|e| DatabaseError(Box::new(e)))?;
			info!("Initializing import block/state (header-hash: {})",
				finalized_hash,
			);
			let data = db.state_iter_at(&finalized_hash, Some(&config))?;
			use sc_client_api::BlockImportOperation;
			let state_root = op.inject_finalized_state(&finalized_hash, data)
				.map_err(|e| DatabaseError(Box::new(e)))?;
			// TODO get state root from header and pass as param
			if expected_root != state_root {
				panic!("Unexpected root {:?}, in header {:?}.", state_root, expected_root);
			}
			/* only state import, headers are already written.
				operation.op.set_block_data(
				import_headers.post().clone(),
				body,
				justification,
				leaf_state,
			)?;
			*/
			backend.commit_operation(op)
				.map_err(|e| DatabaseError(Box::new(e)))?;
	
			if self.without_snapshot {
				// clear snapshot db
				db.clear_snapshot_db()?;
			} else {
				db.update_running_conf(
					Some(dest_config.primary_source),
					Some(dest_config.debug_assert),
					dest_config.pruning,
					dest_config.lazy_pruning,
					Some(dest_config.cache_size),
				)?;
				if dest_config.pruning.is_some() {
					// run pruning now
					unimplemented!();
				}
			}
		} else {
			unimplemented!();
		}
		Ok(())
	}
}

impl SnapshotExportCmd {
	/// Run the export-snapshot command
	pub async fn run<B, BA>(
		&self,
		backend: Arc<BA>,
		database_config: DatabaseConfig,
	) -> error::Result<()>
	where
		B: BlockT,
		BA: sc_client_api::backend::Backend<B>,
		B::Hash: FromStr,
		<B::Hash as FromStr>::Err: Debug,
		<<B::Header as HeaderT>::Number as FromStr>::Err: Debug,
	{
		if let DatabaseConfig::RocksDb { ref path, .. } = database_config {
			info!("DB path: {}", path.display());
		}

		let db = backend.snapshot_db().expect(UNSUPPORTED);

		let from = if let Some(from) = self.from.as_ref() {
			Some(from.parse()?)
		} else {
			None
		};

		let chain_info = backend.blockchain().info();
		let finalized_hash = chain_info.finalized_hash;
		let finalized_number = chain_info.finalized_number;
		let (to, default_block) = if let Some(to) = self.to.as_ref() {
			let to = to.parse()?;
			let to_hash = backend.blockchain().hash(to)?.expect("Block number out of range.");
			(Some(to), to_hash)
		} else {
			(None, finalized_hash)
		};
		let state_visitor = StateVisitorImpl(&backend, &default_block);
		let db_mode = match self.db_mode {
			SnapshotMode::Default => sc_client_api::SnapshotDBMode::NoDiff,
			SnapshotMode::Xdelta3 => sc_client_api::SnapshotDBMode::Xdelta3Diff,
		};

		if let Some(path) = &self.output {
			let mut out = std::fs::File::create(path)?;
			if self.state_only {
				out.write(&[StateOnly::Yes as u8])?;
			} else {
				out.write(&[StateOnly::No as u8])?;
				let to = to.unwrap_or(finalized_number);
				let to_hash = default_block; 
				let from = from.unwrap_or(to);
				let from_hash = backend.blockchain().hash(to)?.expect("Block number out of range.");
				backend.snapshot_sync().export_sync_meta(&mut out, from, from_hash, to, to_hash)?;
			}
			db.export_snapshot(
				&mut out,
				finalized_number,
				from,
				to,
				self.flat,
				db_mode,
				state_visitor,
			)?;
		} else {
			let mut out = std::io::stdout();
			if self.state_only {
				out.write(&[StateOnly::Yes as u8])?;
			} else{
				out.write(&[StateOnly::No as u8])?;
				let to = to.unwrap_or(finalized_number);
				let to_hash = default_block; 
				let from = from.unwrap_or(to);
				let from_hash = backend.blockchain().hash(to)?.expect("Block number out of range.");
				backend.snapshot_sync().export_sync_meta(&mut out, from, from_hash, to, to_hash)?;
				println!("finalized: {:?} {:?}", finalized_number, to_hash);
				let header = backend.blockchain().header(BlockId::Hash(to_hash.clone()))?
					.expect("Missing header");
				let expected_root = header.state_root().clone();
				println!("finalized root: {:?}", expected_root);
	
			}
			db.export_snapshot(
				&mut out,
				finalized_number,
				from,
				to,
				self.flat,
				db_mode,
				state_visitor,
			)?;
			println!("finalized ex: {:?} {:?}", finalized_number, to);
		};

		Ok(())
	}
}

impl CliConfiguration for SnapshotManageCmd {
	fn shared_params(&self) -> &SharedParams {
		&self.shared_params
	}

	fn database_params(&self) -> Option<&DatabaseParams> {
		Some(&self.database_params)
	}

	fn pruning_params(&self) -> Option<&PruningParams> {
		Some(&self.pruning_params)	
	}
}

impl CliConfiguration for SnapshotExportCmd {
	fn shared_params(&self) -> &SharedParams {
		&self.shared_params
	}

	fn database_params(&self) -> Option<&DatabaseParams> {
		Some(&self.database_params)
	}

	fn pruning_params(&self) -> Option<&PruningParams> {
		Some(&self.pruning_params)	
	}
}

impl CliConfiguration for SnapshotImportCmd {
	fn shared_params(&self) -> &SharedParams {
		&self.shared_params
	}

	fn database_params(&self) -> Option<&DatabaseParams> {
		Some(&self.database_params)
	}

	fn pruning_params(&self) -> Option<&PruningParams> {
		Some(&self.pruning_params)	
	}
}

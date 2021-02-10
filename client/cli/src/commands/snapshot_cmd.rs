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
use sc_service::{
	config::DatabaseConfig, chain_ops::export_blocks,
};
use sc_client_api::{BlockBackend, UsageProvider};
use sp_runtime::traits::{Block as BlockT, Header as HeaderT};
use std::fmt::Debug;
use std::fs;
use std::io;
use std::path::PathBuf;
use std::str::FromStr;
use std::sync::Arc;
use structopt::StructOpt;
use structopt::clap::arg_enum;

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

/// The `snapshot` command used to manage snapshot db.
#[derive(Debug, StructOpt)]
pub struct SnapshotManageCmd {
	/// Apply pruning on the snapshot.
	/// Can be use on archive state db to prune manually.
	///
	/// Default is non flat.
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
	#[structopt(long)]
	pub do_update_conf: bool,

	/// Experimental, same as do init, but also revert state at the given
	/// block number.
	/// TODO can be implemented later (revert), as clear and later init
	/// is a ok initial strategy. (but if maintaining full history
	/// it is not).
	#[structopt(long, value_name = "HASH or NUMBER")]
	pub init_at: Option<BlockNumberOrHash>,

	#[structopt(long)]
	/// Snapshot db is used as primary key value backend.
	pub use_as_primary: bool,

	#[structopt(long)]
	/// Snapshot db checked against trie state for debugging.
	pub debug_assert: bool,

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
	pub pruning_params: PruningParams,

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

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub database_params: DatabaseParams,
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

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub database_params: DatabaseParams,
}

/// The `snapshot` command used to import snapshot.
/// TODO shared param with manage cmd
#[derive(Debug, StructOpt)]
pub struct SnapshotImportCmd {
	#[structopt(long, value_name = "COUNT")]
	/// Limit the number of trie states that get build
	/// from thiss snapshot, starting from  latest state.
	pub limit_state_building: Option<u32>,

	/// Experimental, this do revert state to snapshot latest block
	/// and do not clear state.
	/// TODO can be implemented later (revert), as clear and later init
	/// is a ok initial strategy. (but if maintaining full history
	/// it is not).
	#[structopt(long, value_name = "HASH or NUMBER")]
	pub init_at: Option<BlockNumberOrHash>,

	#[structopt(long)]
	/// Snapshot db is used as primary key value backend.
	pub use_as_primary: bool,

	#[structopt(long)]
	/// Snapshot db checked against trie state for debugging.
	pub debug_assert: bool,

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
	pub pruning_params: PruningParams,

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

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub database_params: DatabaseParams,
}

impl SnapshotExportCmd {
	/// Run the export-blocks command
	pub async fn run<B, C>(
		&self,
		client: Arc<C>,
		database_config: DatabaseConfig,
	) -> error::Result<()>
	where
		B: BlockT,
		C: BlockBackend<B> + UsageProvider<B> + 'static,
		<<B::Header as HeaderT>::Number as FromStr>::Err: Debug,
	{
		if let DatabaseConfig::RocksDb { ref path, .. } = database_config {
			info!("DB path: {}", path.display());
		}
		unimplemented!()
/*
		let from = self.from.as_ref().and_then(|f| f.parse().ok()).unwrap_or(1u32);
		let to = self.to.as_ref().and_then(|t| t.parse().ok());

		let binary = self.binary;

		let file: Box<dyn io::Write> = match &self.output {
			Some(filename) => Box::new(fs::File::create(filename)?),
			None => Box::new(io::stdout()),
		};

		export_blocks(client, file, from.into(), to, binary)
			.await
			.map_err(Into::into)
*/
	}
}

impl CliConfiguration for SnapshotExportCmd {
	fn shared_params(&self) -> &SharedParams {
		&self.shared_params
	}

	fn database_params(&self) -> Option<&DatabaseParams> {
		Some(&self.database_params)
	}
}

impl CliConfiguration for SnapshotManageCmd {
	fn pruning_params(&self) -> Option<&PruningParams> {
		Some(&self.pruning_params)
	}

	fn database_params(&self) -> Option<&DatabaseParams> {
		Some(&self.database_params)
	}

	fn shared_params(&self) -> &SharedParams {
		&self.shared_params
	}
}

impl CliConfiguration for SnapshotImportCmd {
	fn pruning_params(&self) -> Option<&PruningParams> {
		Some(&self.pruning_params)
	}

	fn database_params(&self) -> Option<&DatabaseParams> {
		Some(&self.database_params)
	}

	fn shared_params(&self) -> &SharedParams {
		&self.shared_params
	}
}

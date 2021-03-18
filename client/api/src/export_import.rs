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

//! Api related to snapshot export and import.

use sp_blockchain::{HeaderBackend, HeaderMetadata, Error};
use sp_runtime::traits::{NumberFor, Block as BlockT};
use std::borrow::Borrow;
use crate::DatabaseError;
use codec::{Encode, Decode};
use sp_database::{error, StateIter, StateIterDelta};


#[derive(Clone, Debug, Encode, Decode)]
/// Different storage mode.
pub enum SnapshotDBMode {
	/// Do not apply binary diff between consecutive values.
	NoDiff,
	/// Use xdelta3 VcDiff.
	Xdelta3Diff,
}

impl Default for SnapshotDBMode {
	fn default() -> Self {
		SnapshotDBMode::NoDiff
	}
}

#[derive(Clone, Debug, Default, Encode, Decode)]
/// Configuration of snapshot db conf.
pub struct SnapshotDbConf {
	/// Is snapshot db active.
	pub enabled: bool,
	/// Should we use this db value instead of trie value in state machine
	/// when possible.
	pub primary_source: bool,
	/// Snapshot lru cache and size.
	pub cache_size: u32,
	/// Do we use node backend.
	pub no_node_backend: bool,
	/// Do we maintain key modification journaling for pruning?
	pub journal_pruning: bool,
	/// Should we debug value access in state machine against the trie values.
	pub debug_assert: bool,
	/// Lower block support, this should block reorg before it.
	/// It contains encoded start block number.
	pub start_block: Option<Vec<u8>>,
	/// Diff usage.
	pub diff_mode: SnapshotDBMode,
	/// If defined, pruning window size to apply, `None` for archive.
	pub pruning: Option<Option<u32>>,
	/// Lazy pruning window. (place holder TODO unimplemented)
	pub lazy_pruning: Option<u32>,
	/// Technical field to identify if the conf has been initialized.
	/// TODO remove and have Variable::is_defined function in remote historied_db
	pub lazy_set: bool,
}

/// Range covered by snapshot.
#[derive(Clone, Debug)]
pub struct RangeSnapshot<B: BlockT> {
	/// Number to start from.
	pub from: NumberFor<B>,

	/// Hash to start from.
	pub from_hash: B::Hash,

	/// Number of max block.
	pub to: NumberFor<B>,

	/// Hash of max block.
	pub to_hash: B::Hash,

	/// Kind of snapshot db to use.
	pub mode: SnapshotDBMode,

	/// Is the snapshot flat (only write last state).
	pub flat: bool,
}

/// Implement exposed acces method to the snapshot db.
pub trait SnapshotDb<B: BlockT> {
	/// Disable snapshot db and remove its content.
	fn clear_snapshot_db(&self) -> error::Result<()>;

	/// Change current snapshot db behavior.
	fn update_running_conf(
		&self,
		use_as_primary: Option<bool>,
		debug_assert: Option<bool>,
		pruning_window: Option<Option<u32>>,
		lazy_pruning_window: Option<u32>,
		cache_size: Option<u32>,
	) -> error::Result<()>;

	/// Reset db at a given block.
	fn re_init(
		&self,
		config: SnapshotDbConf,
		best_block: B::Hash,
		state_visit: impl StateVisitor,
	) -> error::Result<()>;

	/// Export a snapshot file.
	fn export_snapshot(
		&self,
		output: &mut dyn std::io::Write,
		range: &RangeSnapshot<B>,
		default_flat: impl StateVisitor,
	) -> error::Result<()>;

	/// Iterate on all values at a given block.
	/// Note that we could also use `BuildStorage` trait
	/// but don't as it would put the whole storage in memory.
	/// (actually when importing we put the whole storage in
	/// memory into the state machine transaction, but doesn't
	/// sound like a reason to put more in memory).
	/// So we do not use `reset_storage` but similar code at client level.
	fn state_iter_at<'a>(
		&'a self,
		at: &B::Hash,
		config: Option<&SnapshotDbConf>,
	) -> error::Result<StateIter<'a>>;

	/// Iterate on all values that differs from parent block at a given block.
	fn state_iter_diff_at<'a>(
		&'a self,
		_at: &B::Hash,
		_parent: &B::Hash,
	) -> error::Result<StateIterDelta<'a>> {
		unimplemented!("TODO");
	}

	/// Import snapshot db content.
	fn import_snapshot_db(
		&self,
		from: &mut dyn std::io::Read,
		config: &SnapshotDbConf,
		range: &RangeSnapshot<B>,
	) -> error::Result<()>;
}

/// Visitor trait use to initiate a snapshot db.
pub trait StateVisitor {
	/// Visit with call back taking the child trie root path and related key values for arguments.
	///
	/// The ordered is required to be top trie then child trie by prefixed storage key order, with
	/// every trie key values consecutively ordered.
	fn state_visit(
		&self,
		visitor: impl FnMut(Option<&[u8]>, Vec<u8>, Vec<u8>) -> error::Result<()>,
	) -> error::Result<()>;
}

/// The error type for snapshot database operations.
#[derive(Debug)]
pub enum SnapshotDbError {
	Unsupported,
}

impl std::fmt::Display for SnapshotDbError {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		match self {
			SnapshotDbError::Unsupported => {
				write!(f, "Unsupported snapshot db.")
			},
		}
	}
}

impl std::error::Error for SnapshotDbError {
	fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
		None
	}
}

fn unsupported_error<R>() -> error::Result<R> {
	Err(error::DatabaseError(Box::new(SnapshotDbError::Unsupported)))
}

/// Use '()' when no snapshot implementation.
impl<B: BlockT> SnapshotDb<B> for () {
	fn clear_snapshot_db(&self) -> error::Result<()> {
		unsupported_error()
	}

	fn update_running_conf(
		&self,
		_use_as_primary: Option<bool>,
		_debug_assert: Option<bool>,
		_pruning_window: Option<Option<u32>>,
		_lazy_pruning_window: Option<u32>,
		_cache_size: Option<u32>,
	) -> error::Result<()> {
		unsupported_error()
	}

	fn re_init(
		&self,
		_config: SnapshotDbConf,
		_best_block: B::Hash,
		_state_visit: impl StateVisitor,
	) -> error::Result<()> {
		unsupported_error()
	}

	fn export_snapshot(
		&self,
		_output: &mut dyn std::io::Write,
		_range: &RangeSnapshot<B>,
		_default_flat: impl StateVisitor,
	) -> error::Result<()> {
		unsupported_error()
	}

	fn state_iter_at<'a>(
		&'a self,
		_at: &B::Hash,
		_config: Option<&SnapshotDbConf>,
	) -> error::Result<StateIter<'a>> {
		unsupported_error()
	}

	fn import_snapshot_db(
		&self,
		_from: &mut dyn std::io::Read,
		_config: &SnapshotDbConf,
		_range: &RangeSnapshot<B>,
	) -> error::Result<()> {
		unsupported_error()
	}
}

/// A state visitor implementation for a given backend at a given block.
pub struct StateVisitorImpl<'a, B: BlockT, BA>(pub &'a BA, pub &'a B::Hash);

impl<'a, B, BA> StateVisitor for StateVisitorImpl<'a, B, BA>
	where
		B: BlockT,
		BA: crate::backend::Backend<B>,
{
	fn state_visit(
		&self,
		mut visitor: impl FnMut(Option<&[u8]>, Vec<u8>, Vec<u8>) -> std::result::Result<(), DatabaseError>,
	) -> std::result::Result<(), DatabaseError> {
		let mut state = self.0.state_at(sp_runtime::generic::BlockId::Hash(self.1.clone()))
			.map_err(|e| DatabaseError(Box::new(e)))?;
		use sp_state_machine::Backend;
		let trie_state = state.as_trie_backend().expect("Snapshot runing on a trie backend.");

		let mut prev_child = None;
		let prev_child = &mut prev_child;
		let mut prefixed_storage_key = None;
		let prefixed_storage_key = &mut prefixed_storage_key;
		trie_state.for_key_values(|child, key, value| {
			if child != prev_child.as_ref() {
				*prefixed_storage_key = child.map(|ci| ci.prefixed_storage_key().into_inner());
				*prev_child = child.cloned();
			}
			visitor(
				prefixed_storage_key.as_ref().map(Vec::as_slice),
				key,
				value,
			).expect("Failure adding value to snapshot db.");
		}).map_err(|e| {
			let error: String = e.into();
			DatabaseError(Box::new(sp_blockchain::Error::Backend(error)))
		})?;
		Ok(())
	}
}

// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

//! The overlayed changes to state.

mod changeset;
mod offchain;
mod filters;
mod markers;
mod loggers;

pub use offchain::OffchainOverlayedChanges;
use crate::{
	backend::Backend,
	stats::StateMachineStats,
};
use sp_std::{vec::Vec, any::{TypeId, Any}, boxed::Box, fmt::Debug};
use self::changeset::OverlayedChangeSet;

#[cfg(feature = "std")]
use crate::{
	ChangesTrieTransaction,
	changes_trie::{
		build_changes_trie,
		State as ChangesTrieState,
	},
};
use crate::changes_trie::BlockNumber;
#[cfg(feature = "std")]
use std::collections::{HashMap as Map, hash_map::Entry as MapEntry};
#[cfg(not(feature = "std"))]
use sp_std::collections::btree_map::{BTreeMap as Map, Entry as MapEntry};
use sp_std::collections::btree_set::BTreeSet;
use codec::{Decode, Encode};
use sp_core::storage::{well_known_keys::EXTRINSIC_INDEX, ChildInfo};
use sp_core::offchain::OffchainOverlayedChange;
use hash_db::Hasher;
use crate::DefaultError;
use sp_externalities::{Extensions, Extension, TaskId, WorkerResult,
	WorkerDeclaration, Change};

pub use self::changeset::{OverlayedValue, NoOpenTransaction, AlreadyInRuntime, NotInRuntime};

/// Changes that are made outside of extrinsics are marked with this index;
pub const NO_EXTRINSIC_INDEX: u32 = 0xffffffff;

/// Storage key.
pub type StorageKey = Vec<u8>;

/// Storage value.
pub type StorageValue = Vec<u8>;

/// In memory array of storage values.
pub type StorageCollection = Vec<(StorageKey, Option<StorageValue>)>;

/// In memory arrays of storage values for multiple child tries.
pub type ChildStorageCollection = Vec<(StorageKey, StorageCollection)>;

/// In memory array of storage values.
pub type OffchainChangesCollection = Vec<((Vec<u8>, Vec<u8>), OffchainOverlayedChange)>;

/// Keep trace of extrinsics index for a modified value.
#[derive(Debug, Default, Eq, PartialEq, Clone)]
pub struct Extrinsics(Vec<u32>);

impl Extrinsics {
	/// Extracts extrinsics into a `BTreeSets`.
	fn copy_extrinsics_into(&self, dest: &mut BTreeSet<u32>) {
		dest.extend(self.0.iter())
	}

	/// Add an extrinsics.
	fn insert(&mut self, ext: u32) {
		if Some(&ext) != self.0.last() {
			self.0.push(ext);
		}
	}

	/// Extend `self` with `other`.
	fn extend(&mut self, other: Self) {
		self.0.extend(other.0.into_iter());
	}
}

/// The set of changes that are overlaid onto the backend.
///
/// It allows changes to be modified using nestable transactions.
#[derive(Debug, Default, Clone)]
pub struct OverlayedChanges {
	/// Top level storage changes.
	top: OverlayedChangeSet,
	/// Child storage changes. The map key is the child storage key without the common prefix.
	children: Map<StorageKey, (OverlayedChangeSet, ChildInfo)>,
	/// Offchain related changes.
	offchain: OffchainOverlayedChanges,
	/// Transaction index changes,
	transaction_index_ops: Vec<IndexOperation>,
	/// True if extrinsics stats must be collected.
	collect_extrinsics: bool,
	/// Collect statistic on this execution.
	stats: StateMachineStats,
	/// Marker keeping trace of worker async externalities in use.
	markers: markers::Markers,
	/// Filters over some key and prefix accesses.
	filters: filters::Filters,
	/// Logger for optimistic workers.
	optimistic_logger: loggers::AccessLogger,
}

impl OverlayedChanges {
	/// An overlay that can be use for child worker.
	/// It contains the overlay changes and ensure
	/// we do not commit or rollback them.
	/// Return None if cannot be spawn from parent.
	pub fn child_worker_overlay(&mut self, worker_id: TaskId, declaration: WorkerDeclaration) -> Option<Self> {
		if !self.declare_child_worker(worker_id, declaration.clone()) {
			return None;
		}
		let mut result = OverlayedChanges::default();
		result.top = self.top.clone();
		result.children = self.children.clone();
		result.stats = Default::default();
		result.start_transaction();
		let transaction_offset = result.top.transaction_depth();
		result.markers = markers::Markers::from_start_depth(transaction_offset);


		result.set_worker_declaration(declaration);

		Some(result)
	}
}

/// Transcation index operation.
#[derive(Debug, Clone)]
pub enum IndexOperation {
	/// Insert transaction into index.
	Insert {
		/// Extrinsic index in the current block.
		extrinsic: u32,
		/// Data offset in the extrinsic.
		offset: u32,
	},
	/// Renew existing transaction storage.
	Renew {
		/// Extrinsic index in the current block.
		extrinsic: u32,
		/// Referenced index hash.
		hash: Vec<u8>,
		/// Expected data size.
		size: u32,
	}
}

/// A storage changes structure that can be generated by the data collected in [`OverlayedChanges`].
///
/// This contains all the changes to the storage and transactions to apply theses changes to the
/// backend.
pub struct StorageChanges<Transaction, H: Hasher, N: BlockNumber> {
	/// All changes to the main storage.
	///
	/// A value of `None` means that it was deleted.
	pub main_storage_changes: StorageCollection,
	/// All changes to the child storages.
	pub child_storage_changes: ChildStorageCollection,
	/// Offchain state changes to write to the offchain database.
	pub offchain_storage_changes: OffchainChangesCollection,
	/// A transaction for the backend that contains all changes from
	/// [`main_storage_changes`](StorageChanges::main_storage_changes) and from
	/// [`child_storage_changes`](StorageChanges::child_storage_changes).
	/// [`offchain_storage_changes`](StorageChanges::offchain_storage_changes).
	pub transaction: Transaction,
	/// The storage root after applying the transaction.
	pub transaction_storage_root: H::Out,
	/// Contains the transaction for the backend for the changes trie.
	///
	/// If changes trie is disabled the value is set to `None`.
	#[cfg(feature = "std")]
	pub changes_trie_transaction: Option<ChangesTrieTransaction<H, N>>,
	/// Phantom data for block number until change trie support no_std.
	#[cfg(not(feature = "std"))]
	pub _ph: sp_std::marker::PhantomData<N>,

	/// Changes to the transaction index,
	#[cfg(feature = "std")]
	pub transaction_index_changes: Vec<IndexOperation>,
}

#[cfg(feature = "std")]
impl<Transaction, H: Hasher, N: BlockNumber> StorageChanges<Transaction, H, N> {
	/// Deconstruct into the inner values
	pub fn into_inner(self) -> (
		StorageCollection,
		ChildStorageCollection,
		OffchainChangesCollection,
		Transaction,
		H::Out,
		Option<ChangesTrieTransaction<H, N>>,
		Vec<IndexOperation>,
	) {
		(
			self.main_storage_changes,
			self.child_storage_changes,
			self.offchain_storage_changes,
			self.transaction,
			self.transaction_storage_root,
			self.changes_trie_transaction,
			self.transaction_index_changes,
		)
	}
}

/// The storage transaction are calculated as part of the `storage_root` and
/// `changes_trie_storage_root`. These transactions can be reused for importing the block into the
/// storage. So, we cache them to not require a recomputation of those transactions.
pub struct StorageTransactionCache<Transaction, H: Hasher, N: BlockNumber> {
	/// Contains the changes for the main and the child storages as one transaction.
	pub(crate) transaction: Option<Transaction>,
	/// The storage root after applying the transaction.
	pub(crate) transaction_storage_root: Option<H::Out>,
	/// Contains the changes trie transaction.
	#[cfg(feature = "std")]
	pub(crate) changes_trie_transaction: Option<Option<ChangesTrieTransaction<H, N>>>,
	/// The storage root after applying the changes trie transaction.
	#[cfg(feature = "std")]
	pub(crate) changes_trie_transaction_storage_root: Option<Option<H::Out>>,
	/// Phantom data for block number until change trie support no_std.
	#[cfg(not(feature = "std"))]
	pub(crate) _ph: sp_std::marker::PhantomData<N>,
}

impl<Transaction, H: Hasher, N: BlockNumber> StorageTransactionCache<Transaction, H, N> {
	/// Reset the cached transactions.
	pub fn reset(&mut self) {
		*self = Self::default();
	}
}

impl<Transaction, H: Hasher, N: BlockNumber> Default for StorageTransactionCache<Transaction, H, N> {
	fn default() -> Self {
		Self {
			transaction: None,
			transaction_storage_root: None,
			#[cfg(feature = "std")]
			changes_trie_transaction: None,
			#[cfg(feature = "std")]
			changes_trie_transaction_storage_root: None,
			#[cfg(not(feature = "std"))]
			_ph: Default::default(),
		}
	}
}

impl<Transaction: Default, H: Hasher, N: BlockNumber> Default for StorageChanges<Transaction, H, N> {
	fn default() -> Self {
		Self {
			main_storage_changes: Default::default(),
			child_storage_changes: Default::default(),
			offchain_storage_changes: Default::default(),
			transaction: Default::default(),
			transaction_storage_root: Default::default(),
			#[cfg(feature = "std")]
			changes_trie_transaction: None,
			#[cfg(not(feature = "std"))]
			_ph: Default::default(),
			#[cfg(feature = "std")]
			transaction_index_changes: Default::default(),
		}
	}
}

impl OverlayedChanges {
	/// Whether no changes are contained in the top nor in any of the child changes.
	pub fn is_empty(&self) -> bool {
		self.top.is_empty() && self.children.is_empty()
	}

	/// Ask to collect/not to collect extrinsics indices where key(s) has been changed.
	pub fn set_collect_extrinsics(&mut self, collect_extrinsics: bool) {
		self.collect_extrinsics = collect_extrinsics;
	}

	/// Returns a double-Option: None if the key is unknown (i.e. and the query should be referred
	/// to the backend); Some(None) if the key has been deleted. Some(Some(...)) for a key whose
	/// value has been set.
	pub fn storage(&mut self, key: &[u8]) -> Option<Option<&[u8]>> {
		self.filters.guard_read(None, key);
		self.optimistic_logger.log_read(None, key);
		let stats = &mut self.stats;
		self.top.get(key).map(|x| {
			let value = x.value();
			let size_read = value.map(|x| x.len() as u64).unwrap_or(0);
			stats.tally_read_modified(size_read);
			value.map(AsRef::as_ref)
		})
	}

	/// Returns mutable reference to current value.
	/// If there is no value in the overlay, the given callback is used to initiate the value.
	/// Warning this function registers a change, so the mutable reference MUST be modified.
	///
	/// Can be rolled back or committed when called inside a transaction.
	#[must_use = "A change was registered, so this value MUST be modified."]
	pub fn value_mut_or_insert_with(
		&mut self,
		key: &[u8],
		init: impl Fn() -> StorageValue,
	) -> &mut StorageValue {
		self.filters.guard_write(None, key);
		// no guard read as write supersed it.
		self.optimistic_logger.log_write(None, key);
		// we need to log read here as we can read it.
		self.optimistic_logger.log_read(None, key);
		let extrinsic_index = self.extrinsic_index();
		let value = self.top.modify(key.to_vec(), init, extrinsic_index);

		// if the value was deleted initialise it back with an empty vec
		change_read_value_mut_default(value)
	}

	/// Returns a double-Option: None if the key is unknown (i.e. and the query should be referred
	/// to the backend); Some(None) if the key has been deleted. Some(Some(...)) for a key whose
	/// value has been set.
	pub fn child_storage(&mut self, child_info: &ChildInfo, key: &[u8]) -> Option<Option<&[u8]>> {
		self.filters.guard_read(Some(child_info), key);
		self.optimistic_logger.log_read(Some(child_info), key);
		let map = self.children.get_mut(child_info.storage_key())?;
		let value = map.0.get(key)?.value();
		let size_read = value.map(|x| x.len() as u64).unwrap_or(0);
		self.stats.tally_read_modified(size_read);
		Some(value.map(AsRef::as_ref))
	}

	/// Set a new value for the specified key.
	///
	/// Can be rolled back or committed when called inside a transaction.
	pub(crate) fn set_storage(&mut self, key: StorageKey, val: Option<StorageValue>) {
		self.filters.guard_write(None, key.as_slice());
		self.optimistic_logger.log_write(None, key.as_slice());
		let size_write = val.as_ref().map(|x| x.len() as u64).unwrap_or(0);
		self.stats.tally_write_overlay(size_write);
		let extrinsic_index = self.extrinsic_index();
		self.top.set(key, val.into(), extrinsic_index);
	}

	/// Set a new value for the specified key and child.
	///
	/// `None` can be used to delete a value specified by the given key.
	///
	/// Can be rolled back or committed when called inside a transaction.
	pub(crate) fn set_child_storage(
		&mut self,
		child_info: &ChildInfo,
		key: StorageKey,
		val: Option<StorageValue>,
	) {
		self.filters.guard_write(Some(child_info), key.as_slice());
		self.optimistic_logger.log_write(Some(child_info), key.as_slice());
		let extrinsic_index = self.extrinsic_index();
		let size_write = val.as_ref().map(|x| x.len() as u64).unwrap_or(0);
		self.stats.tally_write_overlay(size_write);
		let storage_key = child_info.storage_key().to_vec();
		let top = &self.top;
		let (changeset, info) = self.children.entry(storage_key).or_insert_with(||
			(
				top.spawn_child(),
				child_info.clone()
			)
		);
		let updatable = info.try_update(child_info);
		debug_assert!(updatable);
		changeset.set(key, val.into(), extrinsic_index);
	}

	/// Clear child storage of given storage key.
	///
	/// Can be rolled back or committed when called inside a transaction.
	pub(crate) fn clear_child_storage(
		&mut self,
		child_info: &ChildInfo,
	) {
		self.filters.guard_write_prefix(Some(child_info), &[]);
		self.optimistic_logger.log_write_prefix(Some(child_info), &[]);
		let extrinsic_index = self.extrinsic_index();
		let storage_key = child_info.storage_key().to_vec();
		let top = &self.top;
		let (changeset, info) = self.children.entry(storage_key).or_insert_with(||
			(
				top.spawn_child(),
				child_info.clone()
			)
		);
		let updatable = info.try_update(child_info);
		debug_assert!(updatable);
		changeset.clear_where(|_, _| true, extrinsic_index);
	}

	/// Removes all key-value pairs which keys share the given prefix.
	///
	/// Can be rolled back or committed when called inside a transaction.
	pub(crate) fn clear_prefix(&mut self, prefix: &[u8]) {
		self.filters.guard_write_prefix(None, prefix);
		self.optimistic_logger.log_write_prefix(None, prefix);
		let extrinsic_index = self.extrinsic_index();
		self.top.clear_where(|key, _| key.starts_with(prefix), extrinsic_index);
	}

	/// Removes all key-value pairs which keys share the given prefix.
	///
	/// Can be rolled back or committed when called inside a transaction
	pub(crate) fn clear_child_prefix(
		&mut self,
		child_info: &ChildInfo,
		prefix: &[u8],
	) {
		self.filters.guard_write_prefix(Some(child_info), prefix);
		self.optimistic_logger.log_write_prefix(Some(child_info), prefix);
		let extrinsic_index = self.extrinsic_index();
		let storage_key = child_info.storage_key().to_vec();
		let top = &self.top;
		let (changeset, info) = self.children.entry(storage_key).or_insert_with(||
			(
				top.spawn_child(),
				child_info.clone()
			)
		);
		let updatable = info.try_update(child_info);
		debug_assert!(updatable);
		changeset.clear_where(|key, _| key.starts_with(prefix), extrinsic_index);
	}

	/// Returns the current nesting depth of the transaction stack.
	///
	/// A value of zero means that no transaction is open and changes are committed on write.
	pub fn transaction_depth(&self) -> usize {
		// The top changeset and all child changesets transact in lockstep and are
		// therefore always at the same transaction depth.
		self.top.transaction_depth()
	}

	/// Set access declaration in the parent worker.
	///
	/// For worker declaration it also guard child declaration on parent, resulting in failure when
	/// child declaration allows more than current parent allowed access.
	///
	/// Return false if the declaration is incompatible with current parent worker accesses.
	/// TODO check if we can &WorkerDeclaration
	pub fn declare_child_worker(&mut self, child_marker: TaskId, declaration: WorkerDeclaration) -> bool {
		match declaration {
			WorkerDeclaration::Stateless
			| WorkerDeclaration::ReadLastBlock
			| WorkerDeclaration::ReadAtSpawn
			| WorkerDeclaration::WriteAtSpawn => (),
			WorkerDeclaration::ReadOptimistic => {
				self.optimistic_logger.log_writes_against(Some(child_marker));
			},
			WorkerDeclaration::WriteLightOptimistic => {
				self.optimistic_logger.log_writes_against(Some(child_marker));
			},
			WorkerDeclaration::WriteOptimistic => {
				self.optimistic_logger.log_reads_against(Some(child_marker));
				self.optimistic_logger.log_writes_against(Some(child_marker));
			},
			WorkerDeclaration::ReadDeclarative(filter, failure) => {
				if !self.filters.guard_child_filter_read(&filter) {
					return false;
				}
				self.filters.set_failure_handler(Some(child_marker), failure);
				// TODO consider merging add_change and forbid_writes (or even the full block).
				self.filters.add_change(WorkerDeclaration::ReadDeclarative(filter.clone(), failure), child_marker);
				self.filters.forbid_writes(filter, child_marker);
			},
			WorkerDeclaration::WriteLightDeclarative(filter, failure) => {
				if !self.filters.guard_child_filter_write(&filter) {
					return false;
				}
				self.filters.set_failure_handler(Some(child_marker), failure);
				// TODO see if possible to only push worker type??
				self.filters.add_change(WorkerDeclaration::WriteLightDeclarative(filter.clone(), failure), child_marker);
				self.filters.forbid_writes(filter, child_marker);
			},
			WorkerDeclaration::WriteDeclarative(filters, failure) => {
				if !self.filters.guard_child_filter_read(&filters.read_only) {
					return false;
				}
				if !self.filters.guard_child_filter_write(&filters.read_write) {
					return false;
				}
				self.filters.set_failure_handler(Some(child_marker), failure);
				self.filters.add_change(WorkerDeclaration::WriteDeclarative(filters.clone(), failure), child_marker);
				self.filters.forbid_reads(filters.read_write, child_marker);
				self.filters.forbid_writes(filters.read_only, child_marker);
			},
		}
		self.markers.set_marker(child_marker);
		true
	}

	/// Set access declaration in the child worker.
	pub fn set_worker_declaration(&mut self, declaration: WorkerDeclaration) {
		match declaration {
			WorkerDeclaration::Stateless
			| WorkerDeclaration::ReadLastBlock
			| WorkerDeclaration::ReadAtSpawn
			| WorkerDeclaration::WriteAtSpawn => (),
			WorkerDeclaration::ReadOptimistic => {
				self.optimistic_logger.log_reads_against(None);
			},
			WorkerDeclaration::WriteLightOptimistic => {
				self.optimistic_logger.log_writes_against(None);
			},
			WorkerDeclaration::WriteOptimistic => {
				self.optimistic_logger.log_reads_against(None);
				self.optimistic_logger.log_writes_against(None);
			},
			WorkerDeclaration::ReadDeclarative(filter, failure) => {
				self.filters.set_failure_handler(None, failure); 
				self.filters.allow_reads(filter);
			},
			WorkerDeclaration::WriteLightDeclarative(filter, failure) => {
				self.filters.set_failure_handler(None, failure);
				self.filters.allow_writes(filter);
			},
			WorkerDeclaration::WriteDeclarative(filters, failure) => {
				self.filters.set_failure_handler(None, failure);
				self.filters.allow_reads(filters.read_only);
				self.filters.allow_writes(filters.read_write);
			},
		}
	}

	/// Check if worker result is compatible with changes
	/// that happens in parent worker state.
	///
	/// Return `None` when the worker execution should be invalidated.
	pub fn resolve_worker_result(&mut self, result: WorkerResult) -> Option<Vec<u8>> {
		if !self.filters.on_worker_result(&result)
			|| !self.optimistic_logger.on_worker_result(&result)
			|| !self.markers.on_worker_result(&result) {
			return None;
		}

		match result {
			WorkerResult::Optimistic(result, state_delta, ..)
			| WorkerResult::Valid(result, state_delta)
			| WorkerResult::CallAt(result, state_delta, ..) => {
				if let Some(delta) = state_delta {
					self.inject_worker_delta(delta);
				}
				Some(result)
			},
			WorkerResult::Invalid => None,
			WorkerResult::RuntimePanic => {
				panic!("Runtime panic from a worker.")
			},
			WorkerResult::HardPanic => {
				panic!("Panic running a worker.")
			},
		}
	}

	/// A worker was dissmissed.
	///
	/// Update internal state relative to this worker.
	pub fn dismiss_worker(&mut self, id: TaskId) {
		self.optimistic_logger.remove_worker(id);
		self.filters.remove_worker(id);
		self.markers.remove_worker(id);
	}

	/// Start a new nested transaction.
	///
	/// This allows to either commit or roll back all changes that where made while this
	/// transaction was open. Any transaction must be closed by either `rollback_transaction` or
	/// `commit_transaction` before this overlay can be converted into storage changes.
	///
	/// Changes made without any open transaction are committed immediately.
	pub fn start_transaction(&mut self) {
		self.markers.start_transaction();
		self.top.start_transaction();
		for (_, (changeset, _)) in self.children.iter_mut() {
			changeset.start_transaction();
		}
		self.offchain.overlay_mut().start_transaction();
	}

	/// Rollback the last transaction started by `start_transaction`.
	///
	/// Any changes made during that transaction are discarded. Returns an error if
	/// there is no open transaction that can be rolled back.
	#[must_use]
	pub fn rollback_transaction(&mut self) -> Result<Vec<TaskId>, NoOpenTransaction> {
		let to_kill = self.markers.rollback_transaction();
		self.top.rollback_transaction()?;
		retain_map(&mut self.children, |_, (changeset, _)| {
			changeset.rollback_transaction()
				.expect("Top and children changesets are started in lockstep; qed");
			!changeset.is_empty()
		});
		self.offchain.overlay_mut().rollback_transaction()
			.expect("Top and offchain changesets are started in lockstep; qed");
		Ok(to_kill)
	}

	/// Commit the last transaction started by `start_transaction`.
	///
	/// Any changes made during that transaction are committed. Returns an error if there
	/// is no open transaction that can be committed.
	#[must_use]
	pub fn commit_transaction(&mut self) -> Result<Vec<TaskId>, NoOpenTransaction> {
		let to_kill = self.markers.commit_transaction();
		self.top.commit_transaction()?;
		for (_, (changeset, _)) in self.children.iter_mut() {
			changeset.commit_transaction()
				.expect("Top and children changesets are started in lockstep; qed");
		}
		self.offchain.overlay_mut().commit_transaction()
			.expect("Top and offchain changesets are started in lockstep; qed");
		Ok(to_kill)
	}

	/// Call this before transfering control to the runtime.
	///
	/// This protects all existing transactions from being removed by the runtime.
	/// Calling this while already inside the runtime will return an error.
	pub fn enter_runtime(&mut self) -> Result<(), AlreadyInRuntime> {
		self.top.enter_runtime()?;
		for (_, (changeset, _)) in self.children.iter_mut() {
			changeset.enter_runtime()
				.expect("Top and children changesets are entering runtime in lockstep; qed")
		}
		self.offchain.overlay_mut().enter_runtime()
			.expect("Top and offchain changesets are started in lockstep; qed");
		Ok(())
	}

	/// Call this when control returns from the runtime.
	///
	/// This commits all dangling transaction left open by the runtime.
	/// Calling this while outside the runtime will return an error.
	pub fn exit_runtime(&mut self) -> Result<(), NotInRuntime> {
		self.top.exit_runtime()?;
		for (_, (changeset, _)) in self.children.iter_mut() {
			changeset.exit_runtime()
				.expect("Top and children changesets are entering runtime in lockstep; qed");
		}
		self.offchain.overlay_mut().exit_runtime()
			.expect("Top and offchain changesets are started in lockstep; qed");
		Ok(())
	}

	/// Consume all changes up to a given transaction depth (top + children)
	/// and return them.
	///
	/// Panics:
	/// Panics if `transaction_depth() > initial_depth`
	fn drain_committed_for(&mut self, initial_depth: usize) -> (
		impl Iterator<Item=(StorageKey, Change)>,
		impl Iterator<Item=(StorageKey, (impl Iterator<Item=(StorageKey, Change)>, ChildInfo))>,
	) {
		use sp_std::mem::take;
		(
			take(&mut self.top).drain_commited_for(initial_depth),
			take(&mut self.children).into_iter()
				.map(move |(key, (val, info))| (
						key,
						(val.drain_commited_for(initial_depth), info)
					)
				),
		)
	}

	/// Consume all changes (top + children) and return them.
	///
	/// After calling this function no more changes are contained in this changeset.
	///
	/// Panics:
	/// Panics if `transaction_depth() > 0`
	fn drain_committed(&mut self) -> (
		impl Iterator<Item=(StorageKey, Option<StorageValue>)>,
		impl Iterator<Item=(StorageKey, (impl Iterator<Item=(StorageKey, Option<StorageValue>)>, ChildInfo))>,
	) {
		use sp_std::mem::take;
		(
			take(&mut self.top).drain_commited()
				.map(|(k, change)| (k, change_to_change_set(change))),
			take(&mut self.children).into_iter()
				.map(|(key, (val, info))| (
						key,
						(val.drain_commited()
							.map(|(k, change)| (k, change_to_change_set(change))),
							info)
					)
				),
		)
	}

	/// Consume all changes (top + children) and return them.
	///
	/// After calling this function no more changes are contained in this changeset.
	///
	/// Panics:
	/// Panics if `transaction_depth() > 0`
	pub fn offchain_drain_committed(&mut self) -> impl Iterator<Item=((StorageKey, StorageKey), OffchainOverlayedChange)> {
		self.offchain.drain()
	}

	/// Get an iterator over all child changes as seen by the current transaction.
	pub fn children(&mut self)
		-> impl Iterator<Item=(impl Iterator<Item=(&StorageKey, &mut OverlayedValue)>, &ChildInfo)> {
		self.children.iter_mut().map(|(_, v)| (v.0.changes(), &v.1))
	}

	/// Get an iterator over all top changes as been by the current transaction.
	pub fn changes(&mut self) -> impl Iterator<Item=(&StorageKey, &mut OverlayedValue)> {
		self.top.changes()
	}

	/// Get an optional iterator over all child changes stored under the supplied key.
	pub fn child_changes(&mut self, key: &[u8])
		-> Option<(impl Iterator<Item=(&StorageKey, &mut OverlayedValue)>, &ChildInfo)> {
		self.children.get_mut(key).map(|(overlay, info)| (overlay.changes(), &*info))
	}

	/// Convert this instance with all changes into a [`StorageChanges`] instance.
	#[cfg(feature = "std")]
	pub fn into_storage_changes<
		B: Backend<H>, H: Hasher + 'static, N: BlockNumber
	>(
		mut self,
		backend: &B,
		changes_trie_state: Option<&ChangesTrieState<H, N>>,
		parent_hash: H::Out,
		mut cache: StorageTransactionCache<B::Transaction, H, N>,
	) -> Result<StorageChanges<B::Transaction, H, N>, DefaultError>
		where H::Out: Ord + Encode + 'static {
		self.drain_storage_changes(backend, changes_trie_state, parent_hash, &mut cache)
	}

	/// Drain all changes into a [`StorageChanges`] instance. Leave empty overlay in place.
	pub fn drain_storage_changes<B: Backend<H>, H: Hasher + 'static, N: BlockNumber>(
		&mut self,
		backend: &B,
		#[cfg(feature = "std")]
		changes_trie_state: Option<&ChangesTrieState<H, N>>,
		parent_hash: H::Out,
		mut cache: &mut StorageTransactionCache<B::Transaction, H, N>,
	) -> Result<StorageChanges<B::Transaction, H, N>, DefaultError>
		where H::Out: Ord + Encode + 'static {
		// If the transaction does not exist, we generate it.
		if cache.transaction.is_none() {
			self.storage_root(backend, &mut cache);
		}

		let (transaction, transaction_storage_root) = cache.transaction.take()
			.and_then(|t| cache.transaction_storage_root.take().map(|tr| (t, tr)))
			.expect("Transaction was be generated as part of `storage_root`; qed");

		// If the transaction does not exist, we generate it.
		#[cfg(feature = "std")]
		if cache.changes_trie_transaction.is_none() {
			self.changes_trie_root(
				backend,
				changes_trie_state,
				parent_hash,
				false,
				&mut cache,
			).map_err(|_| "Failed to generate changes trie transaction")?;
		}

		#[cfg(feature = "std")]
		let changes_trie_transaction = cache.changes_trie_transaction
			.take()
			.expect("Changes trie transaction was generated by `changes_trie_root`; qed");

		let (main_storage_changes, child_storage_changes) = self.drain_committed();
		let offchain_storage_changes = self.offchain_drain_committed().collect();

		#[cfg(feature = "std")]
		let transaction_index_changes = std::mem::take(&mut self.transaction_index_ops);

		Ok(StorageChanges {
			main_storage_changes: main_storage_changes.collect(),
			child_storage_changes: child_storage_changes.map(|(sk, it)| (sk, it.0.collect())).collect(),
			offchain_storage_changes,
			transaction,
			transaction_storage_root,
			#[cfg(feature = "std")]
			changes_trie_transaction,
			#[cfg(feature = "std")]
			transaction_index_changes,
			#[cfg(not(feature = "std"))]
			_ph: Default::default(),
		})
	}

	/// Inserts storage entry responsible for current extrinsic index.
	#[cfg(test)]
	pub(crate) fn set_extrinsic_index(&mut self, extrinsic_index: u32) {
		self.top.set(EXTRINSIC_INDEX.to_vec(), Change::Write(extrinsic_index.encode()), None);
	}

	/// Returns current extrinsic index to use in changes trie construction.
	/// None is returned if it is not set or changes trie config is not set.
	/// Persistent value (from the backend) can be ignored because runtime must
	/// set this index before first and unset after last extrinsic is executed.
	/// Changes that are made outside of extrinsics, are marked with
	/// `NO_EXTRINSIC_INDEX` index.
	fn extrinsic_index(&mut self) -> Option<u32> {
		match self.collect_extrinsics {
			true => Some(
				self.storage(EXTRINSIC_INDEX)
					.and_then(|idx| idx.and_then(|idx| Decode::decode(&mut &*idx).ok()))
					.unwrap_or(NO_EXTRINSIC_INDEX)),
			false => None,
		}
	}

	/// Generate the storage root using `backend` and all changes
	/// as seen by the current transaction.
	///
	/// Returns the storage root and caches storage transaction in the given `cache`.
	pub fn storage_root<H: Hasher, N: BlockNumber, B: Backend<H>>(
		&mut self,
		backend: &B,
		cache: &mut StorageTransactionCache<B::Transaction, H, N>,
	) -> H::Out
		where H::Out: Ord + Encode,
	{
		self.filters.guard_read_all();
		self.optimistic_logger.log_read_all();
		let delta = self.top.changes().map(|(k, v)| (&k[..], v.value().map(|v| &v[..])));
		let child_delta = self.children.iter_mut().map(|(_, v)| (v.0.changes(), &v.1))
			.map(|(changes, info)| (info, changes.map(
				|(k, v)| (&k[..], v.value().map(|v| &v[..]))
			)));

		let (root, transaction) = backend.full_storage_root(delta, child_delta);

		cache.transaction = Some(transaction);
		cache.transaction_storage_root = Some(root);

		root
	}

	/// Generate the changes trie root.
	///
	/// Returns the changes trie root and caches the storage transaction into the given `cache`.
	///
	/// # Panics
	///
	/// Panics on storage error, when `panic_on_storage_error` is set.
	#[cfg(feature = "std")]
	pub fn changes_trie_root<'a, H: Hasher + 'static, N: BlockNumber, B: Backend<H>>(
		&mut self,
		backend: &B,
		changes_trie_state: Option<&'a ChangesTrieState<'a, H, N>>,
		parent_hash: H::Out,
		panic_on_storage_error: bool,
		cache: &mut StorageTransactionCache<B::Transaction, H, N>,
	) -> Result<Option<H::Out>, ()> where H::Out: Ord + Encode + 'static {
		build_changes_trie::<_, H, N>(
			backend,
			changes_trie_state,
			self,
			parent_hash,
			panic_on_storage_error,
		).map(|r| {
			let root = r.as_ref().map(|r| r.1).clone();
			cache.changes_trie_transaction = Some(r.map(|(db, _, cache)| (db, cache)));
			cache.changes_trie_transaction_storage_root = Some(root);
			root
		})
	}

	/// Returns the next (in lexicographic order) storage key in the overlayed alongside its value.
	/// If no value is next then `None` is returned.
	pub fn next_storage_key_change(
		&mut self,
		key: &[u8],
		backend_accessed: Option<&Vec<u8>>,
	) -> Option<(&[u8], &mut OverlayedValue)> {
		self.filters.guard_read_interval(None, key, backend_accessed.map(Vec::as_slice));
		self.optimistic_logger.log_read_interval(None, key, backend_accessed.map(Vec::as_slice));
		self.top.next_change(key)
	}

	/// Returns the next (in lexicographic order) child storage key in the overlayed alongside its
	/// value.  If no value is next then `None` is returned.
	pub fn next_child_storage_key_change(
		&mut self,
		child_info: &ChildInfo,
		key: &[u8],
		backend_accessed: Option<&Vec<u8>>,
	) -> Option<(&[u8], &mut OverlayedValue)> {
		self.filters.guard_read_interval(Some(child_info), key, backend_accessed.map(Vec::as_slice));
		self.optimistic_logger.log_read_interval(Some(child_info), key, backend_accessed.map(Vec::as_slice));
		let storage_key = child_info.storage_key();
		self.children
			.get_mut(storage_key)
			.and_then(|(overlay, _)|
				overlay.next_change(key)
			)
	}

	/// Read only access ot offchain overlay.
	pub fn offchain(&self) -> &OffchainOverlayedChanges {
		&self.offchain
	}

	/// For optimistic worker, we extract logs from the overlay.
	/// When call on a non optimistic worker returns `None`.
	pub fn extract_access_log(&mut self) -> Option<sp_externalities::AccessLog> {
		self.optimistic_logger.extract_parent_log()
	}

	/// Did the filters of this worker (not children) fail.
	pub fn did_fail(&self) -> bool {
		self.filters.is_result_for_parent_invalid()
	}

	/// Extract changes from overlay.
	/// TODO audit cost of this: probably very high when used against externalities.
	pub fn extract_delta(&mut self) -> sp_externalities::StateDelta {
		let (top_iter, children_iter) = self.drain_committed_for(self.markers.start_depth());
		let mut children = Vec::new();
		for (_, (iter, info)) in children_iter {
			let mut added = Vec::new();
			let mut deleted = Vec::new();
			let mut appended = Vec::new();
			let mut incremented = Vec::new();
			for (key, change) in iter {
				match change {
					Change::Write(value) => added.push((key, value)),
					Change::Delete => deleted.push(key),
					Change::Append(value, changes) => appended.push((key, (value, changes))),
					Change::IncrementCounter(value, increment) => incremented.push((key, (value, increment))),
				}
			}
			// TODO implement extraction of delta for logged append and logged delete prefix
			// actually having append and delete prefix as first state component of state machine
			// would be more straight forward and better for all but https://github.com/paritytech/substrate/pull/5280
			// did not have support (delete prefix as first state citizen).
			children.push((info, sp_externalities::TrieDelta {
				added,
				deleted,
				appended,
				incremented,
				deleted_prefix: Vec::new(), // TODO
			}));
		}

		let mut added = Vec::new();
		let mut deleted = Vec::new();
		let mut appended = Vec::new();
		let mut incremented = Vec::new();
		for (key, change) in top_iter {
			match change {
				Change::Write(value) => added.push((key, value)),
				Change::Delete => deleted.push(key),
				Change::Append(value, changes) => appended.push((key, (value, changes))),
				Change::IncrementCounter(value, increment) => incremented.push((key, (value, increment))),
			}
		}
		sp_externalities::StateDelta {
			top: sp_externalities::TrieDelta {
				added,
				deleted,
				appended,
				incremented,
				deleted_prefix: Vec::new(), // TODO
			},
			children,
		}
	}

	/// Write a key value pair to the offchain storage overlay.
	pub fn set_offchain_storage(&mut self, key: &[u8], value: Option<&[u8]>) {
		use sp_core::offchain::STORAGE_PREFIX;
		match value {
			Some(value) => self.offchain.set(STORAGE_PREFIX, key, value),
			None => self.offchain.remove(STORAGE_PREFIX, key),
		}
	}

	/// Add transaction index operation.
	pub fn add_transaction_index(&mut self, op: IndexOperation) {
		self.transaction_index_ops.push(op)
	}

	// TODO doc and check usage
	fn inject_worker_delta(&mut self, delta: sp_externalities::StateDelta) {
		for (key, value) in delta.top.added.into_iter() {
			self.set_storage(key, Some(value));
		}
		for key in delta.top.deleted.into_iter() {
			self.set_storage(key, None);
		}
		for (child_info, delta) in delta.children.into_iter() {
			for (key, value) in delta.added.into_iter() {
				self.set_child_storage(&child_info, key, Some(value));
			}
			for key in delta.deleted.into_iter() {
				self.set_child_storage(&child_info, key, None);
			}
		}
	}
}

#[cfg(feature = "std")]
fn retain_map<K, V, F>(map: &mut Map<K, V>, f: F)
	where
		K: std::cmp::Eq + std::hash::Hash,
		F: FnMut(&K, &mut V) -> bool,
{
	map.retain(f);
}

#[cfg(not(feature = "std"))]
fn retain_map<K, V, F>(map: &mut Map<K, V>, mut f: F)
	where
		K: Ord,
		F: FnMut(&K, &mut V) -> bool,
{
	let old = sp_std::mem::replace(map, Map::default());
	for (k, mut v) in old.into_iter() {
		if f(&k, &mut v) {
			map.insert(k, v);
		}
	}
}

/// An overlayed extension is either a mutable reference
/// or an owned extension.
pub enum OverlayedExtension<'a> {
	MutRef(&'a mut Box<dyn Extension>),
	Owned(Box<dyn Extension>),
}

/// Overlayed extensions which are sourced from [`Extensions`].
///
/// The sourced extensions will be stored as mutable references,
/// while extensions that are registered while execution are stored
/// as owned references. After the execution of a runtime function, we
/// can safely drop this object while not having modified the original
/// list.
pub struct OverlayedExtensions<'a> {
	extensions: Map<TypeId, OverlayedExtension<'a>>,
}

impl<'a> OverlayedExtensions<'a> {
	/// Create a new instance of overlayed extensions from the given extensions.
	pub fn new(extensions: &'a mut Extensions) -> Self {
		Self {
			extensions: extensions
				.iter_mut()
				.map(|(k, v)| (*k, OverlayedExtension::MutRef(v)))
				.collect(),
		}
	}

	/// Return a mutable reference to the requested extension.
	pub fn get_mut(&mut self, ext_type_id: TypeId) -> Option<&mut dyn Any> {
		self.extensions.get_mut(&ext_type_id).map(|ext| match ext {
			OverlayedExtension::MutRef(ext) => ext.as_mut_any(),
			OverlayedExtension::Owned(ext) => ext.as_mut_any(),
		})
	}

	/// Register extension `extension` with the given `type_id`.
	pub fn register(
		&mut self,
		type_id: TypeId,
		extension: Box<dyn Extension>,
	) -> Result<(), sp_externalities::Error> {
		match self.extensions.entry(type_id) {
			MapEntry::Vacant(vacant) => {
				vacant.insert(OverlayedExtension::Owned(extension));
				Ok(())
			},
			MapEntry::Occupied(_) => Err(sp_externalities::Error::ExtensionAlreadyRegistered),
		}
	}

	/// Deregister extension with the given `type_id`.
	///
	/// Returns `true` when there was an extension registered for the given `type_id`.
	pub fn deregister(&mut self, type_id: TypeId) -> bool {
		self.extensions.remove(&type_id).is_some()
	}
}

/// Declaration of radix trees for this crate.
pub mod radix_trees {
	use radix_tree::{Derivative, radix::{RadixConf, impls::Radix256Conf},
		children::{Children, ART48_256}, Value, TreeConf, Node};
	use super::filters::Filter;
	use sp_std::boxed::Box;
	use core::fmt::Debug;

	radix_tree::flatten_children!(
		Children256FlattenART,
		Node256FlattenART,
		Node256NoBackendART,
		ART48_256,
		Radix256Conf,
		(),
	);

	/// Radix tree internally use for filtering key accesses.
	pub type FilterTree<F> = radix_tree::Tree<Node256NoBackendART<Filter<F>>>;

	/// Write access logs with children origin.
	pub type AccessTreeWrite = radix_tree::Tree<Node256NoBackendART<super::loggers::OriginLog>>;

	/// Write access logs.
	pub type AccessTreeWriteParent = radix_tree::Tree<Node256NoBackendART<()>>;
}

fn change_to_change_set(change: Change) -> Option<StorageValue> {
	match change {
		Change::Delete => None,
		Change::Write(value) => Some(value),
		Change::Append(mut value, mut changes) => {
			let mut appendable = crate::ext::StorageAppend::new(&mut value);
			for change in changes.drain(..) {
				appendable.append(change);
			}
			Some(value)
		},
		Change::IncrementCounter(mut value, nb) => {
			for _ in 0..nb {
				// TODO extract and test counter logic.
				let mut nb_digit = value.len();
				if value.last() == Some(&255) {
					while nb_digit > 0 && value[nb_digit - 1] == 255 {
						value[nb_digit - 1] = 0;
						nb_digit -= 1;
					}
					if nb_digit == 0 {
						value.insert(0, 1);
					} else {
						value[nb_digit] += 1;
					}
				}
			}
			Some(value)
		},
	}
}

/*fn change_read_value(change: &Change) -> Option<StorageValue> {
	//fn read_value(&mut self) -> Option<&StorageValue> {
		// TODO consider mut access to overlay so that this function
		// occurs no overhead by resolving write only operation on read.
		// TODO this clone is not acceptable !!! (does clone value when not
		// needed.
	change_to_change_set(change.clone())
}*/

fn change_read_value_mut(change: &mut Change) -> Option<&mut StorageValue> {
	*change = match change_to_change_set(sp_std::mem::replace(change, Default::default())) {
		Some(value) => Change::Write(value),
		None => Change::Delete,
	};
	match change {
		Change::Write(value) => Some(value),
		Change::Delete => None,
		_ => unreachable!("Initialized above"),
	}
}

fn change_read_value_mut_default(change: &mut Change) -> &mut StorageValue {
	*change = match change_to_change_set(sp_std::mem::replace(change, Default::default())) {
		Some(value) => Change::Write(value),
		// deleted value is intiatialized back to empty value.
		None => Change::Write(Default::default()),
	};
	match change {
		Change::Write(value) => value,
		_ => unreachable!("Initialized above"),
	}
}

#[cfg(test)]
mod tests {
	use hex_literal::hex;
	use sp_core::{Blake2Hasher, traits::Externalities};
	use crate::InMemoryBackend;
	use crate::ext::Ext;
	use super::*;
	use std::collections::BTreeMap;

	fn assert_extrinsics(
		overlay: &mut OverlayedChangeSet,
		key: impl AsRef<[u8]>,
		expected: Vec<u32>,
	) {
		assert_eq!(
			overlay.get(key.as_ref()).unwrap().extrinsics().into_iter().collect::<Vec<_>>(),
			expected
		)
	}

	#[test]
	fn overlayed_storage_works() {
		let mut overlayed = OverlayedChanges::default();

		let key = vec![42, 69, 169, 142];

		assert!(overlayed.storage(&key).is_none());

		overlayed.start_transaction();

		overlayed.set_storage(key.clone(), Some(vec![1, 2, 3]));
		assert_eq!(overlayed.storage(&key).unwrap(), Some(&[1, 2, 3][..]));

		overlayed.commit_transaction().unwrap();

		assert_eq!(overlayed.storage(&key).unwrap(), Some(&[1, 2, 3][..]));

		overlayed.start_transaction();

		overlayed.set_storage(key.clone(), Some(vec![]));
		assert_eq!(overlayed.storage(&key).unwrap(), Some(&[][..]));

		overlayed.set_storage(key.clone(), None);
		assert!(overlayed.storage(&key).unwrap().is_none());

		overlayed.rollback_transaction().unwrap();

		assert_eq!(overlayed.storage(&key).unwrap(), Some(&[1, 2, 3][..]));

		overlayed.set_storage(key.clone(), None);
		assert!(overlayed.storage(&key).unwrap().is_none());
	}

	#[test]
	fn offchain_overlayed_storage_transactions_works() {
		use sp_core::offchain::STORAGE_PREFIX;
		fn check_offchain_content(
			state: &OverlayedChanges,
			nb_commit: usize,
			expected: Vec<(Vec<u8>, Option<Vec<u8>>)>,
		) {
			let mut state = state.clone();
			for _ in 0..nb_commit {
				state.commit_transaction().unwrap();
			}
			let offchain_data: Vec<_> = state.offchain_drain_committed().collect();
			let expected: Vec<_> = expected.into_iter().map(|(key, value)| {
				let change = match value {
					Some(value) => OffchainOverlayedChange::SetValue(value),
					None => OffchainOverlayedChange::Remove,
				};
				((STORAGE_PREFIX.to_vec(), key), change)
			}).collect();
			assert_eq!(offchain_data, expected);
		}

		let mut overlayed = OverlayedChanges::default();

		let key = vec![42, 69, 169, 142];

		check_offchain_content(&overlayed, 0, vec![]);

		overlayed.start_transaction();

		overlayed.set_offchain_storage(key.as_slice(), Some(&[1, 2, 3][..]));
		check_offchain_content(&overlayed, 1, vec![(key.clone(), Some(vec![1, 2, 3]))]);

		overlayed.commit_transaction().unwrap();

		check_offchain_content(&overlayed, 0, vec![(key.clone(), Some(vec![1, 2, 3]))]);

		overlayed.start_transaction();

		overlayed.set_offchain_storage(key.as_slice(), Some(&[][..]));
		check_offchain_content(&overlayed, 1, vec![(key.clone(), Some(vec![]))]);

		overlayed.set_offchain_storage(key.as_slice(), None);
		check_offchain_content(&overlayed, 1, vec![(key.clone(), None)]);

		overlayed.rollback_transaction().unwrap();

		check_offchain_content(&overlayed, 0, vec![(key.clone(), Some(vec![1, 2, 3]))]);

		overlayed.set_offchain_storage(key.as_slice(), None);
		check_offchain_content(&overlayed, 0, vec![(key.clone(), None)]);
	}


	#[test]
	fn overlayed_storage_root_works() {
		let initial: BTreeMap<_, _> = vec![
			(b"doe".to_vec(), b"reindeer".to_vec()),
			(b"dog".to_vec(), b"puppyXXX".to_vec()),
			(b"dogglesworth".to_vec(), b"catXXX".to_vec()),
			(b"doug".to_vec(), b"notadog".to_vec()),
		].into_iter().collect();
		let backend = InMemoryBackend::<Blake2Hasher>::from(initial);
		let mut overlay = OverlayedChanges::default();
		overlay.set_collect_extrinsics(false);

		overlay.start_transaction();
		overlay.set_storage(b"dog".to_vec(), Some(b"puppy".to_vec()));
		overlay.set_storage(b"dogglesworth".to_vec(), Some(b"catYYY".to_vec()));
		overlay.set_storage(b"doug".to_vec(), Some(vec![]));
		overlay.commit_transaction().unwrap();

		overlay.start_transaction();
		overlay.set_storage(b"dogglesworth".to_vec(), Some(b"cat".to_vec()));
		overlay.set_storage(b"doug".to_vec(), None);

		let mut cache = StorageTransactionCache::default();
		let mut ext = Ext::new(
			&mut overlay,
			&mut cache,
			&backend,
			crate::changes_trie::disabled_state::<_, u64>(),
			None,
		);
		const ROOT: [u8; 32] = hex!("39245109cef3758c2eed2ccba8d9b370a917850af3824bc8348d505df2c298fa");

		assert_eq!(&ext.storage_root()[..], &ROOT);
	}

	#[test]
	fn extrinsic_changes_are_collected() {
		let mut overlay = OverlayedChanges::default();
		overlay.set_collect_extrinsics(true);

		overlay.start_transaction();

		overlay.set_storage(vec![100], Some(vec![101]));

		overlay.set_extrinsic_index(0);
		overlay.set_storage(vec![1], Some(vec![2]));

		overlay.set_extrinsic_index(1);
		overlay.set_storage(vec![3], Some(vec![4]));

		overlay.set_extrinsic_index(2);
		overlay.set_storage(vec![1], Some(vec![6]));

		assert_extrinsics(&mut overlay.top, vec![1], vec![0, 2]);
		assert_extrinsics(&mut overlay.top, vec![3], vec![1]);
		assert_extrinsics(&mut overlay.top, vec![100], vec![NO_EXTRINSIC_INDEX]);

		overlay.start_transaction();

		overlay.set_extrinsic_index(3);
		overlay.set_storage(vec![3], Some(vec![7]));

		overlay.set_extrinsic_index(4);
		overlay.set_storage(vec![1], Some(vec![8]));

		assert_extrinsics(&mut overlay.top, vec![1], vec![0, 2, 4]);
		assert_extrinsics(&mut overlay.top, vec![3], vec![1, 3]);
		assert_extrinsics(&mut overlay.top, vec![100], vec![NO_EXTRINSIC_INDEX]);

		overlay.rollback_transaction().unwrap();

		assert_extrinsics(&mut overlay.top, vec![1], vec![0, 2]);
		assert_extrinsics(&mut overlay.top, vec![3], vec![1]);
		assert_extrinsics(&mut overlay.top, vec![100], vec![NO_EXTRINSIC_INDEX]);
	}

	#[test]
	fn next_storage_key_change_works() {
		let mut overlay = OverlayedChanges::default();
		overlay.start_transaction();
		overlay.set_storage(vec![20], Some(vec![20]));
		overlay.set_storage(vec![30], Some(vec![30]));
		overlay.set_storage(vec![40], Some(vec![40]));
		overlay.commit_transaction().unwrap();
		overlay.set_storage(vec![10], Some(vec![10]));
		overlay.set_storage(vec![30], None);

		// next_prospective < next_committed
		let next_to_5 = overlay.next_storage_key_change(&[5], None).unwrap();
		assert_eq!(next_to_5.0.to_vec(), vec![10]);
		assert_eq!(next_to_5.1.value(), Some(&vec![10]));

		// next_committed < next_prospective
		let next_to_10 = overlay.next_storage_key_change(&[10], None).unwrap();
		assert_eq!(next_to_10.0.to_vec(), vec![20]);
		assert_eq!(next_to_10.1.value(), Some(&vec![20]));

		// next_committed == next_prospective
		let next_to_20 = overlay.next_storage_key_change(&[20], None).unwrap();
		assert_eq!(next_to_20.0.to_vec(), vec![30]);
		assert_eq!(next_to_20.1.value(), None);

		// next_committed, no next_prospective
		let next_to_30 = overlay.next_storage_key_change(&[30], None).unwrap();
		assert_eq!(next_to_30.0.to_vec(), vec![40]);
		assert_eq!(next_to_30.1.value(), Some(&vec![40]));

		overlay.set_storage(vec![50], Some(vec![50]));
		// next_prospective, no next_committed
		let next_to_40 = overlay.next_storage_key_change(&[40], None).unwrap();
		assert_eq!(next_to_40.0.to_vec(), vec![50]);
		assert_eq!(next_to_40.1.value(), Some(&vec![50]));
	}

	#[test]
	fn next_child_storage_key_change_works() {
		let child_info = ChildInfo::new_default(b"Child1");
		let child_info = &child_info;
		let mut overlay = OverlayedChanges::default();
		overlay.start_transaction();
		overlay.set_child_storage(child_info, vec![20], Some(vec![20]));
		overlay.set_child_storage(child_info, vec![30], Some(vec![30]));
		overlay.set_child_storage(child_info, vec![40], Some(vec![40]));
		overlay.commit_transaction().unwrap();
		overlay.set_child_storage(child_info, vec![10], Some(vec![10]));
		overlay.set_child_storage(child_info, vec![30], None);

		// next_prospective < next_committed
		let next_to_5 = overlay.next_child_storage_key_change(child_info, &[5], None).unwrap();
		assert_eq!(next_to_5.0.to_vec(), vec![10]);
		assert_eq!(next_to_5.1.value(), Some(&vec![10]));

		// next_committed < next_prospective
		let next_to_10 = overlay.next_child_storage_key_change(child_info, &[10], None).unwrap();
		assert_eq!(next_to_10.0.to_vec(), vec![20]);
		assert_eq!(next_to_10.1.value(), Some(&vec![20]));

		// next_committed == next_prospective
		let next_to_20 = overlay.next_child_storage_key_change(child_info, &[20], None).unwrap();
		assert_eq!(next_to_20.0.to_vec(), vec![30]);
		assert_eq!(next_to_20.1.value(), None);

		// next_committed, no next_prospective
		let next_to_30 = overlay.next_child_storage_key_change(child_info, &[30], None).unwrap();
		assert_eq!(next_to_30.0.to_vec(), vec![40]);
		assert_eq!(next_to_30.1.value(), Some(&vec![40]));

		overlay.set_child_storage(child_info, vec![50], Some(vec![50]));
		// next_prospective, no next_committed
		let next_to_40 = overlay.next_child_storage_key_change(child_info, &[40], None).unwrap();
		assert_eq!(next_to_40.0.to_vec(), vec![50]);
		assert_eq!(next_to_40.1.value(), Some(&vec![50]));
	}
}

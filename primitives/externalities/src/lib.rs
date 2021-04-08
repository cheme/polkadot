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

#![cfg_attr(not(feature = "std"), no_std)]

//! Substrate externalities abstraction
//!
//! The externalities mainly provide access to storage and to registered extensions. Extensions
//! are for example the keystore or the offchain externalities. These externalities are used to
//! access the node from the runtime via the runtime interfaces.
//!
//! This crate exposes the main [`Externalities`] trait.

use sp_std::{any::{Any, TypeId}, vec::Vec, boxed::Box};

use sp_storage::{ChildInfo, TrackedStorageKey};
use ambassador::{Delegate, delegatable_trait};

pub use scope_limited::{set_and_run_with_externalities, with_externalities,
	with_externalities_and_extension, externalities_and_extension};
pub use extensions::{Extension, Extensions, ExtensionStore};

mod extensions;
mod scope_limited;

const INCOMPATIBLE_CHILD_WORKER_TYPE: &str = "Incompatible child worker type";

/// Externalities error.
#[derive(Debug)]
pub enum Error {
	/// Same extension cannot be registered twice.
	ExtensionAlreadyRegistered,
	/// Extensions are not supported.
	ExtensionsAreNotSupported,
	/// Extension `TypeId` is not registered.
	ExtensionIsNotRegistered(TypeId),
	/// Failed to update storage,
	StorageUpdateFailed(&'static str),
	/// Extension store is locked due to an
	/// extension accessing externalities in
	/// a mutable manner.
	ExtensionLocked,
}

/// The Substrate externalities.
///
/// Provides access to the storage and to other registered extensions.
#[delegatable_trait]
pub trait Externalities: ExtensionStore {
	/// Write a key value pair to the offchain storage database.
	fn set_offchain_storage(&mut self, key: &[u8], value: Option<&[u8]>);

	/// Read runtime storage.
	fn storage(&self, key: &[u8]) -> Option<Vec<u8>>;

	/// Get storage value hash.
	///
	/// This may be optimized for large values.
	fn storage_hash(&self, key: &[u8]) -> Option<Vec<u8>>;

	/// Get child storage value hash.
	///
	/// This may be optimized for large values.
	///
	/// Returns an `Option` that holds the SCALE encoded hash.
	fn child_storage_hash(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Option<Vec<u8>>;

	/// Read child runtime storage.
	///
	/// Returns an `Option` that holds the SCALE encoded hash.
	fn child_storage(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Option<Vec<u8>>;

	/// Set storage entry `key` of current contract being called (effective immediately).
	fn set_storage(&mut self, key: Vec<u8>, value: Vec<u8>) {
		self.place_storage(key, Some(value));
	}

	/// Set child storage entry `key` of current contract being called (effective immediately).
	fn set_child_storage(
		&mut self,
		child_info: &ChildInfo,
		key: Vec<u8>,
		value: Vec<u8>,
	) {
		self.place_child_storage(child_info, key, Some(value))
	}

	/// Clear a storage entry (`key`) of current contract being called (effective immediately).
	fn clear_storage(&mut self, key: &[u8]) {
		self.place_storage(key.to_vec(), None);
	}

	/// Clear a child storage entry (`key`) of current contract being called (effective immediately).
	fn clear_child_storage(
		&mut self,
		child_info: &ChildInfo,
		key: &[u8],
	) {
		self.place_child_storage(child_info, key.to_vec(), None)
	}

	/// Whether a storage entry exists.
	fn exists_storage(&self, key: &[u8]) -> bool {
		self.storage(key).is_some()
	}

	/// Whether a child storage entry exists.
	fn exists_child_storage(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> bool {
		self.child_storage(child_info, key).is_some()
	}

	/// Returns the key immediately following the given key, if it exists.
	fn next_storage_key(&self, key: &[u8]) -> Option<Vec<u8>>;

	/// Returns the key immediately following the given key, if it exists, in child storage.
	fn next_child_storage_key(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Option<Vec<u8>>;

	/// Clear an entire child storage.
	///
	/// Deletes all keys from the overlay and up to `limit` keys from the backend. No
	/// limit is applied if `limit` is `None`. Returned boolean is `true` if the child trie was
	/// removed completely and `false` if there are remaining keys after the function
	/// returns. Returned `u32` is the number of keys that was removed at the end of the
	/// operation.
	///
	/// # Note
	///
	/// An implementation is free to delete more keys than the specified limit as long as
	/// it is able to do that in constant time.
	fn kill_child_storage(&mut self, child_info: &ChildInfo, limit: Option<u32>) -> (bool, u32);

	/// Clear storage entries which keys are start with the given prefix.
	fn clear_prefix(&mut self, prefix: &[u8]);

	/// Clear child storage entries which keys are start with the given prefix.
	fn clear_child_prefix(
		&mut self,
		child_info: &ChildInfo,
		prefix: &[u8],
	);

	/// Set or clear a storage entry (`key`) of current contract being called (effective immediately).
	fn place_storage(&mut self, key: Vec<u8>, value: Option<Vec<u8>>);

	/// Set or clear a child storage entry.
	fn place_child_storage(
		&mut self,
		child_info: &ChildInfo,
		key: Vec<u8>,
		value: Option<Vec<u8>>,
	);

	/// Get the trie root of the current storage map.
	///
	/// This will also update all child storage keys in the top-level storage map.
	///
	/// The returned hash is defined by the `Block` and is SCALE encoded.
	fn storage_root(&mut self) -> Vec<u8>;

	/// Get the trie root of a child storage map.
	///
	/// This will also update the value of the child storage keys in the top-level storage map.
	///
	/// If the storage root equals the default hash as defined by the trie, the key in the top-level
	/// storage map will be removed.
	fn child_storage_root(
		&mut self,
		child_info: &ChildInfo,
	) -> Vec<u8>;

	/// Append storage item.
	///
	/// This assumes specific format of the storage item. Also there is no way to undo this operation.
	fn storage_append(
		&mut self,
		key: Vec<u8>,
		value: Vec<u8>,
	);

	/// Get the changes trie root of the current storage overlay at a block with given `parent`.
	///
	/// `parent` expects a SCALE encoded hash.
	///
	/// The returned hash is defined by the `Block` and is SCALE encoded.
	fn storage_changes_root(&mut self, parent: &[u8]) -> Result<Option<Vec<u8>>, ()>;

	/// Start a new nested transaction.
	///
	/// This allows to either commit or roll back all changes made after this call to the
	/// top changes or the default child changes. For every transaction there cam be a
	/// matching call to either `storage_rollback_transaction` or `storage_commit_transaction`.
	/// Any transactions that are still open after returning from runtime are committed
	/// automatically.
	///
	/// Changes made without any open transaction are committed immediately.
	fn storage_start_transaction(&mut self);

	/// Rollback the last transaction started by `storage_start_transaction`.
	///
	/// Any changes made during that storage transaction are discarded. Returns an error when
	/// no transaction is open that can be closed.
	///
	/// Return possible task ids of tasks that will not be in synch with the thread to allow
	/// early kill.
	fn storage_rollback_transaction(&mut self) -> Result<Vec<TaskId>, ()>;

	/// Commit the last transaction started by `storage_start_transaction`.
	///
	/// Any changes made during that storage transaction are committed. Returns an error when
	/// no transaction is open that can be closed.
	///
	/// Return possible task ids of tasks that will not be in synch with the thread to allow
	/// early kill.
	fn storage_commit_transaction(&mut self) -> Result<Vec<TaskId>, ()>;

	/// Index specified transaction slice and store it.
	fn storage_index_transaction(&mut self, _index: u32, _offset: u32) {
		unimplemented!("storage_index_transaction");
	}

	/// Renew existing piece of transaction storage.
	fn storage_renew_transaction_index(&mut self, _index: u32, _hash: &[u8], _size: u32) {
		unimplemented!("storage_renew_transaction_index");
	}

	/// !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
	/// Benchmarking related functionality and shouldn't be used anywhere else!
	/// !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
	///
	/// Wipes all changes from caches and the database.
	///
	/// The state will be reset to genesis.
	fn wipe(&mut self);

	/// !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
	/// Benchmarking related functionality and shouldn't be used anywhere else!
	/// !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
	///
	/// Commits all changes to the database and clears all caches.
	fn commit(&mut self);

	/// !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
	/// Benchmarking related functionality and shouldn't be used anywhere else!
	/// !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
	///
	/// Gets the current read/write count for the benchmarking process.
	fn read_write_count(&self) -> (u32, u32, u32, u32);

	/// !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
	/// Benchmarking related functionality and shouldn't be used anywhere else!
	/// !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
	///
	/// Resets read/write count for the benchmarking process.
	fn reset_read_write_count(&mut self);

	/// !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
	/// Benchmarking related functionality and shouldn't be used anywhere else!
	/// !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
	///
	/// Gets the current DB tracking whitelist.
	fn get_whitelist(&self) -> Vec<TrackedStorageKey>;

	/// !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
	/// Benchmarking related functionality and shouldn't be used anywhere else!
	/// !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
	///
	/// Adds new storage keys to the DB tracking whitelist.
	fn set_whitelist(&mut self, new: Vec<TrackedStorageKey>);

	/// Get externalities to use from within a child worker.
	fn get_worker_externalities(
		&mut self,
		worker_id: TaskId,
		declaration: WorkerDeclaration,
	) -> Box<dyn AsyncExternalities>;

	/// Resolve worker result does update externality state
	/// and also apply rules relative to the exernality state.
	///
	/// This method must be call before processing any worker result,
	/// for instance from a worker point of view the result may be valid,
	/// but after checking against parent externalities, it may change
	/// to invalid (`None`).
	fn resolve_worker_result(&mut self, result: WorkerResult) -> Option<Vec<u8>>;

	/// Worker result have been dissmiss, inner externality state and constraint
	/// needs to be lifted.
	fn dismiss_worker(&mut self, id: TaskId);
}

/// Substrate externalities that can be use within a worker context.
pub trait AsyncExternalities: Externalities + Send {
	/// Extract changes made to state for this worker.
	fn extract_delta(&mut self) -> Option<StateDelta>;

	/// After execution, we call back async externalities to check
	/// produce worker result.
	fn extract_state(&mut self) -> AsyncExternalitiesPostExecution;
}

/// State of async externality of a child workre after 'join' is called.
pub enum AsyncExternalitiesPostExecution {
	/// Some condition fails and the state is invalid.
	/// With an invalid state we consider that worker
	/// execution, even if it did finish is invalid.
	/// Therefore 'join' implementation should never
	/// return result when externality is in this state.
	Invalid,

	/// Assuming that child worker state is valid, we can
	/// return the result to the parent worker on 'join'.
	Valid,

	/// This requires to check the result against
	/// parent worker externalities with `resolve_worker_result`.
	NeedResolve,

	/// Optimistic worker state accesses to be checked
	/// against other worker results.
	/// This can result in 'join' returning an invalid
	/// result.
	Optimistic(AccessLog),
}

/// Result from worker execution.
///
/// Note that an error that is expected should
/// be serialize in a `Valid` result payload.
#[derive(codec::Encode, codec::Decode)]
pub enum WorkerResult {
	/// Payload resulting from a successfull
	/// call that is guaranted to be valid
	/// at this point.
	/// eg. a stateless worker.
	Valid(Vec<u8>, Option<StateDelta>),
	/// Result that require to be checked against
	/// its parent externality state.
	CallAt(Vec<u8>, Option<StateDelta>, TaskId),
	/// Optimistic strategy call reply, it contains
	/// a log of accessed keys during child execution.
	Optimistic(Vec<u8>, Option<StateDelta>, TaskId, AccessLog),
	/// A worker execution that is not valid.
	/// For instance when asumption on state
	/// are required.
	Invalid,
	/// Internal panic when runing the worker.
	/// This propagate panic in caller.
	RuntimePanic,
	/// Technical panic when runing the worker.
	/// This propagate panic in caller, and also
	/// indicate the process should be stop.
	HardPanic,
}

/// Changes to state made by a worker.
#[derive(codec::Encode, codec::Decode)]
pub struct StateDelta {
	pub top: TrieDelta,
	pub children: Vec<(ChildInfo, TrieDelta)>,
}

impl Default for StateDelta {
	fn default() -> Self {
		StateDelta {
			top: TrieDelta {
				added: Vec::new(),
				appended: Vec::new(),
				deleted: Vec::new(),
				deleted_prefix: Vec::new(),
			},
			children: Vec::new(),
		}
	}
}

impl StateDelta {
	/// Does state delta contain change.
	pub fn is_empty(&self) -> bool {
		self.top.added.is_empty()
			&& self.top.deleted.is_empty()
			&& self.children.is_empty()
	}
}

#[derive(codec::Encode, codec::Decode)]
pub struct TrieDelta {
	/// Key values added or modified.
	pub added: Vec<(Vec<u8>, Vec<u8>)>,
	/// Values appended at a given key location.
	/// TODO feeding this force use to maintain an
	/// append log, but seems worth it as size
	/// of trie delta will be way lower (unimplemented
	/// at this point).
	pub appended: Vec<(Vec<u8>, Vec<Vec<u8>>)>,
	/// Keys deleted.
	pub deleted: Vec<Vec<u8>>,
	/// Key prefix deleted and subsequent.
	/// TODO feeding this force use to maintain a
	/// delete prefix log, but worth it when considering
	/// the size of encoding this.
	/// TODO implement TODO apply before all operation and
	/// have added updated from content in prefix.
	pub deleted_prefix: Vec<Vec<u8>>,
}

/// Log of a given worker call.
#[derive(codec::Encode, codec::Decode, Default)]
pub struct AccessLog {
	/// Worker did iterate over the full state.
	/// (in practice it did not iterate but uses
	/// merkle hash over the full state when calculating
	/// a storage root).
	pub read_all: bool,
	/// Log of access for main state.
	pub top_logger: StateLog,
	/// Log of access for individual child state.
	/// Note that the child root isn't logged in top_logger
	/// because it is always written with its right state
	/// at the end (actually triggers read_all that supersed
	/// the other fields).
	pub children_logger: Vec<(Vec<u8>, StateLog)>,
}

impl AccessLog {
	/// Return true if a read related information was logged.
	pub fn has_read(&self) -> bool {
		if self.read_all {
			return true;
		}
		if self.top_logger.has_read() {
			return true;
		}
		for (_key, logger) in self.children_logger.iter() {
			if logger.has_read() {
				return true;
			}
		}
		false
	}
	/// Return true if a write related information was logged.
	pub fn has_read_write(&self) -> bool {
		if self.top_logger.has_read_write() {
			return true;
		}
		for (_key, logger) in self.children_logger.iter() {
			if logger.has_read_write() {
				return true;
			}
		}
		false
	}
}

/// Log of a given trie state.
#[derive(codec::Encode, codec::Decode, Default)]
pub struct StateLog {
	/// Read only access to a key.
	pub read_keys: Vec<Vec<u8>>,
	/// Read and write access to a key.
	pub read_write_keys: Vec<Vec<u8>>,
	/// Read and write access to a whole prefix (eg key removal
	/// by prefix).
	pub read_write_prefix: Vec<Vec<u8>>,
	/// Worker did iterate over a given interval.
	/// Interval is a pair of inclusive start and end key.
	pub read_intervals: Vec<(Vec<u8>, Option<Vec<u8>>)>,
	/// Key write with no read access.
	pub write_only_key: Vec<Vec<u8>>, 
	/// Append operation in write only mode.
	pub write_only_append_key: Vec<Vec<u8>>, 
}

impl StateLog {
	/// Check that no incompatible access are done.
	/// TODO debug assert call it where relevant: only for test or double check
	pub fn validate(&self) -> bool {
		if !self.write_only_key.is_empty() || !self.write_only_append_key.is_empty() {
			unimplemented!()
		}
		true
	}
	/// Return true if a read related information was logged.
	pub fn has_read(&self) -> bool {
		!self.read_keys.is_empty() || !self.read_intervals.is_empty()
	}
	/// Return true if a write related information was logged.
	pub fn has_read_write(&self) -> bool {
		!self.read_write_keys.is_empty() || !self.read_write_prefix.is_empty()
	}
}

/// A unique identifier type for a child worker.
/// This is not unique between nested worker (unique
/// id with nested support would be an array of u64, but
/// not needed).
pub type TaskId = u64;

/// How declaration error is handled.
#[derive(Debug, Clone, Copy, codec::Encode, codec::Decode)]
pub enum DeclarationFailureHandling {
	/// Do panic on conflict, this is a strict mode where
	/// we cut useless computation, and need some strong
	/// assertion over our declaration.
	Panic,
	/// On conflict return `None` at join.
	/// This is very similar to optimistic `WorkerType` because
	/// we run the whole computation and can have a no result at
	/// the end.
	InvalidAtJoin,
}

impl Default for DeclarationFailureHandling {
	fn default() -> Self {
		DeclarationFailureHandling::Panic
	}
}

/// Allowed workers execution mode.
#[derive(Debug)]
#[repr(u8)]
pub enum WorkerType {
	/// Worker panic on state access from externalities.
	Stateless = 0,

	/// Worker access state read only on the backend unmodified state,
	/// it does not see change made during previous processing
	/// (same state at the one resulting from last state transition:
	/// last block state).
	ReadLastBlock = 1,

	/// Externalities access read only the backend unmodified state,
	/// and the change at the time of spawn.
	/// In this case when joining we ensure the transaction at launch
	/// is still valid.
	ReadAtSpawn = 2,

	/// Same as `ReadAtSpawn`, but we also check that the between parent and child worker
	/// is the same for the whole worker execution.
	/// So read access on a child worker is not compatible with write access on
	/// the parent.
	///
	/// This can only be usefull when we want the state use by child to be the one use on
	/// join (usually we can do with it being the state use at spawn).
	///
	/// We return `None` on join if some state access break this asumption.
	ReadOptimistic = 3,

	/// Same as `ReadOptimistic`, but we do not check conflict on join.
	/// Instead we declare child workre read accesses and check during processing
	/// that there is no invalid access.
	///
	/// As for all declarative types, depending on failure access declaration
	/// an illegal access can either result in panic or returning `None`
	/// on join (as in optimistic mode).
	ReadDeclarative = 4,

	/// `ReadAtSpawn` with allowed write.
	/// Write from child workers always overwrite write from parent workers
	/// at `join`.
	WriteAtSpawn = 5,

	/// Write on parent and child workers are mutually exclusives.
	/// When conflict happens, child worker returns `None` on join.
	///
	/// As for all optimistic type, the workers need to log access and resolve
	/// error on result access only.
	/// We define it as light as it does allow read access of data that
	/// is write in a different worker.
	WriteLightOptimistic = 6,

	/// Same as `WriteLightOptimistic`, but conflict are detected depending on access
	/// declaration.
	/// We declare allowed write access for child worker (which is forbidden access
	/// in the parent worker).
	/// We define it as light as it does allow read access of data that
	/// is write in a different worker.
	WriteLightDeclarative = 7,

	/// Same as `WriteLightOptimistic`, with the additional constraint that we connot read data
	/// when it is writable in a parent or a child worker.
	///
	/// So write from child exclude read from parent and write from parent exclude read
	/// from child.
	WriteOptimistic = 8,

	/// Same as `WriteOptimistic`, but conflict are detected depending on access
	/// declaration.
	/// We declare allowed write access for child worker and allowed read only access
	/// (no need to declare read access for already declared write access).
	WriteDeclarative = 9,
}

impl Default for WorkerType {
	fn default() -> Self {
		WorkerType::Stateless
	}
}

impl WorkerType {
	/// Similar purpose as `TryFrom<u8>`.
	pub fn from_u8(kind: u8) -> Option<WorkerType> {
		Some(match kind {
			0 => WorkerType::Stateless,
			1 => WorkerType::ReadLastBlock,
			2 => WorkerType::ReadAtSpawn,
			3 => WorkerType::ReadOptimistic,
			4 => WorkerType::ReadDeclarative,
			5 => WorkerType::WriteAtSpawn,
			6 => WorkerType::WriteLightOptimistic,
			7 => WorkerType::WriteLightDeclarative,
			8 => WorkerType::WriteOptimistic,
			9 => WorkerType::WriteDeclarative,
			_ => return None,
		})
	}

	/// Depending on concurrency management strategy
	/// we may need to resolve the result against
	/// parent externalities.
	pub fn need_resolve(&self) -> bool {
		match *self {
			WorkerType::Stateless => false,
			WorkerType::ReadLastBlock => false,
			_ => true,
		}
	}

	/// Panic if spawning a child worker of a given type is not possible.
	/// TODO there is way to have more compatibility
	/// eg : - declarative from a optimistic by logging declarative accesses
	/// on join.
	/// - optimistic from declarative by runing accesses on join.
	pub fn guard_compatible_child_workers(&self, kind: WorkerType) {
		match kind {
			WorkerType::Stateless => (),
			WorkerType::ReadLastBlock => match kind {
				WorkerType::ReadLastBlock => (),
				_ => panic!("{}", INCOMPATIBLE_CHILD_WORKER_TYPE),
			},
			WorkerType::ReadAtSpawn => match kind {
				WorkerType::Stateless => (),
				WorkerType::ReadAtSpawn => (),
				_ => panic!("{}", INCOMPATIBLE_CHILD_WORKER_TYPE),
			},
			WorkerType::ReadOptimistic => match kind {
				WorkerType::Stateless => (),
				WorkerType::ReadAtSpawn => (),
				WorkerType::ReadOptimistic => (),
				_ => panic!("{}", INCOMPATIBLE_CHILD_WORKER_TYPE),
			},
			WorkerType::ReadDeclarative => match kind {
				WorkerType::ReadAtSpawn => (),
				WorkerType::ReadDeclarative => (),
				_ => panic!("{}", INCOMPATIBLE_CHILD_WORKER_TYPE),
			},
			WorkerType::WriteAtSpawn => match kind {
				WorkerType::WriteAtSpawn => (),
				_ => panic!("{}", INCOMPATIBLE_CHILD_WORKER_TYPE),
			},
			WorkerType::WriteLightOptimistic => match kind {
				WorkerType::WriteLightOptimistic => (),
				_ => panic!("{}", INCOMPATIBLE_CHILD_WORKER_TYPE),
			},
			WorkerType::WriteLightDeclarative => match kind {
				WorkerType::WriteLightDeclarative => (),
				_ => panic!("{}", INCOMPATIBLE_CHILD_WORKER_TYPE),
			},
			WorkerType::WriteOptimistic => match kind {
				WorkerType::WriteOptimistic => (),
				_ => panic!("{}", INCOMPATIBLE_CHILD_WORKER_TYPE),
			},
			WorkerType::WriteDeclarative => match kind {
				WorkerType::WriteDeclarative => (),
				_ => panic!("{}", INCOMPATIBLE_CHILD_WORKER_TYPE),
			},
		}
	}
}

/// Access filter on storage when spawning worker.
#[derive(Debug, Clone, codec::Encode, codec::Decode)]
pub enum WorkerDeclaration {
	/// Declaration for `WorkerType::Stateless`, no content.
	Stateless,

	/// Declaration for `WorkerType::ReadLastBlock`, no content.
	ReadLastBlock,

	/// Declaration for `WorkerType::ReadAtSpawn`, no content.
	ReadAtSpawn,

	/// Declaration for `WorkerType::ReadOptimistic`, no content.
	ReadOptimistic,

	/// Declaration for `WorkerType::ReadDeclarative`.
	/// Declaration is child worker allowed read access.
	ReadDeclarative(AccessDeclaration, DeclarationFailureHandling),

	/// Declaration for `WorkerType::ReadAtSpawn`, no content.
	WriteAtSpawn,

	/// Declaration for `WorkerType::WriteLightOptimistic`, no content.
	WriteLightOptimistic,

	/// Declaration for `WorkerType::WriteLightDeclarative`.
	/// Declaration is child worker allowed write access, read access
	/// is not filtered.
	WriteLightDeclarative(AccessDeclaration, DeclarationFailureHandling),

	/// Declaration for `WorkerType::WriteOptimistic`, no content.
	WriteOptimistic,

	/// Declaration for `WorkerType::WriteDeclarative`.
	WriteDeclarative(AccessDeclarations, DeclarationFailureHandling),
}

impl WorkerDeclaration {
	/// Extract type from declaration.
	pub fn get_type(&self) -> WorkerType {
		match self {
			WorkerDeclaration::Stateless => WorkerType::Stateless,
			WorkerDeclaration::ReadLastBlock => WorkerType::ReadLastBlock,
			WorkerDeclaration::ReadAtSpawn => WorkerType::ReadAtSpawn,
			WorkerDeclaration::ReadOptimistic => WorkerType::ReadOptimistic,
			WorkerDeclaration::ReadDeclarative(..) => WorkerType::ReadDeclarative,
			WorkerDeclaration::WriteAtSpawn => WorkerType::WriteAtSpawn,
			WorkerDeclaration::WriteLightOptimistic => WorkerType::WriteLightOptimistic,
			WorkerDeclaration::WriteLightDeclarative(..) => WorkerType::WriteLightDeclarative,
			WorkerDeclaration::WriteOptimistic => WorkerType::WriteOptimistic,
			WorkerDeclaration::WriteDeclarative(..) => WorkerType::WriteDeclarative,
		}
	}
}

/// Access filters on storage.
/// Please define key only once and sort them.
#[derive(Debug, Clone, codec::Encode, codec::Decode)]
pub struct AccessDeclarations {
	/// Read access, depending on mode, this should exclude a concurrent write access.
	pub read_only: AccessDeclaration,
	/// Read and write access, depending on mode, this should exclude a concurrent read
	/// or write access.
	pub read_write: AccessDeclaration,
}

/// Access filter on storage.
#[derive(Debug, Clone, codec::Encode, codec::Decode)]
pub struct AccessDeclaration {
	/// Lock over a full prefix.
	///
	/// Gives access to all key starting with any of the declared prefixes.
	pub prefixes_lock: Vec<Vec<u8>>,

	/// Lock only over a given key.
	pub keys_lock: Vec<Vec<u8>>,
}

impl AccessDeclaration {
	/// Is there any declaration.
	pub fn is_empty(&self) -> bool {
		self.prefixes_lock.is_empty() && self.keys_lock.is_empty()
	}
}

impl AccessDeclaration {
	/// Declaration for top prefix only.
	pub fn top_prefix() -> Self {
		AccessDeclaration {
			prefixes_lock: sp_std::vec![Vec::new()],
			keys_lock: Vec::new(),
		}
	}
}

/// Extension for the [`Externalities`] trait.
pub trait ExternalitiesExt {
	/// Tries to find a registered extension and returns a mutable reference.
	fn extension<T: Any + Extension>(&mut self) -> Option<&mut T>;

	/// Register extension `ext`.
	///
	/// Should return error if extension is already registered or extensions are not supported.
	fn register_extension<T: Extension>(&mut self, ext: T) -> Result<(), Error>;

	/// Deregister and drop extension of `T` type.
	///
	/// Should return error if extension of type `T` is not registered or
	/// extensions are not supported.
	fn deregister_extension<T: Extension>(&mut self) -> Result<(), Error>;
}

impl ExternalitiesExt for &mut dyn Externalities {
	fn extension<T: Any + Extension>(&mut self) -> Option<&mut T> {
		self.extension_by_type_id(TypeId::of::<T>()).and_then(Any::downcast_mut)
	}

	fn register_extension<T: Extension>(&mut self, ext: T) -> Result<(), Error> {
		self.register_extension_with_type_id(TypeId::of::<T>(), Box::new(ext))
	}

	fn deregister_extension<T: Extension>(&mut self) -> Result<(), Error> {
		self.deregister_extension_by_type_id(TypeId::of::<T>())
	}
}

/// Externalities with partially locked extension store.
///
/// It forbid access to a mutably borrowed extension as if the extension
/// was behind a refcell.
/// Note that we do an unsafe inner unsafe access and therefore
/// also lock `register_extension` and `deregister_extension`.
#[derive(Delegate)]
#[delegate(Externalities, target = "externalities")]
pub struct ExternalitiesLockedExtension<'a> {
	externalities: &'a mut dyn Externalities,
	locked: TypeId,
}

impl<'a> ExtensionStore for ExternalitiesLockedExtension<'a> {
	fn extension_by_type_id(&mut self, type_id: TypeId) -> Option<&mut dyn Any> {
		if self.locked == type_id {
			panic!("Reentrant mutable access to extension.");
		}
		self.externalities.extension_by_type_id(type_id)
	}

	fn register_extension_with_type_id(
		&mut self,
		_type_id: TypeId,
		_extension: Box<dyn Extension>,
	) -> Result<(), Error> {
		Err(Error::ExtensionLocked)
	}

	fn deregister_extension_by_type_id(&mut self, _type_id: TypeId) -> Result<(), Error> {
		Err(Error::ExtensionLocked)
	}
}

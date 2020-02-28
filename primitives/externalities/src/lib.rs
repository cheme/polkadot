// Copyright 2017-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Substrate externalities abstraction
//!
//! The externalities mainly provide access to storage and to registered extensions. Extensions
//! are for example the keystore or the offchain externalities. These externalities are used to
//! access the node from the runtime via the runtime interfaces.
//!
//! This crate exposes the main [`Externalities`] trait.

use std::any::{Any, TypeId};

use sp_storage::{ChildInfo, ContextHandle};

pub use scope_limited::{set_and_run_with_externalities, with_externalities};
pub use extensions::{Extension, Extensions, ExtensionStore};

mod extensions;
mod scope_limited;

/// The Substrate externalities.
///
/// Provides access to the storage and to other registered extensions.
pub trait Externalities: ExtensionStore {
	/// switch back to initial context.
	/// To switch to a previous contex, the runtime will
	/// need to store the stacked context by itself.
	fn initial_child_context(
		&mut self,
	);

	/// Change current context to another one, if the handle is invalid
	/// it returns false.
	/// In case this return false, runtime must always switch or create
	/// context as a fallback (otherwhise future change in handle management
	/// would break consensus).
	fn switch_child_context(
		&mut self,
		handle: ContextHandle,
	) -> bool;

	/// This function change runtime context to a different state defined by this storage_key.
	/// Storage key is related to the top context and not the current context.
	/// If context does not exist it is created.
	///
	/// Return a handle of the context.
	fn switch_or_create_child_context(
		&mut self,
		child_info: &ChildInfo,
	) -> ContextHandle;
	
	/// Same as `switch_or_create_context` but with no creation.
	fn switch_no_create_child_context(
		&mut self,
		child_info: &ChildInfo,
	) -> Option<ContextHandle>;
	
	/// Read runtime storage.
	fn storage(&self, key: &[u8]) -> Option<Vec<u8>>;

	/// Get storage value hash. This may be optimized for large values.
	fn storage_hash(&self, key: &[u8]) -> Option<Vec<u8>>;

	/// Read original runtime storage, ignoring any overlayed changes.
	fn original_storage(&self, key: &[u8]) -> Option<Vec<u8>>;

	/// Get original storage value hash, ignoring any overlayed changes.
	/// This may be optimized for large values.
	///
	/// Returns an `Option` that holds the SCALE encoded hash.
	fn original_storage_hash(&self, key: &[u8]) -> Option<Vec<u8>>;

	/// Set storage entry `key` of current contract being called (effective immediately).
	fn set_storage(&mut self, key: Vec<u8>, value: Vec<u8>) {
		self.place_storage(key, Some(value));
	}

	/// Clear a storage entry (`key`) of current contract being called (effective immediately).
	fn clear_storage(&mut self, key: &[u8]) {
		self.place_storage(key.to_vec(), None);
	}

	/// Whether a storage entry exists.
	fn exists_storage(&self, key: &[u8]) -> bool {
		self.storage(key).is_some()
	}

	/// Returns the key immediately following the given key, if it exists.
	fn next_storage_key(&self, key: &[u8]) -> Option<Vec<u8>>;

	/// Clear entire storage, if possible.
	/// Return true if storage was cleared.
	fn kill_storage(&mut self) -> bool;

	/// Clear storage entries which keys are start with the given prefix.
	fn clear_prefix(&mut self, prefix: &[u8]);

	/// Set or clear a storage entry (`key`) of current contract being called (effective immediately).
	fn place_storage(&mut self, key: Vec<u8>, value: Option<Vec<u8>>);

	/// Get the identity of the chain.
	fn chain_id(&self) -> u64;

	/// Get the trie root of the current storage map. This will also update all child storage keys
	/// in the top-level storage map.
	///
	/// The hash is defined by the `Block`.
	///
	/// Returns the SCALE encoded hash.
	fn storage_root(&mut self) -> Vec<u8>;

	/// Get the change trie root of the current storage overlay at a block with given parent.
	/// `parent` is expects a SCALE encoded hash.
	///
	/// The hash is defined by the `Block`.
	///
	/// Returns the SCALE encoded hash.
	fn storage_changes_root(&mut self, parent: &[u8]) -> Result<Option<Vec<u8>>, ()>;

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
}

/// Extension for the [`Externalities`] trait.
pub trait ExternalitiesExt {
	/// Tries to find a registered extension and returns a mutable reference.
	fn extension<T: Any + Extension>(&mut self) -> Option<&mut T>;
}

impl ExternalitiesExt for &mut dyn Externalities {
	fn extension<T: Any + Extension>(&mut self) -> Option<&mut T> {
		self.extension_by_type_id(TypeId::of::<T>()).and_then(Any::downcast_mut)
	}
}

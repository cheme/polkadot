// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

//! Operation on runtime child storages.
//!
//! This module is a currently only a variant of unhashed with additional `child_info`.
// NOTE: could replace unhashed by having only one kind of storage (top trie being the child info
// of null length parent storage key).

use crate::sp_std::prelude::*;
use codec::{Codec, Encode, Decode};
pub use sp_core::storage::{ChildInfo, ChildType, ContextHandle};

#[derive(Clone, Copy)]
pub struct ChildContext<'a> {
	child_info: &'a ChildInfo,
	handle: Option<ContextHandle>
}

impl<'a> ChildContext<'a> {
	fn switch_context_create(&mut self) {
		if !self.handle.map(|h| {
			sp_io::default_child_storage::switch_context(h)
		}).unwrap_or(false) {
			match self.child_info.child_type() {
				ChildType::ParentKeyId => {
					let handle = sp_io::default_child_storage::switch_or_create_context(
						self.child_info.storage_key()
					);
					self.handle = Some(handle);
				}
			}
		};
	}
	fn switch_context_no_create(&mut self) -> bool {
		if !self.handle.map(|h| {
			sp_io::default_child_storage::switch_context(h)
		}).unwrap_or(false) {
			match self.child_info.child_type() {
				ChildType::ParentKeyId => {
					self.handle = sp_io::default_child_storage::switch_no_create_context(
						self.child_info.storage_key()
					);
					self.handle.is_some()
				}
			}
		} else {
			true
		}
	}
	/// Run on a child context.
	pub fn with_context_create<F, R>
	(
		&mut self,
		process: F,
		mut parent: Option<&mut ChildContext>,
	) -> R
		where
			F: Fn() -> R,
	{
		self.switch_context_create();
		let r = process();
		if let Some(parent) = parent.as_mut() {
			// could also assert no create is true
			parent.switch_context_create();
		} else {
			sp_io::default_child_storage::initial_context();
		}
		r
	}
	/// Run on a child context.
	pub fn with_context_no_create<F, R>
	(
		&mut self,
		process: F,
		mut parent: Option<&mut ChildContext>,
	) -> Option<R>
		where
			F: Fn() -> R,
	{
		if self.switch_context_no_create() {
			let r = Some(process());
			if let Some(parent) = parent.as_mut() {
				if !parent.switch_context_no_create() {
					runtime_print!("Error could not restore a parent context");
					sp_io::default_child_storage::initial_context();
				}
			} else {
				sp_io::default_child_storage::initial_context();
			}
			r
		} else {
			None
		}
	}
}

impl<'a> From<&'a ChildInfo> for ChildContext<'a> {
	fn from(child_info: &'a ChildInfo) -> Self {
		ChildContext {
			child_info,
			handle: None,
		}
	}
}

/// Return the value of the item in storage under `key`, or `None` if there is no explicit entry.
pub fn get<T: Decode + Sized>(
	child_info: &ChildInfo,
	key: &[u8],
) -> Option<T> {
	ChildContext::from(child_info).with_context_no_create(|| {
		sp_io::storage::get(
			key,
		).and_then(|v| {
			Decode::decode(&mut &v[..]).map(Some).unwrap_or_else(|_| {
				// TODO #3700: error should be handleable.
				runtime_print!(
					"ERROR: Corrupted state in child trie at {:?}/{:?}",
					child_info.storage_key(),
					key,
				);
				None
			})
		})
	}, None).flatten()
}

/// Return the value of the item in storage under `key`, or the type's default if there is no
/// explicit entry.
pub fn get_or_default<T: Decode + Sized + Default>(
	child_info: &ChildInfo,
	key: &[u8],
) -> T {
	get(child_info, key).unwrap_or_else(Default::default)
}

/// Return the value of the item in storage under `key`, or `default_value` if there is no
/// explicit entry.
pub fn get_or<T: Decode + Sized>(
	child_info: &ChildInfo,
	key: &[u8],
	default_value: T,
) -> T {
	get(child_info, key).unwrap_or(default_value)
}

/// Return the value of the item in storage under `key`, or `default_value()` if there is no
/// explicit entry.
pub fn get_or_else<T: Decode + Sized, F: FnOnce() -> T>(
	child_info: &ChildInfo,
	key: &[u8],
	default_value: F,
) -> T {
	get(child_info, key).unwrap_or_else(default_value)
}

/// Put `value` in storage under `key`.
pub fn put<T: Encode>(
	child_info: &ChildInfo,
	key: &[u8],
	value: &T,
) {
	ChildContext::from(child_info).with_context_create(|| {
		value.using_encoded(|slice|
			sp_io::storage::set(
				key,
				slice,
			)
		)
	}, None)
}

/// Remove `key` from storage, returning its value if it had an explicit entry or `None` otherwise.
pub fn take<T: Decode + Sized>(
	child_info: &ChildInfo,
	key: &[u8],
) -> Option<T> {
	let r = get(child_info, key);
	if r.is_some() {
		kill(child_info, key);
	}
	r
}

/// Remove `key` from storage, returning its value, or, if there was no explicit entry in storage,
/// the default for its type.
pub fn take_or_default<T: Codec + Sized + Default>(
	child_info: &ChildInfo,
	key: &[u8],
) -> T {
	take(child_info, key).unwrap_or_else(Default::default)
}

/// Return the value of the item in storage under `key`, or `default_value` if there is no
/// explicit entry. Ensure there is no explicit entry on return.
pub fn take_or<T: Codec + Sized>(
	child_info: &ChildInfo,
	key: &[u8],
	default_value: T,
) -> T {
	take(child_info, key).unwrap_or(default_value)
}

/// Return the value of the item in storage under `key`, or `default_value()` if there is no
/// explicit entry. Ensure there is no explicit entry on return.
pub fn take_or_else<T: Codec + Sized, F: FnOnce() -> T>(
	child_info: &ChildInfo,
	key: &[u8],
	default_value: F,
) -> T {
	take(child_info, key).unwrap_or_else(default_value)
}

/// Check to see if `key` has an explicit entry in storage.
pub fn exists(
	child_info: &ChildInfo,
	key: &[u8],
) -> bool {
	ChildContext::from(child_info).with_context_no_create(|| {
		sp_io::storage::read(
			key, &mut [0;0][..], 0,
		).is_some()
	}, None).unwrap_or(false)
}

/// Remove all `storage_key` key/values
pub fn kill_storage(
	child_info: &ChildInfo,
) -> bool {
	ChildContext::from(child_info).with_context_no_create(|| {
		sp_io::storage::storage_kill()
	}, None).unwrap_or(true)
}

/// Ensure `key` has no explicit entry in storage.
pub fn kill(
	child_info: &ChildInfo,
	key: &[u8],
) {
	ChildContext::from(child_info).with_context_no_create(|| {
		sp_io::storage::clear(
			key,
		);
	}, None);
}

/// Get a Vec of bytes from storage.
pub fn get_raw(
	child_info: &ChildInfo,
	key: &[u8],
) -> Option<Vec<u8>> {
	ChildContext::from(child_info).with_context_no_create(|| {
		sp_io::storage::get(
			key,
		)
	}, None).flatten()
}

/// Put a raw byte slice into storage.
pub fn put_raw(
	child_info: &ChildInfo,
	key: &[u8],
	value: &[u8],
) {
	ChildContext::from(child_info).with_context_create(|| {
		sp_io::storage::set(
			key,
			value,
		)
	}, None);
}

/// Calculate current child root value.
pub fn root(
	child_info: &ChildInfo,
) -> Vec<u8> {
	match child_info.child_type() {
		ChildType::ParentKeyId => sp_io::storage::root(
		)
	}
}

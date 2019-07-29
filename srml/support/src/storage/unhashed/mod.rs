// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! Operation on unhashed runtime storage

use crate::rstd::borrow::Borrow;
use super::{Codec, Encode, Decode, KeyedVec, Vec};
use substrate_primitives::Hasher;

pub mod generator;

/// Return the value of the item in storage under `key`, or `None` if there is no explicit entry.
pub fn get<H, T>(key: &[u8]) -> Option<T>
	where
		H: Hasher,
		H::Out: Ord,
		T: Decode + Sized,
{
	runtime_io::storage::<H>(key).map(|val| {
		Decode::decode(&mut &val[..]).expect("storage is not null, therefore must be a valid type")
	})
}

/// Return the value of the item in storage under `key`, or the type's default if there is no
/// explicit entry.
pub fn get_or_default<H, T>(key: &[u8]) -> T
	where
		H: Hasher,
		H::Out: Ord,
		T: Decode + Sized + Default,
{
	get::<H, T>(key).unwrap_or_else(Default::default)
}

/// Return the value of the item in storage under `key`, or `default_value` if there is no
/// explicit entry.
pub fn get_or<H, T>(key: &[u8], default_value: T) -> T
	where
		H: Hasher,
		H::Out: Ord,
		T: Decode + Sized,
{
	get::<H, T>(key).unwrap_or(default_value)
}

/// Return the value of the item in storage under `key`, or `default_value()` if there is no
/// explicit entry.
pub fn get_or_else<H, T, F>(key: &[u8], default_value: F) -> T
	where
		H: Hasher,
		H::Out: Ord,
		T: Decode + Sized,
		F: FnOnce() -> T,
{
	get::<H, T>(key).unwrap_or_else(default_value)
}

/// Put `value` in storage under `key`.
pub fn put<H, T>(key: &[u8], value: &T)
	where
		H: Hasher,
		H::Out: Ord,
		T: Encode + ?Sized,
{
	value.using_encoded(|slice| runtime_io::set_storage::<H>(key, slice));
}

/// Remove `key` from storage, returning its value if it had an explicit entry or `None` otherwise.
pub fn take<H, T>(key: &[u8]) -> Option<T>
	where
		H: Hasher,
		H::Out: Ord,
		T: Decode + Sized,
{
	let r = get::<H, T>(key);
	if r.is_some() {
		kill::<H>(key);
	}
	r
}

/// Remove `key` from storage, returning its value, or, if there was no explicit entry in storage,
/// the default for its type.
pub fn take_or_default<H, T>(key: &[u8]) -> T
	where
		H: Hasher,
		H::Out: Ord,
		T: Decode + Sized + Default,
{
	take::<H, T>(key).unwrap_or_else(Default::default)
}

/// Return the value of the item in storage under `key`, or `default_value` if there is no
/// explicit entry. Ensure there is no explicit entry on return.
pub fn take_or<H, T>(key: &[u8], default_value: T) -> T
	where
		H: Hasher,
		H::Out: Ord,
		T: Decode + Sized,
{
	take::<H, T>(key).unwrap_or(default_value)
}

/// Return the value of the item in storage under `key`, or `default_value()` if there is no
/// explicit entry. Ensure there is no explicit entry on return.
pub fn take_or_else<H, T, F>(key: &[u8], default_value: F) -> T
	where
		H: Hasher,
		H::Out: Ord,
		T: Decode + Sized,
		F: FnOnce() -> T,
{
	take::<H, T>(key).unwrap_or_else(default_value)
}

/// Check to see if `key` has an explicit entry in storage.
pub fn exists<H>(key: &[u8]) -> bool
	where
		H: Hasher,
		H::Out: Ord,
{
	runtime_io::read_storage::<H>(key, &mut [0;0][..], 0).is_some()
}

/// Ensure `key` has no explicit entry in storage.
pub fn kill<H>(key: &[u8])
	where
		H: Hasher,
		H::Out: Ord,
{
	runtime_io::clear_storage::<H>(key);
}

/// Ensure keys with the given `prefix` have no entries in storage.
pub fn kill_prefix<H>(prefix: &[u8])
	where
		H: Hasher,
		H::Out: Ord,
{
	runtime_io::clear_prefix::<H>(prefix);
}

/// Get a Vec of bytes from storage.
pub fn get_raw<H>(key: &[u8]) -> Option<Vec<u8>>
	where
		H: Hasher,
		H::Out: Ord,
{
	runtime_io::storage::<H>(key)
}

/// Put a raw byte slice into storage.
pub fn put_raw<H>(key: &[u8], value: &[u8])
	where
		H: Hasher,
		H::Out: Ord,
{
	runtime_io::set_storage::<H>(key, value)
}

/// A trait to conveniently store a vector of storable data.
pub trait StorageVec<H>
	where
		H: Hasher,
		H::Out: Ord,
{
	type Item: Default + Sized + Codec;
	const PREFIX: &'static [u8];

	/// Get the current set of items.
	fn items() -> Vec<Self::Item> {
		(0..Self::count()).into_iter().map(Self::item).collect()
	}

	/// Set the current set of items.
	fn set_items<I, T>(items: I)
		where
			I: IntoIterator<Item=T>,
			T: Borrow<Self::Item>,
	{
		let mut count: u32 = 0;

		for i in items.into_iter() {
			put::<H, _>(&count.to_keyed_vec(Self::PREFIX), i.borrow());
			count = count.checked_add(1).expect("exceeded runtime storage capacity");
		}

		Self::set_count(count);
	}

	fn set_item(index: u32, item: &Self::Item) {
		if index < Self::count() {
			put::<H, _>(&index.to_keyed_vec(Self::PREFIX), item);
		}
	}

	fn clear_item(index: u32) {
		if index < Self::count() {
			kill::<H>(&index.to_keyed_vec(Self::PREFIX));
		}
	}

	fn item(index: u32) -> Self::Item {
		get_or_default::<H, _>(&index.to_keyed_vec(Self::PREFIX))
	}

	fn set_count(count: u32) {
		(count..Self::count()).for_each(Self::clear_item);
		put::<H, _>(&b"len".to_keyed_vec(Self::PREFIX), &count);
	}

	fn count() -> u32 {
		get_or_default::<H, _>(&b"len".to_keyed_vec(Self::PREFIX))
	}
}

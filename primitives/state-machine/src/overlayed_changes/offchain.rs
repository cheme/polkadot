// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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

//! Overlayed changes for offchain indexing.

use sp_core::offchain::OffchainOverlayedChange;
use sp_std::prelude::Vec;
use super::changeset::{OverlayedMap, OverlayedEntry};

/// In-memory storage for offchain workers recoding changes for the actual offchain storage implementation.
#[derive(Debug, Clone)]
pub enum OffchainOverlayedChanges {
	/// Writing overlay changes to the offchain worker database is disabled by configuration.
	Disabled,
	/// Overlay changes can be recorded using the inner collection of this variant,
	/// where the identifier is the tuple of `(prefix, key)`.
	Enabled(OverlayedMap<(Vec<u8>, Vec<u8>), OffchainOverlayedChange>),
}

impl Default for OffchainOverlayedChanges {
	fn default() -> Self {
		Self::Disabled
	}
}

impl OffchainOverlayedChanges {
	/// Create the disabled variant.
	pub fn disabled() -> Self {
		Self::Disabled
	}

	/// Create the enabled variant.
	pub fn enabled() -> Self {
		Self::Enabled(OverlayedMap::default())
	}

	/// Consume the offchain storage and iterate over all key value pairs.
	pub fn into_iter(self) -> OffchainOverlayedChangesIntoIter {
		OffchainOverlayedChangesIntoIter::new(self)
	}

	/// Iterate over all key value pairs by reference.
	pub fn iter<'a>(&'a self) -> OffchainOverlayedChangesIter {
		OffchainOverlayedChangesIter::new(&self)
	}

	/// Drain all elements of changeset.
	pub fn drain(&mut self) -> OffchainOverlayedChangesIntoIter {
		OffchainOverlayedChangesIntoIter::drain(self)
	}

	/// Remove a key and its associated value from the offchain database.
	pub fn remove(&mut self, prefix: &[u8], key: &[u8]) {
		if let Self::Enabled(storage) = self {
			let _ = storage.set(
				(prefix.to_vec(), key.to_vec()),
				OffchainOverlayedChange::Remove,
				None,
			);
		}
	}

	/// Set the value associated with a key under a prefix to the value provided.
	pub fn set(&mut self, prefix: &[u8], key: &[u8], value: &[u8]) {
		if let Self::Enabled(storage) = self {
			let _ = storage.set(
				(prefix.to_vec(), key.to_vec()),
				OffchainOverlayedChange::SetValue(value.to_vec()),
				None,
			);
		}
	}

	/// Remove a key and its associated value from the local offchain database.
	pub fn remove_local(&mut self, prefix: &[u8], key: &[u8]) {
		if let Self::Enabled(storage) = self {
			let _ = storage.set(
				(prefix.to_vec(), key.to_vec()),
				OffchainOverlayedChange::RemoveLocal,
				None,
			);
		}
	}

	/// Set the value associated with a key under a prefix to the local value provided.
	pub fn set_local(&mut self, prefix: &[u8], key: &[u8], value: &[u8]) {
		if let Self::Enabled(storage) = self {
			let _ = storage.set(
				(prefix.to_vec(), key.to_vec()),
				OffchainOverlayedChange::SetValueLocal(value.to_vec()),
				None,
			);
		}
	}

	/// Obtain a associated value to the given key in storage with prefix.
	pub fn get(&self, prefix: &[u8], key: &[u8]) -> Option<OffchainOverlayedChange> {
		if let Self::Enabled(storage) = self {
			let key = (prefix.to_vec(), key.to_vec());
			storage.get(&key).map(|entry| entry.value_ref()).cloned()
		} else {
			None
		}
	}

	/// Reference to inner change set.
	pub fn overlay(&self) -> Option<&OverlayedMap<(Vec<u8>, Vec<u8>), OffchainOverlayedChange>> {
		if let Self::Enabled(storage) = self {
			Some(&storage)
		} else {
			None
		}
	}

	/// Mutable reference to inner change set.
	pub fn overlay_mut(&mut self) -> Option<&mut OverlayedMap<(Vec<u8>, Vec<u8>), OffchainOverlayedChange>> {
		if let Self::Enabled(storage) = self {
			Some(storage)
		} else {
			None
		}
	}

}

use sp_std::collections::btree_map;

/// Iterate by reference over the prepared offchain worker storage changes.
pub struct OffchainOverlayedChangesIter<'i> {
	inner: Option<sp_std::iter::Map<
		btree_map::Iter<'i, (Vec<u8>,Vec<u8>), OverlayedEntry<OffchainOverlayedChange>>,
		fn((&'i (Vec<u8>, Vec<u8>), &'i OverlayedEntry<OffchainOverlayedChange>))
			-> (&'i (Vec<u8>, Vec<u8>), &'i OffchainOverlayedChange),
	>>,

}

impl<'i> Iterator for OffchainOverlayedChangesIter<'i> {
	type Item = (&'i (Vec<u8>, Vec<u8>), &'i OffchainOverlayedChange);
	fn next(&mut self) -> Option<Self::Item> {
		if let Some(ref mut iter) = self.inner {
			iter.next()
		} else {
			None
		}
	}
}

impl<'i> OffchainOverlayedChangesIter<'i> {
	/// Create a new iterator based on a refernce to the parent container.
	pub fn new(container: &'i OffchainOverlayedChanges) -> Self {
		match container {
			OffchainOverlayedChanges::Enabled(inner) => Self {
				inner: Some(inner.changes.iter().map(map_kv_ref))
			},
			OffchainOverlayedChanges::Disabled => Self { inner: None, },
		}
	}
}


/// Iterate by value over the prepared offchain worker storage changes.
pub struct OffchainOverlayedChangesIntoIter {
	inner: Option<sp_std::iter::Map<
		btree_map::IntoIter<(Vec<u8>,Vec<u8>), OverlayedEntry<OffchainOverlayedChange>>,
		fn(((Vec<u8>, Vec<u8>), OverlayedEntry<OffchainOverlayedChange>))
			-> ((Vec<u8>, Vec<u8>), OffchainOverlayedChange),
	>>,
}

impl Iterator for OffchainOverlayedChangesIntoIter {
	type Item = ((Vec<u8>, Vec<u8>), OffchainOverlayedChange);
	fn next(&mut self) -> Option<Self::Item> {
		if let Some(ref mut iter) = self.inner {
			iter.next()
		} else {
			None
		}
	}
}

fn map_kv(
	kv: ((Vec<u8>, Vec<u8>), OverlayedEntry<OffchainOverlayedChange>)
) -> ((Vec<u8>, Vec<u8>), OffchainOverlayedChange) {
	(kv.0, kv.1.into_value())
}

fn map_kv_ref<'i>(
	kv: (&'i (Vec<u8>, Vec<u8>), &'i OverlayedEntry<OffchainOverlayedChange>)
) -> (&'i (Vec<u8>, Vec<u8>), &'i OffchainOverlayedChange) {
	(kv.0, kv.1.value_ref())
}

impl OffchainOverlayedChangesIntoIter {
	/// Create a new iterator by consuming the collection.
	pub fn new(container: OffchainOverlayedChanges) -> Self {
		match container {
			OffchainOverlayedChanges::Enabled(inner) => Self {
				inner: Some(inner.changes.into_iter().map(map_kv))
			},
			OffchainOverlayedChanges::Disabled => Self { inner: None, },
		}
	}

	/// Create a new iterator by taking a mut reference to the collection,
	/// for the lifetime of the created drain iterator.
	pub fn drain(container: &mut OffchainOverlayedChanges) -> Self {
		match container {
			OffchainOverlayedChanges::Enabled(ref mut inner) => {
				let inner = sp_std::mem::replace(inner, Default::default());
				Self {
					inner: Some(inner.changes.into_iter().map(map_kv))
				}
			},
			OffchainOverlayedChanges::Disabled => Self { inner: None, },
		}
	}
}

#[cfg(test)]
mod test {
	use super::*;
	use sp_core::offchain::STORAGE_PREFIX;

	#[test]
	fn test_drain() {
		let mut ooc = OffchainOverlayedChanges::enabled();
		ooc.set(STORAGE_PREFIX,b"kkk", b"vvv");
		let drained = ooc.drain().count();
		assert_eq!(drained, 1);
		let leftover = ooc.iter().count();
		assert_eq!(leftover, 0);

		ooc.set(STORAGE_PREFIX, b"a", b"v");
		ooc.set(STORAGE_PREFIX, b"b", b"v");
		ooc.set(STORAGE_PREFIX, b"c", b"v");
		ooc.set(STORAGE_PREFIX, b"d", b"v");
		ooc.set(STORAGE_PREFIX, b"e", b"v");
		assert_eq!(ooc.iter().count(), 5);
	}

	#[test]
	fn test_accumulated_set_remove_set() {
		let mut ooc = OffchainOverlayedChanges::enabled();
		ooc.set(STORAGE_PREFIX, b"ppp", b"qqq");
		ooc.remove(STORAGE_PREFIX, b"ppp");
		// keys are equiv, so it will overwrite the value and the overlay will contain
		// one item
		assert_eq!(ooc.iter().count(), 1);

		ooc.set(STORAGE_PREFIX, b"ppp", b"rrr");
		let mut iter = ooc.into_iter();
		assert_eq!(
			iter.next(),
			Some(
				((STORAGE_PREFIX.to_vec(), b"ppp".to_vec()),
				OffchainOverlayedChange::SetValue(b"rrr".to_vec()))
			)
		);
		assert_eq!(iter.next(), None);
	}
}

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

//! The overlayed changes to state.

#[cfg(test)]
use std::iter::FromIterator;
use std::collections::{HashMap, BTreeMap, BTreeSet};
use codec::Decode;
use crate::changes_trie::{NO_EXTRINSIC_INDEX, Configuration as ChangesTrieConfig};
use sp_core::storage::{well_known_keys::EXTRINSIC_INDEX, OwnedChildInfo, ChildInfo};
use crate::{Layers, LayerEntry, LayeredOpsResult};
use std::ops;

/// The overlayed changes to state to be queried on top of the backend.
///
/// A transaction shares all prospective changes within an inner overlay
/// that can be cleared.
#[derive(Debug, Default, Clone)]
pub struct OverlayedChanges {
	/// Changes with their history.
	pub(crate) changes: OverlayedChangeSet,
	/// Changes trie configuration. None by default, but could be installed by the
	/// runtime if it supports change tries.
	pub(crate) changes_trie_config: Option<ChangesTrieConfig>,
}

/// The storage value, used inside OverlayedChanges.
#[derive(Debug, Default, Clone)]
#[cfg_attr(test, derive(PartialEq))]
pub struct OverlayedValue {
	/// Current value. None if value has been deleted.
	pub value: Option<Vec<u8>>,
	/// The set of extinsic indices where the values has been changed.
	/// Is filled only if runtime has announced changes trie support.
	pub extrinsics: Option<BTreeSet<u32>>,
}

type TreeChangeSet = BTreeMap<Vec<u8>, Layers<OverlayedValue>>;

/// Overlayed change set, content keep trace of its history.
///
/// Maps containing a linear history of each values are used.
#[derive(Debug, Clone)]
#[cfg_attr(test, derive(PartialEq))]
pub struct OverlayedChangeSet {
	/// Current number of stacked transaction.
	pub(crate) number_transactions: usize,
	/// Top level storage changes.
	pub(crate) top: TreeChangeSet,
	/// Child storage changes.
	/// OwnedChildInfo is currently an absolute value, for some child trie
	/// operations (eg full deletion) it will need to change
	/// to `Layers<OwnedChildInfo>`.
	pub(crate) children: HashMap<Vec<u8>, (TreeChangeSet, OwnedChildInfo)>,
}

impl Default for OverlayedChangeSet {
	fn default() -> Self {
		OverlayedChangeSet {
			number_transactions: crate::COMMITTED_LAYER + 1,
			top: Default::default(),
			children: Default::default(),
		}
	}
}

#[cfg(test)]
impl FromIterator<(Vec<u8>, OverlayedValue)> for OverlayedChangeSet {
	fn from_iter<T: IntoIterator<Item = (Vec<u8>, OverlayedValue)>>(iter: T) -> Self {
		let mut result = OverlayedChangeSet::default();
		result.top = iter.into_iter().map(|(k, value)| (k, {
			let mut history = Layers::default();
			history.push_unchecked(LayerEntry { value, index: crate::COMMITTED_LAYER });
			history
		})).collect();
		result
	}
}

/// Variant of historical data `set` function with internal extrinsics update.
/// It avoids accessing two times the historical value item.
/// It does remove latest historical dropped items.
fn set_with_extrinsic_overlayed_value(
	history: &mut Layers<OverlayedValue>,
	number_transaction: usize,
	value: Option<Vec<u8>>,
	extrinsic_index: Option<u32>,
) {
	if let Some(extrinsic) = extrinsic_index {
		set_with_extrinsic_inner_overlayed_value(history, number_transaction, value, extrinsic)
	} else {
		history.set(number_transaction, OverlayedValue {
			value,
			extrinsics: None,
		})
	}
}

fn set_with_extrinsic_inner_overlayed_value(
	history: &mut Layers<OverlayedValue>,
	number_transaction: usize,
	value: Option<Vec<u8>>,
	extrinsic_index: u32,
) {
	if let Some(current) = history.get_mut() {
		if current.index == number_transaction {
			current.value.value = value;
			current.value.extrinsics.get_or_insert_with(Default::default)
				.insert(extrinsic_index);
		} else {
			let mut extrinsics = current.value.extrinsics.clone();
			extrinsics.get_or_insert_with(Default::default)
				.insert(extrinsic_index);
			history.push_unchecked(LayerEntry {
				index: number_transaction,
				value: OverlayedValue {
					value,
					extrinsics,
				},
			});
		}
	} else {
		let mut extrinsics: Option<BTreeSet<u32>> = None;
		extrinsics.get_or_insert_with(Default::default)
			.insert(extrinsic_index);
		history.push_unchecked(LayerEntry {
			index: number_transaction,
			value: OverlayedValue {
				value,
				extrinsics,
			},
		});
	}
}

impl OverlayedChangeSet {
	/// Whether the change set is empty.
	pub fn is_empty(&self) -> bool {
		self.top.is_empty() && self.children.is_empty()
	}

	/// Discard prospective changes from the change set.
	pub fn discard_prospective(&mut self) {
		retain(&mut self.top, |_, history| history.discard_prospective() != LayeredOpsResult::Cleared);
		self.children.retain(|_, (map, _child_info)| {
			retain(map, |_, history| history.discard_prospective() != LayeredOpsResult::Cleared);
			!map.is_empty()
		});
		self.number_transactions = 1;
	}

	/// Commit prospective changes into the change set.
	pub fn commit_prospective(&mut self) {
		retain(&mut self.top, |_, history| history.commit_prospective() != LayeredOpsResult::Cleared);
		self.children.retain(|_, (map, _child_info)| {
			retain(map, |_, history| history.commit_prospective() != LayeredOpsResult::Cleared);
			!map.is_empty()
		});
		self.number_transactions = 1;
	}

	/// Create a new transactional layer.
	pub fn start_transaction(&mut self) {
		self.number_transactions += 1;
	}

	/// Discard a transactional layer.
	/// There is always a transactional layer running
	/// (discarding the last trasactional layer open a new one).
	pub fn discard_transaction(&mut self) {
		let number_transactions = self.number_transactions.saturating_sub(1);

		retain(&mut self.top, |_, history| history.discard_transaction(number_transactions) != LayeredOpsResult::Cleared);
		self.children.retain(|_, (map, _child_info)| {
			retain(map, |_, history| history.discard_transaction(number_transactions) != LayeredOpsResult::Cleared);
			!map.is_empty()
		});
		if number_transactions == crate::COMMITTED_LAYER {
			self.number_transactions = crate::COMMITTED_LAYER + 1;
		} else {
			self.number_transactions = number_transactions;
		}
	}

	/// Commit a transactional layer into previous transaction layer.
	pub fn commit_transaction(&mut self) {
		if self.number_transactions > crate::COMMITTED_LAYER + 1 {
			self.number_transactions -= 1;
		}

		let number_transactions = self.number_transactions;
		retain(&mut self.top, |_, history| history.commit_transaction(number_transactions) != LayeredOpsResult::Cleared);
		self.children.retain(|_, (map, _child_info)| {
			retain(map, |_, history| history.commit_transaction(number_transactions) != LayeredOpsResult::Cleared);
			!map.is_empty()
		});
	}

	/// Iterator over current values for a given overlay, including change trie information.
	pub fn iter_overlay(
		&self,
		storage_key: Option<&[u8]>,
	) -> (impl Iterator<Item = (&[u8], &OverlayedValue)>, Option<ChildInfo>) {
		let (option_map, option_child_info) = if let Some(storage_key) = storage_key.as_ref() {
			if let Some((content, child_info)) = self.children.get(*storage_key) {
				(Some(content), Some(child_info.as_ref()))
			} else {
				(None, None)
			}
		} else {
			(Some(&self.top), None)
		};
		(option_map
			.into_iter()
			.flat_map(move |map| map.iter()
				.filter_map(move |(k, v)|
					v.get().map(|v| (k.as_slice(), v)))
			), option_child_info)

	}

	/// Iterator over current values for a given overlay.
	pub fn iter_values(
		&self,
		storage_key: Option<&[u8]>,
	) -> impl Iterator<Item = (&[u8], Option<&[u8]>)> {
		self.iter_overlay(storage_key).0
			.map(|(k, v)| (k, v.value.as_ref().map(|v| v.as_slice())))
	}

	/// Iterator over current values of all children overlays.
	pub fn children_iter(
		&self,
	) -> impl Iterator<Item=(
		&[u8],
		impl Iterator<Item = (&[u8], Option<&[u8]>)>,
		ChildInfo,
	)> {
		self.children.iter()
			.map(move |(keyspace, child_content)| (
				keyspace.as_slice(),
				child_content.0.iter()
					.filter_map(move |(k, v)| v.get().map(|v| (
						k.as_slice(),
						v.value.as_ref()
							.map(|v| v.as_slice()),
					))),
				child_content.1.as_ref(),
			))
	}

	/// Iterator over current values of all children overlays.
	/// This is a variant of `children_iter` with owned `Vec<u8>` keys and values.
	pub fn owned_children_iter<'a>(
		&'a self,
	) -> impl Iterator<Item=(
		Vec<u8>,
		impl Iterator<Item = (Vec<u8>, Option<Vec<u8>>)> + 'a,
		OwnedChildInfo,
	)> + 'a {
		self.children.iter()
			.map(move |(keyspace, (map, child_info))| (
				keyspace.to_vec(),
				map.iter()
					.filter_map(move |(k, v)|
						v.get()
							.map(|v| (k.to_vec(), v.value.as_ref().map(|v| v.to_vec())))),
				child_info.to_owned(),
			))
	}

	/// Iterator over current values of all children overlays, including change trie information.
	pub fn children_iter_overlay(
		&self,
	) -> impl Iterator<Item=(
		&[u8],
		impl Iterator<Item = (&[u8], &OverlayedValue)>,
		ChildInfo,
	)> {
		self.children.iter()
			.map(move |(keyspace, (map, child_info))| (
				keyspace.as_slice(),
				map.iter()
					.filter_map(move |(k, v)|
						v.get().map(|v| (k.as_slice(), v))),
				child_info.as_ref(),
			))
	}

	/// Test only method for accessing current prospective values.
	/// This method is only here to keep compatibility with previous tests,
	/// please do not use for new tests.
	#[cfg(test)]
	pub(crate) fn top_prospective(&self) -> BTreeMap<Vec<u8>, OverlayedValue> {
		let mut result = BTreeMap::new();
		for (k, v) in self.top.iter() {
			if let Some(v) = v.get_prospective() {
				result.insert(k.clone(), v.clone());
			}
		}
		result
	}

	/// Test only method to access current committed changes.
	/// This method is only here to keep compatibility with previous tests,
	/// please do not use for new tests.
	#[cfg(test)]
	pub(crate) fn top_committed(&self) -> BTreeMap<Vec<u8>, OverlayedValue> {
		let mut result = BTreeMap::new();
		for (k, v) in self.top.iter() {
			if let Some(v) = v.get_committed() {
				result.insert(k.clone(), v.clone());
			}
		}
		result
	}
}

impl OverlayedChanges {
	/// Whether the overlayed changes are empty.
	pub fn is_empty(&self) -> bool {
		self.changes.is_empty()
	}

	/// Sets the changes trie configuration.
	///
	/// Returns false if configuration has been set already and we now trying
	/// to install different configuration. This isn't supported now.
	pub(crate) fn set_changes_trie_config(&mut self, config: ChangesTrieConfig) -> bool {
		if let Some(ref old_config) = self.changes_trie_config {
			// we do not support changes trie configuration' change now
			if *old_config != config {
				return false;
			}
		}

		self.changes_trie_config = Some(config);
		true
	}

	/// Returns a double-Option: None if the key is unknown (i.e. and the query should be refered
	/// to the backend); Some(None) if the key has been deleted. Some(Some(...)) for a key whose
	/// value has been set.
	pub fn storage(&self, key: &[u8]) -> Option<Option<&[u8]>> {
		if let Some(overlay_value) = self.changes.top.get(key) {
			if let Some(o_value) = overlay_value.get() {
				return Some(o_value.value.as_ref().map(|v| v.as_slice()))
			}
		}
		None
	}

	/// Returns a double-Option: None if the key is unknown (i.e. and the query should be refered
	/// to the backend); Some(None) if the key has been deleted. Some(Some(...)) for a key whose
	/// value has been set.
	pub fn child_storage(&self, storage_key: &[u8], key: &[u8]) -> Option<Option<&[u8]>> {
		if let Some(map) = self.changes.children.get(storage_key) {
			if let Some(overlay_value) = map.0.get(key) {
				if let Some(o_value) = overlay_value.get() {
					return Some(o_value.value.as_ref().map(|v| v.as_slice()))
				}
			}
		}
		None
	}

	/// Inserts the given key-value pair into the prospective change set.
	///
	/// `None` can be used to delete a value specified by the given key.
	pub fn set_storage(&mut self, key: Vec<u8>, value: Option<Vec<u8>>) {
		let extrinsic_index = self.extrinsic_index();
		let entry = self.changes.top.entry(key).or_default();
		set_with_extrinsic_overlayed_value(entry, self.changes.number_transactions, value, extrinsic_index);
	}

	/// Inserts the given key-value pair into the prospective child change set.
	///
	/// `None` can be used to delete a value specified by the given key.
	pub(crate) fn set_child_storage(
		&mut self,
		storage_key: Vec<u8>,
		child_info: ChildInfo,
		key: Vec<u8>,
		value: Option<Vec<u8>>,
	) {
		let extrinsic_index = self.extrinsic_index();
		let map_entry = self.changes.children.entry(storage_key)
			.or_insert_with(|| (Default::default(), child_info.to_owned()));
		let updatable = map_entry.1.try_update(child_info);
		debug_assert!(updatable);

		let entry = map_entry.0.entry(key).or_default();
		set_with_extrinsic_overlayed_value(
			entry,
			self.changes.number_transactions,
			value,
			extrinsic_index,
		);
	}

	/// Clear child storage of given storage key.
	///
	/// NOTE that this doesn't take place immediately but written into the prospective
	/// change set, and still can be reverted by [`discard_prospective`].
	///
	/// [`discard_prospective`]: #method.discard_prospective
	pub(crate) fn clear_child_storage(
		&mut self,
		storage_key: &[u8],
		child_info: ChildInfo,
	) {
		let extrinsic_index = self.extrinsic_index();
		let number_transaction = self.changes.number_transactions;
		let map_entry = self.changes.children.entry(storage_key.to_vec())
			.or_insert_with(|| (Default::default(), child_info.to_owned()));
		let updatable = map_entry.1.try_update(child_info);
		debug_assert!(updatable);

		map_entry.0.values_mut()
			.for_each(|e| set_with_extrinsic_overlayed_value(e, number_transaction, None, extrinsic_index));
	}

	/// Removes all key-value pairs which keys share the given prefix.
	///
	/// NOTE that this doesn't take place immediately but written into the prospective
	/// change set, and still can be reverted by [`discard_prospective`].
	///
	/// [`discard_prospective`]: #method.discard_prospective
	pub(crate) fn clear_prefix(&mut self, prefix: &[u8]) {
		let extrinsic_index = self.extrinsic_index();

		for (key, entry) in self.changes.top.iter_mut() {
			if key.starts_with(prefix) {
				set_with_extrinsic_overlayed_value(entry, self.changes.number_transactions, None, extrinsic_index);
			}
		}
	}

	pub(crate) fn clear_child_prefix(
		&mut self,
		storage_key: &[u8],
		child_info: ChildInfo,
		prefix: &[u8],
	) {
		let extrinsic_index = self.extrinsic_index();
		if let Some(child_change) = self.changes.children.get_mut(storage_key) {
			let updatable = child_change.1.try_update(child_info);
			debug_assert!(updatable);

			for (key, entry) in child_change.0.iter_mut() {
				if key.starts_with(prefix) {
					set_with_extrinsic_overlayed_value(entry, self.changes.number_transactions, None, extrinsic_index);
				}
			}
		}
	}

	/// Discard prospective changes to state.
	pub fn discard_prospective(&mut self) {
		self.changes.discard_prospective();
	}

	/// Commit prospective changes to state.
	pub fn commit_prospective(&mut self) {
		self.changes.commit_prospective();
	}

	/// Create a new transactional layer.
	pub fn start_transaction(&mut self) {
		self.changes.start_transaction();
	}

	/// Discard a transactional layer.
	/// A transaction is always running (history always end with pending).
	pub fn discard_transaction(&mut self) {
		self.changes.discard_transaction();
	}

	/// Commit a transactional layer.
	pub fn commit_transaction(&mut self) {
		self.changes.commit_transaction();
	}

	/// Consume `OverlayedChanges` and take committed set.
	pub fn into_committed(self) -> (
		impl Iterator<Item=(Vec<u8>, Option<Vec<u8>>)>,
		impl Iterator<Item=(Vec<u8>, impl Iterator<Item=(Vec<u8>, Option<Vec<u8>>)>, OwnedChildInfo)>,
	){
		let top = self.changes.top;
		let children = self.changes.children;
		(
			top.into_iter()
				.filter_map(move |(k, v)| v.into_committed()
					.map(|v| (k, v.value))),
			children.into_iter().map(move |(storage_key, child_content)| (
				storage_key,
				child_content.0.into_iter()
					.filter_map(move |(k, v)| v.into_committed()
						.map(|v| (k, v.value))),
				child_content.1.to_owned(),
			))
		)
	}

	/// Inserts storage entry responsible for current extrinsic index.
	#[cfg(test)]
	pub(crate) fn set_extrinsic_index(&mut self, extrinsic_index: u32) {
		use codec::Encode;
		self.set_storage(EXTRINSIC_INDEX.to_vec(), Some(extrinsic_index.encode()));
	}

	/// Test only method to create a change set from committed
	/// and prospective content.
	#[cfg(test)]
	pub(crate) fn new_from_top(
		committed: Vec<(Vec<u8>, Option<Vec<u8>>)>,
		prospective: Vec<(Vec<u8>, Option<Vec<u8>>)>,
		changes_trie_config: Option<ChangesTrieConfig>,
	) -> Self {
		let changes = OverlayedChangeSet::default();
		let mut result = OverlayedChanges {
			changes,
			changes_trie_config,
		};
		committed.into_iter().for_each(|(k, v)| result.set_storage(k, v));
		result.changes.commit_prospective();
		prospective.into_iter().for_each(|(k, v)| result.set_storage(k, v));
		result
	}

	/// Returns current extrinsic index to use in changes trie construction.
	/// None is returned if it is not set or changes trie config is not set.
	/// Persistent value (from the backend) can be ignored because runtime must
	/// set this index before first and unset after last extrinsic is executied.
	/// Changes that are made outside of extrinsics, are marked with
	/// `NO_EXTRINSIC_INDEX` index.
	fn extrinsic_index(&self) -> Option<u32> {
		match self.changes_trie_config.is_some() {
			true => Some(
				self.storage(EXTRINSIC_INDEX)
					.and_then(|idx| idx.and_then(|idx| Decode::decode(&mut &*idx).ok()))
					.unwrap_or(NO_EXTRINSIC_INDEX)),
			false => None,
		}
	}

	#[cfg(any(test, feature = "test-helpers"))]
	/// Iterator over current values of the overlay.
	pub fn iter_values(
		&self,
		storage_key: Option<&[u8]>,
	) -> impl Iterator<Item = (&[u8], Option<&[u8]>)> {
		self.changes.iter_values(storage_key)
	}

	#[cfg(any(test, feature = "test-helpers"))]
	/// Count the number of key value pairs, at every history number_transaction.
	/// Should only be use for debugging or testing, this is slow
	/// and technical.
	pub fn top_count_keyvalue_pair(&self) -> usize {
		let mut result = 0;
		for (_, v) in self.changes.top.iter() {
			result += v.len()
		}
		result
	}

	/// Get child info for a storage key.
	/// Take the latest value so prospective first.
	pub fn child_info(&self, storage_key: &[u8]) -> Option<ChildInfo> {
		if let Some((_, child_info)) = self.changes.children.get(storage_key) {
			return Some(child_info.as_ref());
		}
		None
	}

	/// Returns the next (in lexicographic order) storage key in the overlayed alongside its value.
	/// If no value is next then `None` is returned.
	pub fn next_storage_key_change(&self, key: &[u8]) -> Option<(&[u8], &OverlayedValue)> {
		let range = (ops::Bound::Excluded(key), ops::Bound::Unbounded);

		let mut next_keys = self.changes.top.range::<[u8], _>(range);
		while let Some((key, historic_value)) = next_keys.next() {
			if let Some(overlay_value) = historic_value.get() {
				return Some((key, overlay_value));
			}
		}
		None
	}

	/// Returns the next (in lexicographic order) child storage key in the overlayed alongside its
	/// value.  If no value is next then `None` is returned.
	pub fn next_child_storage_key_change(
		&self,
		storage_key: &[u8],
		key: &[u8]
	) -> Option<(&[u8], &OverlayedValue)> {
		let range = (ops::Bound::Excluded(key), ops::Bound::Unbounded);

		if let Some(child) = self.changes.children.get(storage_key) {
			let mut next_keys = child.0.range::<[u8], _>(range);
			while let Some((key, historic_value)) = next_keys.next() {
				if let Some(overlay_value) = historic_value.get() {
					return Some((key, overlay_value));
				}
			}
		}
		None
	}
}

/// This is an implementation of retain for btreemap,
/// this is used to keep a similar api with previous
/// hashmap usage.
/// This could also be easilly replace if btreemap gets
/// an implementation for retain in the future.
fn retain<K: Ord + Clone, V, F>(map: &mut BTreeMap<K, V>, mut f: F) where
    F: FnMut(&K, &mut V) -> bool, {
	// this is use to discard some historical values when
	// their status is cleared.
	// Regarding this use case we will only remove individually.
	// Rebuilding trie from iterator may be better if there is
	// more removal.
	// Regarding this use case skipping removal can be a better
	// choice.
	let mut rem = Vec::new();
	for (k, v) in map.iter_mut() {
		if !f(k, v) {
			rem.push(k.clone());
		}
	}
	for k in rem {
		map.remove(&k);
	}
}

#[cfg(test)]
impl From<Option<Vec<u8>>> for OverlayedValue {
	fn from(value: Option<Vec<u8>>) -> OverlayedValue {
		OverlayedValue { value, ..Default::default() }
	}
}

#[cfg(test)]
mod tests {
	use hex_literal::hex;
	use sp_core::{
		Blake2Hasher, traits::Externalities, storage::well_known_keys::EXTRINSIC_INDEX,
	};
	use crate::backend::InMemory;
	use crate::changes_trie::InMemoryStorage as InMemoryChangesTrieStorage;
	use crate::ext::Ext;
	use super::*;

	fn strip_extrinsic_index(mut map: BTreeMap<Vec<u8>, OverlayedValue>)
		-> BTreeMap<Vec<u8>, OverlayedValue>
	{
		map.remove(&EXTRINSIC_INDEX.to_vec());
		map
	}

	#[test]
	fn overlayed_storage_works() {
		let mut overlayed = OverlayedChanges::default();

		let key = vec![42, 69, 169, 142];

		assert!(overlayed.storage(&key).is_none());

		overlayed.set_storage(key.clone(), Some(vec![1, 2, 3]));
		assert_eq!(overlayed.storage(&key).unwrap(), Some(&[1, 2, 3][..]));

		overlayed.commit_prospective();
		assert_eq!(overlayed.storage(&key).unwrap(), Some(&[1, 2, 3][..]));

		overlayed.set_storage(key.clone(), Some(vec![]));
		assert_eq!(overlayed.storage(&key).unwrap(), Some(&[][..]));

		overlayed.set_storage(key.clone(), None);
		assert!(overlayed.storage(&key).unwrap().is_none());

		overlayed.discard_prospective();
		assert_eq!(overlayed.storage(&key).unwrap(), Some(&[1, 2, 3][..]));

		overlayed.set_storage(key.clone(), None);
		overlayed.commit_prospective();
		assert!(overlayed.storage(&key).unwrap().is_none());
	}

	#[test]
	fn overlayed_storage_root_works() {
		let initial: BTreeMap<_, _> = vec![
			(b"doe".to_vec(), b"reindeer".to_vec()),
			(b"dog".to_vec(), b"puppyXXX".to_vec()),
			(b"dogglesworth".to_vec(), b"catXXX".to_vec()),
			(b"doug".to_vec(), b"notadog".to_vec()),
		].into_iter().collect();
		let backend = InMemory::<Blake2Hasher>::from(initial);
		let mut overlay = OverlayedChanges::new_from_top(
			vec![
				(b"dog".to_vec(), Some(b"puppy".to_vec()).into()),
				(b"dogglesworth".to_vec(), Some(b"catYYY".to_vec()).into()),
				(b"doug".to_vec(), Some(vec![]).into()),
			].into_iter().collect(),
			vec![
				(b"dogglesworth".to_vec(), Some(b"cat".to_vec()).into()),
				(b"doug".to_vec(), None.into()),
			].into_iter().collect(), None);

		let changes_trie_storage = InMemoryChangesTrieStorage::<Blake2Hasher, u64>::new();
		let mut ext = Ext::new(
			&mut overlay,
			&backend,
			Some(&changes_trie_storage),
			None,
		);
		const ROOT: [u8; 32] = hex!("39245109cef3758c2eed2ccba8d9b370a917850af3824bc8348d505df2c298fa");

		assert_eq!(&ext.storage_root()[..], &ROOT);
	}

	#[test]
	fn changes_trie_configuration_is_saved() {
		let mut overlay = OverlayedChanges::default();
		assert!(overlay.changes_trie_config.is_none());
		assert_eq!(
			overlay.set_changes_trie_config(
				ChangesTrieConfig { digest_interval: 4, digest_levels: 1, },
			),
			true,
		);
		assert!(overlay.changes_trie_config.is_some());
	}

	#[test]
	fn changes_trie_configuration_is_saved_twice() {
		let mut overlay = OverlayedChanges::default();
		assert!(overlay.changes_trie_config.is_none());
		assert_eq!(overlay.set_changes_trie_config(ChangesTrieConfig {
			digest_interval: 4, digest_levels: 1,
		}), true);
		overlay.set_extrinsic_index(0);
		overlay.set_storage(vec![1], Some(vec![2]));
		assert_eq!(overlay.set_changes_trie_config(ChangesTrieConfig {
			digest_interval: 4, digest_levels: 1,
		}), true);
		assert_eq!(
			strip_extrinsic_index(overlay.changes.top_prospective()),
			vec![
				(vec![1], OverlayedValue { value: Some(vec![2]),
				 extrinsics: Some(vec![0].into_iter().collect()) }),
			].into_iter().collect(),
		);
	}

	#[test]
	fn panics_when_trying_to_save_different_changes_trie_configuration() {
		let mut overlay = OverlayedChanges::default();
		assert_eq!(overlay.set_changes_trie_config(ChangesTrieConfig {
			digest_interval: 4, digest_levels: 1,
		}), true);
		assert_eq!(overlay.set_changes_trie_config(ChangesTrieConfig {
			digest_interval: 2, digest_levels: 1,
		}), false);
	}

	#[test]
	fn extrinsic_changes_are_collected() {
		let mut overlay = OverlayedChanges::default();
		let _ = overlay.set_changes_trie_config(ChangesTrieConfig {
			digest_interval: 4, digest_levels: 1,
		});

		overlay.set_storage(vec![100], Some(vec![101]));

		overlay.set_extrinsic_index(0);
		overlay.set_storage(vec![1], Some(vec![2]));

		overlay.set_extrinsic_index(1);
		overlay.set_storage(vec![3], Some(vec![4]));

		overlay.set_extrinsic_index(2);
		overlay.set_storage(vec![1], Some(vec![6]));

		assert_eq!(strip_extrinsic_index(overlay.changes.top_prospective()),
			vec![
				(vec![1], OverlayedValue { value: Some(vec![6]),
				 extrinsics: Some(vec![0, 2].into_iter().collect()) }),
				(vec![3], OverlayedValue { value: Some(vec![4]),
				 extrinsics: Some(vec![1].into_iter().collect()) }),
				(vec![100], OverlayedValue { value: Some(vec![101]),
				 extrinsics: Some(vec![NO_EXTRINSIC_INDEX].into_iter().collect()) }),
			].into_iter().collect());

		overlay.commit_prospective();

		overlay.set_extrinsic_index(3);
		overlay.set_storage(vec![3], Some(vec![7]));

		overlay.set_extrinsic_index(4);
		overlay.set_storage(vec![1], Some(vec![8]));

		assert_eq!(strip_extrinsic_index(overlay.changes.top_committed()),
			vec![
				(vec![1], OverlayedValue { value: Some(vec![6]),
				 extrinsics: Some(vec![0, 2].into_iter().collect()) }),
				(vec![3], OverlayedValue { value: Some(vec![4]),
				 extrinsics: Some(vec![1].into_iter().collect()) }),
				(vec![100], OverlayedValue { value: Some(vec![101]),
				 extrinsics: Some(vec![NO_EXTRINSIC_INDEX].into_iter().collect()) }),
			].into_iter().collect());

		assert_eq!(strip_extrinsic_index(overlay.changes.top_prospective()),
			vec![
				(vec![1], OverlayedValue { value: Some(vec![8]),
					extrinsics: Some(vec![0, 2, 4].into_iter().collect()) }),
				(vec![3], OverlayedValue { value: Some(vec![7]),
					extrinsics: Some(vec![1, 3].into_iter().collect()) }),
			].into_iter().collect());

		overlay.commit_prospective();

		assert_eq!(strip_extrinsic_index(overlay.changes.top_committed()),
			vec![
				(vec![1], OverlayedValue { value: Some(vec![8]),
				 extrinsics: Some(vec![0, 2, 4].into_iter().collect()) }),
				(vec![3], OverlayedValue { value: Some(vec![7]),
				 extrinsics: Some(vec![1, 3].into_iter().collect()) }),
				(vec![100], OverlayedValue { value: Some(vec![101]),
				 extrinsics: Some(vec![NO_EXTRINSIC_INDEX].into_iter().collect()) }),
			].into_iter().collect());

		assert_eq!(overlay.changes.top_prospective(),
			Default::default());
	}

	#[test]
	fn overlayed_storage_transactions() {
		let mut overlayed = OverlayedChanges::default();

		let key = vec![42, 69, 169, 142];

		assert!(overlayed.storage(&key).is_none());

		// discard transaction similar to discard prospective if no transaction.

		overlayed.set_storage(key.clone(), Some(vec![1, 2, 3]));
		assert_eq!(overlayed.storage(&key).unwrap(), Some(&[1, 2, 3][..]));

		overlayed.discard_transaction();
		assert_eq!(overlayed.storage(&key), None);

		overlayed.discard_prospective();
		assert_eq!(overlayed.storage(&key), None);

		overlayed.set_storage(key.clone(), Some(vec![1, 2, 3]));
		assert_eq!(overlayed.storage(&key).unwrap(), Some(&[1, 2, 3][..]));

		overlayed.commit_transaction();
		assert_eq!(overlayed.storage(&key).unwrap(), Some(&[1, 2, 3][..]));

		overlayed.discard_transaction();
		assert_eq!(overlayed.storage(&key), None);
		// basic transaction test
		// tx:1
		overlayed.set_storage(key.clone(), Some(vec![1, 2, 3]));
		assert_eq!(overlayed.storage(&key).unwrap(), Some(&[1, 2, 3][..]));

		overlayed.start_transaction();
		// tx:2
		overlayed.set_storage(key.clone(), Some(vec![1, 2, 3, 4]));
		assert_eq!(overlayed.storage(&key).unwrap(), Some(&[1, 2, 3, 4][..]));

		overlayed.start_transaction();
		// tx:3
		overlayed.set_storage(key.clone(), None);
		assert_eq!(overlayed.storage(&key).unwrap(), None);

		overlayed.discard_transaction();
		// tx:2
		assert_eq!(overlayed.storage(&key).unwrap(), Some(&[1, 2, 3, 4][..]));

		overlayed.start_transaction();
		// tx:3
		overlayed.set_storage(key.clone(), None);
		assert_eq!(overlayed.storage(&key).unwrap(), None);

		overlayed.commit_transaction();
		// tx:2
		assert_eq!(overlayed.storage(&key).unwrap(), None);

		overlayed.discard_transaction();
		// tx:1
		assert_eq!(overlayed.storage(&key).unwrap(), Some(&[1, 2, 3][..]));
		overlayed.discard_prospective();
		assert_eq!(overlayed.storage(&key), None);

		// multiple transaction end up to prospective value
		overlayed.start_transaction();
		overlayed.set_storage(key.clone(), Some(vec![1]));
		overlayed.start_transaction();
		overlayed.set_storage(key.clone(), Some(vec![1, 2]));
		overlayed.start_transaction();
		overlayed.set_storage(key.clone(), Some(vec![1, 2, 3]));

		overlayed.commit_prospective();
		assert_eq!(overlayed.storage(&key).unwrap(), Some(&[1, 2, 3][..]));
	}

	#[test]
	fn next_storage_key_change_works() {
		let mut overlay = OverlayedChanges::default();
		overlay.set_storage(vec![20], Some(vec![20]));
		overlay.set_storage(vec![30], Some(vec![30]));
		overlay.set_storage(vec![40], Some(vec![40]));
		overlay.commit_prospective();
		overlay.set_storage(vec![10], Some(vec![10]));
		overlay.set_storage(vec![30], None);

		// next_prospective < next_committed
		let next_to_5 = overlay.next_storage_key_change(&[5]).unwrap();
		assert_eq!(next_to_5.0.to_vec(), vec![10]);
		assert_eq!(next_to_5.1.value, Some(vec![10]));

		// next_committed < next_prospective
		let next_to_10 = overlay.next_storage_key_change(&[10]).unwrap();
		assert_eq!(next_to_10.0.to_vec(), vec![20]);
		assert_eq!(next_to_10.1.value, Some(vec![20]));

		// next_committed == next_prospective
		let next_to_20 = overlay.next_storage_key_change(&[20]).unwrap();
		assert_eq!(next_to_20.0.to_vec(), vec![30]);
		assert_eq!(next_to_20.1.value, None);

		// next_committed, no next_prospective
		let next_to_30 = overlay.next_storage_key_change(&[30]).unwrap();
		assert_eq!(next_to_30.0.to_vec(), vec![40]);
		assert_eq!(next_to_30.1.value, Some(vec![40]));

		overlay.set_storage(vec![50], Some(vec![50]));
		// next_prospective, no next_committed
		let next_to_40 = overlay.next_storage_key_change(&[40]).unwrap();
		assert_eq!(next_to_40.0.to_vec(), vec![50]);
		assert_eq!(next_to_40.1.value, Some(vec![50]));
	}

	#[test]
	fn next_child_storage_key_change_works() {
		let child = b"Child1".to_vec();
		let child_info = ChildInfo::new_default(b"uniqueid");
		let mut overlay = OverlayedChanges::default();
		overlay.set_child_storage(child.clone(), child_info, vec![20], Some(vec![20]));
		overlay.set_child_storage(child.clone(), child_info, vec![30], Some(vec![30]));
		overlay.set_child_storage(child.clone(), child_info, vec![40], Some(vec![40]));
		overlay.commit_prospective();
		overlay.set_child_storage(child.clone(), child_info, vec![10], Some(vec![10]));
		overlay.set_child_storage(child.clone(), child_info, vec![30], None);

		// next_prospective < next_committed
		let next_to_5 = overlay.next_child_storage_key_change(&child, &[5]).unwrap();
		assert_eq!(next_to_5.0.to_vec(), vec![10]);
		assert_eq!(next_to_5.1.value, Some(vec![10]));

		// next_committed < next_prospective
		let next_to_10 = overlay.next_child_storage_key_change(&child, &[10]).unwrap();
		assert_eq!(next_to_10.0.to_vec(), vec![20]);
		assert_eq!(next_to_10.1.value, Some(vec![20]));

		// next_committed == next_prospective
		let next_to_20 = overlay.next_child_storage_key_change(&child, &[20]).unwrap();
		assert_eq!(next_to_20.0.to_vec(), vec![30]);
		assert_eq!(next_to_20.1.value, None);

		// next_committed, no next_prospective
		let next_to_30 = overlay.next_child_storage_key_change(&child, &[30]).unwrap();
		assert_eq!(next_to_30.0.to_vec(), vec![40]);
		assert_eq!(next_to_30.1.value, Some(vec![40]));

		overlay.set_child_storage(child.clone(), child_info, vec![50], Some(vec![50]));
		// next_prospective, no next_committed
		let next_to_40 = overlay.next_child_storage_key_change(&child, &[40]).unwrap();
		assert_eq!(next_to_40.0.to_vec(), vec![50]);
		assert_eq!(next_to_40.1.value, Some(vec![50]));
	}
}

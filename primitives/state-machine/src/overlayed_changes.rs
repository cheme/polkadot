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

use crate::{
	backend::Backend, ChangesTrieTransaction,
	changes_trie::{
		NO_EXTRINSIC_INDEX, BlockNumber, build_changes_trie,
		State as ChangesTrieState,
	},
};

#[cfg(test)]
use std::iter::FromIterator;
use std::collections::{HashMap, BTreeMap, BTreeSet};
use codec::{Decode, Encode};
use sp_core::storage::{well_known_keys::EXTRINSIC_INDEX, OwnedChildInfo, ChildInfo};
use crate::transaction_layers::{Layers, LayerEntry, LayeredOpsResult, COMMITTED_LAYER};
use std::ops;
#[cfg(not(test))]
use std::rc::{Rc, Weak};
#[cfg(test)]
// TestExternalities need to be sync
use std::sync::{Arc as Rc, Weak};
use hash_db::Hasher;

/// The overlayed changes to state to be queried on top of the backend.
///
/// A transaction shares all prospective changes within an inner overlay
/// that can be cleared.
#[derive(Debug, Default, Clone)]
pub struct OverlayedChanges {
	/// Changes with their history.
	pub(crate) changes: OverlayedChangeSet,
	/// True if extrinsiscs stats must be collected.
	pub(crate) collect_extrinsics: bool,
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

#[derive(Debug, Clone, Default)]
#[cfg_attr(test, derive(PartialEq))]
pub struct TreeChangeSet {
	/// Mapping between key and values.
	pub(crate) map: BTreeMap<Rc<[u8]>, Layers<OverlayedValue>>,
	/// Bookkeeping of changed keys for layers (indexed
	/// by layer index).
	pub(crate) changes: Changes,
}

/// Store information on changes that occurs.
#[derive(Debug, Clone, Default)]
pub struct Changes(Vec<ChangeLayer>);

/// Store information on changes that occurs
/// for a given transaction layer.
#[derive(Debug, Clone, Default)]
pub struct ChangeLayer {
	/// All keys that where touched, being `Weak` rc pointer
	/// we can store one multiple time and not care when
	/// dropping (we always reset the value one).
	pub changes: Vec<ChangeReference>,
	/// If true all value in layer have been change so changes
	/// bookkeeping get dropped.
	pub cleared: bool,
}

impl Changes {
	fn len_from(&self, layer_index: usize) -> (bool, usize) {
		let mut cleared = false;
		let mut result = 0;
		for i in layer_index .. self.0.len() {
			if self.0[i].cleared {
				cleared = true;
				result = 0;
				break;
			}
			// we only take the max value to account for possible redundancy between layer
			// this will lead to suboptimal processing (but otherwhise we can use a single
			// value in n layer to force full scan).
			result = std::cmp::max(result, self.0[i].changes.len());
		}
		(cleared, result)
	}

	fn set_pointer(&mut self, pointer: ChangeReference, layer_index: usize) {
		for _ in self.0.len() .. layer_index + 1 {
			self.0.push(Default::default());
		}
		self.0[layer_index].changes.push(pointer);
	}

	fn set_pointers(&mut self, mut pointers: Vec<ChangeReference>, layer_index: usize) {
		for _ in self.0.len() .. layer_index + 1 {
			self.0.push(Default::default());
		}
		self.0[layer_index].changes.append(&mut pointers);
	}

	fn set_cleared(&mut self, layer_index: usize) {
		for _ in self.0.len() .. layer_index + 1 {
			self.0.push(Default::default());
		}
		self.0[layer_index].changes.clear();
		self.0[layer_index].cleared = true;
	}
}
#[cfg(test)]
impl PartialEq for Changes {
	// ignore change layer data when comparing in tests
  fn eq(&self, _other: &Changes) -> bool {
		true
	}
}
/// Reference to a change entry.
pub type ChangeReference = (Weak<()>, Weak<[u8]>);

/// Treshold for applying commit or discard operation
/// to specific key (when there is enough value changed
/// doing the operation on the whole map is more efficient).
/// First is set size, second is size factor, third is multiplicator factor,
/// fourth is divisor factor, fifth is base multiplicator, sixth is base divisor.
const APPLY_BY_KEY_TRESHOLD: (usize, usize, usize, usize, usize, usize) = (100, 10, 1, 2, 1, 4);

fn apply_selective(total_len: usize, change_len: usize) -> bool {
	if change_len >= total_len {
		return false;
	}
	let mut mult = APPLY_BY_KEY_TRESHOLD.4;
	let mut div = APPLY_BY_KEY_TRESHOLD.5;
	let mut total_len_mult = total_len;
	while APPLY_BY_KEY_TRESHOLD.0 < total_len_mult {
		total_len_mult /= APPLY_BY_KEY_TRESHOLD.1;
		mult *= APPLY_BY_KEY_TRESHOLD.2;
		div *= APPLY_BY_KEY_TRESHOLD.3;
	}
	let treshold = total_len * mult / div;
	change_len <= treshold
}

#[test]
fn test_apply_selective() {
	assert!(!apply_selective(1, 1));
	assert!(!apply_selective(1, 2));
	// quick test over bench values.
	assert!(!apply_selective(100, 50));
	assert!(!apply_selective(100, 26));
	assert!(apply_selective(100, 25));
	assert!(!apply_selective(1000, 250));
	assert!(!apply_selective(1000, 126));
	assert!(apply_selective(1000, 125));
	assert!(!apply_selective(10_000, 1_250));
	assert!(!apply_selective(10_000, 626));
	assert!(apply_selective(10_000, 625));


}

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
			number_transactions: COMMITTED_LAYER + 1,
			top: Default::default(),
			children: Default::default(),
		}
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
	pub main_storage_changes: Vec<(Vec<u8>, Option<Vec<u8>>)>,
	/// All changes to the child storages.
	pub child_storage_changes: Vec<(Vec<u8>, Vec<(Vec<u8>, Option<Vec<u8>>)>)>,
	/// A transaction for the backend that contains all changes from
	/// [`main_storage_changes`](Self::main_storage_changes) and from
	/// [`child_storage_changes`](Self::child_storage_changes).
	pub transaction: Transaction,
	/// The storage root after applying the transaction.
	pub transaction_storage_root: H::Out,
	/// Contains the transaction for the backend for the changes trie.
	///
	/// If changes trie is disabled the value is set to `None`.
	pub changes_trie_transaction: Option<ChangesTrieTransaction<H, N>>,
}

impl<Transaction, H: Hasher, N: BlockNumber> StorageChanges<Transaction, H, N> {
	/// Deconstruct into the inner values
	pub fn into_inner(self) -> (
		Vec<(Vec<u8>, Option<Vec<u8>>)>,
		Vec<(Vec<u8>, Vec<(Vec<u8>, Option<Vec<u8>>)>)>,
		Transaction,
		H::Out,
		Option<ChangesTrieTransaction<H, N>>,
	) {
		(
			self.main_storage_changes,
			self.child_storage_changes,
			self.transaction,
			self.transaction_storage_root,
			self.changes_trie_transaction,
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
	pub(crate) changes_trie_transaction: Option<Option<ChangesTrieTransaction<H, N>>>,
	/// The storage root after applying the changes trie transaction.
	pub(crate) changes_trie_transaction_storage_root: Option<Option<H::Out>>,
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
			changes_trie_transaction: None,
			changes_trie_transaction_storage_root: None,
		}
	}
}

impl<Transaction: Default, H: Hasher, N: BlockNumber> Default for StorageChanges<Transaction, H, N> {
	fn default() -> Self {
		Self {
			main_storage_changes: Default::default(),
			child_storage_changes: Default::default(),
			transaction: Default::default(),
			transaction_storage_root: Default::default(),
			changes_trie_transaction: None,
		}
	}
}

#[cfg(test)]
impl FromIterator<(Vec<u8>, OverlayedValue)> for OverlayedChangeSet {
	fn from_iter<T: IntoIterator<Item = (Vec<u8>, OverlayedValue)>>(iter: T) -> Self {
		let mut result = OverlayedChangeSet::default();
		result.top = TreeChangeSet { 
			map: iter.into_iter().map(|(k, value)| (k.into(), {
				let mut history = Layers::default();
				history.push_unchecked(LayerEntry { value, index: COMMITTED_LAYER });
				history
			})).collect(),
			changes: Default::default(),
		};
		result
	}
}

/// Variant of historical data `set` function with internal extrinsics update.
/// It avoids accessing two times the historical value item.
/// It does remove latest historical dropped items.
/// TODO remove key param and return only handle
fn set_with_extrinsic_overlayed_value(
	key: Weak<[u8]>,
	history: &mut Layers<OverlayedValue>,
	number_transaction: usize,
	value: Option<Vec<u8>>,
	extrinsic_index: Option<u32>,
) -> Option<ChangeReference> {
	if let Some(extrinsic) = extrinsic_index {
		set_with_extrinsic_inner_overlayed_value(key, history, number_transaction, value, extrinsic)
	} else {
		let handle = history.set(number_transaction, OverlayedValue {
			value,
			extrinsics: None,
		});
		Some((handle, key))
	}
}

fn set_with_extrinsic_inner_overlayed_value(
	key: Weak<[u8]>,
	history: &mut Layers<OverlayedValue>,
	number_transaction: usize,
	value: Option<Vec<u8>>,
	extrinsic_index: u32,
) -> Option<ChangeReference> {
	if let Some(current) = history.get_mut() {
		if current.index == number_transaction {
			current.value.value = value;
			current.value.extrinsics.get_or_insert_with(Default::default)
				.insert(extrinsic_index);
			Some((history.handle().expect("from same item as get_mut"), key))
		} else {
			let mut extrinsics = current.value.extrinsics.clone();
			extrinsics.get_or_insert_with(Default::default)
				.insert(extrinsic_index);
			let handle = history.push_unchecked(LayerEntry {
				index: number_transaction,
				value: OverlayedValue {
					value,
					extrinsics,
				},
			});
			Some((handle, key))
		}
	} else {
		let mut extrinsics: Option<BTreeSet<u32>> = None;
		extrinsics.get_or_insert_with(Default::default)
			.insert(extrinsic_index);
		let handle = history.push_unchecked(LayerEntry {
			index: number_transaction,
			value: OverlayedValue {
				value,
				extrinsics,
			},
		});
		Some((handle, key))
	}
}

impl OverlayedChangeSet {
	/// Whether the change set is empty.
	pub fn is_empty(&self) -> bool {
		self.top.map.is_empty() && self.children.is_empty()
	}

	/// Discard prospective changes from the change set.
	pub fn discard_prospective(&mut self) {
		retain_treshold(
			&mut self.top,
			None,
			COMMITTED_LAYER + 1,
			|_, history| history.discard_prospective() != LayeredOpsResult::Cleared,
		);
		self.children.retain(|_, (map, _child_info)| {
			retain_treshold(
				map,
				None,
				COMMITTED_LAYER + 1,
				|_, history| history.discard_prospective() != LayeredOpsResult::Cleared,
			);
			!map.map.is_empty()
		});
		self.number_transactions = 1;
	}

	/// Commit prospective changes into the change set.
	pub fn commit_prospective(&mut self) {
		retain_treshold(
			&mut self.top,
			None,
			COMMITTED_LAYER + 1,
			|_, history| history.commit_prospective() != LayeredOpsResult::Cleared,
		);
		self.children.retain(|_, (map, _child_info)| {
			retain_treshold(
				map,
				None,
				COMMITTED_LAYER + 1,
				|_, history| history.commit_prospective() != LayeredOpsResult::Cleared,
			);
			!map.map.is_empty()
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
		let treshold_transactions = self.number_transactions;
		self.number_transactions = self.number_transactions.saturating_sub(1);
		let number_transactions = self.number_transactions;
		retain_treshold(
			&mut self.top,
			None,
			treshold_transactions,
			|_, history| history.discard_transaction(number_transactions) != LayeredOpsResult::Cleared,
		);
		self.children.retain(|_, (map, _child_info)| {
			retain_treshold(
				map,
				None,
				treshold_transactions,
				|_, history| history.discard_transaction(number_transactions) != LayeredOpsResult::Cleared,
			);
			!map.map.is_empty()
		});
		if number_transactions == COMMITTED_LAYER {
			// start new transaction
			self.start_transaction();
		} else {
			self.number_transactions = number_transactions;
		}
	}

	/// Commit a transactional layer into previous transaction layer.
	pub fn commit_transaction(&mut self) {
		if self.number_transactions == COMMITTED_LAYER + 1 {
			// do nothing
			return;
		}
		let treshold_transactions = self.number_transactions;
		self.number_transactions = self.number_transactions.saturating_sub(1);
		let number_transactions = self.number_transactions;
		let len_from = self.top.changes.len_from(treshold_transactions);
		let mut changed = Vec::with_capacity(len_from.1);
		retain_treshold(
			&mut self.top,
			Some(len_from),
			treshold_transactions,
			|key, history| {
				match history.commit_transaction(number_transactions) {
					LayeredOpsResult::Changed => {
						changed.push((
							history.handle().expect("would be cleared if empty"),
							Rc::downgrade(key),
						));
						true
					},
					LayeredOpsResult::Unchanged => true,
					LayeredOpsResult::Cleared => false,
				}
			},
		);
		self.top.changes.set_pointers(changed, number_transactions);
		self.children.retain(|_, (map, _child_info)| {
			let len_from = map.changes.len_from(treshold_transactions);
			let mut changed = Vec::with_capacity(len_from.1);
			retain_treshold(
				map,
				Some(len_from),
				treshold_transactions,
				|key, history| {
					match history.commit_transaction(number_transactions) {
						LayeredOpsResult::Changed => {
							changed.push((
								history.handle().expect("would be cleared if empty"),
								Rc::downgrade(key),
							));
							true
						},
						LayeredOpsResult::Unchanged => true,
						LayeredOpsResult::Cleared => false,
					}
				},
			);
			map.changes.set_pointers(changed, number_transactions);
			!map.map.is_empty()
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
			.flat_map(move |map| map.map.iter()
				.filter_map(move |(k, v)|
					v.get().map(|v| (k.as_ref(), v)))
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
				child_content.0.map.iter()
					.filter_map(move |(k, v)| v.get().map(|v| (
						k.as_ref(),
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
				map.map.iter()
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
				map.map.iter()
					.filter_map(move |(k, v)|
						v.get().map(|v| (k.as_ref(), v))),
				child_info.as_ref(),
			))
	}

	/// Test only method for accessing current prospective values.
	/// This method is only here to keep compatibility with previous tests,
	/// please do not use for new tests.
	#[cfg(test)]
	pub(crate) fn top_prospective(&self) -> BTreeMap<Vec<u8>, OverlayedValue> {
		let mut result = BTreeMap::new();
		for (k, v) in self.top.map.iter() {
			if let Some(v) = v.get_prospective() {
				result.insert(k.to_vec(), v.clone());
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
		for (k, v) in self.top.map.iter() {
			if let Some(v) = v.get_committed() {
				result.insert(k.to_vec(), v.clone());
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

	/// Ask to collect/not to collect extrinsics indices where key(s) has been changed.
	pub fn set_collect_extrinsics(&mut self, collect_extrinsics: bool) {
		self.collect_extrinsics = collect_extrinsics;
	}

	/// Returns a double-Option: None if the key is unknown (i.e. and the query should be referred
	/// to the backend); Some(None) if the key has been deleted. Some(Some(...)) for a key whose
	/// value has been set.
	pub fn storage(&self, key: &[u8]) -> Option<Option<&[u8]>> {
		if let Some(overlay_value) = self.changes.top.map.get(key) {
			if let Some(o_value) = overlay_value.get() {
				return Some(o_value.value.as_ref().map(|v| v.as_slice()))
			}
		}
		None
	}

	/// Returns a double-Option: None if the key is unknown (i.e. and the query should be referred
	/// to the backend); Some(None) if the key has been deleted. Some(Some(...)) for a key whose
	/// value has been set.
	pub fn child_storage(&self, storage_key: &[u8], key: &[u8]) -> Option<Option<&[u8]>> {
		if let Some(map) = self.changes.children.get(storage_key) {
			if let Some(overlay_value) = map.0.map.get(key) {
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
		let key: Rc<[u8]> = key.into();
		let entry = self.changes.top.map.entry(key);
		let number_transactions =	self.changes.number_transactions;
		if let Some(pointer) = set_with_extrinsic_overlayed_value(
			Rc::downgrade(entry.key()),
			entry.or_default(),
			number_transactions,
			value,
			extrinsic_index,
		) {
			self.changes.top.changes.set_pointer(pointer, number_transactions);
		};
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
		let key: Rc<[u8]> = key.into();
		let map_entry = self.changes.children.entry(storage_key)
			.or_insert_with(|| (Default::default(), child_info.to_owned()));
		let updatable = map_entry.1.try_update(child_info);
		debug_assert!(updatable);

		let number_transactions =	self.changes.number_transactions;
		let entry = map_entry.0.map.entry(key);
		if let Some(pointer) = set_with_extrinsic_overlayed_value(
			Rc::downgrade(entry.key()),
			entry.or_default(),
			number_transactions,
			value,
			extrinsic_index,
		) {
			map_entry.0.changes.set_pointer(pointer, number_transactions);
		};
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
		let number_transactions = self.changes.number_transactions;
		let map_entry = self.changes.children.entry(storage_key.to_vec())
			.or_insert_with(|| (Default::default(), child_info.to_owned()));
		let updatable = map_entry.1.try_update(child_info);
		debug_assert!(updatable);

		map_entry.0.map.iter_mut()
			.for_each(|e| {
				set_with_extrinsic_overlayed_value(Rc::downgrade(e.0), e.1, number_transactions, None, extrinsic_index);
			});
		map_entry.0.changes.set_cleared(number_transactions);
	}

	/// Removes all key-value pairs which keys share the given prefix.
	///
	/// NOTE that this doesn't take place immediately but written into the prospective
	/// change set, and still can be reverted by [`discard_prospective`].
	///
	/// [`discard_prospective`]: #method.discard_prospective
	pub(crate) fn clear_prefix(&mut self, prefix: &[u8]) {
		let extrinsic_index = self.extrinsic_index();

		let number_transactions = self.changes.number_transactions;
		for (key, entry) in self.changes.top.map.iter_mut() {
			if key.starts_with(prefix) {
				if let Some(pointer) = set_with_extrinsic_overlayed_value(
					Rc::downgrade(key),
					entry,
					number_transactions,
					None,
					extrinsic_index,
				) {
					self.changes.top.changes.set_pointer(pointer, number_transactions);
				}
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
		let number_transactions = self.changes.number_transactions;
		if let Some(child_change) = self.changes.children.get_mut(storage_key) {
			let updatable = child_change.1.try_update(child_info);
			debug_assert!(updatable);

			for (key, entry) in child_change.0.map.iter_mut() {
				if key.starts_with(prefix) {
					if let Some(pointer) = set_with_extrinsic_overlayed_value(
						Rc::downgrade(key),
						entry, 
						number_transactions,
						None,
						extrinsic_index,
					) {
						child_change.0.changes.set_pointer(pointer, number_transactions);
					}
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
			top.map.into_iter()
				.filter_map(move |(k, v)| v.into_committed()
					.map(|v| (k.as_ref().to_vec(), v.value))),
			children.into_iter().map(move |(storage_key, child_content)| (
				storage_key,
				child_content.0.map.into_iter()
					.filter_map(move |(k, v)| v.into_committed()
						.map(|v| (k.as_ref().to_vec(), v.value))),
				child_content.1.to_owned(),
			))
		)
	}

	/// Convert this instance with all changes into a [`StorageChanges`] instance.
	pub fn into_storage_changes<
		B: Backend<H>, H: Hasher, N: BlockNumber
	>(
		self,
		backend: &B,
		changes_trie_state: Option<&ChangesTrieState<H, N>>,
		parent_hash: H::Out,
		mut cache: StorageTransactionCache<B::Transaction, H, N>,
	) -> Result<StorageChanges<B::Transaction, H, N>, String>
	where
		H::Out: Ord + Encode + 'static,
	{
		// If the transaction does not exist, we generate it.
		if cache.transaction.is_none() {
			self.storage_root(backend, &mut cache);
		}

		let (transaction, transaction_storage_root) = cache.transaction.take()
			.and_then(|t| cache.transaction_storage_root.take().map(|tr| (t, tr)))
			.expect("Transaction was be generated as part of `storage_root`; qed");

		// If the transaction does not exist, we generate it.
		if cache.changes_trie_transaction.is_none() {
			self.changes_trie_root(
				backend,
				changes_trie_state,
				parent_hash,
				false,
				&mut cache,
			).map_err(|_| "Failed to generate changes trie transaction")?;
		}

		let changes_trie_transaction = cache.changes_trie_transaction
			.take()
			.expect("Changes trie transaction was generated by `changes_trie_root`; qed");

		let (main_storage_changes, child_storage_changes) = self.into_committed();

		Ok(StorageChanges {
			main_storage_changes: main_storage_changes.collect(),
			child_storage_changes: child_storage_changes.map(|(sk, it, _child_info)|
				(sk, it.collect())
			).collect(),
			transaction,
			transaction_storage_root,
			changes_trie_transaction,
		})
	}

	/// Inserts storage entry responsible for current extrinsic index.
	#[cfg(test)]
	pub(crate) fn set_extrinsic_index(&mut self, extrinsic_index: u32) {
		self.set_storage(EXTRINSIC_INDEX.to_vec(), Some(extrinsic_index.encode()));
	}

	/// Test only method to create a change set from committed
	/// and prospective content.
	#[cfg(test)]
	pub(crate) fn new_from_top(
		committed: Vec<(Vec<u8>, Option<Vec<u8>>)>,
		prospective: Vec<(Vec<u8>, Option<Vec<u8>>)>,
		collect_extrinsics: bool,
	) -> Self {
		let changes = OverlayedChangeSet::default();
		let mut result = OverlayedChanges {
			changes,
			collect_extrinsics,
		};
		committed.into_iter().for_each(|(k, v)| result.set_storage(k, v));
		result.changes.commit_prospective();
		prospective.into_iter().for_each(|(k, v)| result.set_storage(k, v));
		result
	}

	/// Returns current extrinsic index to use in changes trie construction.
	/// None is returned if it is not set or changes trie config is not set.
	/// Persistent value (from the backend) can be ignored because runtime must
	/// set this index before first and unset after last extrinsic is executed.
	/// Changes that are made outside of extrinsics, are marked with
	/// `NO_EXTRINSIC_INDEX` index.
	fn extrinsic_index(&self) -> Option<u32> {
		match self.collect_extrinsics {
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
		for (_, v) in self.changes.top.map.iter() {
			result += v.len()
		}
		result
	}

	/// Generate the storage root using `backend` and all changes from `prospective` and `committed`.
	///
	/// Returns the storage root and caches storage transaction in the given `cache`.
	pub fn storage_root<H: Hasher, N: BlockNumber, B: Backend<H>>(
		&self,
		backend: &B,
		cache: &mut StorageTransactionCache<B::Transaction, H, N>,
	) -> H::Out
		where
			H::Out: Ord + Encode,
	{
		let child_delta_iter = self.changes.owned_children_iter();

		// compute and memoize
		let delta = self.changes.iter_values(None).map(|(k, v)| (k.to_vec(), v.map(|s| s.to_vec())));

		let (root, transaction) = backend.full_storage_root(delta, child_delta_iter);
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
	pub fn changes_trie_root<'a, H: Hasher, N: BlockNumber, B: Backend<H>>(
		&self,
		backend: &B,
		changes_trie_state: Option<&'a ChangesTrieState<'a, H, N>>,
		parent_hash: H::Out,
		panic_on_storage_error: bool,
		cache: &mut StorageTransactionCache<B::Transaction, H, N>,
	) -> Result<Option<H::Out>, ()>
		where
			H::Out: Ord + Encode + 'static,
	{
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

		let mut next_keys = self.changes.top.map.range::<[u8], _>(range);
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
			let mut next_keys = child.0.map.range::<[u8], _>(range);
			while let Some((key, historic_value)) = next_keys.next() {
				if let Some(overlay_value) = historic_value.get() {
					return Some((key, overlay_value));
				}
			}
		}
		None
	}
}

fn retain_treshold(
	change: &mut TreeChangeSet,
	len_from: Option<(bool, usize)>,
	from: usize,
	mut f: impl FnMut(&Rc<[u8]>, &mut Layers<OverlayedValue>) -> bool,
) {
	let (cleared, len_from) = if let Some(param) = len_from {
		(param.0, param.1)
	} else {
		change.changes.len_from(from)
	};
	if !cleared && len_from == 0 {
		change.changes.0.truncate(from);
	}
	if !cleared && apply_selective(change.map.len(), len_from) {
		for layer in from .. change.changes.0.len() {
			for (pointer, weak_key) in change.changes.0[layer].changes.drain(..) {
				if pointer.upgrade().is_some() {
					let key = weak_key.upgrade().expect("Key is in a parent container of pointer");
					if let Some(value) = change.map.get_mut(&key) {
						if !f(&key, value) {
							change.map.remove(&key);
						}
					}
				}
			}
		}
	} else {
		retain(&mut change.map, f);
	}
	change.changes.0.truncate(from);
}

/// This is an implementation of retain for btreemap,
/// this is used to keep a similar api with previous
/// hashmap usage.
/// This could also be easilly replace if btreemap gets
/// an implementation for retain in the future.
fn retain<K: Ord + Clone, V, F>(map: &mut BTreeMap<K, V>, mut f: F)
	where
		F: FnMut(&K, &mut V) -> bool,
{
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
	use crate::InMemoryBackend;
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
		let backend = InMemoryBackend::<Blake2Hasher>::from(initial);
		let mut overlay = OverlayedChanges::new_from_top(
			vec![
				(b"dog".to_vec(), Some(b"puppy".to_vec()).into()),
				(b"dogglesworth".to_vec(), Some(b"catYYY".to_vec()).into()),
				(b"doug".to_vec(), Some(vec![]).into()),
			].into_iter().collect(),
			vec![
				(b"dogglesworth".to_vec(), Some(b"cat".to_vec()).into()),
				(b"doug".to_vec(), None.into()),
			].into_iter().collect(), false);

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

// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

#[cfg(test)] use std::iter::FromIterator;
use std::collections::{HashMap, BTreeSet};
use codec::Decode;
use crate::changes_trie::{NO_EXTRINSIC_INDEX, Configuration as ChangesTrieConfig};
use primitives::storage::well_known_keys::EXTRINSIC_INDEX;
use primitives::child_trie::{KeySpace, ChildTrie, ChildTrieReadRef};

/// The overlayed changes to state to be queried on top of the backend.
///
/// A transaction shares all prospective changes within an inner overlay
/// that can be cleared.
#[derive(Debug, Default, Clone)]
pub struct OverlayedChanges {
	/// Changes that are not yet committed.
	pub(crate) prospective: OverlayedChangeSet,
	/// Committed changes.
	pub(crate) committed: OverlayedChangeSet,
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

/// All changes related to a child trie.
#[derive(Debug, Clone)]
#[cfg_attr(test, derive(PartialEq))]
pub struct ChildOverlayChangeSet {
	/// Currently change trie are not manage for child trie value
	/// and we only keep trace of extrinsic index globally.
	pub extrinsics: Option<BTreeSet<u32>>,
	/// Mapping of key with optional value, if value is `None` that is a removal.
	pub values: HashMap<Vec<u8>, Option<Vec<u8>>>,
	/// Child trie value.
	pub child_trie: ChildTrie,
	/// Status for child.
	pub status: ChildStatus,
}

/// Child status.
#[derive(Debug, Copy, Clone, PartialEq)]
pub enum ChildStatus {
	/// keyspace dropped and node to be removed.
	Deleted,
	/// Keyspace deleted, but node is updated to
	/// a new keyspace. Node will be updated
	/// unless it has no content and no extension
	/// content.
	KeySpaceOnly,
	/// Nothing to do, node will only need
	/// update if some content has been
	/// set (change of root).
	Untouched,
}

/// Prospective or committed overlayed change set.
#[derive(Debug, Default, Clone)]
#[cfg_attr(test, derive(PartialEq))]
pub struct OverlayedChangeSet {
	/// Top level storage changes.
	pub top: HashMap<Vec<u8>, OverlayedValue>,
	/// Child storage changes.
	pub children: HashMap<KeySpace, ChildOverlayChangeSet>,
	/// Association from parent storage location to keyspace.
	pub pending_child: HashMap<Vec<u8>, KeySpace>,
	/// Keyspace marked for deletion (deletion of a full child).
	/// No attached logic on the keyspace (checking for child deletion
	/// is pending child purpose).
	pub keyspace_to_delete: BTreeSet<KeySpace>,
}

#[cfg(test)]
impl FromIterator<(Vec<u8>, OverlayedValue)> for OverlayedChangeSet {
	fn from_iter<T: IntoIterator<Item = (Vec<u8>, OverlayedValue)>>(iter: T) -> Self {
		Self {
			top: iter.into_iter().collect(),
			children: Default::default(),
			pending_child: Default::default(),
			keyspace_to_delete: Default::default(),
		}
	}
}

impl OverlayedChangeSet {
	/// Whether the change set is empty.
	pub fn is_empty(&self) -> bool {
		self.top.is_empty()
			&& self.children.is_empty()
	}

	/// Clear the change set.
	pub fn clear(&mut self) {
		self.top.clear();
		self.children.clear();
		self.pending_child.clear();
	}
}

#[derive(Debug, Clone)]
#[cfg_attr(test, derive(PartialEq))]
/// Possible result from value
/// query in the overlay.
pub enum OverlayedValueResult<'a> {
	/// The key is unknown (i.e. and the query should be refered
	/// to the backend)
	NotFound,
	/// The key has been deleted.
	Deleted,
	/// Current value set in the overlay.
	Modified(&'a[u8]),
}

impl OverlayedChanges {
	/// Whether the overlayed changes are empty.
	pub fn is_empty(&self) -> bool {
		self.prospective.is_empty()
			&& self.committed.is_empty()
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

	/// Get the `OverlayedValueResult` for a given key.
	pub fn storage(&self, key: &[u8]) -> OverlayedValueResult {
		match self.prospective.top.get(key).or_else(|| self.committed.top.get(key)) {
			Some(OverlayedValue { value: Some(val), .. }) => OverlayedValueResult::Modified(val.as_ref()),
			Some(OverlayedValue { value: None, .. }) => OverlayedValueResult::Deleted,
			None => OverlayedValueResult::NotFound,
		}
	}

	/// Get the `OverlayedValueResult` for a given child key.
	pub fn child_storage(&self, child_trie: ChildTrieReadRef, key: &[u8]) -> OverlayedValueResult {
		let keyspace = child_trie.keyspace();

		let mut former_keyspace_deleted = false;
		match self.prospective.children.get(keyspace).and_then(|map| {
			match map.status {
				ChildStatus::Deleted
				| ChildStatus::KeySpaceOnly => {
					former_keyspace_deleted = true;
					None
				},
				ChildStatus::Untouched => map.values.get(key),
			}
		}) {
			Some(Some(val)) =>
				return OverlayedValueResult::Modified(val.as_ref()),
			Some(None) =>
				return OverlayedValueResult::Deleted,
			None => (),
		}

		if former_keyspace_deleted {
			return OverlayedValueResult::Deleted;
		}

		match self.committed.children.get(keyspace).and_then(|map| {
			match map.status {
				ChildStatus::Deleted
				| ChildStatus::KeySpaceOnly => {
					former_keyspace_deleted = true;
					None
				},
				ChildStatus::Untouched => map.values.get(key),
			}
		}) {
			Some(Some(val)) =>
				return OverlayedValueResult::Modified(val.as_ref()),
			Some(None) =>
				return OverlayedValueResult::Deleted,
			None => (),
		}

		if former_keyspace_deleted {
			return OverlayedValueResult::Deleted;
		} else {
			return OverlayedValueResult::NotFound;
		}

	}

	/// returns a child trie if present
	pub fn child_trie(&self, storage_key: &[u8]) -> Option<Option<ChildTrie>> {
		// no check for keyspace to delete as the child trie keyspace if child trie
		// is still here shall be updated.
		match self.prospective.pending_child.get(storage_key) {
			Some(keyspace) => {
				let map = self.prospective.children.get(keyspace)
					.expect("pending entry always have a children association; qed");
				if map.status == ChildStatus::Deleted {
					return Some(None);
				} else {
					return Some(Some(map.child_trie.clone()));
				}
			},
			None => (),
		}

		match self.committed.pending_child.get(storage_key) {
			Some(keyspace) => {
				let map = self.committed.children.get(keyspace)
					.expect("pending entry always have a children association; qed");
				if map.status == ChildStatus::Deleted {
					return Some(None);
				} else {
					return Some(Some(map.child_trie.clone()));
				}
			},
			None => (),
		}

		None
	}

	/// Inserts the given key-value pair into the prospective change set.
	///
	/// `None` can be used to delete a value specified by the given key.
	pub(crate) fn set_storage(&mut self, key: Vec<u8>, val: Option<Vec<u8>>) {
		let extrinsic_index = self.extrinsic_index();
		let entry = self.prospective.top.entry(key).or_default();
		entry.value = val;

		if let Some(extrinsic) = extrinsic_index {
			entry.extrinsics.get_or_insert_with(Default::default)
				.insert(extrinsic);
		}
	}

	/// Inserts the given key-value pair into the prospective child change set.
	///
	/// `None` can be used to delete a value specified by the given key.
	pub(crate) fn set_child_storage(&mut self, child_trie: &ChildTrie, key: Vec<u8>, val: Option<Vec<u8>>) {
		// Note that we do not check keyspace_to_delete and using a cloned child trie can lead
		// to recreate an child trie that was delete. User shall therefore be attentive to not
		// use cloned trie (except for technical reason).
		let extrinsic_index = self.extrinsic_index();
		let p = &mut self.prospective.children;
		let pc = &mut self.prospective.pending_child;
		let map_entry = p.entry(child_trie.keyspace().clone())
			.or_insert_with(|| {
				let parent = child_trie.parent_slice().to_vec();
				pc.insert(parent, child_trie.keyspace().clone());
				ChildOverlayChangeSet {
					extrinsics: None,
					values: Default::default(),
					child_trie: child_trie.clone(),
					status: ChildStatus::Untouched,
				}
			});
		// if deleted then we used a child trie with incorrect keyspace
		// so code is incorrect.
		debug_assert!(map_entry.status == ChildStatus::Untouched);

		map_entry.values.insert(key, val);
		if let Some(extrinsic) = extrinsic_index {
			map_entry.extrinsics.get_or_insert_with(Default::default)
				.insert(extrinsic);
		}
	}

	/// Try to update child trie. Some changes are not allowed:
	/// - keyspace
	/// - root
	/// - parent path
	pub(crate) fn set_child_trie(&mut self, child_trie: ChildTrie) -> bool {
		let extrinsic_index = self.extrinsic_index();

		if let Some(old_ct) = self.prospective.pending_child
			.get(child_trie.parent_slice()) {
			let old_ct = self.prospective.children.get_mut(old_ct)
				.expect("pending entry always have a children association; qed");
			let exts = &mut old_ct.extrinsics;
			let status = old_ct.status;
			let old_ct = &mut old_ct.child_trie;
			if old_ct.is_updatable_with(&child_trie) && status == ChildStatus::Untouched {
				*old_ct = child_trie;
				if let Some(extrinsic) = extrinsic_index {
					exts.get_or_insert_with(Default::default)
						.insert(extrinsic);
				}
			} else {
				return false;
			}
		} else {
			let mut exts = if let Some(old_ct) = self.committed.pending_child
				.get(child_trie.parent_slice()).and_then(|k| self.committed.children.get(k)) {
				if old_ct.child_trie.is_updatable_with(&child_trie)
					&& old_ct.status == ChildStatus::Untouched {
					old_ct.extrinsics.clone()
				} else {
					return false;
				}
			} else { Default::default() };
			self.prospective.pending_child
				.insert(child_trie.parent_slice().to_vec(), child_trie.keyspace().clone());
			if let Some(extrinsic) = extrinsic_index {
				exts.get_or_insert_with(Default::default)
					.insert(extrinsic);
			}
			self.prospective.children.insert(
				child_trie.keyspace().to_vec(),
				ChildOverlayChangeSet {
					extrinsics: exts,
					values: Default::default(),
					child_trie: child_trie.clone(),
					status: ChildStatus::Untouched,
				}
			);
		}
		true
	}

	/// Clear child storage of given storage key.
	/// This is a global operation over a full keyspace.
	/// We can still keep the child trie info but with a new keyspace.
	///
	/// NOTE that this doesn't take place immediately but written into the prospective
	/// change set, and still can be reverted by [`discard_prospective`].
	///
	/// [`discard_prospective`]: #method.discard_prospective
	pub(crate) fn kill_child_storage(
		&mut self,
		child_trie: ChildTrie,
		keep_trie: Option<KeySpace>,
	) -> (Option<ChildTrie>, bool) {
		let extrinsic_index = self.extrinsic_index();

		if let Some(new_keyspace) = keep_trie {
			let keyspace_to_delete = &mut self.prospective.keyspace_to_delete;
			let committed_children = &self.committed.children;
			if let Some(ct) = self.prospective.children.get(child_trie.keyspace())
				.or_else(|| committed_children.get(child_trie.keyspace())) {
				let old_is_new = ct.child_trie.is_new();
				let (old_ks, new_ct) = ct.child_trie.clone().remove_or_replace_keyspace(Some(new_keyspace));

				if !old_is_new {
					old_ks.map(|ks| keyspace_to_delete.insert(ks));
				}
				let new_ct = new_ct.expect("a new keyspace in parameter");
				let extrinsics = if let Some(extrinsic) = extrinsic_index {
					let mut extrinsics = ct.extrinsics.clone();
					extrinsics.get_or_insert_with(Default::default)
						.insert(extrinsic);
					extrinsics
				} else { None };
	
				// only usefull if ct is from committed
				self.prospective.pending_child.insert(new_ct.parent_slice().to_vec(), new_ct.keyspace().clone());
				self.prospective.children.insert(new_ct.keyspace().clone(), ChildOverlayChangeSet {
					child_trie: new_ct.clone(),
					values: Default::default(),
					extrinsics,
					status: ChildStatus::KeySpaceOnly,
				});
				return (Some(new_ct), false);
			} else {
				// no such child trie in overlay
				// still need to drop keyspace and update keyspace from
				// a possible backend: returning true in second result.
				return (None, true);
			}
		}

		// not keeping trie node
		self.prospective.pending_child.remove(child_trie.parent_slice());

		let clear_child = |v: &mut ChildOverlayChangeSet, k_to_delete: &mut BTreeSet<Vec<u8>>| {
			v.status = ChildStatus::Deleted;
			v.values.clear();
			if let Some(extrinsic) = extrinsic_index {
				v.extrinsics.get_or_insert_with(Default::default).insert(extrinsic);
			}
			let (old_ks, new_ct) = v.child_trie.clone().remove_or_replace_keyspace(None);
			debug_assert!(new_ct.is_none());
			if !v.child_trie.is_new() {
				old_ks.map(|ks| k_to_delete.insert(ks));
			}
		};
		if let Some(v) = self.prospective.children.get_mut(child_trie.keyspace()) {
			clear_child(v, &mut self.prospective.keyspace_to_delete);
		} else if let Some(v) = self.committed.children.get(child_trie.keyspace()) {
			let mut v = v.clone();
			clear_child(&mut v, &mut self.prospective.keyspace_to_delete);
			self.prospective.pending_child.insert(
				v.child_trie.parent_slice().to_vec(),
				v.child_trie.keyspace().clone(),
			);
			self.prospective.children.insert(v.child_trie.keyspace().clone(), v);
		} else {
			// no such child trie in overlay
			// still need to drop keyspace and update keyspace from
			// a possible backend: returning true in second result.
			return (None, true);
		}
		(None, false)
	}

	/// Removes all key-value pairs which keys share the given prefix.
	///
	/// NOTE that this doesn't take place immediately but written into the prospective
	/// change set, and still can be reverted by [`discard_prospective`].
	///
	/// [`discard_prospective`]: #method.discard_prospective
	pub(crate) fn clear_prefix(&mut self, prefix: &[u8]) {
		let extrinsic_index = self.extrinsic_index();

		// Iterate over all prospective and mark all keys that share
		// the given prefix as removed (None).
		for (key, entry) in self.prospective.top.iter_mut() {
			if key.starts_with(prefix) {
				entry.value = None;

				if let Some(extrinsic) = extrinsic_index {
					entry.extrinsics.get_or_insert_with(Default::default)
						.insert(extrinsic);
				}
			}
		}

		// Then do the same with keys from commited changes.
		// NOTE that we are making changes in the prospective change set.
		for key in self.committed.top.keys() {
			if key.starts_with(prefix) {
				let entry = self.prospective.top.entry(key.clone()).or_default();
				entry.value = None;

				if let Some(extrinsic) = extrinsic_index {
					entry.extrinsics.get_or_insert_with(Default::default)
						.insert(extrinsic);
				}
			}
		}
	}

	pub(crate) fn clear_child_prefix(&mut self, child_trie: &ChildTrie, prefix: &[u8]) {
		let extrinsic_index = self.extrinsic_index();
		let map_entry = self.prospective.children.entry(child_trie.keyspace().clone())
			.or_insert_with(|| ChildOverlayChangeSet {
				extrinsics: None,
				values: Default::default(),
				child_trie: child_trie.clone(),
				status: ChildStatus::Untouched,
			});

		for (key, entry) in map_entry.values.iter_mut() {
			if key.starts_with(prefix) {
				*entry = None;

				if let Some(extrinsic) = extrinsic_index {
					map_entry.extrinsics.get_or_insert_with(Default::default)
						.insert(extrinsic);
				}
			}
		}

		if let Some(child_committed) = self.committed.children.get(child_trie.keyspace()) {
			// Then do the same with keys from commited changes.
			// NOTE that we are making changes in the prospective change set.
			for key in child_committed.values.keys() {
				if key.starts_with(prefix) {
					let entry = map_entry.values.entry(key.clone()).or_default();
					*entry = None;

					if let Some(extrinsic) = extrinsic_index {
						map_entry.extrinsics.get_or_insert_with(Default::default)
							.insert(extrinsic);
					}
				}
			}
		}
	}

	/// Discard prospective changes to state.
	pub fn discard_prospective(&mut self) {
		self.prospective.clear();
	}

	/// Commit prospective changes to state.
	pub fn commit_prospective(&mut self) {
		if self.committed.is_empty() {
			::std::mem::swap(&mut self.prospective, &mut self.committed);
		} else {
			for (key, val) in self.prospective.top.drain() {
				let entry = self.committed.top.entry(key).or_default();
				entry.value = val.value;

				if let Some(prospective_extrinsics) = val.extrinsics {
					entry.extrinsics.get_or_insert_with(Default::default)
						.extend(prospective_extrinsics);
				}
			}
			for (storage_key, ChildOverlayChangeSet {extrinsics, values, child_trie, status})
				in self.prospective.children.drain() {
				let entry = self.committed.children.entry(storage_key)
					.or_insert_with(|| ChildOverlayChangeSet {
						extrinsics: None,
						values: Default::default(),
						child_trie: child_trie.clone(),
						status: ChildStatus::Untouched,
					});

				match status {
					ChildStatus::KeySpaceOnly => {
						entry.values.clear();
						entry.values.extend(values.iter().map(|(k, v)| (k.clone(), v.clone())));
						entry.status = ChildStatus::Untouched; // no need to know keyspace deleted here
						debug_assert!(entry.child_trie.keyspace() != child_trie.keyspace());
					},
					ChildStatus::Deleted => {
						entry.values.clear();
						entry.status = ChildStatus::Deleted;
					},
					ChildStatus::Untouched => {
						entry.values.extend(values.iter().map(|(k, v)| (k.clone(), v.clone())));
						entry.status = ChildStatus::Untouched;
					}
				}
				entry.child_trie = child_trie;

				if let Some(prospective_extrinsics) = extrinsics {
					entry.extrinsics.get_or_insert_with(Default::default)
						.extend(prospective_extrinsics);
				}
			}
			self.committed.pending_child.extend(self.prospective.pending_child.drain());
			let p_keyspace_to_delete = ::std::mem::replace(&mut self.prospective.keyspace_to_delete, BTreeSet::new());
			self.committed.keyspace_to_delete.extend(p_keyspace_to_delete.into_iter());
		}
	}

	/// Consume `OverlayedChanges` and take committed set.
	///
	/// Panics:
	/// Will panic if there are any uncommitted prospective changes.
	pub fn into_committed(self) -> (
		impl Iterator<Item=(Vec<u8>, Option<Vec<u8>>)>,
		impl Iterator<Item=(Vec<u8>, impl Iterator<Item=(Vec<u8>, Option<Vec<u8>>)>)>,
		impl Iterator<Item=Vec<u8>>,
	){
		assert!(self.prospective.is_empty());
		(
			self.committed.top.into_iter().map(|(k, v)| (k, v.value)),
			self.committed.children.into_iter().map(|(sk, v)| (sk, v.values.into_iter())),
			self.committed.keyspace_to_delete.into_iter(),
		)
	}

	/// Inserts storage entry responsible for current extrinsic index.
	#[cfg(test)]
	pub(crate) fn set_extrinsic_index(&mut self, extrinsic_index: u32) {
		use codec::Encode;
		self.prospective.top.insert(EXTRINSIC_INDEX.to_vec(), OverlayedValue {
			value: Some(extrinsic_index.encode()),
			extrinsics: None,
		});
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
				match self.storage(EXTRINSIC_INDEX) {
					OverlayedValueResult::Modified(idx) => Decode::decode(&mut &*idx)
						.unwrap_or(NO_EXTRINSIC_INDEX),
					OverlayedValueResult::Deleted
					| OverlayedValueResult::NotFound => NO_EXTRINSIC_INDEX,
				}
			),
			false => None,
		}
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
	use primitives::{Blake2Hasher, H256};
	use primitives::storage::well_known_keys::EXTRINSIC_INDEX;
	use crate::backend::InMemory;
	use crate::changes_trie::InMemoryStorage as InMemoryChangesTrieStorage;
	use crate::ext::Ext;
	use crate::Externalities;
	use super::*;

	fn strip_extrinsic_index(map: &HashMap<Vec<u8>, OverlayedValue>) -> HashMap<Vec<u8>, OverlayedValue> {
		let mut clone = map.clone();
		clone.remove(&EXTRINSIC_INDEX.to_vec());
		clone
	}

	#[test]
	fn overlayed_storage_works() {
		let mut overlayed = OverlayedChanges::default();

		let key = vec![42, 69, 169, 142];

		assert_eq!(overlayed.storage(&key), OverlayedValueResult::NotFound);

		overlayed.set_storage(key.clone(), Some(vec![1, 2, 3]));
		assert_eq!(overlayed.storage(&key), OverlayedValueResult::Modified(&[1, 2, 3][..]));

		overlayed.commit_prospective();
		assert_eq!(overlayed.storage(&key), OverlayedValueResult::Modified(&[1, 2, 3][..]));

		overlayed.set_storage(key.clone(), Some(vec![]));
		assert_eq!(overlayed.storage(&key), OverlayedValueResult::Modified(&[][..]));

		overlayed.set_storage(key.clone(), None);
		assert_eq!(overlayed.storage(&key), OverlayedValueResult::Deleted);

		overlayed.discard_prospective();
		assert_eq!(overlayed.storage(&key), OverlayedValueResult::Modified(&[1, 2, 3][..]));

		overlayed.set_storage(key.clone(), None);
		overlayed.commit_prospective();
		assert_eq!(overlayed.storage(&key), OverlayedValueResult::Deleted);
	}

	#[test]
	fn overlayed_storage_root_works() {
		let initial: HashMap<_, _> = vec![
			(b"doe".to_vec(), b"reindeer".to_vec()),
			(b"dog".to_vec(), b"puppyXXX".to_vec()),
			(b"dogglesworth".to_vec(), b"catXXX".to_vec()),
			(b"doug".to_vec(), b"notadog".to_vec()),
		].into_iter().collect();
		let backend = InMemory::<Blake2Hasher>::from(initial);
		let mut overlay = OverlayedChanges {
			committed: vec![
				(b"dog".to_vec(), Some(b"puppy".to_vec()).into()),
				(b"dogglesworth".to_vec(), Some(b"catYYY".to_vec()).into()),
				(b"doug".to_vec(), Some(vec![]).into()),
			].into_iter().collect(),
			prospective: vec![
				(b"dogglesworth".to_vec(), Some(b"cat".to_vec()).into()),
				(b"doug".to_vec(), None.into()),
			].into_iter().collect(),
			..Default::default()
		};

		let changes_trie_storage = InMemoryChangesTrieStorage::<Blake2Hasher, u64>::new();
		let mut ext = Ext::new(
			&mut overlay,
			&backend,
			Some(&changes_trie_storage),
			crate::NeverOffchainExt::new(),
			None,
		);
		const ROOT: [u8; 32] = hex!("39245109cef3758c2eed2ccba8d9b370a917850af3824bc8348d505df2c298fa");

		assert_eq!(ext.storage_root(), H256::from(ROOT));
	}

	#[test]
	fn changes_trie_configuration_is_saved() {
		let mut overlay = OverlayedChanges::default();
		assert!(overlay.changes_trie_config.is_none());
		assert_eq!(overlay.set_changes_trie_config(ChangesTrieConfig {
			digest_interval: 4, digest_levels: 1,
		}), true);
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
			strip_extrinsic_index(&overlay.prospective.top),
			vec![
				(vec![1], OverlayedValue { value: Some(vec![2]), extrinsics: Some(vec![0].into_iter().collect()) }),
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

		assert_eq!(strip_extrinsic_index(&overlay.prospective.top),
			vec![
				(vec![1], OverlayedValue { value: Some(vec![6]), extrinsics: Some(vec![0, 2].into_iter().collect()) }),
				(vec![3], OverlayedValue { value: Some(vec![4]), extrinsics: Some(vec![1].into_iter().collect()) }),
				(vec![100], OverlayedValue { value: Some(vec![101]), extrinsics: Some(vec![NO_EXTRINSIC_INDEX].into_iter().collect()) }),
			].into_iter().collect());

		overlay.commit_prospective();

		overlay.set_extrinsic_index(3);
		overlay.set_storage(vec![3], Some(vec![7]));

		overlay.set_extrinsic_index(4);
		overlay.set_storage(vec![1], Some(vec![8]));

		assert_eq!(strip_extrinsic_index(&overlay.committed.top),
			vec![
				(vec![1], OverlayedValue { value: Some(vec![6]), extrinsics: Some(vec![0, 2].into_iter().collect()) }),
				(vec![3], OverlayedValue { value: Some(vec![4]), extrinsics: Some(vec![1].into_iter().collect()) }),
				(vec![100], OverlayedValue { value: Some(vec![101]), extrinsics: Some(vec![NO_EXTRINSIC_INDEX].into_iter().collect()) }),
			].into_iter().collect());

		assert_eq!(strip_extrinsic_index(&overlay.prospective.top),
			vec![
				(vec![1], OverlayedValue { value: Some(vec![8]), extrinsics: Some(vec![4].into_iter().collect()) }),
				(vec![3], OverlayedValue { value: Some(vec![7]), extrinsics: Some(vec![3].into_iter().collect()) }),
			].into_iter().collect());

		overlay.commit_prospective();

		assert_eq!(strip_extrinsic_index(&overlay.committed.top),
			vec![
				(vec![1], OverlayedValue { value: Some(vec![8]), extrinsics: Some(vec![0, 2, 4].into_iter().collect()) }),
				(vec![3], OverlayedValue { value: Some(vec![7]), extrinsics: Some(vec![1, 3].into_iter().collect()) }),
				(vec![100], OverlayedValue { value: Some(vec![101]), extrinsics: Some(vec![NO_EXTRINSIC_INDEX].into_iter().collect()) }),
			].into_iter().collect());

		assert_eq!(overlay.prospective,
			Default::default());
	}
}

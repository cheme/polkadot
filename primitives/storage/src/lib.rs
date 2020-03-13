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

//! Primitive types for storage related stuff.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")]
use serde::{Serialize, Deserialize};
#[cfg(feature = "std")]
use sp_std::collections::btree_map::BTreeMap;
use sp_debug_derive::RuntimeDebug;

use sp_std::vec::Vec;

/// Storage key.
#[derive(PartialEq, Eq, RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Hash, PartialOrd, Ord, Clone))]
pub struct StorageKey(
	#[cfg_attr(feature = "std", serde(with="impl_serde::serialize"))]
	pub Vec<u8>,
);

/// Storage data associated to a [`StorageKey`].
#[derive(PartialEq, Eq, RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Hash, PartialOrd, Ord, Clone))]
pub struct StorageData(
	#[cfg_attr(feature = "std", serde(with="impl_serde::serialize"))]
	pub Vec<u8>,
);

/// Map of data to use in a storage, it is a collection of
/// byte key and values.
#[cfg(feature = "std")]
pub type StorageMap = BTreeMap<Vec<u8>, Vec<u8>>;

#[cfg(feature = "std")]
#[derive(Debug, PartialEq, Eq, Clone)]
/// Child trie storage data.
pub struct StorageChild {
	/// Child data for storage.
	pub data: StorageMap,
	/// Associated child info for a child
	/// trie.
	pub child_info: ChildInfo,
	/// Associated child change, not that
	/// it does not always have a strict
	/// change semantic.
	pub child_change: ChildChange,
}

#[cfg(feature = "std")]
#[derive(Default, Debug, Clone)]
/// Struct containing data needed for a storage.
pub struct Storage {
	/// Top trie storage data.
	pub top: StorageMap,
	/// Children trie storage data.
	/// The key does not including prefix, for the `default`
	/// trie kind, so this is exclusively for the `ChildType::ParentKeyId`
	/// tries.
	pub children_default: std::collections::HashMap<Vec<u8>, StorageChild>,
}

/// Storage change set
#[derive(RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, PartialEq, Eq))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
pub struct StorageChangeSet<Hash> {
	/// Block hash
	pub block: Hash,
	/// A list of changes
	pub changes: Vec<(StorageKey, Option<StorageData>)>,
}

/// List of all well known keys and prefixes in storage.
pub mod well_known_keys {
	/// Wasm code of the runtime.
	///
	/// Stored as a raw byte vector. Required by substrate.
	pub const CODE: &'static [u8] = b":code";

	/// Number of wasm linear memory pages required for execution of the runtime.
	///
	/// The type of this value is encoded `u64`.
	pub const HEAP_PAGES: &'static [u8] = b":heappages";

	/// Current extrinsic index (u32) is stored under this key.
	pub const EXTRINSIC_INDEX: &'static [u8] = b":extrinsic_index";

	/// Changes trie configuration is stored under this key.
	pub const CHANGES_TRIE_CONFIG: &'static [u8] = b":changes_trie";

	/// Prefix of child storage keys.
	pub const CHILD_STORAGE_KEY_PREFIX: &'static [u8] = b":child_storage:";

	/// Whether a key is a child storage key.
	///
	/// This is convenience function which basically checks if the given `key` starts
	/// with `CHILD_STORAGE_KEY_PREFIX` and doesn't do anything apart from that.
	pub fn is_child_storage_key(key: &[u8]) -> bool {
		// Other code might depend on this, so be careful changing this.
		key.starts_with(CHILD_STORAGE_KEY_PREFIX)
	}

	/// Determine whether a child trie key is valid.
	///
	/// For now, the only valid child trie keys are those starting with `:child_storage:default:`.
	///
	/// `trie_root` can panic if invalid value is provided to them.
	pub fn is_child_trie_key_valid(storage_key: &[u8]) -> bool {
		let has_right_prefix = storage_key.starts_with(super::DEFAULT_CHILD_TYPE_PARENT_PREFIX);
		if has_right_prefix {
			// This is an attempt to catch a change of `is_child_storage_key`, which
			// just checks if the key has prefix `:child_storage:` at the moment of writing.
			debug_assert!(
				is_child_storage_key(&storage_key),
				"`is_child_trie_key_valid` is a subset of `is_child_storage_key`",
			);
		}
		has_right_prefix
	}

	/// Return true if the variable part of the key is empty.
	pub fn is_child_trie_key_empty(storage_key: &[u8]) -> bool {
		storage_key.len() == b":child_storage:default:".len()
	}
}

/// Information related to a child state.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "std", derive(PartialEq, Eq, Hash, PartialOrd, Ord))]
pub enum ChildInfo {
	/// This is the one used by default.
	ParentKeyId(ChildTrieParentKeyId),
}

/// How should I update between two child state.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "std", derive(PartialEq, Eq, Hash, PartialOrd, Ord))]
pub enum ChildUpdate {
	/// Merge the new values.
	Merge,
	/// Ignore the new values, for instance on a bulk deleted
	/// child state.
	Ignore,
	/// No update possible.
	Incompatible,
}

impl ChildInfo {
	/// Instantiates child information for a default child trie
	/// of kind `ChildType::ParentKeyId`, using an unprefixed parent
	/// storage key.
	pub fn new_default(storage_key: &[u8]) -> Self {
		let data = storage_key.to_vec();
		ChildInfo::ParentKeyId(ChildTrieParentKeyId { data })
	}

	/// Same as `new_default` but with `Vec<u8>` as input.
	pub fn new_default_from_vec(storage_key: Vec<u8>) -> Self {
		ChildInfo::ParentKeyId(ChildTrieParentKeyId {
			data: storage_key,
		})
	}

	/// Try to update with another instance, return false if both instance
	/// are not compatible.
	/// Passing current child change as parameter is needed
	pub fn try_update(&mut self, self_change: &ChildChange, other: &ChildInfo) -> ChildUpdate {
		match (self, self_change) {
			(_, ChildChange::BulkDeleteByKeyspace) => ChildUpdate::Ignore,
			(ChildInfo::ParentKeyId(child_trie), ChildChange::Update) => child_trie.try_update(other),
		}
	}

	/// Top trie defined as the unique crypto id trie with
	/// 0 length unique id.
	pub fn top_trie() -> Self {
		Self::new_default(&[])
	}

	/// Top trie defined as the unique crypto id trie with
	/// 0 length unique id.
	pub fn is_top_trie(&self) -> bool {
		match self {
			ChildInfo::ParentKeyId(ChildTrieParentKeyId { data }) => data.len() == 0,
		}
	}

	/// Create child info from a prefixed storage key and a given type.
	pub fn resolve_child_info(child_type: u32, storage_key: &[u8]) -> Option<Self> {
		match ChildType::new(child_type) {
			Some(ChildType::ParentKeyId) => {
				Some(Self::new_default(storage_key))
			},
			None => None,
		}
	}

	/// Returns a single byte vector containing packed child info content and its child info type.
	/// This can be use as input for `resolve_child_info`.
	pub fn info(&self) -> (&[u8], u32) {
		match self {
			ChildInfo::ParentKeyId(ChildTrieParentKeyId {
				data,
			}) => (data, ChildType::ParentKeyId as u32),
		}
	}

	/// Owned variant of `info`.
	pub fn into_info(self) -> (Vec<u8>, u32) {
		match self {
			ChildInfo::ParentKeyId(ChildTrieParentKeyId {
				data,
			}) => (data, ChildType::ParentKeyId as u32),
		}
	}

	/// Returns byte sequence (keyspace) that can be use by underlying db to isolate keys.
	/// This is a unique id of the child trie. The collision resistance of this value
	/// depends on the type of child info use. For `ChildInfo::Default` it is and need to be.
	pub fn keyspace(&self) -> &[u8] {
		match self {
			ChildInfo::ParentKeyId(..) => self.storage_key(),
		}
	}

	/// Returns a reference to the location in the direct parent of
	/// this trie but without the common prefix for this kind of
	/// child trie.
	pub fn storage_key(&self) -> &[u8] {
		match self {
			ChildInfo::ParentKeyId(ChildTrieParentKeyId {
				data,
			}) => &data[..],
		}
	}

	/// Return a the full location in the direct parent of
	/// this trie.
	pub fn prefixed_storage_key(&self) -> Vec<u8> {
		match self {
			ChildInfo::ParentKeyId(ChildTrieParentKeyId {
				data,
			}) => ChildType::ParentKeyId.new_prefixed_key(data.as_slice()),
		}
	}

	/// Returns a the full location in the direct parent of
	/// this trie.
	pub fn into_prefixed_storage_key(self) -> Vec<u8> {
		match self {
			ChildInfo::ParentKeyId(ChildTrieParentKeyId {
				mut data,
			}) => {
				ChildType::ParentKeyId.do_prefix_key(&mut data);
				data
			},
		}
	}

	/// Returns the type for this child info.
	pub fn child_type(&self) -> ChildType {
		match self {
			ChildInfo::ParentKeyId(..) => ChildType::ParentKeyId,
		}
	}

	/// Return `ChildChange` applicable for this state in the case of a bulk
	/// content deletion.
	pub fn bulk_delete_change(&self) -> ChildChange {
		match self {
			ChildInfo::ParentKeyId(..) => ChildChange::BulkDeleteByKeyspace,
		}
	}
}

/// Type of child.
/// It does not strictly define different child type, it can also
/// be related to technical consideration or api variant.
#[repr(u32)]
#[derive(Clone, Copy, PartialEq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub enum ChildType {
	/// If runtime module ensures that the child key is a unique id that will
	/// only be used once, its parent key is used as a child trie unique id.
	ParentKeyId = 1,
}

impl ChildType {
	/// Try to get a child type from its `u32` representation.
	pub fn new(repr: u32) -> Option<ChildType> {
		Some(match repr {
			r if r == ChildType::ParentKeyId as u32 => ChildType::ParentKeyId,
			_ => return None,
		})
	}

	/// Transform a prefixed key into a tuple of the child type
	/// and the unprefixed representation of the key.
	pub fn from_prefixed_key<'a>(storage_key: &'a [u8]) -> Option<(Self, &'a [u8])> {
		let match_type = |storage_key: &'a [u8], child_type: ChildType| {
			let prefix = child_type.parent_prefix();
			if storage_key.starts_with(prefix) {
				Some((child_type, &storage_key[prefix.len()..]))
			} else {
				None
			}
		};
		match_type(storage_key, ChildType::ParentKeyId)
	}

	/// Produce a prefixed key for a given child type.
	fn new_prefixed_key(&self, key: &[u8]) -> Vec<u8> {
		let parent_prefix = self.parent_prefix();
		let mut result = Vec::with_capacity(parent_prefix.len() + key.len());
		result.extend_from_slice(parent_prefix);
		result.extend_from_slice(key);
		result
	}

	/// Prefixes a vec with the prefix for this child type.
	fn do_prefix_key(&self, key: &mut Vec<u8>) {
		let parent_prefix = self.parent_prefix();
		let key_len = key.len();
		if parent_prefix.len() > 0 {
			key.resize(key_len + parent_prefix.len(), 0);
			key.copy_within(..key_len, parent_prefix.len());
			key[..parent_prefix.len()].copy_from_slice(parent_prefix);
		}
	}

	/// Returns the location reserved for this child trie in their parent trie if there
	/// is one.
	pub fn parent_prefix(&self) -> &'static [u8] {
		match self {
			&ChildType::ParentKeyId => DEFAULT_CHILD_TYPE_PARENT_PREFIX,
		}
	}
}

/// A child trie of default type.
/// It uses the same default implementation as the top trie,
/// top trie being a child trie with no keyspace and no storage key.
/// Its keyspace is the variable (unprefixed) part of its storage key.
/// It shares its trie nodes backend storage with every other
/// child trie, so its storage key needs to be a unique id
/// that will be use only once.
/// Those unique id also required to be long enough to avoid any
/// unique id to be prefixed by an other unique id.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "std", derive(PartialEq, Eq, Hash, PartialOrd, Ord))]
pub struct ChildTrieParentKeyId {
	/// Data is the storage key without prefix.
	data: Vec<u8>,
}

impl ChildTrieParentKeyId {
	/// Try to update with another instance, return false if both instance
	/// are not compatible.
	fn try_update(&mut self, other: &ChildInfo) -> ChildUpdate {
		match other {
			ChildInfo::ParentKeyId(other) => if self.data[..] == other.data[..] {
				ChildUpdate::Merge
			} else {
				ChildUpdate::Incompatible
			},
		}
	}
}

#[cfg(feature = "std")]
#[derive(Clone, PartialEq, Eq, Debug)]
/// Type for storing a map of child trie related information.
/// A few utilities methods are defined.
pub struct ChildrenMap<T>(pub BTreeMap<ChildInfo, T>);

/// Type alias for storage of children related content. 
pub type ChildrenVec<T> = Vec<(ChildInfo, T)>;

/// Type alias for storage of children related content. 
pub type ChildrenSlice<'a, T> = &'a [(ChildInfo, T)];

#[cfg(feature = "std")]
impl<T> sp_std::ops::Deref for ChildrenMap<T> {
	type Target = BTreeMap<ChildInfo, T>;

	fn deref(&self) -> &Self::Target {
		&self.0
	}
}

#[cfg(feature = "std")]
impl<T> sp_std::ops::DerefMut for ChildrenMap<T> {
	fn deref_mut(&mut self) -> &mut Self::Target {
		&mut self.0
	}
}

#[cfg(feature = "std")]
impl<T> sp_std::default::Default for ChildrenMap<T> {
	fn default() -> Self {
		ChildrenMap(BTreeMap::new())
	}
}

#[cfg(feature = "std")]
impl<T> ChildrenMap<T> {
	/// Extend for `ChildrenMap` is usually about merging entries,
	/// this method extends two maps, by applying a merge function
	/// on each of its entries.
	pub fn extend_with(
		&mut self,
		other: impl Iterator<Item = (ChildInfo, T)>,
		merge: impl Fn(&mut T, T),
	) {
		use sp_std::collections::btree_map::Entry;
		for (child_info, child_content) in other {
			match self.0.entry(child_info) {
				Entry::Occupied(mut entry) => {
					merge(entry.get_mut(), child_content)
				},
				Entry::Vacant(entry) => {
					entry.insert(child_content);
				},
			}
		}
	}

	/// Extends two maps, by extending entries with the same key.
	pub fn extend_replace(
		&mut self,
		other: impl Iterator<Item = (ChildInfo, T)>,
	) {
		self.0.extend(other)
	}

	/// Retains only the elements specified by the predicate.
	pub fn retain(&mut self, mut f: impl FnMut(&ChildInfo, &mut T) -> bool) {
		let mut to_del = Vec::new();
		for (k, v) in self.0.iter_mut() {
			if !f(k, v) {
				// this clone can be avoid with unsafe code
				to_del.push(k.clone());
			}
		}
		for k in to_del {
			self.0.remove(&k);
		}
	}
}

#[cfg(feature = "std")]
impl<T> IntoIterator for ChildrenMap<T> {
	type Item = (ChildInfo, T);
	type IntoIter = sp_std::collections::btree_map::IntoIter<ChildInfo, T>;

	fn into_iter(self) -> Self::IntoIter {
		self.0.into_iter()
	}
}

const DEFAULT_CHILD_TYPE_PARENT_PREFIX: &'static [u8] = b":child_storage:default:";

/// Information related to change to apply on a whole child trie.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "std", derive(PartialEq, Eq, Hash, PartialOrd, Ord))]
pub enum ChildChange {
	/// Update to content of child trie.
	Update,
	/// The child trie allow to delete base on keyspace only.
	/// This deletion means that any joined key delta will be ignored.
	BulkDeleteByKeyspace,
}

impl Default for ChildChange {
	fn default() -> Self {
		ChildChange::Update
	}
}

#[test]
fn test_prefix_default_child_info() {
	let child_info = ChildInfo::new_default(b"any key");
	let prefix = child_info.child_type().parent_prefix();
	assert!(prefix.starts_with(well_known_keys::CHILD_STORAGE_KEY_PREFIX));
	assert!(prefix.starts_with(DEFAULT_CHILD_TYPE_PARENT_PREFIX));
}

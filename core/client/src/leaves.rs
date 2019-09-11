// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

//! Helper for managing the set of available leaves in the chain for DB implementations.

use std::collections::BTreeMap;
use std::cmp::Reverse;
use kvdb::{KeyValueDB, DBTransaction};
use sr_primitives::traits::SimpleArithmetic;
use codec::{Encode, Decode};
use crate::error;

#[derive(Debug, Clone, PartialEq, Eq)]
struct LeafSetItem<H, N> {
	hash: H,
	number: Reverse<N>,
	branch_ranges: StatesRef,
}

/// A displaced leaf after import.
#[must_use = "Displaced items from the leaf set must be handled."]
pub struct ImportDisplaced<H, N> {
	new_hash: H,
	displaced: LeafSetItem<H, N>,
}

/// Displaced leaves after finalization.
#[must_use = "Displaced items from the leaf set must be handled."]
pub struct FinalizationDisplaced<H, N> {
	leaves: BTreeMap<Reverse<N>, Vec<(H, StatesRef)>>,
}

impl<H, N: Ord> FinalizationDisplaced<H, N> {
	/// Merge with another. This should only be used for displaced items that
	/// are produced within one transaction of each other.
	pub fn merge(&mut self, mut other: Self) {
		// this will ignore keys that are in duplicate, however
		// if these are actually produced correctly via the leaf-set within
		// one transaction, then there will be no overlap in the keys.
		self.leaves.append(&mut other.leaves);
	}
}

/// list of leaf hashes ordered by number (descending).
/// stored in memory for fast access.
/// this allows very fast checking and modification of active leaves.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LeafSet<H, N> {
	storage: BTreeMap<Reverse<N>, Vec<(H, StatesRef)>>,
	pending_added: Vec<LeafSetItem<H, N>>,
	pending_removed: Vec<H>,
	branch_range_cache: BTreeMap<u64, LinearStates>,
	branch_range_treshold: u64,
	branch_range_changed: Vec<u64>,
	branch_range_removed: Vec<u64>,
}

impl<H, N> LeafSet<H, N> where
	H: Clone + PartialEq + Decode + Encode + AsRef<[u8]>,
	N: std::fmt::Debug + Clone + SimpleArithmetic + Decode + Encode,
{
	/// Construct a new, blank leaf set.
	pub fn new() -> Self {
		Self {
			storage: BTreeMap::new(),
			pending_added: Vec::new(),
			pending_removed: Vec::new(),
			branch_range_cache: BTreeMap::new(),
			branch_range_treshold: DEFAULT_START_TRESHOLD,
			branch_range_changed: Vec::new(),
			branch_range_removed: Vec::new(),
		}
	}

	/// Read the leaf list from the DB, using given prefix for keys.
	pub fn read_from_db(
		db: &dyn KeyValueDB,
		column: Option<u32>,
		prefix: &[u8],
		treshold_key: &[u8],
		column_block_numbers: Option<u32>,
		column_branch_range: Option<u32>,
	) -> error::Result<Self> {
		let mut storage = BTreeMap::new();

		let branch_range_treshold = read_branch_state_treshold(db, column, treshold_key)?
			.unwrap_or(DEFAULT_START_TRESHOLD);
		for (key, value) in db.iter_from_prefix(column, prefix) {
			if !key.starts_with(prefix) { break }
			let raw_hash = &mut &key[prefix.len()..];
			let hash = match Decode::decode(raw_hash) {
				Ok(hash) => hash,
				Err(_) => return Err(error::Error::Backend("Error decoding hash".into())),
			};
			let number = match Decode::decode(&mut &value[..]) {
				Ok(tuple) => tuple,
				Err(_) => return Err(error::Error::Backend("Error decoding number".into())),
			};
			let branch_index = read_branch_index(db, column_block_numbers, &hash)?;
			// default to 0 for existing content (no associated data) so a branch that do
			// not exist is fine.
			let branch_index = branch_index.map(|t| t.0).unwrap_or(0);
			let state_ref = Self::read_state_ref(
				db,
				column_branch_range,
				branch_index,
			)?;
			storage.entry(Reverse(number)).or_insert_with(Vec::new).push((hash, state_ref));
		}
		Ok(Self {
			storage,
			pending_added: Vec::new(),
			pending_removed: Vec::new(),
			branch_range_cache: BTreeMap::new(),
			branch_range_treshold,
			branch_range_changed: Vec::new(),
			branch_range_removed: Vec::new(),
		})
	}

	/// Get history of branch for branch index, up to a given treshold.
	/// TODO EMCH move to trait and db
	pub fn read_state_ref(
		db: &dyn KeyValueDB,
		column_branch_range: Option<u32>,
		branch_index: u64,
	) -> error::Result<StatesRef> {
		unimplemented!()
	}
	
	/// update the leaf list on import. returns a displaced leaf if there was one.
	pub fn import(&mut self, hash: H, number: N, parent_hash: H, branch_index: u64) -> Option<ImportDisplaced<H, N>> {
		// avoid underflow for genesis.
		let displaced = if number != N::zero() {
			let new_number = Reverse(number.clone() - N::one());
			let was_displaced = self.remove_leaf(&new_number, &parent_hash);

			if let Some(parent_branch_ranges) = was_displaced {
				self.pending_removed.push(parent_hash.clone());
				Some(ImportDisplaced {
					new_hash: hash.clone(),
					displaced: LeafSetItem {
						hash: parent_hash,
						number: new_number,
						branch_ranges: parent_branch_ranges,
					},
				})
			} else {
				None
			}
		} else {
			None
		};

		let branch_ranges = unimplemented!("TODO EMCH cat branch inde xinto parent ranges");
		self.insert_leaf(Reverse(number.clone()), hash.clone(), branch_ranges);
		self.pending_added.push(LeafSetItem { hash, number: Reverse(number), branch_ranges });
		displaced
	}

	/// Note a block height finalized, displacing all leaves with number less than the finalized block's.
	///
	/// Although it would be more technically correct to also prune out leaves at the
	/// same number as the finalized block, but with different hashes, the current behavior
	/// is simpler and our assumptions about how finalization works means that those leaves
	/// will be pruned soon afterwards anyway.
	pub fn finalize_height(&mut self, number: N) -> FinalizationDisplaced<H, N> {
		let boundary = if number == N::zero() {
			return FinalizationDisplaced { leaves: BTreeMap::new() };
		} else {
			number - N::one()
		};

		let below_boundary = self.storage.split_off(&Reverse(boundary));
		// TODO EMCH here we also do add branch range update/delete and revert content
		// (happening in cache only).
		self.pending_removed.extend(
			below_boundary.values().flat_map(|h| h.iter().map(|(h, _)| h)).cloned()
		);
		FinalizationDisplaced {
			leaves: below_boundary,
		}
	}

	/// Undo all pending operations.
	///
	/// This returns an `Undo` struct, where any
	/// `Displaced` objects that have returned by previous method calls
	/// should be passed to via the appropriate methods. Otherwise,
	/// the on-disk state may get out of sync with in-memory state.
	pub fn undo(&mut self) -> Undo<H, N> {
		Undo { inner: self }
	}

	/// currently since revert only affects the canonical chain
	/// we assume that parent has no further children
	/// and we add it as leaf again
	pub fn revert(
		&mut self,
		hash: H,
		number: N,
		parent_hash: H,
		parent_branch_index: u64,
		tx: &mut DBTransaction,
		column_block_numbers: Option<u32>,
	) {
		self.remove_leaf(&Reverse(number), &hash);
		let parent_branch_ranges = unimplemented!("TODO EMCH get ranges from removed parent then drop last, with hard assertion on parent presence");
		self.insert_leaf(Reverse(number.clone() - N::one()), parent_hash, parent_branch_ranges);
		tx.delete(column_block_numbers, hash.as_ref());
	}

	/// returns an iterator over all hashes in the leaf set
	/// ordered by their block number descending.
	pub fn hashes(&self) -> Vec<H> {
		self.storage.iter().flat_map(|(_, hashes)| hashes.iter().map(|(h, _)| h)).cloned().collect()
	}

	/// Write the leaf list to the database transaction.
	pub fn prepare_transaction(
		&mut self,
		tx: &mut DBTransaction,
		column: Option<u32>,
		prefix: &[u8],
		column_block_numbers: Option<u32>,
	) {
		let mut buf = prefix.to_vec();
    // TODO EMCH no need for portablility here always write new version.
		for LeafSetItem { hash, number, branch_ranges } in self.pending_added.drain(..) {
			hash.using_encoded(|s| buf.extend(s));
			debug_assert!(branch_ranges.0.len() > 0, "no leaf set item with empty branches range");
			let branch_index = branch_ranges.0[branch_ranges.0.len() - 1].branch_ix;
			// TODO EMCH this need some implementation: stored per block does not seems fine.
			// Branch are ultimately in leaf (restoring in case of leaf broken,
			// would be done by simply setting to non appendable).
			let is_appendable = false;
			// TODO EMCH consider storing in a prefix ?
			tx.put_vec(column_block_numbers, hash.as_ref(), (branch_index, is_appendable).encode());
			tx.put_vec(column, &buf[..], number.0.encode());

			buf.truncate(prefix.len()); // reuse allocation.
		}
		for hash in self.pending_removed.drain(..) {
			hash.using_encoded(|s| buf.extend(s));
			tx.delete(column, &buf[..]);
			buf.truncate(prefix.len()); // reuse allocation.
		}
	}

	#[cfg(test)]
	fn contains(&self, number: N, hash: H) -> bool {
		self.storage.get(&Reverse(number))
			.map_or(false, |hashes| hashes.iter().find(|(h, _)| h == &hash).is_some())
	}

	fn insert_leaf(&mut self, number: Reverse<N>, hash: H, branch_ranges: StatesRef) {
		self.storage.entry(number).or_insert_with(Vec::new).push((hash, branch_ranges));
	}

	// returns a branch index if this leaf was contained, nothing otherwise.
	fn remove_leaf(&mut self, number: &Reverse<N>, hash: &H) -> Option<StatesRef> {
		let mut empty = false;
		let removed = self.storage.get_mut(number).map_or(None, |leaves| {
			let mut found = None;
			leaves.retain(|(h, b)| if h == hash {
				// TODO EMCH rewrite to avoid this clone
				found = Some(b.clone());
				false
			} else {
				true
			});

			if leaves.is_empty() { empty = true }

			found
		});

		if removed.is_some() && empty {
			self.storage.remove(number);
		}

		removed
	}
}

/// Helper for undoing operations.
pub struct Undo<'a, H: 'a, N: 'a> {
	inner: &'a mut LeafSet<H, N>,
}

impl<'a, H: 'a, N: 'a> Undo<'a, H, N> where
	H: Clone + PartialEq + Decode + Encode + AsRef<[u8]>,
	N: std::fmt::Debug + Clone + SimpleArithmetic + Decode + Encode,
{
	/// Undo an imported block by providing the displaced leaf.
	pub fn undo_import(&mut self, displaced: ImportDisplaced<H, N>) {
		let new_number = Reverse(displaced.displaced.number.0.clone() + N::one());
		// recursively remove next leaves
		self.inner.remove_leaf(&new_number, &displaced.new_hash);
		self.inner.insert_leaf(
			new_number,
			displaced.displaced.hash,
			displaced.displaced.branch_ranges,
		);
	}

	/// Undo a finalization operation by providing the displaced leaves.
	pub fn undo_finalization(&mut self, mut displaced: FinalizationDisplaced<H, N>) {
		self.inner.storage.append(&mut displaced.leaves);
	}
}

impl<'a, H: 'a, N: 'a> Drop for Undo<'a, H, N> {
	fn drop(&mut self) {
		self.inner.pending_added.clear();
		self.inner.pending_removed.clear();
	}
}

/// Read a stored branch index for a block hash.
pub fn read_branch_index<H: AsRef<[u8]> + Clone>(
	db: &dyn KeyValueDB,
	key_lookup_col: Option<u32>,
	id: H,
) -> Result<Option<(u64, bool)>, error::Error> {
	if let Some(buffer) = db.get(
		key_lookup_col,
		id.as_ref(),
	).map_err(|err| error::Error::Backend(format!("{}", err)))? {
		match Decode::decode(&mut &buffer[..]) {
			Ok(v) => Ok(Some(v)),
			Err(err) => Err(error::Error::Backend(
				format!("Error decoding block branch index: {}", err)
			)),
		}
	} else {
		Ok(None)
	}
}

/// Read a stored branch treshould corresponding to
/// a branch index bellow which there is only valid values.
/// TODO EMCH this should be in db: TODO create a BranchIndexBackend
/// that db implements.
pub fn read_branch_state_treshold(
	db: &dyn KeyValueDB,
	key_lookup_col: Option<u32>,
	key: &[u8],
) -> Result<Option<u64>, error::Error> {
	if let Some(buffer) = db.get(
		key_lookup_col,
		key,
	).map_err(|err| error::Error::Backend(format!("{}", err)))? {
		match Decode::decode(&mut &buffer[..]) {
			Ok(i) => Ok(i),
			Err(err) => Err(error::Error::Backend(
				format!("Error decoding branch index treshold: {}", err)
			)),
		}
	} else {
		Ok(None)
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn it_works() {
		let mut set = LeafSet::new();
		set.import([0u8], 0u32, [0u8], 1);

		set.import([1_1], 1, [0], 1);
		set.import([2_1], 2, [1_1], 1);
		set.import([3_1], 3, [2_1], 1);

		assert!(set.contains(3, [3_1]));
		assert!(!set.contains(2, [2_1]));
		assert!(!set.contains(1, [1_1]));
		assert!(!set.contains(0, [0]));

		set.import([2_2], 2, [1_1], 2);

		assert!(set.contains(3, [3_1]));
		assert!(set.contains(2, [2_2]));
	}

	#[test]
	fn flush_to_disk() {
		const PREFIX: &[u8] = b"abcdefg";
		const TRESHOLD: &[u8] = b"hijkl";
		let db = ::kvdb_memorydb::create(3);

		let mut set = LeafSet::new();
		set.import([0u8], 0u32, [0u8], 1);

		set.import([1_1], 1, [0], 1);
		set.import([2_1], 2, [1_1], 1);
		set.import([3_1], 3, [2_1], 1);

		let mut tx = DBTransaction::new();

		set.prepare_transaction(&mut tx, None, PREFIX, Some(1));
		db.write(tx).unwrap();

		let set2 = LeafSet::read_from_db(&db, None, PREFIX, TRESHOLD, Some(1), Some(2)).unwrap();
		assert_eq!(set, set2);
	}

	#[test]
	fn two_leaves_same_height_can_be_included() {
		let mut set = LeafSet::new();

		set.import([1_1u8], 10u32, [0u8], 1);
		set.import([1_2], 10, [0], 2);

		assert!(set.storage.contains_key(&Reverse(10)));
		assert!(set.contains(10, [1_1]));
		assert!(set.contains(10, [1_2]));
		assert!(!set.contains(10, [1_3]));
	}

	#[test]
	fn finalization_consistent_with_disk() {
		const PREFIX: &[u8] = b"prefix";
		const TRESHOLD: &[u8] = b"hijkl";
		let db = ::kvdb_memorydb::create(3);

		let mut set = LeafSet::new();
		set.import([10u8, 1u8], 10u32, [0u8, 0u8], 1);
		set.import([11, 1], 11, [10, 2], 2);
		set.import([11, 2], 11, [10, 2], 3);
		set.import([12, 1], 12, [11, 123], 4);

		assert!(set.contains(10, [10, 1]));

		let mut tx = DBTransaction::new();
		set.prepare_transaction(&mut tx, None, PREFIX, Some(1));
		db.write(tx).unwrap();

		let _ = set.finalize_height(11);
		let mut tx = DBTransaction::new();
		set.prepare_transaction(&mut tx, None, PREFIX, Some(1));
		db.write(tx).unwrap();

		assert!(set.contains(11, [11, 1]));
		assert!(set.contains(11, [11, 2]));
		assert!(set.contains(12, [12, 1]));
		assert!(!set.contains(10, [10, 1]));

		let set2 = LeafSet::read_from_db(&db, None, PREFIX, TRESHOLD, Some(1), Some(2)).unwrap();
		assert_eq!(set, set2);
	}

	#[test]
	fn undo_finalization() {
		let mut set = LeafSet::new();
		set.import([10u8, 1], 10u32, [0u8, 0u8], 1);
		set.import([11, 1], 11, [10, 2], 2);
		set.import([11, 2], 11, [10, 2], 3);
		set.import([12, 1], 12, [11, 123], 4);

		let displaced = set.finalize_height(11);
		assert!(!set.contains(10, [10, 1]));

		set.undo().undo_finalization(displaced);
		assert!(set.contains(10, [10, 1]));
	}
}



// TODO EMCH temporary structs until merge with historied-data branch.

/// This is a simple range, end non inclusive.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinearStatesRef {
	start: usize,
	end: usize,
}

impl LinearStatesRef {
	/// Return true if the state exists, false otherwhise.
	pub fn get_state(&self, index: usize) -> bool {
		index < self.end && index >= self.start
	}
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StatesBranchRef {
	branch_ix: u64,
	state: LinearStatesRef,
}

/// Reference to state that is enough for query updates, but not
/// for gc.
/// Values are ordered by branch_ix,
/// and only a logic branch path should be present.
///
/// Note that an alternative could be a pointer to a full state
/// branch for a given branch index, here we use an in memory
/// copied representation in relation to an actual use case.
///
/// First value is an ordered array of valid branches, second value
/// is a branch index treshold under which all branch are valid
/// (expect all historied data state to be fully garbage collected
/// upon a single trie path, for instance in case of a tree of block
/// that would be at finalize (remove all non finalize data from this point
/// so there is no need to track the single remaining path)).
pub type StatesRef = (Vec<StatesBranchRef>, u64);


#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinearStates {
	/// Index of first element (only use for indexed access).
	/// Element before offset are not in state.
	offset: usize,
	/// number of elements: all elements equal or bellow
	/// this index are valid, over this index they are not.
	len: usize,
	/// Maximum index before first deletion, it indicates
	/// if the state is modifiable (when an element is dropped
	/// we cannot append and need to create a new branch).
	max_len_ix: usize,
}

impl Default for LinearStates {
	// initialize with one element
	fn default() -> Self {
		Self::new_from(0)
	}
}

impl LinearStates {
	pub fn new_from(offset: usize) -> Self {
		LinearStates {
			offset,
			len: 1,
			max_len_ix: offset,
		}
	}

	pub fn state_ref(&self) -> LinearStatesRef {
		LinearStatesRef {
			start: self.offset,
			end: self.offset + self.len,
		}
	}

	pub fn has_deleted_index(&self) -> bool {
		self.max_len_ix >= self.offset + self.len
	}

	pub fn add_state(&mut self) -> bool {
		if !self.has_deleted_index() {
			self.len += 1;
			self.max_len_ix += 1;
			true
		} else {
			false
		}
	}

	/// return possible dropped state
	pub fn drop_state(&mut self) -> Option<usize> {
		if self.len > 0 {
			self.len -= 1;
			Some(self.len)
		} else {
			None
		}
	}

	/// act as a truncate, returning range of deleted (end excluded)
	/// TODO consider removal
	pub fn keep_state(&mut self, index: usize) -> (usize, usize) {
		if index < self.offset {
			return (self.offset, self.offset);
		}
		if self.len > (index - self.offset) {
			let old_len = self.len;
			self.len = index - self.offset;
			(index, old_len)
		} else {
			(index, index)
		}
	}

	/// Return true if state exists.
	pub fn get_state(&self, index: usize) -> bool {
		if index < self.offset {
			return false;
		}
		self.len > index + self.offset
	}

	pub fn latest_ix(&self) -> Option<usize> {
		if self.len > 0 {
			Some(self.offset + self.len - 1)
		} else {
			None
		}
	}

}

const DEFAULT_START_TRESHOLD: u64 = 1;

// TODO EMCH end from historied - data

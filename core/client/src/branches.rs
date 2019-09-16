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

//! Helper for managing the set of available branches in the chain for DB implementations.

use std::collections::{BTreeMap, BTreeSet, HashMap, btree_map::Entry};
use std::cmp::Reverse;
use kvdb::{KeyValueDB, DBTransaction};
use sr_primitives::traits::SimpleArithmetic;
use primitives::offstate::{BranchRanges, LinearStatesRef, StatesBranchRef};
use codec::{Encode, Decode};
use crate::error;
use std::hash::Hash as StdHash;
use std::convert::TryInto;

#[derive(Clone)]
/// Displaced leaves after finalization and removal of any non
/// finalized deprecated values (branch index less than finalization block).
#[must_use = "Displaced items from the leaf set must be handled."]
pub struct TresholdUpdateDisplaced {
	ranges: BTreeMap<u64, Option<LinearStates>>,
	treshold: u64,
}

impl TresholdUpdateDisplaced {
	/// Merge with another. This should only be used for displaced items that
	/// are produced within one transaction of each other.
	pub fn merge(&mut self, mut other: Self) {
		debug_assert!(self.treshold <= other.treshold);
		// this will ignore keys that are in duplicate, however
		// if these are actually produced correctly via the leaf-set within
		// one transaction, then there will be no overlap in the keys.
		self.ranges.append(&mut other.ranges);
		self.treshold = other.treshold;
	}
}

/// current branches range definition, indexed by branch
/// numbers.
///
/// New branches index are using `last_index`.
/// `treshold` is a branch index under which branches are undefined
/// but data there is seen as finalized.
///
/// Also acts as a cache, storage can store
/// unknown db value as `None`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RangeSet {
	storage: BTreeMap<u64, Option<LinearStates>>,
	last_index_original: u64,
	last_index: u64,
	treshold_original: u64,
	treshold: u64,
	// change and removed concern both storage and appendable
	changed: BTreeSet<u64>,
	removed: BTreeSet<u64>,
}

const DEFAULT_START_TRESHOLD: u64 = 1;

impl Default for RangeSet {
	fn default() -> Self {
		RangeSet {
			storage: BTreeMap::new(),
			last_index_original: 0,
			last_index: 0,
			treshold_original: DEFAULT_START_TRESHOLD,
			treshold: DEFAULT_START_TRESHOLD,
			changed: BTreeSet::new(),
			removed: BTreeSet::new(),
		}
	}
}

impl RangeSet {

	#[cfg(test)]
	/// access to last_index_original for test only.
	pub fn last_index_original(&mut self) -> &mut u64 {
		&mut self.last_index_original
	}

	#[cfg(test)]
	/// test access to treshold.
	pub fn range_treshold(&self) -> u64 {
		self.treshold
	}

	#[cfg(test)]
	/// test access to strage.
	pub fn inner_storage(&self) -> &BTreeMap<u64, Option<LinearStates>> {
		&self.storage
	}


	/// Construct a new range set
	pub fn new(treshold: u64, last_index: u64) -> Self {
		RangeSet {
			storage: BTreeMap::new(),
			last_index_original: last_index,
			last_index,
			treshold_original: treshold,
			treshold,
			changed: BTreeSet::new(),
			removed: BTreeSet::new(),
		}
	}

	/// TODO EMCH move to trait and db side ?
	pub fn read_branch_ranges(
		&mut self,
		db: &dyn KeyValueDB,
		column_branch_range: Option<u32>,
		mut branch_index: u64,
	) -> error::Result<BranchRanges> {
		let mut result = Vec::new();
		if branch_index < self.treshold {
			return Ok(result);
		}
		loop {
			if let Some(StatesBranch{ state, parent_branch_index, .. }) = read_branch_range_with_cache(
				db,
				column_branch_range,
				branch_index,
				&mut self.storage,
			)? {
				// TODO EMCH consider vecdeque ??
				result.insert(0, StatesBranchRef {
					state: state.clone(),
					branch_index: branch_index,
				});

				branch_index = *parent_branch_index;
				if branch_index < self.treshold {
					break;
				}
			} else {
				// no parent branch, cut the reading with error
				return Err(error::Error::Backend("Inconsistent branch history or treshold".into()));
			}
		}
		Ok(result)
	}

	pub fn branch_ranges_from_cache(
		&self,
		mut branch_index: u64,
	) -> BranchRanges {
		// TODO EMCH transform this method to an iterator!!!
		// (avoid some intermediatory Vec (eg when building Hashset)
		let mut result = Vec::new();
		if branch_index < self.treshold {
			return result;
		}
		let mut previous_start = u64::max_value();
		loop {
			if let Some(Some(StatesBranch{ state, parent_branch_index, .. })) = self.storage.get(&branch_index) {
				// TODO EMCH consider vecdeque ??
				let state = if state.end > previous_start {
					LinearStatesRef {
						start: state.start,
						end: previous_start,
					}
				} else { state.clone() };

				previous_start = state.start;

				result.insert(0, StatesBranchRef {
					state,
					branch_index,
				});

				branch_index = *parent_branch_index;
				if branch_index < self.treshold {
					break;
				}
			} else {
				debug_assert!(false, "inconsistent branch range cache");
				break;
			}
		}
		result
	}


	/// Return anchor index for this branch history:
	/// - same index as input if branch is not empty
	/// - parent index if branch is empty
	pub fn drop_state(
		&mut self,
		branch_index: u64,
	) -> error::Result<u64> {
		let mut do_remove = None;
		match self.storage.get_mut(&branch_index) {
			Some(Some(branch_state)) => {
				if let Some(drop_index) = branch_state.drop_state() {
					if drop_index == 0 {
						self.removed.insert(branch_index);
						do_remove = Some(branch_state.parent_branch_index);
					} else {
						branch_state.can_append = false;
						self.changed.insert(branch_index);
					}
				} else {
					// deleted branch, do nothing
				}
			},
			Some(None) => (), // already dropped.
			None => // TODO not sure keeping this error (we may want to clear storage)
				return Err(error::Error::Backend("storage should contain every branch ref".into())),
		}

		if let Some(parent_index) = do_remove {
			self.storage.remove(&branch_index);
			Ok(parent_index)
		} else {
			Ok(branch_index)
		}
	}

	/// Return anchor index for this branch history:
	/// - same index as input if the branch was modifiable
	/// - new index in case of branch range creation
	pub fn add_state<N: TryInto<u64> + Clone>(
		&mut self,
		branch_index: u64,
		number: &N,
	) -> error::Result<u64> {
		let mut create_new = false;
		if branch_index == 0 || branch_index < self.treshold {
			create_new = true;
		} else { match self.storage.get_mut(&branch_index) {
			Some(Some(branch_state)) => {
				let number = if let Ok(number) = <N as TryInto<u64>>::try_into(number.clone()) {
					number
				} else {
					return Err(error::Error::Backend("non u64 convertible block number".into()));
				};
				if branch_state.can_append && branch_state.can_add(number) {
					branch_state.add_state();
					self.changed.insert(branch_index);
				} else {
					create_new = true;
				}
			},
			Some(None) => 
				return Err(error::Error::Backend("trying to add to a dropped branch range.".into())),
			None => // TODO not sure keeping this error (we may want to clear storage)
				return Err(error::Error::Backend("trying to add ta a non existant branch range.".into())),
		}}

		if create_new {
			self.last_index += 1;
			// TODO EMCH change code to use direcly number instead of u64
			if let Ok(number) = <N as TryInto<u64>>::try_into(number.clone()) {
				let state = StatesBranch::new(number, branch_index);
				self.storage.insert(self.last_index, Some(state));
				self.changed.insert(self.last_index);
				Ok(self.last_index)
			} else {
				Err(error::Error::Backend("non u64 convertible block number".into()))
			}
		} else {
			Ok(branch_index)
		}
	}

	// TODO EMCH this access can be optimize at multiple places (by returning ref
	// instead of an anchor_id).
	pub fn state_ref(&self, branch_index: u64) -> Option<StatesBranchRef> {
		self.storage.get(&branch_index).and_then(|v| v.as_ref().map(|v| v.state_ref()))
			.map(|state| StatesBranchRef {
				branch_index,
				state,
			})
	}

	/// Read the range list from the DB
	pub fn read_from_db(
		db: &dyn KeyValueDB,
		column: Option<u32>,
		treshold_key: &[u8],
		last_branch_index_key: &[u8],
	) -> error::Result<Self> {
		let treshold = read_branch_state_treshold(db, column, treshold_key)?
			.unwrap_or(DEFAULT_START_TRESHOLD);
		let last_index = read_branch_last_index(db, column, last_branch_index_key)?;
		Ok(RangeSet::new(treshold, last_index))
	}

	/// update the range set on import. returns a displaced leaf if there was one.
	pub fn import<N: TryInto<u64> + Clone>(
		&mut self,
		number: &N,
		parent_branch_index: u64,
		parent_branch_range: Option<BranchRanges>,
	) -> (BranchRanges, u64) {

		if let Some(mut branch_ranges) = parent_branch_range {
			let anchor_index = self.add_state(parent_branch_index, number)
				.expect("coherent branch index state"); // TODO EMCH fail in add_state
			if anchor_index == parent_branch_index {
				branch_ranges.pop();
			}
			branch_ranges.push(self.state_ref(anchor_index).expect("added just above"));
			(branch_ranges, anchor_index)
		} else {
			let anchor_index = self.add_state(parent_branch_index, number)
				.expect("coherent branch index state"); // TODO EMCH fail in add_state
			(vec![self.state_ref(anchor_index).expect("added just above")], anchor_index)
		}
	}

	/// Apply a post finalize update of treshold: requires
	/// that values before new treshold are all clear (since
	/// we stop maintaining branches for them).
	pub fn update_finalize_treshold(
		&mut self,
		branch_index: u64,
		full: bool,
	) -> TresholdUpdateDisplaced {

		// range set update
		let old_treshold = self.treshold;
		self.treshold = branch_index;
		let removed_ranges = if branch_index == 0 || !full {
			// remove cached value under treshold only
			let new_storage = self.storage.split_off(&(self.treshold));
			std::mem::replace(&mut self.storage, new_storage)
		} else {
			let new_storage = self.storage.split_off(&(self.treshold));
			let mut removed = std::mem::replace(&mut self.storage, new_storage);
			self.finalize_full(&mut removed, branch_index);
			removed
		};
		self.removed.extend(removed_ranges.keys().cloned());

		// TODO EMCH here we also do add branch range update/delete and revert content
		// (happening in cache only).
		TresholdUpdateDisplaced {
			ranges: removed_ranges,
			treshold: old_treshold,
		}
	}

	/// Apply a post finalize without considering treshold.
	fn finalize_full(
		&mut self,
		output: &mut BTreeMap<u64, Option<LinearStates>>,
		branch_index: u64,
	) {
		// TODO EMCH consider working directly on ordered vec (should be fastest in most cases)
		let mut finalize_branches_map: BTreeMap<_, _> = self.branch_ranges_from_cache(branch_index)
			.into_iter().map(|r| (r.branch_index, r.state)).collect();

		for (index, state) in self.storage.iter_mut() {
			if let Some(final_state) = finalize_branches_map.remove(&index) {
				// update for case where end of range differs (see `branch_ranges_from_cache`).
				state.as_mut().map(|state| {
					if state.state != final_state {
						output.insert(*index, Some(state.clone()));
						state.state = final_state;
						state.can_append = false;
					}
				});
			} else {
				output.insert(*index, state.take());
			}
		}
	}

	#[cfg(test)]
	pub fn test_finalize_full(
		&mut self,
		branch_index: u64,
	) -> TresholdUpdateDisplaced {
		let mut removed_ranges = BTreeMap::new();
		self.finalize_full(&mut removed_ranges, branch_index);
		self.removed.extend(removed_ranges.keys().cloned());
		TresholdUpdateDisplaced {
			ranges: removed_ranges,
			treshold: self.treshold,
		}
	}

	/// Undo a branch treshold update operation by providing the delta.
	pub fn undo_ranges_treshold_update(&mut self, mut displaced: TresholdUpdateDisplaced) {
		self.treshold = displaced.treshold;
		self.storage.append(&mut displaced.ranges);
	}

	/// Drop pending updates, this unsafe as it should
	pub fn undo_ranges_treshold_update_clear_pending(&mut self) {
		self.removed.clear();
		self.changed.clear();
	}

	/// Revert some ranges, without any way to revert.
	/// Returning ranges for the parent index.
	pub fn revert(&mut self, branch_ix: u64) -> BranchRanges {
		let parent_branch_index = if branch_ix != 0 {
			self.drop_state(branch_ix)
				// silenced error
				.unwrap_or(0)
		} else {
			0
		};

		self.branch_ranges_from_cache(parent_branch_index)
	}

	/// Write the range list updates to the database transaction.
	pub fn prepare_transaction(
		&mut self,
		tx: &mut DBTransaction,
		column: Option<u32>,
		treshold_key: &[u8],
		last_branch_index_key: &[u8],
		column_branch_range: Option<u32>,
	) {
		// ranges info updates
		if self.treshold != self.treshold_original {
			tx.put_vec(column, treshold_key, self.treshold.encode());
		}
		if self.last_index != self.last_index_original {
			tx.put_vec(column, last_branch_index_key, self.last_index.encode());
		}
		for changed in std::mem::replace(&mut self.changed, BTreeSet::new()).into_iter() {
			if !self.removed.contains(&changed) {
				if let Some(Some(states)) = self.storage.get(&changed) {
					tx.put_vec(column_branch_range, &index_to_key(changed)[..], states.encode());
				}
			}
		}
		for removed in std::mem::replace(&mut self.removed, BTreeSet::new()).into_iter() {
			tx.delete(column_branch_range, &index_to_key(removed)[..]);
		}

	}

	#[cfg(test)]
	pub fn contains_range(&self, branch_index: u64, size: u64) -> bool {
		if let Some(Some(s)) = self.storage.get(&branch_index) {
			(s.state_ref().end - s.state_ref().start) == size
		} else {
			false
		}
	}

}

/// Read a stored branch treshold corresponding to
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
			Ok(i) => Ok(Some(i)),
			Err(err) => Err(error::Error::Backend(
				format!("Error decoding branch index treshold: {}", err)
			)),
		}
	} else {
		Ok(None)
	}
}

/// Read a stored branch treshold corresponding to
/// a branch index bellow which there is only valid values.
/// TODO EMCH this should be in db: TODO create a BranchIndexBackend
/// that db implements.
pub fn read_branch_last_index(
	db: &dyn KeyValueDB,
	key_lookup_col: Option<u32>,
	key: &[u8],
) -> Result<u64, error::Error> {
	if let Some(buffer) = db.get(
		key_lookup_col,
		key,
	).map_err(|err| error::Error::Backend(format!("{}", err)))? {
		match Decode::decode(&mut &buffer[..]) {
			Ok(i) => Ok(i),
			Err(err) => Err(error::Error::Backend(
				format!("Error decoding branch last index: {}", err)
			)),
		}
	} else {
		Ok(0)
	}
}

/// Read a stored branch ranges.
/// TODO EMCH this should be in db: TODO create a BranchIndexBackend
/// that db implements.
pub fn read_branch_range(
	db: &dyn KeyValueDB,
	key_lookup_col: Option<u32>,
	branch_index: u64,
) -> Result<Option<StatesBranch>, error::Error> {
	if let Some(buffer) = db.get(
		key_lookup_col,
		&index_to_key(branch_index)[..],
	).map_err(|err| error::Error::Backend(format!("{}", err)))? {
		match Decode::decode(&mut &buffer[..]) {
			Ok(i) => Ok(Some(i)),
			Err(err) => Err(error::Error::Backend(
				format!("Error decoding branch range: {}", err)
			)),
		}
	} else {
		Ok(None)
	}
}
/// Read a stored branch ranges using a cache
/// TODO EMCH this should be in db: TODO create a BranchIndexBackend
/// that db implements.
pub fn read_branch_range_with_cache<'a>(
	db: &dyn KeyValueDB,
	key_lookup_col: Option<u32>,
	branch_index: u64,
	cache: &'a mut BTreeMap<u64, Option<StatesBranch>>,
) -> Result<Option<&'a StatesBranch>, error::Error> {
	match cache.entry(branch_index) {
		Entry::Occupied(e) => {
			Ok(e.into_mut().as_ref())
		},
		Entry::Vacant(e) => {
			Ok(e.insert(
				read_branch_range(db, key_lookup_col, branch_index)?
			).as_ref())
		},
	}
}

// TODO EMCH move to db util to
fn index_to_key(index: u64) -> [u8; 8] {
	// using be encoding, to get key ordering similar as index
	index.to_be_bytes()
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[derive(Encode, Decode)]
pub struct StatesBranch {
	state: LinearStatesRef,
	can_append: bool,
	parent_branch_index: u64,
}


// TODO EMCH temporary structs until merge with historied-data branch.

type LinearStates = StatesBranch;

impl Default for LinearStates {
	// initialize with one element
	fn default() -> Self {
		Self::new(0, 0)
	}
}

impl LinearStates {
	pub fn new(offset: u64, parent_branch_index: u64) -> Self {
		let offset = offset as u64;
		LinearStates {
			state: LinearStatesRef {
				start: offset,
				end: offset + 1,
			},
			can_append: true,
			parent_branch_index,
		}
	}

	pub fn state_ref(&self) -> LinearStatesRef {
		self.state.clone()
	}

	pub fn has_deleted_index(&self) -> bool {
		!self.can_append
	}

	pub fn add_state(&mut self) -> bool {
		if !self.has_deleted_index() {
			self.state.end += 1;
			true
		} else {
			false
		}
	}

	/// return possible dropped state
	pub fn drop_state(&mut self) -> Option<u64> {
		if self.state.end - self.state.start > 0 {
			self.state.end -= 1;
			Some(self.state.end)
		} else {
			None
		}
	}

	/// Return true if state exists.
	pub fn get_state(&self, index: u64) -> bool {
		index < self.state.end && index >= self.state.start
	}

	/// Return true if you can add this index.
	pub fn can_add(&self, index: u64) -> bool {
		index == self.state.end
	}

	pub fn latest_ix(&self) -> Option<u64> {
		if self.state.end - self.state.start > 0 {
			Some(self.state.end - 1)
		} else {
			None
		}
	}

}

// TODO EMCH end from historied - data

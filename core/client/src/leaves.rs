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

use std::collections::{BTreeMap, BTreeSet, HashMap, btree_map::Entry};
use std::cmp::Reverse;
use kvdb::{KeyValueDB, DBTransaction};
use sr_primitives::traits::SimpleArithmetic;
use codec::{Encode, Decode};
use crate::error;
use std::hash::Hash as StdHash;
use std::convert::TryInto;

#[derive(Debug, Clone, PartialEq, Eq)]
struct LeafSetItem<H, N> {
	hash: H,
	number: Reverse<N>,
	branch_ranges: BranchRanges,
}

#[derive(Clone)]
/// A displaced leaf after import.
#[must_use = "Displaced items from the leaf set must be handled."]
pub struct ImportDisplaced<H, N> {
	new_hash: H,
	displaced: LeafSetItem<H, N>,
}

#[derive(Clone)]
/// Displaced leaves after finalization.
#[must_use = "Displaced items from the leaf set must be handled."]
pub struct FinalizationDisplaced<H, N> {
	leaves: BTreeMap<Reverse<N>, Vec<(H, BranchRanges)>>,
	leaves_final: Vec<(Reverse<N>, H, BranchRanges)>,
	ranges: BTreeMap<u64, Option<LinearStates>>,
	treshold: u64,
}

impl<H, N: Ord> FinalizationDisplaced<H, N> {
	/// Merge with another. This should only be used for displaced items that
	/// are produced within one transaction of each other.
	pub fn merge(&mut self, mut other: Self) {
		// this will ignore keys that are in duplicate, however
		// if these are actually produced correctly via the leaf-set within
		// one transaction, then there will be no overlap in the keys.
		self.leaves.append(&mut other.leaves);
		self.leaves_final.append(&mut other.leaves_final);
	}
}

/// list of leaf hashes ordered by number (descending).
/// stored in memory for fast access.
/// this allows very fast checking and modification of active leaves.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LeafSet<H, N> {
	storage: BTreeMap<Reverse<N>, Vec<(H, BranchRanges)>>,
	// TODO EMCH check if branches from LeafSetItem is of any need here.
	// at this time only its last item seems read.
	pending_added: Vec<LeafSetItem<H, N>>,
	pending_removed: Vec<H>,
	ranges: RangeSet,
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

impl RangeSet {
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
		loop {
			if let Some(Some(StatesBranch{ state, parent_branch_index, .. })) = self.storage.get(&branch_index) {
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
			ranges: RangeSet {
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

	/// Read the leaf list from the DB, using given prefix for keys.
	pub fn read_from_db(
		db: &dyn KeyValueDB,
		column: Option<u32>,
		prefix: &[u8],
		treshold_key: &[u8],
		last_branch_index_key: &[u8],
		column_block_numbers: Option<u32>,
		column_branch_range: Option<u32>,
	) -> error::Result<Self> {
		let mut storage = BTreeMap::new();

		let treshold = read_branch_state_treshold(db, column, treshold_key)?
			.unwrap_or(DEFAULT_START_TRESHOLD);
		let last_index = read_branch_last_index(db, column, last_branch_index_key)?;
		let mut ranges = RangeSet {
			storage: BTreeMap::new(),
			last_index_original: last_index,
			last_index,
			treshold_original: treshold,
			treshold,
			changed: BTreeSet::new(),
			removed: BTreeSet::new(),
		};
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
			let branch_index = branch_index.unwrap_or(0);
			let state_ref = ranges.read_branch_ranges(
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
			ranges,
		})
	}

	/// update the leaf list on import. returns a displaced leaf if there was one.
	pub fn import(
		&mut self,
		hash: H,
		number: N,
		parent_hash: H,
		parent_branch_index: u64,
	) -> (Option<ImportDisplaced<H, N>>, u64) {
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

		let (branch_ranges, branch_index) = if let Some(imported) = displaced.as_ref() {
			let mut branch_ranges = imported.displaced.branch_ranges.clone();
			let anchor_index = self.ranges.add_state(parent_branch_index, &number)
				.expect("coherent branch index state"); // TODO EMCH fail in add_state
			if anchor_index == parent_branch_index {
				branch_ranges.pop();
			}
			branch_ranges.push(self.ranges.state_ref(anchor_index).expect("added just above"));
			(branch_ranges, anchor_index)
		} else {
			let anchor_index = self.ranges.add_state(parent_branch_index, &number)
				.expect("coherent branch index state"); // TODO EMCH fail in add_state
			(vec![self.ranges.state_ref(anchor_index).expect("added just above")], anchor_index)
		};

		self.insert_leaf(Reverse(number.clone()), hash.clone(), branch_ranges.clone());
		self.pending_added.push(LeafSetItem { hash, number: Reverse(number), branch_ranges });
		(displaced, branch_index)
	}

	/// Note a block height finalized, displacing all leaves with number less than the finalized block's.
	///
	/// Although it would be more technically correct to also prune out leaves at the
	/// same number as the finalized block, but with different hashes, the current behavior
	/// is simpler and our assumptions about how finalization works means that those leaves
	/// will be pruned soon afterwards anyway.
	///
	/// TODO EMCH this way of doing things mean that there is a synchronous removal of data on
	/// finalize -> this is not really what we want as we should only move treshold on data gc (this
	/// currently implies a full gc on finalisation).
	pub fn finalize_height(&mut self, number: N, branch_index: u64, full: bool) -> FinalizationDisplaced<H, N> {
		let boundary = if number == N::zero() {
			return FinalizationDisplaced {
				leaves: BTreeMap::new(),
				leaves_final: Vec::new(),
				treshold: self.ranges.treshold,
				ranges: BTreeMap::new(),
			};
		} else {
			number - N::one()
		};

		let (displaced, displaced_final) = if branch_index == 0 || !full {
			// just remove leaf that we know are behind this index.
			(self.storage.split_off(&Reverse(boundary)), Default::default())
		} else {
			// remove leafs that do not contain branch_index in their history
			let displaced = self.storage.split_off(&Reverse(boundary));
			let mut displaced_final = Vec::new();
			for (reverse_number, blocks) in std::mem::replace(&mut self.storage, BTreeMap::new()) {
				for (hash, ranges) in blocks.into_iter() {
					let mut find = false;
					for range in ranges.iter() {
						if range.branch_index == branch_index {
							find = true;
							break;
						}
					}
					if find {
						self.storage.entry(reverse_number.clone())
								.or_insert_with(Default::default)
								.push((hash, ranges));
					} else {
						displaced_final.push((reverse_number.clone(), hash, ranges));
					}
				}
			}
			(displaced, displaced_final)
		};
		self.pending_removed.extend(
			displaced.values().flat_map(|h| h.iter().map(|(h, _)| h.clone()))
		);
		self.pending_removed.extend(
			displaced_final.iter().map(|(_, h, _)| h.clone())
		);

		// range set update
		let old_treshold = self.ranges.treshold;
		self.ranges.treshold = branch_index;
		let removed_ranges = if branch_index == 0 || !full {
			// remove cached value under treshold only
			let new_storage = self.ranges.storage.split_off(&(self.ranges.treshold));
			std::mem::replace(&mut self.ranges.storage, new_storage)
		} else {
			let finalize_branches_set: BTreeSet<_> = self.ranges.branch_ranges_from_cache(branch_index)
				.into_iter().map(|r| r.branch_index).collect();
			let new_storage = self.ranges.storage.split_off(&(self.ranges.treshold));
			let mut removed = std::mem::replace(&mut self.ranges.storage, new_storage);
			for (index, state) in self.ranges.storage.iter_mut() {
				if !finalize_branches_set.contains(&index) {
					removed.insert(*index, state.take());
				}
			}
			removed
		};
		self.ranges.removed.extend(removed_ranges.keys().cloned());

		// TODO EMCH here we also do add branch range update/delete and revert content
		// (happening in cache only).
		FinalizationDisplaced {
			leaves: displaced,
			leaves_final: displaced_final,
			ranges: removed_ranges,
			treshold: old_treshold,
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
		branch_ix: u64,
		parent_hash: H,
		parent_branch_ix: u64,
		tx: &mut DBTransaction,
	) {
		let parent_branch_index = if branch_ix != 0 {
			self.ranges.drop_state(branch_ix)
				// silenced error
				.unwrap_or(0)
		} else {
			0
		};

		let parent_branch_ranges = self.ranges.branch_ranges_from_cache(parent_branch_index);

		self.insert_leaf(Reverse(number.clone() - N::one()), parent_hash, parent_branch_ranges);
		self.remove_leaf(&Reverse(number), &hash);
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
		treshold_key: &[u8],
		last_branch_index_key: &[u8],
		column_block_numbers: Option<u32>,
		column_branch_range: Option<u32>,
	) {
		let mut buf = prefix.to_vec();
    // TODO EMCH no need for portablility here always write new version.
		for LeafSetItem { hash, number, branch_ranges } in self.pending_added.drain(..) {
			hash.using_encoded(|s| buf.extend(s));
			tx.put_vec(column, &buf[..], number.0.encode());
			buf.truncate(prefix.len()); // reuse allocation.

			if let Some(last) = branch_ranges.last() {
				tx.put_vec(column_block_numbers, hash.as_ref(), last.branch_index.encode());
			}
		}
		for hash in self.pending_removed.drain(..) {
			hash.using_encoded(|s| buf.extend(s));
			tx.delete(column, &buf[..]);
			buf.truncate(prefix.len()); // reuse allocation.

			tx.delete(column_block_numbers, hash.as_ref());
		}

		// ranges info updates
		if self.ranges.treshold != self.ranges.treshold_original {
			tx.put_vec(column, treshold_key, self.ranges.treshold.encode());
		}
		if self.ranges.last_index != self.ranges.last_index_original {
			tx.put_vec(column, last_branch_index_key, self.ranges.last_index.encode());
		}
		for changed in std::mem::replace(&mut self.ranges.changed, BTreeSet::new()).into_iter() {
			if !self.ranges.removed.contains(&changed) {
				if let Some(Some(states)) = self.ranges.storage.get(&changed) {
					tx.put_vec(column_branch_range, &index_to_key(changed)[..], states.encode());
				}
			}
		}
		for removed in std::mem::replace(&mut self.ranges.removed, BTreeSet::new()).into_iter() {
			tx.delete(column_branch_range, &index_to_key(removed)[..]);
		}

	}

	#[cfg(test)]
	fn contains(&self, number: N, hash: H) -> bool {
		self.storage.get(&Reverse(number))
			.map_or(false, |hashes| hashes.iter().find(|(h, _)| h == &hash).is_some())
	}

	fn insert_leaf(&mut self, number: Reverse<N>, hash: H, branch_ranges: BranchRanges) {
		self.storage.entry(number).or_insert_with(Vec::new).push((hash, branch_ranges));
	}

	// returns a branch index if this leaf was contained, nothing otherwise.
	fn remove_leaf(&mut self, number: &Reverse<N>, hash: &H) -> Option<BranchRanges> {
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
		for (reverse_number, hash, ranges) in displaced.leaves_final.into_iter() {
			self.inner.storage.entry(reverse_number)
				.or_insert_with(Default::default)
				.push((hash, ranges))
		}
		self.inner.ranges.treshold = displaced.treshold;
		self.inner.ranges.storage.append(&mut displaced.ranges);
	}
}

impl<'a, H: 'a, N: 'a> Drop for Undo<'a, H, N> {
	fn drop(&mut self) {
		self.inner.pending_added.clear();
		self.inner.pending_removed.clear();
		self.inner.ranges.removed.clear();
		self.inner.ranges.changed.clear();
	}
}

/// Read a stored branch index for a block hash.
pub fn read_branch_index<H: AsRef<[u8]> + Clone>(
	db: &dyn KeyValueDB,
	key_lookup_col: Option<u32>,
	id: H,
) -> Result<Option<u64>, error::Error> {
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

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn it_works() {
		let mut set = LeafSet::new();
		let (_, anchor_1) = set.import([0u8], 0u32, [0u8], 0);

		let (_, anchor_2) = set.import([1_1], 1, [0], anchor_1);
		let (_, anchor_3) = set.import([2_1], 2, [1_1], anchor_2);
		set.import([3_1], 3, [2_1], anchor_3);

		assert!(set.contains(3, [3_1]));
		assert!(!set.contains(2, [2_1]));
		assert!(!set.contains(1, [1_1]));
		assert!(!set.contains(0, [0]));

		set.import([2_2], 2, [1_1], anchor_2);

		assert!(set.contains(3, [3_1]));
		assert!(set.contains(2, [2_2]));
	}

	#[test]
	fn flush_to_disk() {
		const PREFIX: &[u8] = b"abcdefg";
		const TRESHOLD: &[u8] = b"hijkl";
		const LAST_INDEX: &[u8] = b"mnopq";
		let db = ::kvdb_memorydb::create(3);

		let mut set = LeafSet::new();
		let (_, anchor_1) = set.import([0u8], 0u32, [0u8], 0);

		let (_, anchor_2) = set.import([1_1], 1, [0], anchor_1);
		let (_, anchor_3) = set.import([2_1], 2, [1_1], anchor_2);
		set.import([3_1], 3, [2_1], anchor_3);

		let mut tx = DBTransaction::new();
	
		set.prepare_transaction(&mut tx, None, PREFIX, TRESHOLD, LAST_INDEX, Some(1), Some(2));
		db.write(tx).unwrap();

		let set2 = LeafSet::read_from_db(&db, None, PREFIX, TRESHOLD, LAST_INDEX, Some(1), Some(2)).unwrap();
		assert_eq!(set, set2);

	}

	#[test]
	fn two_leaves_same_height_can_be_included() {
		let mut set = LeafSet::new();

		set.import([1_1u8], 10u32, [0u8], 0);
		set.import([1_2], 10, [0], 0);

		assert!(set.storage.contains_key(&Reverse(10)));
		assert!(set.contains(10, [1_1]));
		assert!(set.contains(10, [1_2]));
		assert!(!set.contains(10, [1_3]));
	}

	fn build_finalize_set() ->  (LeafSet<[u8; 2], u32>, u64) {
		let mut set = LeafSet::new();
		set.import([10u8, 1u8], 10u32, [0u8, 0u8], 0);
		let (_, anchor_1) = set.import([10, 2], 10, [0u8, 0u8], 0);
		set.import([11, 1], 11, [10, 2], anchor_1);
		let (_, finalize) = set.import([11, 2], 11, [10, 2], anchor_1);
		let (_, anchor_2) = set.import([11, 123], 11, [10, 2], anchor_1);
		set.import([12, 1], 12, [11, 123], anchor_2);
		(set, finalize)
	}

	#[test]
	fn finalization_consistent_with_disk() {
		const PREFIX: &[u8] = b"prefix";
		const TRESHOLD: &[u8] = b"hijkl";
		const LAST_INDEX: &[u8] = b"mnopq";
		let with_full_finalize = |full: bool| {
			let db = ::kvdb_memorydb::create(3);

			let (mut set, finalize) = build_finalize_set();

			assert!(set.contains(10, [10, 1]));

			let mut tx = DBTransaction::new();
			set.prepare_transaction(&mut tx, None, PREFIX, TRESHOLD, LAST_INDEX, Some(1), Some(2));
			db.write(tx).unwrap();

			// TODO EMCH check ranges to
			let _ = set.finalize_height(11, finalize, full);
			let mut tx = DBTransaction::new();
			set.prepare_transaction(&mut tx, None, PREFIX, TRESHOLD, LAST_INDEX, Some(1), Some(2));
			db.write(tx).unwrap();

			assert!(set.contains(11, [11, 1]));
			assert!(set.contains(11, [11, 2]));
			assert!(set.contains(12, [12, 1]));
			assert!(!set.contains(10, [10, 2]));

			let mut set2 = LeafSet::read_from_db(&db, None, PREFIX, TRESHOLD, LAST_INDEX, Some(1), Some(2)).unwrap();
			assert_eq!(set, set2);
		};
		with_full_finalize(false); // TODO more targeted test as the branch refs differs due to treshold
		with_full_finalize(true);
	}

	#[test]
	fn undo_finalization() {
		let with_full_finalize = |full: bool| {
			let (mut set, finalize) = build_finalize_set();

			let displaced = set.finalize_height(11, finalize, full);
			assert!(!set.contains(10, [10, 1]));

			set.undo().undo_finalization(displaced);
			assert!(set.contains(10, [10, 1]));
			set
		};
		with_full_finalize(false);
		with_full_finalize(true);
	}
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[derive(Encode, Decode)]
pub struct StatesBranchRef {
	pub branch_index: u64,
	pub state: LinearStatesRef,
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[derive(Encode, Decode)]
pub struct StatesBranch {
	state: LinearStatesRef,
	can_append: bool,
	parent_branch_index: u64,
}


// TODO EMCH temporary structs until merge with historied-data branch.

/// This is a simple range, end non inclusive.
#[derive(Debug, Clone, PartialEq, Eq)]
#[derive(Encode, Decode)]
pub struct LinearStatesRef {
	start: u64,
	end: u64,
}

/// Reference to state that is enough for query updates, but not
/// for gc.
/// Values are ordered by branch_ix,
/// and only a logic branch path should be present.
///
/// Note that an alternative could be a pointer to a full state
/// branch for a given branch index, here we use an in memory
/// copied representation in relation to an actual use case.
pub type BranchRanges = Vec<StatesBranchRef>;

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

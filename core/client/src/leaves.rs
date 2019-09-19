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
use crate::branches::{RangeSet, TresholdUpdateDisplaced};
use primitives::offstate::BranchRanges;

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
	// TODO range set cache at this level see branch_range function define for leafset. 
	// TODO EMCH put under rw lock and put BranchRange in it (put arc in branch range
	// to lower mem consumption).
	ranges: RangeSet,
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
			ranges: RangeSet::default(),
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
		let mut ranges = RangeSet::read_from_db(
			db,
			column,
			treshold_key,
			last_branch_index_key,
		)?;
		let mut storage = BTreeMap::new();

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

		let (branch_ranges, branch_index) = self.ranges.import(
			&number,
			parent_branch_index,
			displaced.as_ref().map(|d| d.displaced.branch_ranges.clone()),
		);

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
	pub fn finalize_height(&mut self, number: N, branch_index: u64, full: bool) -> FinalizationDisplaced<H, N> {
		let boundary = if number == N::zero() {
			return FinalizationDisplaced {
				leaves: BTreeMap::new(),
				leaves_final: Vec::new(),
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

		FinalizationDisplaced {
			leaves: displaced,
			leaves_final: displaced_final,
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
		self.ranges.update_finalize_treshold(branch_index, full)
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
	) {
		let parent_branch_ranges = self.ranges.revert(branch_ix);

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

		self.ranges.prepare_transaction( 
			tx,
			column,
			treshold_key,
			last_branch_index_key,
			column_branch_range,
		);

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

	/// fetch branch ranges for hash. Missing block result in empty branch ranges,
	/// which can still be usefull to access finalize default value.
	pub fn branch_ranges(&self, hash: &H) -> Result<BranchRanges, error::Error> {
		// note that cache uses a rwlock (we do not want to borrow write when no cache updates).
		unimplemented!("TODO EMCH implement get caching in leaves and get from leaves no caching.")
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
		displaced.leaves.append(&mut self.inner.storage);
		std::mem::replace(&mut self.inner.storage, displaced.leaves);
		for (reverse_number, hash, ranges) in displaced.leaves_final.into_iter() {
			self.inner.storage.entry(reverse_number)
				.or_insert_with(Default::default)
				.insert(0, (hash, ranges))
		}
	}

	/// Undo a branch treshold update operation by providing the delta.
	pub fn undo_ranges_treshold_update(&mut self, displaced: TresholdUpdateDisplaced) {
		self.inner.ranges.undo_ranges_treshold_update(displaced);
	}

}

impl<'a, H: 'a, N: 'a> Drop for Undo<'a, H, N> {
	fn drop(&mut self) {
		self.inner.pending_added.clear();
		self.inner.pending_removed.clear();
		self.inner.ranges.undo_ranges_treshold_update_clear_pending();
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

		let mut set2 = LeafSet::read_from_db(&db, None, PREFIX, TRESHOLD, LAST_INDEX, Some(1), Some(2)).unwrap();
		// reset original value to be comparable with set
		*set2.ranges.last_index_original() = 0;
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

	// set:
	// 0
	// |> 1: [10,1]
	// |> 2: [10,2] [11,1]
	//       |> 3:  [11,2]
	//       |> 4:  [11,123] [12,1]
	// full finalize: 3
	// 0
	// |> 2: [10,2]
	//       |> 3:  [11,2]
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
		let with_full_finalize = |
			full: bool,
			nodes: &[(u32, [u8;2])],
			not_nodes: &[(u32, [u8;2])],
			ranges: &[(u64, u64)],
			not_ranges: &[(u64, u64)],
			ranges2: Option<&[(u64, u64)]>,
		| {
			let db = ::kvdb_memorydb::create(3);

			let (mut set, finalize) = build_finalize_set();

			assert!(set.contains(10, [10, 1]));
			assert!(set.contains(11, [11, 2]));

			let mut tx = DBTransaction::new();
			set.prepare_transaction(&mut tx, None, PREFIX, TRESHOLD, LAST_INDEX, Some(1), Some(2));
			db.write(tx).unwrap();

			// TODO EMCH check ranges to
			let _ = set.finalize_height(11, finalize, full);
			let mut tx = DBTransaction::new();
			set.prepare_transaction(&mut tx, None, PREFIX, TRESHOLD, LAST_INDEX, Some(1), Some(2));
			db.write(tx).unwrap();

			let mut set2 = LeafSet::read_from_db(&db, None, PREFIX, TRESHOLD, LAST_INDEX, Some(1), Some(2))
				.unwrap();

			for node in nodes {
				assert!(set.contains(node.0, node.1), "contains {:?} {:?}", node.0, node.1);
				assert!(set2.contains(node.0, node.1), "contains2 {:?} {:?}", node.0, node.1);
			}
			for node in not_nodes {
				assert!(!set.contains(node.0, node.1), "contains {:?} {:?}", node.0, node.1);
				assert!(!set2.contains(node.0, node.1), "not contains2 {:?} {:?}", node.0, node.1);
			}
	
			// test ranges changes
			if let Some(range2) = ranges2 {
				let mut ranges2 = set.ranges.clone();
				let _ = ranges2.test_finalize_full(finalize);
				for (range, size) in range2 {
					assert!(ranges2.contains_range(*range, *size), "{} {}", range, size);
				}
			}

			let _ = set.ranges.update_finalize_treshold(finalize, full);
			let _ = set2.ranges.update_finalize_treshold(finalize, full);

			assert!(set.ranges.range_treshold() == 3);
			assert!(set2.ranges.range_treshold() == 3);

			for (node, (range, size)) in nodes.into_iter().zip(ranges) {
				assert!(set.contains(node.0, node.1), "contains {:?} {:?}", node.0, node.1);
				assert!(set2.contains(node.0, node.1), "contains2 {:?} {:?}", node.0, node.1);
				assert!(set.ranges.contains_range(*range, *size), "contains {:?}", range);
				assert!(set2.ranges.contains_range(*range, *size), "contains2 {:?}", range);
			}
			for (node, (range, size)) in not_nodes.into_iter().zip(not_ranges) {
				assert!(!set.contains(node.0, node.1), "contains {:?} {:?}", node.0, node.1);
				assert!(!set2.contains(node.0, node.1), "not contains2 {:?} {:?}", node.0, node.1);
				assert!(!set.ranges.contains_range(*range, *size), "contains {:?}", range);
				assert!(!set2.ranges.contains_range(*range, *size), "contains2 {:?}", range);
			}
	
		};

		with_full_finalize(false,
			&[(11, [11, 1]), (11, [11,2]), (12, [12,1])][..],
			&[(10, [10, 1]), (10, [10, 2]), (11, [11,123])][..],
			&[(3, 1), (4, 2)][..],
			&[(1, 1), (2, 2)][..],
			None,
		);
		with_full_finalize(true,
			&[(11, [11,2])][..],
			&[(10, [10, 1]), (10, [10, 2]), (11, [11,1]), (11, [11,123]), (12, [12,1])][..],
			&[(3, 1)][..],
			&[(1, 1), (2, 2), (4, 2)][..],
			// here 2, 1 test state removal from finalize branch
			Some(&[(2, 1), (3, 1)][..]),
		);
	}

	#[test]
	fn undo_finalization() {
		let with_full_finalize = |full: bool| {
			let (mut set, finalize) = build_finalize_set();

			let reference_set = set.clone();

			let displaced = set.finalize_height(11, finalize, full);
			assert!(!set.contains(10, [10, 1]));

			set.undo().undo_finalization(displaced);
			assert!(set.contains(10, [10, 1]));
			assert_eq!(set.storage, reference_set.storage);

			// test ranges changes
			let displaced = set.ranges.update_finalize_treshold(finalize, full);
			set.undo().undo_ranges_treshold_update(displaced);

			assert_eq!(set.ranges.inner_storage(), reference_set.ranges.inner_storage());
		};

		with_full_finalize(false);
		with_full_finalize(true);
	}
}

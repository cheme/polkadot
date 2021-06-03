// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Structure and implementation used for caching `next_key` calls.
//! This uses ordered mapping with key intervals, see `CachedInterval`.


use std::collections::{HashMap, BTreeMap};
use sp_core::storage::ChildInfo;
use super::{EstimateSize,
};

pub(super) struct LRUOrderedKeys<K> {
	/// We use a BTreeMap for storage internally.
	intervals: BTreeMap<K, Box<KeyOrderedEntry<K>>>,
	/// Intervals for child storages.
	child_intervals: HashMap<Vec<u8>, BTreeMap<K, Box<KeyOrderedEntry<K>>>>,
	/// Current total size of contents.
	used_size: usize,
	/// Limit size of contents.
	limit: usize,
	/// Dummy `KeyOrderedEntry` containing `next` pointer
	/// as the oldest entry.
	/// `prev` pointer is used as the lru entry, meaning
	/// if `prev` equals to `next` the lru structure is empty.
	lru_bound: Box<KeyOrderedEntry<K>>,
}

#[derive(Default)]
pub(super) struct LocalOrderedKeys<K: Ord> {
	/// We use a BTreeMap for storage internally.
	intervals: BTreeMap<K, CachedInterval>,
	/// Intervals for child storages.
	child_intervals: HashMap<Vec<u8>, BTreeMap<K, CachedInterval>>,
}
	
struct KeyOrderedEntry<K> {
	/// Entry accessed before.
	prev: *mut KeyOrderedEntry<K>,
	/// Entry access after.
	next: *mut KeyOrderedEntry<K>,
	/// Used to remove from btreemap.
	/// Specialized lru struct would not need it.
	key: K,
	/// When intervals are in child cache (also only use
	/// to remove from cache).
	child_storage_key: Option<Vec<u8>>,
	/// Actual content.
	state: CachedInterval,
}

unsafe impl<K: Send> Send for LRUOrderedKeys<K> {}
unsafe impl<K: Sync> Sync for LRUOrderedKeys<K> {}

impl<K: Default + EstimateSize> KeyOrderedEntry<K> {
	fn empty() -> Box<Self> {
		let mut lru_bound = Box::new(KeyOrderedEntry {
			prev: std::ptr::null_mut(),
			next: std::ptr::null_mut(),
			key: Default::default(),
			child_storage_key: None,
			state: CachedInterval::Prev,
		});
		let ptr: *mut KeyOrderedEntry<K> = (&mut lru_bound).as_mut();
		lru_bound.prev = ptr;
		lru_bound.next = ptr;
		lru_bound
	}
	fn estimate_size(&self) -> usize {
		self.key.estimate_size() * 2 // apply 2 to account for btreemap internal key storage.
			+ self.child_storage_key.as_ref().map(|k| k.len()).unwrap_or(0) + 1
			+ 2 * 4 // assuming 64 bit arch
			+ 1
	}
}

impl<K> KeyOrderedEntry<K> {
	fn detach(
		&mut self,
	) -> *mut KeyOrderedEntry<K> {
		let prev = self.prev;
		let next = self.next;
		unsafe {
			let s = (*prev).next;
			(*prev).next = next;
			(*next).prev = prev;
			(*s).next = s;
			(*s).prev = s;
			s
		}
	}
	fn lru_touched(
		&mut self,
		lru_bound: &mut Box<KeyOrderedEntry<K>>,
	) {
		let s = self.detach();
		unsafe {
			let ptr: *mut KeyOrderedEntry<K> = lru_bound.as_mut();
			(*s).next = ptr;
			(*s).prev = (*lru_bound).prev;
			(*(*s).prev).next = s;
		}
		(*lru_bound).prev = s;
	}
	fn lru_touched_opt(
		&mut self,
		lru_bound: &mut Option<&mut Box<KeyOrderedEntry<K>>>,
	) {
		lru_bound.as_mut().map(|b| self.lru_touched(b));
	}
}

impl<K: Default + Ord + Clone + EstimateSize + 'static> LRUOrderedKeys<K> {
	pub(super) fn new(limit: usize) -> Self {
		LRUOrderedKeys {
			intervals: BTreeMap::new(),
			child_intervals: HashMap::new(),
			used_size: 0,
			limit,
			lru_bound: KeyOrderedEntry::empty(),
		}
	}

	fn lru_pop(
		&mut self
	) -> bool {
		if self.lru_bound.prev == self.lru_bound.next {
			return false; // empty
		}

		let to_rem = self.lru_bound.next;
		// unsafe { (*to_rem).detach() }; detach is called in remove_interval_entry
		let intervals = if let Some(child) = unsafe { (*to_rem).child_storage_key.as_ref() } {
			self.child_intervals.get_mut(child)
				.expect("Removed only when no entry")
		} else {
			&mut self.intervals
		};
	
		let key = unsafe { &(*to_rem).key };
		let size = Self::remove_interval_entry(intervals, key, false);
		self.used_size -= size;
		true
	}

	pub(super) fn next_storage_key(&mut self, key: &K, child: Option<&ChildInfo>) -> Option<Option<K>> {
		let intervals = if let Some(info) = child {
			if let Some(intervals) = self.child_intervals.get_mut(info.storage_key()) {
				intervals
			} else {
				return None;
			}
		} else {
			&mut self.intervals
		};
		Self::next_storage_key_inner(intervals, key, &mut Some(&mut self.lru_bound))
	}

	fn next_storage_key_inner(
		intervals: &mut BTreeMap<K, Box<KeyOrderedEntry<K>>>,
		key: &K,
		lru_bound: &mut Option<&mut Box<KeyOrderedEntry<K>>>,
	) -> Option<Option<K>> {
		let mut iter = intervals.range_mut(key..);
		let n = iter.next().map(|(k, v)| (k, v.state.clone(), v));
		match n {
			Some((next_key, CachedInterval::Next, v))
			| Some((next_key, CachedInterval::Both, v)) if next_key == key => {
				v.lru_touched_opt(lru_bound);
				let nn = iter.next().map(|(k, v)| {
					v.lru_touched_opt(lru_bound);
					(k, v.state.clone())
				});
				match nn {
					Some((next_key, CachedInterval::Prev))
					| Some((next_key, CachedInterval::Both)) => Some(Some(next_key.clone())),
					Some((_next_key, CachedInterval::Next)) => None, // Should be unreachable
					None => Some(None),
				}
			},
			Some((next_key, CachedInterval::Prev, _v)) if next_key == key => None,
			Some((_next_key, CachedInterval::Next, _v)) => None,
			Some((next_key, _, v)) => {
				v.lru_touched_opt(lru_bound);
				let result = Some(Some(next_key.clone()));
				let nb = intervals.range_mut(..key).next_back().map(|(k, v)| {
					v.lru_touched_opt(lru_bound);
					(k, v.state.clone())
				});
				debug_assert!({
					match nb {
						Some((_prev_key, CachedInterval::Next))
						| Some((_prev_key, CachedInterval::Both)) => true,
						_ => false,
					}
				});
				result
			},
			None => {
				let nb = intervals.range_mut(..key).next_back().map(|(k, v)| (k, v.state.clone(), v));
				match nb {
					Some((_prev_key, CachedInterval::Next, v))
					| Some((_prev_key, CachedInterval::Both, v)) => {
						v.lru_touched_opt(lru_bound);
						Some(None)
					},
					_ => None,
				}
			},
		}
	}

	pub(super) fn merge_local_cache(&mut self, local: &mut LocalOrderedKeys<K>) {
		// start with child trie. Notice there is no fair lru management here.
		for (child, keys) in local.child_intervals.drain() {
			self.merge_local_cache_inner(&keys, Some(&child));
		}
		self.merge_local_cache_inner(&local.intervals, None);
		local.intervals = BTreeMap::new();
	}

	fn merge_local_cache_inner(
		&mut self,
		keys: &BTreeMap<K, CachedInterval>,
		child: Option<&Vec<u8>>,
	) {
		// No conflict of existing interval should happen if we correctly do `enact_value_changes` of
		// previous block.
		let intervals = if let Some(info) = child {
			if let Some(intervals) = self.child_intervals.get_mut(info) {
				intervals
			} else {
				self.child_intervals.insert(info.clone(), Default::default());
				return self.merge_local_cache_inner(keys, child);
			}
		} else {
			&mut self.intervals
		};

		for (k, interval) in keys {
			self.used_size += Self::add_valid_interval_no_lru(intervals, k, child, interval.clone(), &mut self.lru_bound);
		}
		self.apply_lru_limit();
	}

	// `no_lru` only indicate no lru limit applied.
	fn add_valid_interval_no_lru(
		intervals: &mut BTreeMap<K, Box<KeyOrderedEntry<K>>>,
		key: &K,
		child: Option<&Vec<u8>>,
		state: CachedInterval,
		lru_bound: &mut Box<KeyOrderedEntry<K>>,
	) -> usize {
		if state == CachedInterval::Next {
			// Avoid consecutive Next.
			if intervals.range(..=key).next_back()
				.map(|p| p.1.state != CachedInterval::Prev)
				.unwrap_or(false) {
				return 0;
			}
		}

		let mut size = None;
		let size = &mut size;
		let entry = intervals.entry(key.clone()).or_insert_with(|| {
			let mut entry = KeyOrderedEntry::empty();
			entry.key = key.clone();
			entry.child_storage_key = child.cloned();
			entry.state = state.clone();
			entry.lru_touched(lru_bound);
			*size = Some(entry.estimate_size());
			entry
		});
		if size.is_none() {
			entry.state.merge(state);
			entry.lru_touched(lru_bound);
		}
		size.unwrap_or(0)
	}

	fn apply_lru_limit(&mut self) {
		while self.used_size > self.limit {
			if !self.lru_pop() {
				return
			}
		}
	}

	/// Update cached intervals from block change delta.
	pub(super) fn enact_value_changes<'a>(&mut self, key: impl Iterator<Item = (&'a K, bool)>, child: Option<&Vec<u8>>) {
		let intervals = if let Some(info) = child {
			if let Some(intervals) = self.child_intervals.get_mut(info) {
				intervals
			} else {
				return;
			}
		} else {
			&mut self.intervals
		};

		// we do not run both iteration in paralell, as we consider that lru cache can be big
		// and full iteration worst than seeking each changes.
		for (key, changed) in key {
			if changed {
				self.used_size += Self::enact_insert(intervals, key, child, &mut self.lru_bound);
			} else {
				self.used_size -= Self::enact_remove(intervals, key);
			}
		}

		self.apply_lru_limit();
	}

	// This split insert in some existing interval an inserted value.
	fn enact_insert(
		intervals: &mut BTreeMap<K, Box<KeyOrderedEntry<K>>>,
		key: &K,
		child: Option<&Vec<u8>>,
		lru_bound: &mut Box<KeyOrderedEntry<K>>,
	) -> usize {
		let n = intervals.range(key..).next().map(|(k, v)| (k, v.state.clone()));
		let do_insert = match n {
			// Match key
			Some((_, CachedInterval::Next)) => {
				false
			},
			Some((cur_key, CachedInterval::Prev))
			| Some((cur_key, CachedInterval::Both)) if cur_key == key => {
				false
			},
			Some((_cur_key, CachedInterval::Prev))
			| Some((_cur_key, CachedInterval::Both)) => {
				debug_assert!(_cur_key > key);
				true
			},
			None => {
				// check if previous is next or both to see if splitted interval, then insert both
				let nb = intervals.range_mut(..key).next_back().map(|(k, v)| (k, v.state.clone()));
				match nb {
					Some((_, CachedInterval::Next))
					| Some((_, CachedInterval::Both)) => true,
					_ => false,
				}
			},
		};

		if do_insert {
			let mut entry = KeyOrderedEntry::empty();
			entry.key = key.clone();
			entry.child_storage_key = child.cloned();
			entry.state = CachedInterval::Both;
			// We do not touch corresponding interval,
			// would not really make sense since it is not an
			// next_key query.
			entry.lru_touched(lru_bound);
			let size = entry.estimate_size();
			intervals.insert(key.clone(), entry); 
			size
		} else {
			0
		}
	}

	// This merge existing interval when removing a value.
	// If value remove is Next, then we just remove interval because
	// we do not know if it was an existing value.
	fn enact_remove(
		intervals: &mut BTreeMap<K, Box<KeyOrderedEntry<K>>>,
		key: &K,
	) -> usize {
		Self::remove_interval_entry(intervals, key, true)
	}

	pub(super) fn retract_value_changes<'a>(&mut self, keys: impl Iterator<Item = &'a K>, child: Option<&Vec<u8>>) {
		let intervals = if let Some(info) = child {
			if let Some(intervals) = self.child_intervals.get_mut(info) {
				intervals
			} else {
				return;
			}
		} else {
			&mut self.intervals
		};

		// This should invalidates any interval containing any of this changes.
		// TODO consider just clearing cache or doing it in more efficient iteration.
		for key in keys {
			match Self::next_storage_key_inner(intervals, key, &mut None) {
				Some(_) => {
					// get prev
					let prev = intervals.range(..=key).next_back()
						.expect("If cached there is previous value.").0.clone();

					self.used_size -= Self::remove_interval_entry(intervals, &prev, false);
				},
				None => (),
			}
		}
	}

	// return total estimate size of all removed entries
	fn remove_interval_entry(
		intervals: &mut BTreeMap<K, Box<KeyOrderedEntry<K>>>,
		key: &K,
		do_merge: bool,
	) -> usize {
		let mut size_removed = 0;
		let (rem_prev, rem_next) = if let Some(mut siblings) = intervals.remove(key) {
			siblings.detach();
			size_removed += siblings.estimate_size();
			let siblings = siblings.state.clone();
			let mut iter = intervals.range_mut(key..);
			// If merg is define we only remove the both node, otherwhise
			// `both` siblings get updated.
			let both = !do_merge && siblings == CachedInterval::Both;
			let rem_next = if siblings == CachedInterval::Next || both {
				let n = iter.next().map(|(k, v)| (k, v.state.clone(), v));
				match n {
					Some((k, CachedInterval::Prev, _v)) => {
						Some(k.clone())
					},
					Some(kv) => {
						debug_assert!(kv.1.clone() == CachedInterval::Both);
						kv.2.state = CachedInterval::Next;
						None
					},
					_ => None,
				}
			} else {
				None
			};
			let rem_prev = if siblings == CachedInterval::Prev || both {
				let nb = intervals.range_mut(..key).next_back().map(|(k, v)| (k, v.state.clone(), v));
				match nb {
					Some((k, CachedInterval::Next, _v)) => {
						Some(k)
					},
					Some(kv) => {
						debug_assert!(kv.1.clone() == CachedInterval::Both);
						kv.2.state = CachedInterval::Prev;
						None
					},
					_ => None,
				}
			} else {
				None
			};
			(rem_prev.cloned(), rem_next)
		} else {
			return size_removed;
		};
		if let Some(rem) = rem_prev {
			size_removed += intervals.remove(&rem).map(|mut e| {
				e.detach();
				e.estimate_size()
			}).unwrap_or(0);
		}
		if let Some(rem) = rem_next {
			size_removed += intervals.remove(&rem).map(|mut e| {
				e.detach();
				e.estimate_size()
			}).unwrap_or(0);
		}

		size_removed
	}

	pub(super) fn clear(&mut self) {
		let limit = self.limit;
		*self = Self::new(limit);
	}

	pub(super) fn used_size(&self) -> usize {
		self.used_size
	}
}

impl<K: Ord + Clone> LocalOrderedKeys<K> {
	pub(super) fn next_storage_key(&self, key: &K, child: Option<&ChildInfo>) -> Option<Option<&K>> {
		let intervals = if let Some(info) = child {
			if let Some(intervals) = self.child_intervals.get(info.storage_key()) {
				intervals
			} else {
				return None;
			}
		} else {
			&self.intervals
		};
		let mut iter = intervals.range(key..);
		match iter.next() {
			Some((next_key, CachedInterval::Next))
			| Some((next_key, CachedInterval::Both)) if next_key == key => {
				match iter.next() {
					Some((next_key, CachedInterval::Prev))
					| Some((next_key, CachedInterval::Both)) => Some(Some(next_key)),
					Some((_next_key, CachedInterval::Next)) => None, // Should be unreachable
					None => Some(None),
				}
			},
			Some((next_key, CachedInterval::Prev)) if next_key == key => None,
			Some((_next_key, CachedInterval::Next)) => None,
			Some((next_key, _)) => {
				debug_assert!(match intervals.range(..key).next_back() {
					Some((_prev_key, CachedInterval::Next))
					| Some((_prev_key, CachedInterval::Both)) => true,
					_ => false,
				});
				Some(Some(next_key))
			},
			None => match intervals.range(..key).next_back() {
				Some((_prev_key, CachedInterval::Next))
				| Some((_prev_key, CachedInterval::Both)) => Some(None),
				_ => None,
			},
		}
	}

	pub(super) fn insert(&mut self, key: K, child: Option<&ChildInfo>, next: Option<K>) {
		let intervals = if let Some(info) = child {
			if let Some(intervals) = self.child_intervals.get_mut(info.storage_key()) {
				intervals
			} else {
				self.child_intervals.insert(info.storage_key().to_vec(), Default::default());
				return self.insert(key, child, next);
			}
		} else {
			&mut self.intervals
		};
		let process_end_interval = |next_key: Option<(&K, &mut CachedInterval)>| -> (Option<K>, bool) {
			match next_key {
				Some(next_key) if next.is_none() || Some(next_key.0) < next.as_ref() => {
					// having prev would mean we did cache a different interval.
					debug_assert!(next_key.1.clone() == CachedInterval::Next);
					(Some(next_key.0.clone()), false)
				},
				Some(next_key) if Some(next_key.0) == next.as_ref() => {
					if next_key.1.clone() != CachedInterval::Prev {
						*next_key.1 = CachedInterval::Both;
					}
					(None, false)
				},
				_ =>  {
					// next is before or we did not have next, so just insert.
					(None, true)
				},
			}
		};

		let mut iter = intervals.range_mut(&key..);
		// handle start of interval
		let (insert_start, (remove_end, insert_end)) = match iter.next() {
			// Match key
			Some((cur_key, CachedInterval::Next))
			| Some((cur_key, CachedInterval::Both)) if cur_key == &key => {
				debug_assert!({
					match iter.next() {
						Some((_next_key, CachedInterval::Next)) => false,
						Some((next_key, _)) => Some(next_key) == next.as_ref(),
						None => next.is_none(),
					}
				});
				// we already got end of interval 
				return;
			},
			Some(cur_key) if cur_key.0 == &key => {
				*cur_key.1 = CachedInterval::Both;
				(false, process_end_interval(iter.next()))
			},
			// Before interval
			next_key => {
				let processed_next = process_end_interval(next_key);
				match intervals.range_mut(..&key).next_back() {
					Some((prev_key, CachedInterval::Prev)) if prev_key < &key => {
						// no overlap
						(true, processed_next)
					},
					Some(prev_key) if prev_key.1.clone() == CachedInterval::Prev => {
						// prev_key == key (cannot be >)
						*prev_key.1 = CachedInterval::Both;
						(false, processed_next)
					},
					Some(_) => {
						(false, processed_next)
					},
					None => {
						// first key
						(true, processed_next)
					},
				}
			},
		};
		if insert_start {
			intervals.insert(key, CachedInterval::Next);
		}
		if insert_end {
			if let Some(key) = next {
				intervals.insert(key, CachedInterval::Prev);
			}
		}
		if let Some(key) = remove_end {
			intervals.remove(&key);
		}
	}

	// removal is mainly for lru, but both cache shares implementation and
	// this function is used in tests.
	#[cfg(test)]
	fn remove(&mut self, key: K, child: Option<&ChildInfo>) {
		let intervals = if let Some(info) = child {
			if let Some(intervals) = self.child_intervals.get_mut(info.storage_key()) {
				intervals
			} else {
				return;
			}
		} else {
			&mut self.intervals
		};
		let (rem_prev, rem_next) = if let Some(siblings) = intervals.remove(&key) {
			let mut iter = intervals.range_mut(&key..);
			let rem_next = if siblings == CachedInterval::Next || siblings == CachedInterval::Both {
				match iter.next() {
					Some((k, CachedInterval::Prev)) => {
						Some(k.clone())
					},
					Some(k) => {
						debug_assert!(k.1.clone() == CachedInterval::Both);
						*k.1 = CachedInterval::Next;
						None
					},
					_ => None,
				}
			} else {
				None
			};
			let rem_prev = if siblings == CachedInterval::Prev || siblings == CachedInterval::Both {
				match intervals.range_mut(..&key).next_back() {
					Some((k, CachedInterval::Next)) => {
						Some(k)
					},
					Some(k) => {
						debug_assert!(k.1.clone() == CachedInterval::Both);
						*k.1 = CachedInterval::Prev;
						None
					},
					_ => None,
				}
			} else {
				None
			};
			(rem_prev.cloned(), rem_next)
		} else {
			return;
		};
		if let Some(rem) = rem_prev {
			let _ = intervals.remove(&rem);
		}
		if let Some(rem) = rem_next {
			let _ = intervals.remove(&rem);
		}
	}
}

// Could be Copy, but is not for the
// sake of assigning to &mut without surprise.
#[derive(PartialEq, Eq, Clone, Debug)]
enum CachedInterval {
	/// Next key is next key in cache.
	/// The current key could be an undefined key.
	Next,
	/// Previous key is previous key in cache.
	/// The current key cannot be an undefined key.
	Prev,
	/// Next and Previous key are keys in cache.
	/// The current key cannot be an undefined key.
	Both,
}

impl CachedInterval {
	// Return true if it was updated.
	fn merge(&mut self, other: CachedInterval) -> bool {
		match (self.clone(), other) {
			(CachedInterval::Next, CachedInterval::Both)
			| (CachedInterval::Next, CachedInterval::Prev)
			| (CachedInterval::Prev, CachedInterval::Both)
			| (CachedInterval::Prev, CachedInterval::Next) => {
				*self = CachedInterval::Both;
				true
			},
			_ => false
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn interval_map_works() {
		let nb_test = 100;
		let layout = [1, 3, 7, 8];
		let query_range = 10;
		let seed = 0;

		let next_layout = |v: usize| -> Option<usize> {
			for a in layout.iter() {
				if *a > v {
					return Some(*a)
				}
			}
			None
		};
		use rand::{SeedableRng, Rng};
		let mut rng = rand::rngs::SmallRng::seed_from_u64(seed);

		for _ in 0..nb_test {

			let mut l = LocalOrderedKeys::<usize>::default();

			let mut ixs: Vec<_> = (0..query_range).collect();
			while ixs.len() > 0 {
				let ix = ixs.remove(rng.gen::<usize>() % ixs.len());
				l.insert(ix, None, next_layout(ix));
				if ixs.len() == query_range / 2 {
					// middle check
					let mut ixs: Vec<_> = (0..query_range).collect();
					while ixs.len() > 0 {
						let ix = ixs.remove(rng.gen::<usize>() % ixs.len());
						let next = l.next_storage_key(&ix, None);
						if let Some(next) = next {
							// not remove from cache
							assert_eq!(next, next_layout(ix).as_ref());
						}
					}
				}
			}
			let mut ixs: Vec<_> = (0..query_range).collect();
			while ixs.len() > 0 {
				let ix = ixs.remove(rng.gen::<usize>() % ixs.len());
				let next = l.next_storage_key(&ix, None);
				// all in cache
				assert!(next.is_some());
				let next = next.unwrap();
				assert_eq!(next, next_layout(ix).as_ref());
			}
			let mut ixs: Vec<_> = (0..(query_range / 2)).collect();
			while ixs.len() > 0 {
				let ix = ixs.remove(rng.gen::<usize>() % ixs.len());
				l.remove(ix, None);
			}
			let mut ixs: Vec<_> = (0..query_range).collect();
			while ixs.len() > 0 {
				let ix = ixs.remove(rng.gen::<usize>() % ixs.len());
				let next = l.next_storage_key(&ix, None);
				if let Some(next) = next {
					// not remove from cache
					assert_eq!(next, next_layout(ix).as_ref());
				}
			}
		}
	}

	#[test]
	fn interval_lru_works() {
		// estimate size for entry is 
		// 4 * 2 + 1 + 2 * 4 + 1 = 18
		let entry_size = 18;

		let mut input = LocalOrderedKeys::<u32>::default();
		input.insert(4, None, Some(6));

		let mut cache = LRUOrderedKeys::<u32>::new(3 * entry_size);
		cache.merge_local_cache(&mut input);
		cache.merge_local_cache(&mut input);

		assert!(cache.used_size == 2 * entry_size);
		assert_eq!(None, cache.next_storage_key(&0, None));
		assert_eq!(None, cache.next_storage_key(&6, None));
		assert_eq!(Some(Some(6)), cache.next_storage_key(&4, None));

		input.insert(6, None, Some(10));
		cache.merge_local_cache(&mut input);
		assert!(cache.used_size == 3 * entry_size);
		assert_eq!(Some(Some(10)), cache.next_storage_key(&6, None));

		// remove 6 to merge interval
		cache.enact_value_changes(vec![(&6, false)].into_iter(), None);
		assert!(cache.used_size == 2 * entry_size);
		assert_eq!(Some(Some(10)), cache.next_storage_key(&4, None));

		// add starting into interval (with end to valid value).
		input.insert(5, None, Some(10));
		cache.merge_local_cache(&mut input);
		assert!(cache.used_size == 2 * entry_size);
		assert_eq!(Some(Some(10)), cache.next_storage_key(&4, None));

		// add out of interval to get first interval lru removed
		input.insert(15, None, Some(21));
		cache.merge_local_cache(&mut input);
		assert!(cache.used_size == 2 * entry_size);
		assert_eq!(None, cache.next_storage_key(&4, None));
		assert_eq!(None, cache.next_storage_key(&9, None));
		assert_eq!(Some(Some(21)), cache.next_storage_key(&15, None));

		// clear with limit
		cache.limit = 0;
		cache.apply_lru_limit();
		assert!(cache.used_size == 0);
		assert_eq!(None, cache.next_storage_key(&15, None));

		// add then remove with invalidate only
		cache.limit = 3 * entry_size;
		input.insert(15, None, None);
		input.insert(6, None, Some(8));
		cache.merge_local_cache(&mut input);
		assert!(cache.used_size == 3 * entry_size);
		cache.retract_value_changes(vec![&5, &100].into_iter(), None);
		assert!(cache.used_size == 2 * entry_size);
		cache.retract_value_changes(vec![&6].into_iter(), None);
		assert!(cache.used_size == 0);

		// enact_insert
		cache.limit = 3 * entry_size;
		input.insert(3, None, Some(8));
		cache.merge_local_cache(&mut input);
		assert!(cache.used_size == 2 * entry_size);
		cache.enact_value_changes(vec![(&6, true)].into_iter(), None);
		assert!(cache.used_size == 3 * entry_size);
		assert_eq!(Some(Some(6)), cache.next_storage_key(&3, None));
		assert_eq!(Some(Some(8)), cache.next_storage_key(&6, None));

		// empty cross child contents
		let child_0 = ChildInfo::new_default(&[0]);
		let child_2 = ChildInfo::new_default(&[2]);
		cache.clear();
		cache.limit = 5 * entry_size;
		input.insert(15, Some(&child_0), None);
		input.insert(15, Some(&child_2), Some(16));
		cache.merge_local_cache(&mut input);
		assert_eq!(Some(Some(16)), cache.next_storage_key(&15, Some(&child_2)));
		// lru will be at 0
		assert_eq!(Some(None), cache.next_storage_key(&15, Some(&child_0)));
		cache.merge_local_cache(&mut input);
		cache.limit = 3 * entry_size;
		// lru will be at 0
		cache.apply_lru_limit();
		assert_eq!(None, cache.next_storage_key(&15, Some(&child_2)));
		assert_eq!(Some(None), cache.next_storage_key(&15, Some(&child_0)));
	}

	use sp_runtime::{
		traits::BlakeTwo256,
		testing::{H256, Block as RawBlock, ExtrinsicWrapper},
	};
	use sp_state_machine::{InMemoryBackend, StorageCollection};
	use crate::storage_cache::CachingState;
	use crate::{CacheRatios};

	type Block = RawBlock<ExtrinsicWrapper<u32>>;


	const MAX_INITIAL_KEYS: usize = 50;
	const MAX_INITIAL_KEY_LENGTH: usize = 10;
	const MAX_VALUE_LEN: usize = 10;
	const MAX_BLOCKS: usize = 5;
	struct CheckScenario {
		initial_number_of_key: usize, // 0 - 50
		initial_key_length: usize, // 5 - 10
		value_len: usize, // 5 - 10
		lru_limit_size: usize, // 0 - 100 * initial_number_of_key / 100
		nb_random_query: usize, // 0 - initial_number_of_key / 10
		random_query_offset: usize, // 0 - initial_number_of_key
		random_query_number: usize, // 10 - always start at 0
		nb_change_blocks: usize, // 0 - 5
		nb_value_add: usize, // 0 - initial_number_of_key / 10
		value_add_key_len: usize, // 0 - initial_number_of_key / 10
		random_value_add_offset: usize, // 0 - initial_number_of_key
		nb_value_remove: usize, // 0 - initial_number_of_key / 10
	}

	fn usize_param(b: &[u8], ix: usize, bit_offset: usize) -> usize {
		(b[ix] >> bit_offset) as usize
	}

	impl CheckScenario {
		fn initiate_value_pool(random_seed: u64) -> Vec<(Vec<u8>, Vec<u8>)> {
			use rand::{SeedableRng, Rng};
			let mut rng = rand::rngs::SmallRng::seed_from_u64(random_seed);

			let max_number_key = MAX_INITIAL_KEYS
				+ ((MAX_BLOCKS + 2) * (MAX_INITIAL_KEYS / 10));
			(0..max_number_key).map(|_| {
				let mut key = vec![0; MAX_INITIAL_KEY_LENGTH];
				let mut value = vec![0; MAX_VALUE_LEN];
				rng.fill(&mut key[..]);
				rng.fill(&mut value[..]);
				(key, value)
			}).collect()
		}
		fn random(seed: u64) -> Self {
			use rand::{SeedableRng, Rng};
			let mut rng = rand::rngs::SmallRng::seed_from_u64(seed);
			let mut buff = [0u8; 10];
			rng.fill(&mut buff);
			Self::from_random_bytes(&buff[..])
		}
		fn from_random_bytes(bytes: &[u8]) -> Self {
			let initial_number_of_key = 5 + usize_param(bytes, 0, 0) % 50;
			CheckScenario {
				initial_number_of_key,
				initial_key_length: 5 + usize_param(bytes, 0, 6) % 5,
				value_len: 5 + usize_param(bytes, 1, 0) % 5,
				lru_limit_size: (usize_param(bytes, 2, 0) % 100) * initial_number_of_key / 100,
				nb_random_query: usize_param(bytes, 3, 0) % (initial_number_of_key / 5),
				random_query_offset: usize_param(bytes, 4, 0) % initial_number_of_key,
				random_query_number: 1 + usize_param(bytes, 5, 0) % 10,
				nb_change_blocks: usize_param(bytes, 5, 4) % 5,
				nb_value_add: usize_param(bytes, 6, 0) % (initial_number_of_key / 5),
				value_add_key_len: 5 + usize_param(bytes, 7, 0) % 5,
				random_value_add_offset: usize_param(bytes, 8, 0) % initial_number_of_key,
				nb_value_remove: usize_param(bytes, 9, 0) % (initial_number_of_key / 5),
			}
		}
	}

	fn quick_check(scenario: CheckScenario, value_pool: &Vec<(Vec<u8>, Vec<u8>)>) {
		use sp_state_machine::backend::Backend as StateBackend;

		let block_hashes: Vec<_> = (0..15).map(|_| H256::random()).collect();

		let mut backend = InMemoryBackend::<BlakeTwo256>::default();
		let mut backend_reorg = InMemoryBackend::<BlakeTwo256>::default();
		let reorg_ix = scenario.nb_change_blocks - (scenario.nb_change_blocks / 2);
		let mut collection = StorageCollection::default();

		// write some random key content: 0 - 50 value + 10 val in two cht
		(0..scenario.initial_number_of_key).for_each(|ix| {
			let key = value_pool[ix].0[..scenario.initial_key_length].to_vec();
			let value = value_pool[ix].1[..scenario.value_len].to_vec();
			collection.push((key, Some(value)));
		});

		backend.insert(vec![(None, collection)]);
		let shared = crate::storage_cache::new_shared_cache::<Block>(scenario.lru_limit_size, CacheRatios {
			values_top: 0,
			values_children: 0,
			ordered_keys: 1,
		});

		let mut state = CachingState::new(
			backend.clone(),
			shared.clone(),
			Some(block_hashes[0]),
		);

		let query_range = |
			mut query: Vec<u8>,
			nb: usize,
			state: &CachingState<InMemoryBackend<BlakeTwo256>, Block>,
			backend: &InMemoryBackend<BlakeTwo256>,
		| {
			for _ in 0..nb {
				let state_result = state.next_storage_key(query.as_slice()).unwrap();
				let no_cache = backend.next_storage_key(query.as_slice()).unwrap();
				assert_eq!(state_result, no_cache);
				if let Some(state_result) = no_cache {
					query = state_result;
				} else {
					break;
				}
			}
		};

		// Do some 10 random query of 0 to size / 10 content: to feed local cache (use storage key).
		let mut start_key = value_pool[scenario.random_query_offset].0.clone();
		if scenario.nb_random_query > 0 {
			let query_interval = (255u8 - start_key[0]) / scenario.nb_random_query as u8;
			for _ in 0..scenario.nb_random_query {
				query_range(start_key.clone(), scenario.random_query_number, &state, &backend);
				start_key[0] += query_interval;
			}
		}

		// Do a fix query of 5 consecutive keys
		query_range(vec![128u8], 5, &state, &backend);

		let mut offset = scenario.initial_number_of_key;
		let mut offset_remove = scenario.random_value_add_offset;
		// new block with ~ 10 new value Repeat X time with x from 0 to 5
		for i in 0..scenario.nb_change_blocks {
			let mut collection = Vec::new();
			(0..scenario.nb_value_add).for_each(|ix| {
				let key = value_pool[offset + ix].0[..scenario.value_add_key_len].to_vec();
				let value = value_pool[offset + ix].1[..scenario.value_len].to_vec();
					collection.push((key, Some(value)));
			});
			// only remove existing value
			if offset_remove + scenario.nb_value_remove < offset {
				(0..scenario.nb_value_remove).for_each(|ix| {
					let key = value_pool[offset + ix].0[..scenario.initial_key_length].to_vec();
						collection.push((key, None));
				});
			}
			offset += scenario.nb_value_add;
			offset_remove += scenario.nb_value_remove;


			backend.insert(vec![(None, collection.clone())]);
			state.cache.sync_cache(
				&[],
				&[],
				collection.clone(),
				vec![],
				Some(block_hashes[i].clone()),
				Some(i as u64 + 1),
				true,
			);
			state.state().insert(vec![(None, collection)]);

			if i == reorg_ix {
				backend_reorg = backend.clone();
			}
			// between each do the fix query.
			query_range(vec![128u8], 5, &state, &backend);

		}

		// round of random query
		let mut start_key = value_pool[scenario.random_query_offset].0.clone();
		if scenario.nb_random_query > 0 {
			let query_interval = (255u8 - start_key[0]) / scenario.nb_random_query as u8;
			for _ in 0..scenario.nb_random_query {
				query_range(start_key.clone(), scenario.random_query_number, &state, &backend);
				start_key[0] += query_interval;
			}
		}

		// reorg to max_nb_block / 2.
		let offset = scenario.initial_number_of_key;
		let offset_remove = scenario.random_value_add_offset;
		let mut collection = Vec::new();
		(0..scenario.nb_value_add).for_each(|ix| {
			let key = value_pool[offset + ix].0[..scenario.initial_key_length].to_vec();
			let value = value_pool[offset + ix].1[..scenario.value_len].to_vec();
				collection.push((key, Some(value)));
		});
		// only remove existing value
		if offset_remove + scenario.nb_value_remove < offset {
			(0..scenario.nb_value_remove).for_each(|ix| {
				let key = value_pool[offset + ix].0[..scenario.initial_key_length].to_vec();
					collection.push((key, None));
			});
		}


		backend_reorg.insert(vec![(None, collection.clone())]);
		*state.state() = backend_reorg.clone();
		let reverted_hashes: Vec<_> = (0..(scenario.nb_change_blocks / 2)).map(|i| {
			block_hashes[i + 1].clone()
		}).collect(); // TODO not sure about order, may need to reverse iter before collect.
		state.cache.sync_cache(
			&[],
			&reverted_hashes[..],
			collection,
			vec![],
			Some(block_hashes[reorg_ix].clone()),
			Some(reorg_ix as u64 + 1),
			true,
		);

		query_range(vec![128u8], 5, &state, &backend_reorg);
		// round of random query
		let mut start_key = value_pool[scenario.random_query_offset].0.clone();
		if scenario.nb_random_query > 0 {
			let query_interval = (255u8 - start_key[0]) / scenario.nb_random_query as u8;
			for _ in 0..scenario.nb_random_query {
				query_range(start_key.clone(), scenario.random_query_number, &state, &backend_reorg);
				start_key[0] += query_interval;
			}
		}
	}

	#[test]
	fn simple_fuzz_check() {
		let pool = CheckScenario::initiate_value_pool(0);
		for i in 0u64..50 {
			quick_check(CheckScenario::random(i), &pool);
		}
	}
}

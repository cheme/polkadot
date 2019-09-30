// Copyright 2017-2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.	See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.	If not, see <http://www.gnu.org/licenses/>.

//! Data store acyclic directed graph as tree.
//!
//! General structure is an array of linear, each linear originating
//! from another array at designated index.
//!
//! Only support commited and prospective states.

// - for tree
// commit prospective = 
// put commit counter to prospective counter +1, then recurse branch in path to this value. 
// primitive spawn two new branches and end the previous one)
// New branches uses a + 1 commmited counter (meaning prospective).
// Also on commit we branch an new prospective one (counter +1).
// discard prospective = increase prospective counter.
//
// -> 2 counter:
// - committed : every commited are valid value (for block see it as finalized),
// so everithing less or equal is valid.
// Only one branching path should be commited, so prospective value are U32::max_value.
// And we put an actual committed counter to branch on commit
//
// For branch case: some pruning is done over those indexed value (so by commit_ix (similar to
// a block nb) -> therefore we do not use a boolean value).
//
// In fact committed can be a simple boolean: keeping index can help for gc (but there will
// probably need to manage a collection of branch_index to gc: when linear state is reduced).
// 
// TODO consider removing this committed (not strictly needed (except to avoid gc)
//
// - prospective : this is only valid for latest prospective value, is before commited. 
//   - on drop prospective: +1 counter prospective meaning no prospective valid anymore
//   - on commit: prospective = commited index + 1 and update commited index of commited branch (so the commited
//   value remain).
//
//-> only to avoid update on btree.
//

use crate::linear::{
	MemoryOnly as LinearBackend,
};
use crate::HistoriedValue;
use rstd::borrow::Cow;
use rstd::rc::Rc;
use rstd::vec::Vec;
use rstd::collections::btree_map::BTreeMap;
use rstd::convert::{TryFrom, TryInto};


#[derive(Debug, Clone)]
#[cfg_attr(any(test, feature = "test"), derive(PartialEq))]
pub struct BranchState {
	/// Index of first element (only use for indexed access).
	/// Element before offset are not in state.
	offset: u64,
	/// number of elements: all elements equal or bellow
	/// this index are valid, over this index they are not.
	len: u64,
	/// Maximum index before first deletion, it indicates
	/// if the state is modifiable (when an element is dropped
	/// we cannot append and need to create a new branch).
	max_len_ix: u64,
}


pub trait TreeStateTrait<S, I, BI> {
	type Branch: BranchStateTrait<S, BI>;
	type Iter: Iterator<Item = (Self::Branch, I)>;

	fn get_branch(self, index: I) -> Option<Self::Branch>;

	/// Non inclusive.
	fn last_index(self) -> I;

	/// Iterator.
	fn iter(self) -> Self::Iter;
}

pub trait BranchStateTrait<S, I> {

	fn get_node(&self, i: I) -> S;
}


impl<'a> TreeStateTrait<bool, u64, u64> for &'a StatesRef {
	type Branch = (&'a StatesBranchRef, Option<u64>);
	type Iter = StatesRefIter<'a>;

	fn get_branch(self, i: u64) -> Option<Self::Branch> {
		for (b, bi) in self.iter() {
			if bi == i {
				return Some(b);
			} else if bi < i {
				break;
			}
		}
		None
	}

	fn last_index(self) -> u64 {
		let l = self.history.len();
		let l = if l > 0 {
			self.history[l - 1].branch_index
		} else {
			0
		};
		self.upper_branch_index.map(|u| rstd::cmp::min(u, l)).unwrap_or(l)
	}

	fn iter(self) -> Self::Iter {
		let mut end = self.history.len();
		let last_index = self.last_index();
		let upper_node_index = if Some(last_index) == self.upper_branch_index {
			self.upper_node_index
		} else { None };
		while end > 0 {
			if self.history[end - 1].branch_index <= last_index {
				break;
			}
			end -= 1;
		}

		StatesRefIter(self, end, upper_node_index)
	}
}

/// This is a simple range, end non inclusive.
#[derive(Debug, Clone)]
#[cfg_attr(any(test, feature = "test"), derive(PartialEq))]
pub struct BranchStateRef {
	start: u64,
	end: u64,
}

impl<'a> BranchStateTrait<bool, u64> for (&'a StatesBranchRef, Option<u64>) {

	fn get_node(&self, i: u64) -> bool {
		let l = self.0.state.end;
		let upper = self.1.map(|u| rstd::cmp::min(u, l)).unwrap_or(l);
		i >= self.0.state.start && i < upper
	}
}

impl Default for BranchState {
	// initialize with one element
	fn default() -> Self {
		Self::new_from(0)
	}
}

impl BranchState {
	pub fn new_from(offset: u64) -> Self {
		BranchState {
			offset,
			len: 1,
			max_len_ix: offset,
		}
	}

	pub fn state_ref(&self) -> BranchStateRef {
		BranchStateRef {
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
	pub fn drop_state(&mut self) -> Option<u64> {
		if self.len > 0 {
			self.len -= 1;
			Some(self.offset + self.len)
		} else {
			None
		}
	}

	/// act as a truncate, returning range of deleted (end excluded)
	/// TODO consider removal
	pub fn keep_state(&mut self, index: u64) -> (u64, u64) {
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
	pub fn get_state(&self, index: u64) -> bool {
		if index < self.offset {
			return false;
		}
		self.len > index + self.offset
	}

	pub fn latest_ix(&self) -> Option<u64> {
		if self.len > 0 {
			Some(self.offset + self.len - 1)
		} else {
			None
		}
	}

}

impl BranchStateRef {
	/// Return true if the state exists, false otherwhise.
	pub fn get_state(&self, index: u64) -> bool {
		index < self.end && index >= self.start
	}
}

/// At this point this is only use for testing and as an example
/// implementation.
/// It keeps trace of dropped value, and have some costy recursive
/// deletion.
#[derive(Debug, Clone)]
#[cfg_attr(any(test, feature = "test"), derive(PartialEq))]
pub struct TestStates {
	branches: BTreeMap<u64, StatesBranch>,
	last_branch_index: u64,
	committed_ix: usize,
	prospective_ix: usize,
	/// a lower treshold under which every branch are seen
	/// as containing only valid values.
	/// This can only be updated after a full garbage collection.
	valid_treshold: u64,
}

impl StatesBranch {
	pub fn branch_ref(&self) -> StatesBranchRef {
		StatesBranchRef {
			branch_index: self.branch_index,
			state: self.state.state_ref(),
		}
	}
	pub fn is_committed(&self, states: &TestStates) -> bool {
		self.is_committed_internal(states.committed_ix)
	}
	fn is_committed_internal(&self, committed_ix: usize) -> bool {
		self.committed_ix <= committed_ix
	}
	
	pub fn is_prospective(&self, states: &TestStates) -> bool {
		self.is_prospective_internal(states.prospective_ix)
	}
	fn is_prospective_internal(&self, prospective_ix: usize) -> bool {
		self.prospective_ix >= prospective_ix
	}
	fn is_dropped_internal(&self, prospective_ix: usize, committed_ix: usize) -> bool {
		!self.is_committed_internal(committed_ix)
			&& !self.is_prospective_internal(prospective_ix)
	}
	pub fn is_dropped(&self, states: &TestStates) -> bool {
		self.is_dropped_internal(states.prospective_ix, states.committed_ix)
	}
}

impl Default for TestStates {
	fn default() -> Self {
		TestStates {
			branches: Default::default(),
			last_branch_index: 0,
			committed_ix: 0,
			prospective_ix: 0,
			valid_treshold: 0,
		}
	}
}

#[derive(Debug, Clone)]
#[cfg_attr(any(test, feature = "test"), derive(PartialEq))]
pub struct StatesBranch {
	// this is the key (need to growth unless full gc (can still have
	// content pointing to it even if it seems safe to reuse a previously
	// use ix).
	branch_index: u64,
	
	origin_branch_index: u64,
	origin_node_index: u64,

	prospective_ix: usize,

	committed_ix: usize,

	state: BranchState,
}

#[derive(Debug, Clone)]
#[cfg_attr(any(test, feature = "test"), derive(PartialEq))]
pub struct StatesBranchRef {
	branch_index: u64,
	state: BranchStateRef,
}


#[derive(Clone)]
// TODO could benefit from smallvec!!
// of number of node (it still stores a few usize & a vec ptr)
/// Reference to state to use for query updates.
/// It is a single brannch path with branches ordered by branch_index.
///
/// Note that an alternative representation could be a pointer to full
/// tree state with a defined branch index implementing an iterator.
pub struct StatesRef {
	/// Oredered by branch index linear branch states.
	history: Rc<Vec<StatesBranchRef>>,
	/// Index is  include, acts as length of history.
	upper_branch_index: Option<u64>,
	/// Index is not include, acts as a branch ref end value.
	upper_node_index: Option<u64>,
}

/// Iterator, contains index of last inner struct.
pub struct StatesRefIter<'a>(&'a StatesRef, usize, Option<u64>);

impl<'a> Iterator for StatesRefIter<'a> {
	type Item = ((&'a StatesBranchRef, Option<u64>), u64);

	fn next(&mut self) -> Option<Self::Item> {
		if self.1 > 0 {
			let upper_node_index = self.2.take();
			Some((
				(&self.0.history[self.1 - 1], upper_node_index),
				self.0.history[self.1 - 1].branch_index,
			))
		} else {
			None
		}
	}
}

impl StatesRef {
	/// limit to a given branch (included).
	/// Optionally limiting branch to a linear index (included).
	fn limit_branch(&mut self, branch_index: u64, node_index: Option<u64>) {
		debug_assert!(branch_index > 0);
		self.upper_branch_index = Some(branch_index);
		self.upper_node_index = node_index;
	}

	/// remove any limit.
	fn clear_limit(&mut self, branch_index: u64, node_index: u64) {
		self.upper_branch_index = None;
		self.upper_node_index = None;
	}

	// vec like function
	
	fn len(&self) -> usize {
		self.history.len()
	}

	fn branch_state(&self, index: usize) -> &StatesBranchRef {
		&self.history[index]
	}

	fn current_branch_state(&self) -> &StatesBranchRef {
		debug_assert!(self.len() > 0, "No empty branch in ref");
		&self.history[self.len() - 1]
	}

}

impl TestStates {

	/// clear state but keep existing branch values (can be call after a full gc:
	/// enforcing no commited containing dropped values).
	pub fn unsafe_clear(&mut self) {
		self.branches.clear();
		self.last_branch_index = 0;
	}

	/// warning it should be the index of the leaf, otherwhise the ref will be incomplete.
	/// (which is fine as long as we use this state to query something that refer to this state.
	pub fn state_ref(&self, mut branch_index: u64) -> StatesRef {
		let mut result = Vec::new();
		let mut previous_origin_node_index = u64::max_value() - 1;
		while branch_index > self.valid_treshold {
			if let Some(branch) = self.branches.get(&branch_index)
				.filter(|b| !b.is_dropped_internal(self.prospective_ix, self.committed_ix)) {
				let mut branch_ref = branch.branch_ref();
				if branch_ref.state.end > previous_origin_node_index + 1 {
					branch_ref.state.end = previous_origin_node_index + 1;
				}
				previous_origin_node_index = branch.origin_node_index;
				// TODO EMCH consider reversing state_ref
				result.insert(0, branch_ref);
				branch_index = branch.origin_branch_index;
			} else {
				break;
			}
		}
		StatesRef { history: Rc::new(result), upper_branch_index: None, upper_node_index: None }
	}

	// create a branches. End current branch.
	// Return first created index (next branch are sequential indexed)
	// or None if origin branch does not allow branch creation (commited branch or non existing).
	pub fn create_branch(
		&mut self,
		nb_branch: usize,
		branch_index: u64,
		node_index: Option<u64>,
	) -> Option<u64> {
		if nb_branch == 0 {
			return None;
		}

		// for 0 is the first branch creation case
		let node_index = if branch_index == 0 {
			debug_assert!(node_index.is_none());
			0
		} else {
			if let Some(node_index) = self.get_node(branch_index, node_index) {
				node_index
			} else {
				return None;
			}
		};

		let result_ix = self.last_branch_index + 1;
		for i in result_ix .. result_ix + (nb_branch as u64) {
			self.branches.insert(i, StatesBranch {
				branch_index: i,
				origin_branch_index: branch_index,
				origin_node_index: node_index,
				committed_ix: usize::max_value(),
				prospective_ix: self.prospective_ix,
				state: Default::default(),
			});
		}
		self.last_branch_index += nb_branch as u64;

		Some(result_ix)
	}

	/// check if node is valid for given index.
	/// return node_index.
	/// TODO consider renaming?
	pub fn get_node(
		&self,
		branch_index: u64,
		node_index: Option<u64>,
	) -> Option<u64> {
		if let Some(branch) = self.branches.get(&branch_index)
			.filter(|b| !b.is_dropped_internal(self.prospective_ix, self.committed_ix)) {
			if let Some(node_index) = node_index {
				if branch.state.get_state(node_index) {
					Some(node_index)
				} else {
					None
				}
			} else {
				branch.state.latest_ix()
			}
		} else {
			None
		}
	}

	/// Do node exist (return state (being true or false only)).
	pub fn get(&self, branch_index: u64, node_index: u64) -> bool {
		self.get_node(branch_index, Some(node_index)).is_some()
	}

	pub fn branch_state(&self, branch_index: u64) -> Option<&BranchState> {
		self.branches.get(&branch_index)
			.filter(|b| !b.is_dropped_internal(self.prospective_ix, self.committed_ix))
			.map(|b| &b.state)
	}

	// does remove branch if dropped.
	fn access_branch_mut(&mut self, branch_index: u64) -> Option<&mut StatesBranch> {
		if let Some(branch) = self.branches.get(&branch_index) {
			if branch.is_dropped_internal(self.prospective_ix, self.committed_ix) {
				let _ = self.branches.remove(&branch_index);
				return None;
			} else {
				return self.branches.get_mut(&branch_index);
			}
		}
		None
	}

	pub fn branch_state_mut(&mut self, branch_index: u64) -> Option<&mut BranchState> {
		self.access_branch_mut(branch_index)
			.map(|b| &mut b.state)
	}

	/// this function can go into deep recursion with full scan, it indicates
	/// that the in memory model use here should only be use for small data or
	/// tests.
	pub fn apply_drop_state(&mut self, branch_index: u64, node_index: u64) {
		let mut to_delete = Vec::new();
		for (i, s) in self.branches.iter() {
			if s.origin_branch_index == branch_index && s.origin_node_index == node_index {
				to_delete.push(*i);
			}
		}
		for i in to_delete.into_iter() {
			loop {
				match self.branch_state_mut(i).map(|ls| ls.drop_state()) {
					Some(Some(li)) => self.apply_drop_state(i, li),
					Some(None) => break, // we keep empty branch
					None => break,
				}
			}
		}
	}
}

// TODO could benefit from smallvec!! need an estimation
// of number of node (it still stores a usize + a smallvec) 
/// First field is the actual history against which we run
/// the state.
/// Second field is an optional value for the no match case.
#[derive(Debug, Clone)]
#[cfg_attr(any(test, feature = "test"), derive(PartialEq))]
pub struct History<V>(Vec<HistoryBranch<V>>, Option<V>);

impl<V> Default for History<V> {
	fn default() -> Self {
		History(Vec::new(), None)
	}
}

#[derive(Debug, Clone)]
#[cfg_attr(any(test, feature = "test"), derive(PartialEq))]
pub struct HistoryBranch<V> {
	branch_index: u64,
	history: LinearBackend<V, u64>,
}

#[derive(Debug, Clone)]
#[cfg_attr(any(test, feature = "test"), derive(PartialEq))]
pub struct Serialized<'a>(Cow<'a, [u8]>);


impl<V> History<V> {

	/// Set or update value for a given state.
	pub fn set(&mut self, state: &StatesRef, value: V) {
		// TODO EMCH it does not seem stricly needed to pass
		// a full state, double index looks enough.
		// but this api can help using consistent state.
		let branch_state = state.current_branch_state();
		let mut i = self.0.len();
		let (branch_position, new_branch) = loop {
			if i == 0 {
				break (0, true);
			}
			let branch_index = self.0[i - 1].branch_index;
			if branch_index == branch_state.branch_index {
				break (i - 1, false);
			} else if branch_index < branch_state.branch_index {
				break (i, true);
			}
			i -= 1;
		};
		if new_branch {
			let mut history = LinearBackend::<V, u64>::default();
			let index = state.upper_node_index.unwrap_or(branch_state.state.end) - 1;
			history.push(HistoriedValue {
				value,
				index,
			});
			let h_value = HistoryBranch {
				branch_index: branch_state.branch_index,
				history,
			};
			if branch_position == self.0.len() {
				self.0.push(h_value);
			} else {
				self.0.insert(branch_position, h_value);
			}
		} else {
			self.node_set(branch_position, branch_state, state.upper_node_index, value)
		}
	}

	fn node_set(&mut self, index: usize, state: &StatesBranchRef, bound: Option<u64>, value: V) {
		let node_index = bound.unwrap_or(state.state.end) - 1;
		let history = &mut self.0[index];
		let mut index = history.history.len();
		debug_assert!(index > 0);
		loop {
			if index == 0 || history.history[index - 1].index < node_index {
				let h_value = HistoriedValue {
					value,
					index: node_index,
				};
				if index == history.history.len() {
					history.history.push(h_value);
				} else {
					history.history.insert(index, h_value);
				}
				break;
			} else if history.history[index - 1].index == node_index {
				history.history[index - 1].value = value;
				break;
			}
			index -= 1;
		}
	}

	/// Access to last valid value (non dropped state in history).
	/// When possible please use `get_mut` as it can free some memory.
	pub fn get<I, BI, S> (&self, state: S) -> Option<&V> 
		where
			S: TreeStateTrait<bool, I, BI>,
			I: Copy + Eq + TryFrom<usize> + TryInto<usize>,
			BI: Copy + Eq + TryFrom<usize> + TryInto<usize>,
	{
		let mut index = self.0.len();
		// note that we expect branch index to be linearily set
		// along a branch (no state containing unordered branch_index
		// and no history containing unorderd branch_index).
		if index == 0 {
			return self.1.as_ref();
		}

		for (state_branch, state_index) in state.iter() {
			while index > 0 {
				index -= 1;
				if let Ok(branch_index) = self.0[index].branch_index.try_into() {
					if let Ok(state_index) = state_index.try_into() {
						if state_index == branch_index {
							if let Some(result) = self.branch_get(index, &state_branch) {
								return Some(result)
							}
						}
					}
				}
			}
			if index == 0 {
				break;
			}
		}
		self.1.as_ref()
	}

	fn branch_get<S, I>(&self, index: usize, state: &S) -> Option<&V>
		where
			S: BranchStateTrait<bool, I>,
			I: Copy + Eq + TryFrom<usize> + TryInto<usize>,
	{
		let history = &self.0[index];
		let mut index = history.history.len();
		while index > 0 {
			index -= 1;
			if let Some(&v) = history.history.get(index).as_ref() {
				if let Ok(i) = (v.index as usize).try_into() {
					if state.get_node(i) {
						return Some(&v.value);
					}
				}
			}
		}
		None
	}
/*
	/// Access to last valid value (non dropped state in history).
	/// When possible please use `get_mut` as it can free some memory.
	pub fn get_mut(&mut self, state: &StatesRef) -> Option<&mut V> {
		let mut index = self.0.len();
		let mut index_state = state.history.len() - 1;

		// note that we expect branch index to be linearily set
		// along a branch (no state containing unordered branch_index
		// and no history containing unorderd branch_index).
		if index == 0 || index_state == 0 {
			return self.1.as_mut();
		}
		while index > 0 && index_state > 0 {
			index -= 1;
			let branch_index = self.0[index].branch_index;

			while index_state > 0 && state.history[index_state].branch_index > branch_index {
				index_state -= 1;
			}
			if state.history[index_state].branch_index == branch_index {
				if let Some(result) = self.branch_get_unchecked_mut(branch_index, &state.history[index_state]) {
					return Some(result)
				}
			}
		}
		self.1.as_mut()
	}

	fn branch_get_unchecked_mut(&mut self, branch_index: u64, state: &StatesBranchRef) -> Option<&mut V> {
		let history = &mut self.0[branch_index as usize];
		let mut index = history.history.len();
		if index == 0 {
			return None;
		}
		while index > 0 {
			index -= 1;
			if let Some(&mut v) = history.history.get_mut(index).as_mut() {
				if v.index < state.state.end {
					return Some(&mut v.value);
				}
			}
		}
		None
	}
*/
}


#[cfg(test)]
mod test {
	use super::*;

	fn test_states() -> TestStates {
		let mut states = TestStates::default();
		assert_eq!(states.create_branch(1, 0, None), Some(1));
		// root branching.
		assert_eq!(states.create_branch(1, 0, None), Some(2));
		assert_eq!(Some(true), states.branch_state_mut(1).map(|ls| ls.add_state()));
		assert_eq!(states.create_branch(2, 1, None), Some(3));
		assert_eq!(states.create_branch(1, 1, Some(0)), Some(5));
		assert_eq!(states.create_branch(1, 1, Some(2)), None);
		assert_eq!(Some(true), states.branch_state_mut(1).map(|ls| ls.add_state()));
		assert_eq!(Some(Some(2)), states.branch_state_mut(1).map(|ls| ls.drop_state()));
		// cannot create when dropped happen on branch
		assert_eq!(Some(false), states.branch_state_mut(1).map(|ls| ls.add_state()));

		// TODO add content through branching
		assert!(states.get(1, 1));
		// 0> 1: _ _ X
		// |			 |> 3: 1
		// |			 |> 4: 1
		// |		 |> 5: 1
		// |> 2: _

		states
	}

	#[test]
	fn test_remove_attached() {
		let mut states = test_states();
		assert_eq!(Some(Some(1)), states.branch_state_mut(1).map(|ls| ls.drop_state()));
		assert!(states.get(3, 0));
		assert!(states.get(4, 0));
		states.apply_drop_state(1, 1);
		assert!(!states.get(3, 0));
		assert!(!states.get(4, 0));
	}

	#[test]
	fn test_state_refs() {
		let states = test_states();
		let ref_3 = vec![
			StatesBranchRef {
				branch_index: 1,
				state: BranchStateRef { start: 0, end: 2 },
			},
			StatesBranchRef {
				branch_index: 3,
				state: BranchStateRef { start: 0, end: 1 },
			},
		];
		assert_eq!(*states.state_ref(3).history, ref_3);

		let mut states = states;

		assert_eq!(states.create_branch(1, 1, Some(0)), Some(6));
		let ref_6 = vec![
			StatesBranchRef {
				branch_index: 1,
				state: BranchStateRef { start: 0, end: 1 },
			},
			StatesBranchRef {
				branch_index: 6,
				state: BranchStateRef { start: 0, end: 1 },
			},
		];
		assert_eq!(*states.state_ref(6).history, ref_6);

		states.valid_treshold = 3;
		let mut ref_6 = ref_6;
		ref_6.remove(0);
		assert_eq!(*states.state_ref(6).history, ref_6);
	}

	#[test]
	fn test_set_get() {
		// 0> 1: _ _ X
		// |			 |> 3: 1
		// |			 |> 4: 1
		// |		 |> 5: 1
		// |> 2: _
		let states = test_states();
		let mut item: History<u64> = Default::default();

		for i in 0..6 {
			assert_eq!(item.get(&states.state_ref(i)), None);
		}

		// setting value respecting branch build order
		for i in 1..6 {
			item.set(&states.state_ref(i), i);
		}

		for i in 1..6 {
			assert_eq!(item.get(&states.state_ref(i)), Some(&i));
		}

		let mut ref_3 = states.state_ref(3);
		ref_3.limit_branch(1, None);
		assert_eq!(item.get(&ref_3), Some(&1));

		let mut ref_1 = states.state_ref(1);
		ref_1.limit_branch(1, Some(0));
		assert_eq!(item.get(&ref_1), None);
		item.set(&ref_1, 11);
		assert_eq!(item.get(&ref_1), Some(&11));

		item = Default::default();

		// could rand shuffle if rand get imported later.
		let disordered = [
			[1,2,3,5,4],
			[2,5,1,3,4],
			[5,3,2,4,1],
		];
		for r in disordered.iter() {
			for i in r {
				item.set(&states.state_ref(*i), *i);
			}
			for i in r {
				assert_eq!(item.get(&states.state_ref(*i)), Some(i));
			}
		}

	}

}

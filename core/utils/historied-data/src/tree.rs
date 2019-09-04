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

// memo:
// - for linear
// in or out only, state is parent state for in (out can always get gc).
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
// probably need to manage a collection of branch_ix to gc: when linear state is reduced).
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

use crate::{
	State as TransactionState,
};
use crate::linear::{
	MemoryOnly as LinearHistory,
};
use rstd::borrow::Cow;
use rstd::vec::Vec;
use rstd::collections::btree_map::BTreeMap;

#[derive(Debug, Clone)]
#[cfg_attr(any(test, feature = "test"), derive(PartialEq))]
pub struct LinearStates {
	/// number of elements: all elements equal or bellow
	/// this index are valid, over this index they are not.
	len: usize,
	/// Indicates if the state is modifiable (when an element is dropped
	/// we cannot append and need to create a new branch).
	has_deleted_index: bool,
}

impl Default for LinearStates {
	fn default() -> Self {
		LinearStates {
			len: 1,
			has_deleted_index: false,
		}
	}
}

impl LinearStates {
	pub fn add_state(&mut self) -> bool {
		if !self.has_deleted_index {
			self.len += 1;
			true
		} else {
			false
		}
	}

	pub fn drop_state(&mut self) {
		if self.len > 0 {
			self.len -= 1;
			self.has_deleted_index = true;
			// TODO add ix to a to be gc collection
		}
	}

	/// act as a truncate
	pub fn keep_state(&mut self, index: usize) {
		if self.len > index {
			self.len = index;
			self.has_deleted_index = true;
			// TODO add ix to a to be gc collection
		}
	}

	/// get state
	/// simply return true if exists (there is no specific state).
	pub fn get_state(&self, index: usize) -> bool {
		self.len > index
	}

	pub fn latest_ix(&self) -> Option<usize> {
		if self.len > 0 {
			Some(self.len - 1)
		} else {
			None
		}
	}


}
// TODO could benefit from smallvec!! need an estimation
// of number of node (it still stores a usize + a smallvec) 
#[derive(Debug, Clone)]
#[cfg_attr(any(test, feature = "test"), derive(PartialEq))]
pub struct History<V>(Vec<HistoryBranch<V>>);

#[derive(Debug, Clone)]
#[cfg_attr(any(test, feature = "test"), derive(PartialEq))]
pub struct HistoryBranch<V> {
	branch_index: usize,
	history: LinearHistory<V>,
}

#[derive(Debug, Clone)]
#[cfg_attr(any(test, feature = "test"), derive(PartialEq))]
pub struct Serialized<'a>(Cow<'a, [u8]>);

#[derive(Debug, Clone)]
#[cfg_attr(any(test, feature = "test"), derive(PartialEq))]
pub struct States {
	branches: BTreeMap<usize, StatesBranch>,
	last_branch_ix: usize,
	committed_ix: usize,
	prospective_ix: usize,
}

impl StatesBranch {
	pub fn is_committed(&self, states: &States) -> bool {
		self.is_committed_internal(states.committed_ix)
	}
	fn is_committed_internal(&self, committed_ix: usize) -> bool {
		self.committed_ix <= committed_ix
	}
	
	pub fn is_prospective(&self, states: &States) -> bool {
		self.is_prospective_internal(states.prospective_ix)
	}
	fn is_prospective_internal(&self, prospective_ix: usize) -> bool {
		self.prospective_ix >= prospective_ix
	}

	fn is_dropped_internal(&self, prospective_ix: usize, committed_ix: usize) -> bool {
		!self.is_committed_internal(committed_ix)
			&& !self.is_prospective_internal(prospective_ix)
	}
	pub fn is_dropped(&self, states: &States) -> bool {
		self.is_dropped_internal(states.prospective_ix, states.committed_ix)
	}
}

impl Default for States {
	fn default() -> Self {
		States {
			branches: Default::default(),
			last_branch_ix: 0,
			committed_ix: 0,
			prospective_ix: 0,
		}
	}
}

#[derive(Debug, Clone)]
#[cfg_attr(any(test, feature = "test"), derive(PartialEq))]
pub struct StatesBranch {
	// this is the key (need to growth unless full gc (can still have
	// content pointing to it even if it seems safe to reuse a previously
	// use ix).
	branch_ix: usize,
	
	origin_branch_ix: usize,
	origin_linear_ix: usize,

	prospective_ix: usize,

	committed_ix: usize,

	state: LinearStates,
}

// TODO could benefit from smallvec!!
// of number of node (it still stores a few usize & a vec ptr)
/// Reference to state that is enough for query updates, but not
/// for gc.
/// Values are ordered by branch_ix (first value of tuple),
/// and only a logich branch path should be present.
pub type StatesRef = Vec<(usize, StatesBranch)>;

impl States {

	/// clear state but keep existing branch values (can be call after a full gc:
	/// enforcing no commited containing dropped values).
	pub fn unsafe_clear(&mut self) {
		self.branches.clear();
		self.last_branch_ix = 0;
	}

	pub fn as_ref(&self, branch_ix: usize) -> StatesRef {
		unimplemented!();
	}

	// create a branches. End current branch.
	// Return first created index (next branch are sequential indexed)
	// or None if origin branch does not allow branch creation (commited branch or non existing).
	pub fn create_branch(
		&mut self,
		nb_branch: usize,
		branch_ix: usize,
		linear_ix: Option<usize>,
	) -> Option<usize> {
		if nb_branch == 0 {
			return None;
		}

		// for 0 is the first branch creation case
		let linear_ix = if branch_ix == 0 {
			debug_assert!(linear_ix.is_none());
			0
		} else {
			if let Some(linear_ix) = self.get_node(branch_ix, linear_ix) {
				linear_ix
			} else {
				return None;
			}
		};

		let result_ix = self.last_branch_ix + 1;
		for i in result_ix .. result_ix + nb_branch {
			self.branches.insert(i, StatesBranch {
				branch_ix: i,
				origin_branch_ix: branch_ix,
				origin_linear_ix: linear_ix,
				committed_ix: usize::max_value(),
				prospective_ix: self.prospective_ix,
				state: Default::default(),
			});
		}
		self.last_branch_ix += nb_branch;

		Some(result_ix)
	}

	/// check if node is valid for given index.
	/// return linear_ix.
	/// TODO consider renaming?
	pub fn get_node(
		&self,
		branch_ix: usize,
		linear_ix: Option<usize>,
	) -> Option<usize> {
		if let Some(branch) = self.branches.get(&branch_ix) {
			if let Some(linear_ix) = linear_ix {
				if branch.state.get_state(linear_ix) {
					Some(linear_ix)
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

	/// get node without index checks, can panick.
	pub fn get(&self, branch_ix: usize, linear_ix: usize) -> TransactionState {
		unimplemented!();
	}

	pub fn linear_state(&self, branch_ix: usize) -> Option<&LinearStates> {
		self.branches.get(&branch_ix)
			.filter(|b| !b.is_dropped_internal(self.prospective_ix, self.committed_ix))
			.map(|b| &b.state)
	}

	// does remove branch if dropped.
	fn access_branch_mut(&mut self, branch_ix: usize) -> Option<&mut StatesBranch> {
		if let Some(branch) = self.branches.get(&branch_ix) {
			if branch.is_dropped_internal(self.prospective_ix, self.committed_ix) {
				let _ = self.branches.remove(&branch_ix);
				return None;
			} else {
				return self.branches.get_mut(&branch_ix);
			}
		}
		None
	}


	pub fn linear_state_mut (&mut self, branch_ix: usize) -> Option<&mut LinearStates> {
		self.access_branch_mut(branch_ix)
//			.filter(|b| !b.has_children)
			.map(|b| &mut b.state)
	}

}

pub fn ref_get(s: &StatesRef, branch_ix: usize, linear_ix: usize) -> TransactionState {
	unimplemented!();
}

#[cfg(test)]
mod test {
	use super::*;

	fn test_states() -> States {
		let mut states = States::default();
		assert_eq!(states.create_branch(1, 0, None), Some(1));
		// root branching.
		assert_eq!(states.create_branch(1, 0, None), Some(2));
		states.linear_state_mut(1).map(|ls| ls.add_state());
		assert_eq!(states.create_branch(2, 1, None), Some(3));
		assert_eq!(states.create_branch(1, 1, Some(0)), Some(5));
		assert_eq!(states.create_branch(1, 1, Some(2)), None);
		assert_eq!(Some(true), states.linear_state_mut(1).map(|ls| ls.add_state()));
		states.linear_state_mut(1).map(|ls| ls.drop_state());
		// cannot create when dropped happen on branch
		assert_eq!(Some(false), states.linear_state_mut(1).map(|ls| ls.add_state()));
		// TODO add content through branching
		assert!(states.linear_state(1).is_some());
		// 0> 1: _ _
		// |			 |> 3: 1
		// |			 |> 4: 1
		// |		 |> 5: 1
		// |> 2: _

		panic!("{:?}", states);
		states
	}

	#[test]
	fn test_to_define() {
		let states = test_states();
	}
}

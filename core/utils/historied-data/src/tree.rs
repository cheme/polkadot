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

//! Data store acyclic directed graph as trie.
//!
//! General structur is an array of linear, each linear originating
//! from another array at designated index.
//!
//! Only support commited and prospective states.

// memo:
// - for linear
// transaction = new block number (new block new tx)
// commit transaction = fusioning two blocks (should never be use)
// discard transaction = removing a block (latest one in branch).
// - for tree
// commit prospective = 
// put commit counter to prospective counter +1, then recurse branch in path to this value. 
// primitive spawn two new branches and end the previous one)
// New branches uses a + 1 commmited counter (meaning prospective).
// Also on commit we branch an new prospective one (counter +1).
// discard prospective = increase prospective counter.

use crate::{
	State as TransactionState,
};
use crate::linear::{
	History as LinearHistory,
	Serialized as LinearSerialized,
	States as LinearStates,
};
use rstd::borrow::Cow;
use rstd::vec::Vec;
use rstd::collections::btree_map::BTreeMap;

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
    self.state_ix == states.committed_ix
  }
  pub fn is_prospective(&self, states: &States) -> bool {
    self.state_ix > states.prospective_ix
  }
  pub fn is_dropped(&self, states: &States) -> bool {
    self.state_ix != states.committed_ix
    && self.state_ix < states.prospective_ix
  }
}

impl Default for States {
	fn default() -> Self {
		States {
			branches: Default::default(),
			last_branch_ix: 0,
			committed_ix: 0,
			prospective_ix: 1,
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
  // status of the branch, if the index is less than
  // states committed_ix, then the full branch is not in
  // the committed path, and seen as dropped.
  // in between committed and prospective ix it is also a dropped prospective index.
	state_ix: usize,

	origin_branch_ix: usize,

  // when a branch has children it cannot be change (get_mut return none
  // when get return something).
	has_children: bool,

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

	pub fn clear(&mut self) {
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
		branch_ix: usize,
		nb_branch: usize,
	) -> Option<usize> {
		// empty case
		if self.last_branch_ix == 0 {
			self.last_branch_ix = 1;
      for i in 1..nb_branch + 1 {
        self.branches.insert(1, StatesBranch {
          branch_ix: i,
          origin_branch_ix: 0,
          state_ix: self.prospective_ix,
          has_children: false,
          state: Default::default(),
        });
      }
			Some(1)
		} else {
      // TODO get linear state mut mapped over commitedix > commitedix (lazy clear)
      // then check linear ix opt.
			unimplemented!()
		}
	}

	pub fn get(&self, branch_ix: usize, linear_ix: usize) -> TransactionState {
		unimplemented!();
	}

	pub fn linear_state(&self, branch_ix: usize) -> Option<&LinearStates> {
		unimplemented!();
	}

	pub fn linear_state_mut (&mut self, branch_ix: usize) -> Option<&mut LinearStates> {
    // TODO return state prospective, not commited, not branched
		unimplemented!();
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
		assert_eq!(states.create_branch(0, 1), Some(1));
    // root branching.
		assert_eq!(states.create_branch(0, 1), Some(2));
    // new txs
    for _ in 0..3 {
      states.linear_state_mut(1).map(|ls| ls.start_transaction());
    }
		assert_eq!(states.create_branch(1, 2), Some(3));
    assert_eq!(states.linear_state_mut(1), None);
    assert!(states.linear_state(1).is_some());
		states
	}

	#[test]
  fn test_to_define() {
    let states = test_states();
  }
}

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
}

impl Default for States {
	fn default() -> Self {
		States {
			branches: Default::default(),
			last_branch_ix: 0,
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

	// create a branch in branch_ix, return new branch_ix
	pub fn create_branch(
		&mut self,
		branch_ix: usize,
		linear_ix: Option<usize>,
		branch_initial_state: Option<LinearStates>,
	) -> Option<usize> {
		// empty case
		if self.last_branch_ix == 0 {
			debug_assert!(linear_ix.is_none());
			self.last_branch_ix = 1;
			self.branches.insert(1, StatesBranch {
				branch_ix: 1,
				origin_branch_ix: 0,
				origin_linear_ix: 0,
				state: branch_initial_state.unwrap_or_else(Default::default),
			});
			Some(1)
		} else {
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
		unimplemented!();
	}

}

pub fn ref_get(s: &StatesRef, branch_ix: usize, linear_ix: usize) -> TransactionState {
		unimplemented!();
}

#[cfg(test)]
mod test {
	use super::*;

	fn test_state() -> States {
		let mut states = States::default();
		assert_eq!(states.create_branch(0, None, None), Some(1));
		states
	}

}

// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! Offstate storage types

// TODO may remove in favor of utils/historied-data

use codec::{Encode, Decode};
use rstd::prelude::Vec;

/// Reference to state that is enough for query updates, but not
/// for gc.
/// Values are ordered by branch_ix,
/// and only a logic branch path should be present.
///
/// Note that an alternative could be a pointer to a full state
/// branch for a given branch index, here we use an in memory
/// copied representation in relation to an actual use case.
pub type BranchRanges = Vec<StatesBranchRef>;


#[derive(Debug, Clone, PartialEq, Eq)]
#[derive(Encode, Decode)]
pub struct StatesBranchRef {
	pub branch_index: u64,
	pub state: LinearStatesRef,
}

/// This is a simple range, end non inclusive.
#[derive(Debug, Clone, PartialEq, Eq)]
#[derive(Encode, Decode)]
pub struct LinearStatesRef {
	// TODO EMCH makes start and end private
	pub start: u64,
	pub end: u64,
}



// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! Backend for storing data without a state.

use primitives::offstate::{BranchRanges, LinearStatesRef, StatesBranchRef};

pub trait OffstateBackendStorage {
/*	/// state type for querying data
	/// (similar to hash for a trie_backend).
	trait ChanState;*/

	/// Persist a value in storage under given key and prefix.
	fn set(&mut self, prefix: &[u8], key: &[u8], value: &[u8]);

	/// Retrieve a value from storage under given key and prefix.
	fn get(&self, prefix: &[u8], key: &[u8]) -> Option<Vec<u8>>;

}

impl OffstateBackendStorage for TODO {
	//trait ChainState = BranchRanges;

	fn set(&mut self, prefix: &[u8], key: &[u8], value: &[u8]) {
		unimplemented!()
	}

	fn get(&self, prefix: &[u8], key: &[u8]) -> Option<Vec<u8>> {
		unimplemented!()
	}

}

// TODO EMCH implement, generic over a keyvalue db using BranchRanges so it is same impl for inmemory or
// actual ext.
pub struct TODO(pub BranchRanges);


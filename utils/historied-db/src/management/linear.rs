// This file is part of Substrate.

// Copyright (C) 2020-2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.


//! Linear state management implementations.

use crate::Latest;
use crate::management::{Management, ManagementRef, Migrate, LinearManagement};
use sp_std::ops::{AddAssign, SubAssign};
use num_traits::One;

// This is for small state as there is no double
// mapping an some operation goes through full scan.
pub struct LinearInMemoryManagement<H, S> {
	mapping: sp_std::collections::btree_map::BTreeMap<H, S>,
	start_treshold: S,
	current_state: S,
	changed_treshold: bool,
	can_append: bool,
}

impl<H, S: AddAssign<u32>> LinearInMemoryManagement<H, S> {
	pub fn prune(&mut self, nb: usize) {
		self.changed_treshold = true;
		self.start_treshold += nb as u32
	}
}

impl<H: Ord, S: Clone> ManagementRef<H> for LinearInMemoryManagement<H, S> {
	type S = S;
	type GC = S;
	type Migrate = (S, Self::GC);
	fn get_db_state(&mut self, state: &H) -> Option<Self::S> {
		self.mapping.get(state).cloned()
	}
	fn get_gc(&self) -> Option<crate::Ref<Self::GC>> {
		if self.changed_treshold {
			Some(crate::Ref::Owned(self.start_treshold.clone()))
		} else {
			None
		}
	}
}

impl<
H: Ord + Clone,
S: Default + Clone + AddAssign<u32> + Ord,
> Default for LinearInMemoryManagement<H, S> {
	fn default() -> Self {
		let state = S::default();
		let current_state = S::default();
		let mapping = Default::default();
		LinearInMemoryManagement {
			mapping,
			start_treshold: state.clone(),
			current_state,
			changed_treshold: false,
			can_append: true,
		}
	}
}

impl<
H: Ord + Clone,
S: Default + Clone + AddAssign<u32> + Ord,
> Management<H> for LinearInMemoryManagement<H, S> {
	type SE = Latest<S>;

	fn get_db_state_mut(&mut self, state: &H) -> Option<Self::SE> {
		if let Some(state) = self.mapping.get(state) {
			let latest = self.mapping.values().max()
				.map(Clone::clone)
				.unwrap_or(S::default());
			if state == &latest {
				return Some(Latest::unchecked_latest(latest))
			}
		}
		None
	}

	fn latest_state(&mut self) -> Self::SE {
		Latest::unchecked_latest(self.current_state.clone())
	}

	fn latest_external_state(&mut self) -> Option<H> {
		// Actually unimplemented
		None
	}

	fn force_latest_external_state(&mut self, _state: H) { }

	fn reverse_lookup(&mut self, state: &Self::S) -> Option<H> {
		// TODO could be the closest valid and return non optional!!!! TODO
		self.mapping.iter()
			.find(|(_k, v)| v == &state)
			.map(|(k, _v)| k.clone())
	}

	fn get_migrate(&mut self) -> Migrate<H, Self> {
		unimplemented!()
	}

	fn applied_migrate(&mut self) {
		self.changed_treshold = false;
		//self.start_treshold = gc.0; // TODO from backed inner state

		unimplemented!()
	}
}

impl<
H: Ord + Clone,
S: Default + Clone + SubAssign<S> + AddAssign<S> + Ord + One,
> LinearManagement<H> for LinearInMemoryManagement<H, S> {
	fn append_external_state(&mut self, state: H) -> Option<Self::S> {
		if !self.can_append {
			return None;
		}
		self.current_state += S::one();
		self.mapping.insert(state, self.current_state.clone());
		Some(self.current_state.clone())
	}

	fn drop_last_state(&mut self) -> Self::S {
		let mut v = S::default();
		if self.current_state != v {
			v += S::one();
			self.current_state -= v;
		}
		self.can_append = true;
		self.current_state.clone()
	}
}

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

//! History state storage and management.

/// Forkable state management implementations.
pub mod tree;

/// Linear state management implementations.
pub mod linear {

	use crate::{Latest, Management, ManagementRef, Migrate, LinearManagement};
	use sp_std::ops::{AddAssign, SubAssign};

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
	S: Default + Clone + SubAssign<S> + AddAssign<u32> + Ord,
	> LinearManagement<H> for LinearInMemoryManagement<H, S> {
		fn append_external_state(&mut self, state: H) -> Option<Self::S> {
			if !self.can_append {
				return None;
			}
			self.current_state += 1;
			self.mapping.insert(state, self.current_state.clone());
			Some(self.current_state.clone())
		}

		fn drop_last_state(&mut self) -> Self::S {
			let mut v = S::default();
			if self.current_state != v {
				v += 1;
				self.current_state -= v;
			}
			self.can_append = true;
			self.current_state.clone()
		}
	}
}

/*
#[cfg(feature = "std")]
use std::sync::Arc;
#[cfg(not(feature = "std"))]
use alloc::sync::Arc;
*/

use sp_std::vec::Vec;
use sp_std::boxed::Box;
use crate::{Management, Migrate};
/// Dynamic trait to register historied db
/// implementation in order to allow migration
/// (state global change requires to update all associated dbs).
pub trait ManagementConsumer<H, M: Management<H>>: Send + Sync + 'static {
	fn migrate(&self, migrate: &mut Migrate<H, M>);
	fn default_as_neutral_element(&self) -> bool;
}

/// Register db, this associate treemanagement.
pub fn consumer_to_register<H, M: Management<H>, C: ManagementConsumer<H, M> + Clone>(c: &C) -> Box<dyn ManagementConsumer<H, M>> {
	Box::new(c.clone())
}

/* This is not require I guess.
/// Most consume db usage happens in multi-threading scenario.
pub trait ManagementConsumerSync: ManagementConsumer + Send + Sync { }

/// Register db, this associate treemanagement.
pub fn consumer_to_register_sync<C: ManagementConsumerSync + Clone>(c: &C) -> Arc<dyn ManagementConsumer> {
	Arc::new(c.clone())
}

impl<X: ManagementConsumer + Send + Sync> ManagementConsumerSync for X { }
*/
/// Management consumer base implementation.
pub struct JournalForMigrationBasis<S: Ord, K, Db, DbConf> {
	touched_keys: crate::simple_db::SerializeMap<S, Vec<K>, Db, DbConf>,
}

impl<S, K, Db, DbConf> JournalForMigrationBasis<S, K, Db, DbConf>
	where
		S: codec::Codec + Clone + Ord,
		K: codec::Codec + Clone + Ord,
		Db: crate::simple_db::SerializeDB,
		DbConf: crate::simple_db::SerializeInstanceMap,
{
	/// Note that if we got no information of the state, using `is_new` as
	/// false is always safe.
	pub fn add_changes(&mut self, db: &mut Db, state: S, mut changes: Vec<K>, is_new: bool) {
		let mut handle = self.touched_keys.handle(db);
		let changes = if is_new {
			changes.dedup();
			changes
		} else {
			if let Some(existing) = handle.get(&state) {
				let mut existing = existing.clone();
				merge_keys(&mut existing, changes);
				existing
			} else {
				changes.dedup();
				changes
			}
		};
		handle.insert(state, changes);
	}

	pub fn remove_changes_at(&mut self, db: &mut Db, state: &S) -> Option<Vec<K>> {
		let mut handle = self.touched_keys.handle(db);
		handle.remove(state)
	}

	pub fn remove_changes_before(
		&mut self,
		db: &mut Db,
		state: &S,
		result: &mut sp_std::collections::btree_set::BTreeSet<K>,
	) {
		let mut handle = self.touched_keys.handle(db);
		// TODO can be better with entry iterator (or key iterator at least)
		let mut to_remove = Vec::new();
		for kv in handle.iter() {
			if &kv.0 < state {
				to_remove.push(kv.0);
			} else {
				break;
			}
		}
		for state in to_remove.into_iter() {
			if let Some(v) = handle.remove(&state) {
				for k in v {
					result.insert(k);
				}
			}
		}
	}

	pub fn from_db(db: &Db) -> Self {
		JournalForMigrationBasis {
			touched_keys: crate::simple_db::SerializeMap::default_from_db(&db),
		}
	}
}

// TODO test case or btreeset impl.
fn merge_keys<K: Ord>(origin: &mut Vec<K>, mut keys: Vec<K>) {
	origin.sort_unstable();
	keys.sort_unstable();
	let mut cursor: usize = 0;
	let end = origin.len();
	for key in keys.into_iter() {
		if Some(&key) == origin.last() {
			// skip (avoid duplicate in keys)
		} else if cursor == end {
			origin.push(key);
		} else {
			while cursor != end && origin[cursor] < key {
				cursor += 1;
			}
			if cursor < end && origin[cursor] != key {
				origin.push(key);
			}
		}
	}
}

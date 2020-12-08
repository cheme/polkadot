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
//!
//! This associate a tag (for instance a block hash),
//! with historical state index.
//! Tags are usually associated with the generic parameter `H`.
//!
//! It allows building different states from state index
//! for different operation on historical data.

/// Forkable state management implementations.
pub mod tree;

/// Linear state management implementations.
pub mod linear;

/*
#[cfg(feature = "std")]
use std::sync::Arc;
#[cfg(not(feature = "std"))]
use alloc::sync::Arc;
*/

use sp_std::{vec::Vec, boxed::Box, marker::PhantomData};
use crate::Ref;

/// Management maps a historical tag of type `H` with its different db states representation.
pub trait Management<H> {
	/// attached db state needed for query.
	type S;
	/// attached db gc strategy.
	/// TODO at Mut level? also is having a mut variant of any use here?
	type GC;
	type Migrate;
	/// Returns the historical state representation for a given historical tag.
	fn get_db_state(&mut self, tag: &H) -> Option<Self::S>;
	/// returns optional to avoid holding lock of do nothing GC.
	/// TODO this would need RefMut or make the serialize cache layer inner mutable.
	fn get_gc(&self) -> Option<Ref<Self::GC>>;
}

pub trait ManagementMut<H>: Management<H> + Sized {
	/// attached db state needed for update.
	type SE; // TODO rename to latest or pending???

	/// Return state mut for state but only if state exists and is
	/// a terminal writeable leaf (if not you need to create new branch 
	/// from previous state to write).
	fn get_db_state_mut(&mut self, tag: &H) -> Option<Self::SE>;

	/// Get a cursor over the last change of ref (when adding or removing).
	fn latest_state(&mut self) -> Self::SE;

	/// Return latest added external index, can return None
	/// if reverted.
	fn latest_external_state(&mut self) -> Option<H>;

	/// Force change value of latest external state.
	fn force_latest_external_state(&mut self, index: H);

	fn reverse_lookup(&mut self, state: &Self::S) -> Option<H>;

	/// see migrate. When running thes making a backup of this management
	/// state is usually a good idea (this method does not manage
	/// backup or rollback).
	fn get_migrate(&mut self) -> Migrate<H, Self>;

	/// report a migration did run successfully, will update management state
	/// accordingly.
	/// All previously fetch states are unvalid.
	/// There is no type constraint of this, because migration is a specific
	/// case the general type should not be complexified.
	fn applied_migrate(&mut self);
}

/// This trait is for mapping a given state to the DB opaque inner state.
pub trait ForkableManagement<H>: ManagementMut<H> {
	/// Do we keep trace of changes.
	const JOURNAL_DELETE: bool;
	/// Fork at any given internal state.
	type SF;

	/// SF is a state with 
	fn inner_fork_state(&self, s: Self::SE) -> Self::SF;

	/// SF from a S (usually the head of S)
	fn ref_state_fork(&self, s: &Self::S) -> Self::SF;

	fn get_db_state_for_fork(&mut self, tag: &H) -> Option<Self::SF>;

	/// Useful to fork in a independant branch (eg no parent reference found).
	fn init_state_fork(&mut self) -> Self::SF;

	fn latest_state_fork(&mut self) -> Self::SF {
		let se = self.latest_state();
		self.inner_fork_state(se)
	}

	/// This only succeed valid `at`.
	fn append_external_state(&mut self, state: H, at: &Self::SF) -> Option<Self::SE>;

	/// Note that this trait could be simplified to this function only.
	/// But SF can generally be extracted from an SE or an S so it is one less query.
	fn try_append_external_state(&mut self, state: H, at: &H) -> Option<Self::SE> {
		self.get_db_state_for_fork(&at)
			.and_then(|at| self.append_external_state(state, &at))
	}

	/// Warning this should cover all children recursively and can be slow for some
	/// implementations.
	/// Return all dropped tag.
	fn drop_state(&mut self, state: &Self::SF, return_dropped: bool) -> Option<Vec<H>>;

	fn try_drop_state(&mut self, tag: &H, return_dropped: bool) -> Option<Vec<H>> {
		self.get_db_state_for_fork(tag)
			.and_then(|at| self.drop_state(&at, return_dropped))
	}
}

pub trait LinearManagement<H>: Management<H> {
	fn append_external_state(&mut self, state: H) -> Option<Self::S>;

	// cannot be empty: if at initial state we return initial
	// state and initialise with a new initial state.
	fn drop_last_state(&mut self) -> Self::S;
}

/// Latest from fork only, this is for use case of aggregable
/// data cache: to store the aggregate cache.
/// (it only record a single state per fork!! but still need to resolve
/// if new fork is needed so hold almost as much info as a forkable management).
/// NOTE aggregable data cache is a cache that reply to locality
/// (a byte trie with locks that invalidate cache when set storage is call).
/// get_aggregate(aggregate_key)-> option<StructAggregate>
/// set_aggregate(aggregate_key, struct aggregate, [(child_info, lockprefixes)]).
pub trait ForkableHeadManagement<H>: Management<H> {
	fn register_external_state_head(&mut self, state: H, at: &Self::S) -> Self::S;
	fn try_register_external_state_head(&mut self, state: H, at: &H) -> Option<Self::S> {
		self.get_db_state(at).map(|at| self.register_external_state_head(state, &at))
	}
}

/// Type holding a state db to lock the management, until applying migration.
/// TODO consider removing applied migrate, since it is easier to use a transactional
/// backend on historied management.
pub struct Migrate<'a, H, M: ManagementMut<H>>(&'a mut M, M::Migrate, PhantomData<H>);

impl<'a, H, M: ManagementMut<H>> Migrate<'a, H, M> {
	pub fn new(management: &'a mut M, migrate: M::Migrate) -> Self {
		Migrate(management, migrate, PhantomData)
	}

	pub fn applied_migrate(self) {
		self.0.applied_migrate();
	}
	/// When using management from migrate,
	/// please unsure that you are not modifying
	/// management state in an incompatible way
	/// with the migration.
	pub fn management(&mut self) -> &mut M {
		self.0
	}
	pub fn migrate(&mut self) -> &mut M::Migrate {
		&mut self.1
 	}
}

/// Allows to consume event from the state management.
///
/// Current usage is mostly ensuring that migration occurs
/// on every compenent using the state (by registering these
/// components on the state management and implementing `migrate`).
pub trait ManagementConsumer<H, M: ManagementMut<H>>: Send + Sync + 'static {
	/// A migration runing on the state management,
	/// notice that the migrate parameter can be modified
	/// in case it contains data relative to this particular
	/// consumer. It is responsibility of the implementation
	/// to avoid changing this parameter in a way that would
	/// impact others consumer calls.
	fn migrate(&self, migrate: &mut Migrate<H, M>);
}

/// Cast the consumer to a dyn rust object.
pub fn consumer_to_register<H, M: ManagementMut<H>, C: ManagementConsumer<H, M> + Clone>(c: &C) -> Box<dyn ManagementConsumer<H, M>> {
	Box::new(c.clone())
}

/// Management consumer base implementation.
pub struct JournalForMigrationBasis<S: Ord, K, Db, DbConf> {
	touched_keys: crate::mapped_db::Map<S, Vec<K>, Db, DbConf>,
}

impl<S, K, Db, DbConf> JournalForMigrationBasis<S, K, Db, DbConf>
	where
		S: codec::Codec + Clone + Ord,
		K: codec::Codec + Clone + Ord,
		Db: crate::mapped_db::MappedDB,
		DbConf: crate::mapped_db::MapInfo,
{
	/// Note that if we got no information of the state, using `is_new` as
	/// false is always safe.
	pub fn add_changes(&mut self, db: &mut Db, state: S, mut changes: Vec<K>, is_new: bool) {
		let mut mapping = self.touched_keys.mapping(db);
		let changes = if is_new {
			changes.dedup();
			changes
		} else {
			if let Some(existing) = mapping.get(&state) {
				let mut existing = existing.clone();
				merge_keys(&mut existing, changes);
				existing
			} else {
				changes.dedup();
				changes
			}
		};
		mapping.insert(state, changes);
	}

	pub fn remove_changes_at(&mut self, db: &mut Db, state: &S) -> Option<Vec<K>> {
		let mut mapping = self.touched_keys.mapping(db);
		mapping.remove(state)
	}

	// TODO rename drain_changes_before?
	pub fn remove_changes_before(
		&mut self,
		db: &mut Db,
		state: &S,
		result: &mut sp_std::collections::btree_set::BTreeSet<K>,
	) {
		let mut mapping = self.touched_keys.mapping(db);
		// TODO can do better with entry iterator (or key iterator at least)
		let mut to_remove = Vec::new();
		for kv in mapping.iter() {
			if &kv.0 < state {
				to_remove.push(kv.0);
			} else {
				break;
			}
		}
		for state in to_remove.into_iter() {
			if let Some(v) = mapping.remove(&state) {
				for k in v {
					result.insert(k);
				}
			}
		}
	}

	pub fn from_db(db: &Db) -> Self {
		JournalForMigrationBasis {
			touched_keys: crate::mapped_db::Map::default_from_db(&db),
		}
	}
}

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

#[cfg(test)]
mod test {
	use super::*;
	use crate::test::InMemorySimpleDB5;
	#[test]
	fn test_merge_keys() {
		let mut set1 = vec![b"ab".to_vec(), b"bc".to_vec(), b"da".to_vec(), b"ab".to_vec()];
		let mut set2 = vec![b"rb".to_vec(), b"bc".to_vec(), b"rb".to_vec(), b"ab".to_vec()];
		// note that set1 should not have duplicate, so they are kept, while for set 2 they are removed.
		let res = vec![b"ab".to_vec(), b"ab".to_vec(), b"bc".to_vec(), b"da".to_vec(), b"rb".to_vec()];
		merge_keys(&mut set1, set2);
		assert_eq!(set1, res);
	}

	#[test]
	fn test_journal_for_migration() {
		#[derive(Default, Clone)]
		struct Collection;
		impl crate::mapped_db::MapInfo for Collection {
			const STATIC_COL: &'static [u8] = &[0u8, 0, 0, 0];
		}
		let mut db = InMemorySimpleDB5::new();
		{
			let mut journal = JournalForMigrationBasis::<u32, u16, _, Collection>::from_db(&db);
			journal.add_changes(&mut db, 1u32, vec![1u16], true);
			journal.add_changes(&mut db, 2u32, vec![2u16], true);
			journal.add_changes(&mut db, 3u32, vec![3u16], true);
			journal.add_changes(&mut db, 3u32, vec![1u16], false);
			journal.add_changes(&mut db, 8u32, vec![8u16], false);
		}
		{
			let mut journal = JournalForMigrationBasis::<u32, u16, _, Collection>::from_db(&db);
			assert_eq!(journal.remove_changes_at(&mut db, &8u32), Some(vec![8u16]));
			assert_eq!(journal.remove_changes_at(&mut db, &8u32), None);
			let mut set = std::collections::BTreeSet::new();
			journal.remove_changes_before(&mut db, &3u32, &mut set);
			assert_eq!(journal.remove_changes_at(&mut db, &2u32), None);
			assert_eq!(journal.remove_changes_at(&mut db, &1u32), None);
			let set: Vec<u16> = set.into_iter().collect();
			assert_eq!(set, vec![1u16, 2]);
			assert_eq!(journal.remove_changes_at(&mut db, &3u32), Some(vec![3u16, 1]));
		}
		{
			let mut journal = JournalForMigrationBasis::<u32, u16, _, Collection>::from_db(&db);
			assert_eq!(journal.remove_changes_at(&mut db, &8u32), None);
		}
	}
}

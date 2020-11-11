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

//! Traits for Db containing historied value.

use hash_db::{PlainDBRef, PlainDB};
use crate::{UpdateResult, Context, StateIndex,
	historied::{DataBasis, DataMut, Data, DataRef, Value}};
use sp_std::marker::PhantomData;

/// Basis trait for state db.
pub trait StateDBBasis<K> {
	/// State for this db.
	type S;

	/// Check for the existance of a hash-key.
	fn contains(&self, key: &K, at: &Self::S) -> bool;
}

/// Trait for immutable reference of a plain key value db.
pub trait StateDB<K, V>: StateDBBasis<K> {
	/// Look up a given hash into the bytes that hash to it, returning None if the
	/// hash is not known.
	fn get(&self, key: &K, at: &Self::S) -> Option<V>;
}

/// Variant of `StateDB` to return value without copy.
pub trait StateDBRef<K, V> {
	/// State for this db.
	type S;

	/// Look up a given hash into the bytes that hash to it, returning None if the
	/// hash is not known.
	fn get_ref(&self, key: &K, at: &Self::S) -> Option<&V>;
}

pub trait StateDBMut<K, V>: StateDBBasis<K> {
		// TODO associated type from DataMut??
	/// State to use here.
	/// We use a different state than
	/// for the ref as it can use different
	/// constraints.
	type SE;
	/// GC strategy that can be applied.
	/// GC can be run in parallel, it does not
	/// make query incompatible.
	type GC;
	/// Like gc but operation require a lock on the db
	/// and all pending state are invalidated.
	type Migrate;
	/// Insert a datum item into the DB. Insertions are counted and the equivalent
	/// number of `remove()`s must be performed before the data is considered dead.
	/// The caller should ensure that a key only corresponds to one value.
	fn emplace(&mut self, key: K, value: V, at: &Self::SE);

	/// Remove a datum previously inserted. Insertions can be "owed" such that the
	/// same number of `insert()`s may happen without the data being eventually
	/// being inserted into the DB. It can be "owed" more than once.
	/// The caller should ensure that a key only corresponds to one value.
	fn remove(&mut self, key: &K, at: &Self::SE);
	// TODO see issue on value for mut on gc
	fn gc(&mut self, gc: &Self::GC);
	// TODO see issue on value for mut on gc
	fn migrate(&mut self, mig: &mut Self::Migrate);
}

/// Implementation for plain db.
pub struct BTreeMap<K, V, D: Context>(pub(crate) sp_std::collections::btree_map::BTreeMap<K, D>, D::Context, PhantomData<V>);

impl<K: Ord, V, D: Context> BTreeMap<K, V, D> {
	pub fn new(init: D::Context) -> Self {
		BTreeMap(sp_std::collections::btree_map::BTreeMap::new(), init, PhantomData)
	}
}

impl<K: Ord, V, D: DataBasis + Context> StateDBBasis<K> for BTreeMap<K, V, D> {
	type S = D::S;

	fn contains(&self, key: &K, at: &Self::S) -> bool {
		self.0.get(key)
			.map(|h| h.contains(at))
			.unwrap_or(false)
	}
}

impl<K: Ord, V: Value + Clone, D: Data<V> + Context> StateDB<K, V> for BTreeMap<K, V, D> {
	fn get(&self, key: &K, at: &Self::S) -> Option<V> {
		self.0.get(key)
			.and_then(|h| h.get(at))
	}
}

// note that the constraint on state db ref for the associated type is bad (forces V as clonable).
impl<K: Ord, V: Value, D: DataRef<V> + Context> StateDBRef<K, V> for BTreeMap<K, V, D> {
	type S = D::S;

	fn get_ref(&self, key: &K, at: &Self::S) -> Option<&V> {
		self.0.get(key)
			.and_then(|h| h.get_ref(at))
	}
}

impl<K: Ord + Clone, V: Value + Clone + Eq, D: DataMut<V>> StateDBMut<K, V> for BTreeMap<K, V, D> {
	type SE = D::SE;
	type GC = D::GC;
	type Migrate = D::Migrate;

	fn emplace(&mut self, key: K, value: V, at: &Self::SE) {
		if let Some(hist) = self.0.get_mut(&key) {
			hist.set(value, at);
		} else {
			self.0.insert(key, D::new(value, at, self.1.clone()));
		}
	}

	fn remove(&mut self, key: &K, at: &Self::SE) {
		match self.0.get_mut(&key).map(|h| h.discard(at)) {
			Some(UpdateResult::Cleared(_)) => (),
			_ => return,
		}
		self.0.remove(&key);
	}

	fn gc(&mut self, gc: &Self::GC) {
		// retain for btreemap missing here.
		let mut to_remove = Vec::new();
		for (key, h) in self.0.iter_mut() {
			match h.gc(gc) {
				UpdateResult::Cleared(_) => (),
				_ => break,
			}
			to_remove.push(key.clone());
		}
		for k in to_remove {
			self.0.remove(&k);
		}
	}

	fn migrate(&mut self, mig: &mut Self::Migrate) {
		// retain for btreemap missing here.
		let mut to_remove = Vec::new();
		for (key, h) in self.0.iter_mut() {
			match h.migrate(mig) {
				UpdateResult::Cleared(_) => (),
				_ => break,
			}
			to_remove.push(key.clone());
		}
		for k in to_remove {
			self.0.remove(&k);
		}
	}
}

/// Implementation for plain db.
pub struct PlainDBState<K, DB, D, S> {
	db: DB,
	touched_keys: sp_std::collections::btree_map::BTreeMap<S, Vec<K>>, // TODO change that by a journal trait!!
	_ph: PhantomData<D>,
}

impl<K, D: DataBasis, DB: PlainDBRef<K, D>, S> StateDBBasis<K> for PlainDBState<K, DB, D, S> {
	type S = D::S;

	fn contains(&self, key: &K, at: &Self::S) -> bool {
		self.db.get(key)
			.map(|h| h.contains(at))
			.unwrap_or(false)
	}
}

impl<K, V: Value + Clone, D: Data<V>, DB: PlainDBRef<K, D>, S> StateDB<K, V> for PlainDBState<K, DB, D, S> {
	fn get(&self, key: &K, at: &Self::S) -> Option<V> {
		self.db.get(key)
			.and_then(|h| h.get(at))
	}
}


impl<
	K: Ord + Clone,
	V: Value + Clone + Eq,
	D: DataMut<V, Context = ()>,
	DB: PlainDBRef<K, D> + PlainDB<K, D>,
> StateDBMut<K, V> for PlainDBState<K, DB, D, D::Index>
	where
			D::Index: Clone + Ord,
{
	type SE = D::SE;
	type GC = D::GC;
	type Migrate = D::Migrate;

	fn emplace(&mut self, key: K, value: V, at: &Self::SE) {
		if let Some(mut hist) = <DB as PlainDB<_, _>>::get(&self.db, &key) {
			match hist.set(value, at) {
				UpdateResult::Changed(_) => self.db.emplace(key.clone(), hist),
				UpdateResult::Cleared(_) => self.db.remove(&key),
				UpdateResult::Unchanged => return,
			}
		} else {
			self.db.emplace(key.clone(), D::new(value, at, ()));
		}
		self.touched_keys.entry(at.index()).or_default().push(key);
	}

	fn remove(&mut self, key: &K, at: &Self::SE) {
		if let Some(mut hist) = <DB as PlainDB<_, _>>::get(&self.db, &key) {
			match hist.discard(at) {
				UpdateResult::Changed(_) => self.db.emplace(key.clone(), hist),
				UpdateResult::Cleared(_) => self.db.remove(&key),
				UpdateResult::Unchanged => return,
			}
		}
		self.touched_keys.entry(at.index()).or_default().push(key.clone());
	}

	fn gc(&mut self, gc: &Self::GC) {
		let mut keys: sp_std::collections::btree_set::BTreeSet<_> = Default::default();
		for touched in self.touched_keys.values() {
			for key in touched.iter() {
				keys.insert(key.clone());
			}
		}
		for key in keys {
			if let Some(mut hist) = <DB as PlainDB<_, _>>::get(&self.db, &key) {
				match hist.gc(gc) {
					UpdateResult::Changed(_) => self.db.emplace(key, hist),
					UpdateResult::Cleared(_) => self.db.remove(&key),
					UpdateResult::Unchanged => break,
				}
			}
		}
	}

	fn migrate(&mut self, mig: &mut Self::Migrate) {
		// TODO this is from old gc but seems ok (as long as touched is complete).
		// retain for btreemap missing here.
		let mut states = Vec::new();
		// TODO do we really want this error prone prefiltering??
		for touched in self.touched_keys.keys() {
			if D::is_in_migrate(touched, mig) {
				states.push(touched.clone());
			}
		}
		let mut keys: sp_std::collections::btree_set::BTreeSet<_> = Default::default();
		for state in states {
			if let Some(touched) = self.touched_keys.remove(&state) {
				for k in touched {
					keys.insert(k);
				}
			}
		}
		self.touched_keys.clear();
		for key in keys {
			if let Some(mut hist) = <DB as PlainDB<_, _>>::get(&self.db, &key) {
				match hist.migrate(mig) {
					UpdateResult::Changed(_) => self.db.emplace(key, hist),
					UpdateResult::Cleared(_) => self.db.remove(&key),
					UpdateResult::Unchanged => break,
				}
			}
		}
	}
}

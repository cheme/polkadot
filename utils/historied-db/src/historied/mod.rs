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

//! Linear historied data.

#[cfg(not(feature = "std"))]
use sp_std::vec::Vec;
use sp_std::marker::PhantomData;
use crate::{StateDBRef, UpdateResult, InMemoryStateDBRef, StateDB};
use hash_db::{PlainDB, PlainDBRef};
use crate::Latest;
use codec::{Encode, Decode, Input};
use sp_std::ops::Range;
use crate::{Context, DecodeWithContext, Trigger};

pub mod linear;
pub mod tree;

/// Trait for historied value
pub trait ValueRef<V: Item> {
	/// State to query for this value.
	type S;

	/// Get value at this state.
	fn get(&self, at: &Self::S) -> Option<V>;

	/// Check if a value exists at this state.
	fn contains(&self, at: &Self::S) -> bool;

	/// Check if this is empty.
	fn is_empty(&self) -> bool;
}

/// Trait for historied value with differential
/// storage.
pub trait ValueDiff<V: ItemDiff>: ValueRef<V::Diff> {
	/// Get value at this state.
	fn get_diff(&self, at: &Self::S) -> Option<V> {
		let mut builder = V::new_item_builder();
		let mut changes = Vec::new();
		if !self.get_diffs(at, &mut changes) {
			debug_assert!(changes.len() == 0); // Incoherent state no origin for diff
		}
		if changes.len() == 0 {
			return None;
		}
		for change in changes.into_iter().rev() {
			builder.apply_diff(change);
		}
		Some(builder.extract_item())
	}

	/// Accumulate all changes for this state.
	/// Changes are written in reverse order into `changes`.
	/// Return `true` if a complete change was written.
	fn get_diffs(&self, at: &Self::S, changes: &mut Vec<V::Diff>) -> bool;
}

// TODO EMCH refact with 'a for inner value
// and a get value type (see test on rust playground).
// So we only got ValueRef type.
pub trait InMemoryValueRef<V: Item>: ValueRef<V> {
	/// Get reference to the value at this state.
	fn get_ref(&self, at: &Self::S) -> Option<&V>;
}

pub trait InMemoryValueSlice<V: Item>: ValueRef<V> {
	/// Get reference to the value at this state.
	fn get_slice(&self, at: &Self::S) -> Option<&[u8]>;
}

pub trait InMemoryValueRange<S> {
	/// Get reference to the value from which this slice can be build.
	fn get_range(slice: &[u8], at: &S) -> Option<Range<usize>>;
}

/// An item of historied value.
pub trait Item: Sized {
	/// This associeted constant defines if a neutral item
	/// does exist.
	const NEUTRAL: bool;

	/// The storage representation.
	type Storage: Eq;

	/// The neutral item, is a default
	/// item for undefined value.
	/// eg for a value V that can be deleted, it will be
	/// of type `Option<V>` and `None` will be
	/// neutral.
	fn is_neutral(&self) -> bool;

	fn is_storage_neutral(storage: &Self::Storage) -> bool;

	fn from_storage(storage: Self::Storage) -> Self;

	fn into_storage(self) -> Self::Storage;
}

pub trait ItemRef: Item {
	fn from_storage_ref(storage: &Self::Storage) -> &Self;

	fn into_storage_ref(&self) -> &Self::Storage;

	fn from_storage_ref_mut(storage: &mut Self::Storage) -> &mut Self;

	fn into_storage_ref_mut(&mut self) -> &mut Self::Storage;
}

/// An item that can be build from consecutives
/// diffs. TODO rename (itemDiff should be the inner type)
pub trait ItemDiff: Sized {
	/// Internal Diff stored.
	/// Default is the empty value (a neutral value
	/// indicating that there is no content).
	type Diff: Item + Default;

	/// Internal type to build items.
	type ItemBuilder: ItemBuilder<ItemDiff = Self>;

	fn new_item_builder() -> Self::ItemBuilder {
		Self::ItemBuilder::new_item_builder()
	}

	/// Check if the item can be a building source for 
	/// TODO consider a trait specific to diff inner item.
	fn is_complete(diff: &Self::Diff) -> bool;
}

pub trait ItemBuilder {
	type ItemDiff: ItemDiff;

	fn new_item_builder() -> Self;
	fn apply_diff(&mut self, diff: <Self::ItemDiff as ItemDiff>::Diff);
	fn extract_item(&mut self) -> Self::ItemDiff;
}

/// This is a different trait than item diff, because usually
/// we are able to set the diff directly.
/// Eg if we manage a list, our diff will be index and new item.
/// If a vcdiff, it will be vcdiff calculated from a previous call to
/// get.
/// This usually means that we need to fetch item before modifying,
/// at this point this is how we should proceed (even if it means
/// a redundant query for modifying.
///
/// We could consider merging this trait with `ItemDiff`, and
/// have an automated update for the case where we did not fetch
/// the value first.
pub trait DiffBuilder {
	type ItemDiff: ItemDiff;

	fn new_diff_builder() -> Self;
	fn calculate_diff(
		&mut self,
		previous: &Self::ItemDiff,
		target: &Self::ItemDiff,
	) -> <Self::ItemDiff as ItemDiff>::Diff;
}

#[cfg(feature = "std")]
/// Diff using xdelta 3 lib
pub mod xdelta {
	use super::*;

	#[derive(Clone, PartialEq, Eq, Debug, Default)]
	pub struct BytesDelta(Vec<u8>);

	impl std::ops::Deref for BytesDelta {
		type Target = Vec<u8>;
		fn deref(&self) -> &Self::Target {
			&self.0
		}
	}

	impl std::ops::DerefMut for BytesDelta {
		fn deref_mut(&mut self) -> &mut Self::Target {
			&mut self.0
		}
	}

	impl From<Vec<u8>> for BytesDelta {
		fn from(v: Vec<u8>) -> Self {
			BytesDelta(v)
		}
	}

	impl<'a> From<&'a [u8]> for BytesDelta {
		fn from(v: &'a [u8]) -> Self {
			BytesDelta(v.to_vec())
		}
	}

	#[derive(Clone, Eq, Ord, PartialEq, PartialOrd, Debug)]
	pub enum BytesDiff {
		/// Encoded vc diff (contains enum encoding first byte)
		VcDiff(Vec<u8>),
		/// Fully encoded value (contains enum encoding first byte).
		Value(Vec<u8>),
		/// Deleted or non existent value.
		/// This is a neutral element.
		None,
	}

	impl Default for BytesDiff {
		fn default() -> Self {
			BytesDiff::None
		}
	}

	impl Item for BytesDiff {
		const NEUTRAL: bool = true;
		type Storage = Vec<u8>;

		fn is_neutral(&self) -> bool {
			if let BytesDiff::None = self {
				true
			} else {
				false
			}
		}

		fn is_storage_neutral(storage: &Self::Storage) -> bool {
			storage.as_slice() == &[0u8]
		}

		fn from_storage(storage: Self::Storage) -> Self {
			debug_assert!(storage.len() > 0);
			match storage[0] {
				0u8 => {
					debug_assert!(storage.len() == 1);
					BytesDiff::None
				},
				1u8 => BytesDiff::Value(storage),
				2u8 => BytesDiff::VcDiff(storage),
				_ => unreachable!("Item trait does not allow undefined content"),
			}
		}

		fn into_storage(self) -> Self::Storage {
			match self {
				BytesDiff::Value(storage) => {
					debug_assert!(storage[0] == 1u8);
					storage
				},
				BytesDiff::VcDiff(storage) => {
					debug_assert!(storage[0] == 2u8);
					storage
				},
				BytesDiff::None => vec![0], 
			}
		}
	}

	pub struct BytesDiffBuilder;

	impl DiffBuilder for BytesDiffBuilder {
		type ItemDiff = BytesDelta;

		fn new_diff_builder() -> Self {
			BytesDiffBuilder
		}
		fn calculate_diff(
			&mut self,
			previous: &Self::ItemDiff,
			target: &Self::ItemDiff,
		) -> <Self::ItemDiff as ItemDiff>::Diff {
			if target.0.len() == 0 {
				return BytesDiff::None;
			}
			if previous.0.len() == 0 {
				let mut result = target.0.clone();
				result.insert(0, 1u8);
				return BytesDiff::Value(result);
			}
			if let Some(mut result) = xdelta3::encode(target.0.as_slice(), previous.0.as_slice()) {
				result.insert(0, 2u8);
				BytesDiff::VcDiff(result)
			} else {
				// write as standalone
				let mut result = target.0.clone();
				result.insert(0, 1u8);
				BytesDiff::Value(result)
			}
		}
	}

	pub struct BytesItemBuilder(Vec<u8>);

	impl ItemBuilder for BytesItemBuilder {
		type ItemDiff = BytesDelta;

		fn new_item_builder() -> Self {
			BytesItemBuilder(Default::default())
		}
		fn apply_diff(&mut self, diff: <Self::ItemDiff as ItemDiff>::Diff) {
			match diff {
				BytesDiff::Value(mut val) => {
					val.remove(0);
					self.0 = val;
				},
				BytesDiff::None => {
					self.0.clear();
				},
				BytesDiff::VcDiff(diff) => {
					self.0 = xdelta3::decode(&diff[1..], self.0.as_slice())
						.expect("diff build only from diff builder");
				}
			}
		}
		fn extract_item(&mut self) -> Self::ItemDiff {
			BytesDelta(sp_std::mem::replace(&mut self.0, Vec::new()))
		}
	}

	impl ItemDiff for BytesDelta {
		type Diff = BytesDiff;
		type ItemBuilder = BytesItemBuilder;

		fn is_complete(diff: &Self::Diff) -> bool {
			match diff {
				BytesDiff::VcDiff(_) => false,
				BytesDiff::Value(_)
				| BytesDiff::None => true,
			}
		}
	}
}

/// Set delta.
/// TODO even if just an implementation sample, allow multiple changes.
pub mod map_delta{
	use super::*;
	use codec::Codec;
	use sp_std::collections::btree_map::BTreeMap;

	#[derive(Clone, PartialEq, Eq, Debug, Default)]
	pub struct MapDelta<K: Ord, V>(pub BTreeMap<K, V>);

	impl<K: Ord, V> sp_std::ops::Deref for MapDelta<K, V> {
		type Target = BTreeMap<K, V>;
		fn deref(&self) -> &Self::Target {
			&self.0
		}
	}

	impl<K: Ord, V> sp_std::ops::DerefMut for MapDelta<K, V> {
		fn deref_mut(&mut self) -> &mut Self::Target {
			&mut self.0
		}
	}

	impl<K: Ord, V> From<BTreeMap<K, V>> for MapDelta<K, V> {
		fn from(v: BTreeMap<K, V>) -> Self {
			MapDelta(v)
		}
	}

	#[derive(Encode, Decode, Clone, Debug, PartialEq, Eq)]
	pub enum MapDiff<K, V> {
		Reset,
		Insert(K, V),
		Remove(K),
	}

	impl<K, V> Default for MapDiff<K, V> {
		fn default() -> Self {
			MapDiff::Reset
		}
	}

	impl<K: Codec, V: Codec> Item for MapDiff<K, V> {
		const NEUTRAL: bool = true;
		type Storage = Vec<u8>;

		fn is_neutral(&self) -> bool {
			if let MapDiff::Reset = self {
				true
			} else {
				false
			}
		}

		fn is_storage_neutral(storage: &Self::Storage) -> bool {
			storage.as_slice() == &[0u8]
		}

		fn from_storage(storage: Self::Storage) -> Self {
			Self::decode(&mut storage.as_slice())
				.expect("Only encoded data in storage")
		}

		fn into_storage(self) -> Self::Storage {
			self.encode()
		}
	}

	pub struct MapItemBuilder<K, V>(BTreeMap<K, V>);

	impl<K: Ord + Codec, V: Codec> ItemBuilder for MapItemBuilder<K, V> {
		type ItemDiff = MapDelta<K, V>;

		fn new_item_builder() -> Self {
			MapItemBuilder(BTreeMap::default())
		}
		fn apply_diff(&mut self, diff: <Self::ItemDiff as ItemDiff>::Diff) {
			match diff {
				MapDiff::Insert(k, v) => {
					self.0.insert(k, v);
				},
				MapDiff::Remove(k) => {
					self.0.remove(&k);
				},
				MapDiff::Reset => {
					self.0.clear();
				},
			}
		}
		fn extract_item(&mut self) -> Self::ItemDiff {
			MapDelta(sp_std::mem::replace(&mut self.0, BTreeMap::new()))
		}
	}

	impl<K: Ord + Codec, V: Codec> ItemDiff for MapDelta<K, V> {
		type Diff = MapDiff<K, V>;
		type ItemBuilder = MapItemBuilder<K, V>;

		fn is_complete(diff: &Self::Diff) -> bool {
			match diff {
				MapDiff::Reset => true,
				MapDiff::Insert(..)
				| MapDiff::Remove(_) => false,
			}
		}
	}
}
/// Default implementation of Item for `Option`, as this
/// is a common use case.
impl<X: Eq> Item for Option<X> {
	const NEUTRAL: bool = true;

	type Storage = Option<X>;

	#[inline(always)]
	fn is_neutral(&self) -> bool {
		self.is_none()
	}

	#[inline(always)]
	fn is_storage_neutral(storage: &Self::Storage) -> bool {
		storage.is_none()
	}

	#[inline(always)]
	fn from_storage(storage: Self::Storage) -> Self {
		storage
	}

	#[inline(always)]
	fn into_storage(self) -> Self::Storage {
		self
	}
}

impl<X: Eq> ItemRef for Option<X> {
	#[inline(always)]
	fn from_storage_ref(storage: &Self::Storage) -> &Self {
		storage
	}

	#[inline(always)]
	fn into_storage_ref(&self) -> &Self::Storage {
		self
	}

	#[inline(always)]
	fn from_storage_ref_mut(storage: &mut Self::Storage) -> &mut Self {
		storage
	}

	#[inline(always)]
	fn into_storage_ref_mut(&mut self) -> &mut Self::Storage {
		self
	}
}

macro_rules! default_item {
	($name: ty) => {
	impl Item for $name {
		const NEUTRAL: bool = false;
		type Storage = Self;

		#[inline(always)]
		fn is_neutral(&self) -> bool {
			false
		}

		#[inline(always)]
		fn is_storage_neutral(_storage: &Self::Storage) -> bool {
			false
		}

		#[inline(always)]
		fn from_storage(storage: Self::Storage) -> Self {
			storage
		}

		#[inline(always)]
		fn into_storage(self) -> Self::Storage {
			self
		}
	}

	impl ItemRef for $name {
		#[inline(always)]
		fn from_storage_ref(storage: &Self::Storage) -> &Self {
			storage
		}

		#[inline(always)]
		fn into_storage_ref(&self) -> &Self::Storage {
			self
		}

		#[inline(always)]
		fn from_storage_ref_mut(storage: &mut Self::Storage) -> &mut Self {
			storage
		}

		#[inline(always)]
		fn into_storage_ref_mut(&mut self) -> &mut Self::Storage {
			self
		}
	}
}}

default_item!(Vec<u8>);
default_item!(u8);
default_item!(u16);
default_item!(u32);
default_item!(u64);
default_item!(u128);

/// Trait for historied value.
pub trait Value<V: Item>: ValueRef<V> + Context {
	/// State to use for changing value.
	/// We use a different state than
	/// for querying as it can use different
	/// constraints.
	type SE: StateIndex<Self::Index>;

	/// Index a single history item.
	/// TODO this type and trait StateIndex are not very relevant.
	type Index;

	/// GC strategy that can be applied.
	/// GC can be run in parallel, it does not
	/// make query incompatible.
	type GC;
	/// Like gc but operation require a lock on the db
	/// and all pending state are invalidated.
	type Migrate;

	/// Contextiate a new value.
	fn new(value: V, at: &Self::SE, init: Self::Context) -> Self;

	/// Insert or update a value.
	fn set(&mut self, value: V, at: &Self::SE) -> UpdateResult<()>;

	/// Discard history at.
	fn discard(&mut self, at: &Self::SE) -> UpdateResult<Option<V>>;

	/// Garbage collect value.
	fn gc(&mut self, gc: &Self::GC) -> UpdateResult<()>;

	/// Check if migrate should be applied if this state index
	/// got modified.
	fn is_in_migrate(index: &Self::Index, gc: &Self::Migrate) -> bool;

	/// Migrate a value, all value needs to migrate at once, as
	/// the content will not be valid with post-migration states
	/// otherwise.
	fn migrate(&mut self, mig: &Self::Migrate) -> UpdateResult<()>;
}

/// Returns pointer to in memory value.
pub trait InMemoryValue<V: Item>: Value<V> {
	/// Get latest value, can apply updates.
	fn get_mut(&mut self, at: &Self::SE) -> Option<&mut V>;

	/// Similar to value set but returning a pointer on replaced or deleted value.
	/// If the value is change but history is kept (new state), no pointer is returned.
	fn set_mut(&mut self, value: V, at: &Self::SE) -> UpdateResult<Option<V>>;
}

/// Same as `Value` but allows using unsafe index and failing if incorrect.
/// This involves some additional computation to check correctness.
/// It is also usefull when some asumption are not strong enough, for
/// instance if `Value` is subject to concurrent access.
/// TODO an entry api would be more proper (returning optional entry).
pub trait ConditionalValueMut<V: Item>: Value<V> {
	/// Internal index.
	type IndexConditional;

	/// Does state allow modifying this value.
	/// If value is added as parameter, we do not allow overwrite.
	fn can_set(&self, no_overwrite: Option<&V>, at: &Self::IndexConditional) -> bool;

	/// Do update if state allows it, otherwhise return None.
	fn set_if_possible(&mut self, value: V, at: &Self::IndexConditional) -> Option<UpdateResult<()>>;

	/// Do update if state allows it and we are not erasing an existing value, otherwhise return None.
	fn set_if_possible_no_overwrite(&mut self, value: V, at: &Self::IndexConditional) -> Option<UpdateResult<()>>;
}

/// Setting value is usually done on latest state for an history.
/// This trait allow setting values in the past, this is usually
/// not a good idea to maintain state coherency.
pub trait ForceValueMut<V: Item>: Value<V> {
	/// Internal index.
	type IndexForce;

	/// Do update if state allows it, otherwhise return None.
	fn force_set(&mut self, value: V, at: &Self::IndexForce) -> UpdateResult<()>;
}

/// An entry at a given history index.
#[derive(Debug, Clone, Encode, Decode, PartialEq, Eq)]
pub struct HistoriedValue<V, S> {
	/// The stored value.
	pub value: V,
	/// The state this value belongs to.
	pub state: S,
}

impl<V, S> Trigger for HistoriedValue<V, S>
	where
		V: Trigger,
{
	const TRIGGER: bool = V::TRIGGER;

	fn trigger_flush(&mut self) {
		if V::TRIGGER {
			self.value.trigger_flush();
		}
	}
}

impl<V, S> Context for HistoriedValue<V, S>
	where
		V: Context,
{
	type Context = V::Context;
}

impl<V, S> DecodeWithContext for HistoriedValue<V, S>
	where
		V: DecodeWithContext,
		S: Decode,
{
	fn decode_with_context<I: Input>(input: &mut I, init: &Self::Context) -> Option<Self> {
		V::decode_with_context(input, init)
			.and_then(|value| S::decode(input).ok()
				.map(|state| HistoriedValue {
					value,
					state,
				})
			)
	}
}

impl<V, S> HistoriedValue<V, S> {
	/// Apply modification over historied value reference and state.
	pub fn apply<V2, F: Fn((&mut V, &mut S))>(&mut self, f: F) {
		let HistoriedValue { value, state } = self;
		f((value, state))
	}

	/// Map inner historied value.
	pub fn map<V2, F: Fn(V) -> V2>(self, f: F) -> HistoriedValue<V2, S> {
		let HistoriedValue { value, state } = self;
		HistoriedValue { value: f(value), state }
	}
}

impl<'a, V: 'a, S: Clone> HistoriedValue<V, S> {
	/// Get historied reference to the value.
	pub fn as_ref(&self) -> HistoriedValue<&V, S> {
		let HistoriedValue { value, state } = self;
		HistoriedValue { value: &value, state: state.clone() }
	}

	/// Map over a reference of value.
	pub fn map_ref<V2: 'a, F: Fn(&'a V) -> V2>(&'a self, f: F) -> HistoriedValue<V2, S> {
		let HistoriedValue { value, state } = self;
		HistoriedValue { value: f(value), state: state.clone() }
	}
}

impl<V, S> From<(V, S)> for HistoriedValue<V, S> {
	fn from(input: (V, S)) -> HistoriedValue<V, S> {
		HistoriedValue { value: input.0, state: input.1 }
	}
}

/// Implementation for plain db.
pub struct BTreeMap<K, V, H: Context>(pub(crate) sp_std::collections::btree_map::BTreeMap<K, H>, H::Context, PhantomData<V>);

impl<K: Ord, V, H: Context> BTreeMap<K, V, H> {
	pub fn new(init: H::Context) -> Self {
		BTreeMap(sp_std::collections::btree_map::BTreeMap::new(), init, PhantomData)
	}
}

impl<K: Ord, V: Item + Clone, H: ValueRef<V> + Context> StateDBRef<K, V> for BTreeMap<K, V, H> {
	type S = H::S;

	fn get(&self, key: &K, at: &Self::S) -> Option<V> {
		self.0.get(key)
			.and_then(|h| h.get(at))
	}

	fn contains(&self, key: &K, at: &Self::S) -> bool {
		self.0.get(key)
			.map(|h| h.contains(at))
			.unwrap_or(false)
	}
}

// note that the constraint on state db ref for the associated type is bad (forces V as clonable).
impl<K: Ord, V: Item, H: InMemoryValueRef<V> + Context> InMemoryStateDBRef<K, V> for BTreeMap<K, V, H> {
	type S = H::S;

	fn get_ref(&self, key: &K, at: &Self::S) -> Option<&V> {
		self.0.get(key)
			.and_then(|h| h.get_ref(at))
	}
}

impl<K: Ord + Clone, V: Item + Clone + Eq, H: Value<V>> StateDB<K, V> for BTreeMap<K, V, H> {
	type SE = H::SE;
	type GC = H::GC;
	type Migrate = H::Migrate;

	fn emplace(&mut self, key: K, value: V, at: &Self::SE) {
		if let Some(hist) = self.0.get_mut(&key) {
			hist.set(value, at);
		} else {
			self.0.insert(key, H::new(value, at, self.1.clone()));
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
pub struct PlainDBState<K, DB, H, S> {
	db: DB,
	touched_keys: sp_std::collections::btree_map::BTreeMap<S, Vec<K>>, // TODO change that by a journal trait!!
	_ph: PhantomData<H>,
}

impl<K, V: Item + Clone, H: ValueRef<V>, DB: PlainDBRef<K, H>, S> StateDBRef<K, V> for PlainDBState<K, DB, H, S> {
	type S = H::S;

	fn get(&self, key: &K, at: &Self::S) -> Option<V> {
		self.db.get(key)
			.and_then(|h| h.get(at))
	}

	fn contains(&self, key: &K, at: &Self::S) -> bool {
		self.db.get(key)
			.map(|h| h.contains(at))
			.unwrap_or(false)
	}
}

impl<
	K: Ord + Clone,
	V: Item + Clone + Eq,
	H: Value<V, Context = ()>,
	DB: PlainDBRef<K, H> + PlainDB<K, H>,
> StateDB<K, V> for PlainDBState<K, DB, H, H::Index>
	where
			H::Index: Clone + Ord,
{
	type SE = H::SE;
	type GC = H::GC;
	type Migrate = H::Migrate;

	fn emplace(&mut self, key: K, value: V, at: &Self::SE) {
		if let Some(mut hist) = <DB as PlainDB<_, _>>::get(&self.db, &key) {
			match hist.set(value, at) {
				UpdateResult::Changed(_) => self.db.emplace(key.clone(), hist),
				UpdateResult::Cleared(_) => self.db.remove(&key),
				UpdateResult::Unchanged => return,
			}
		} else {
			self.db.emplace(key.clone(), H::new(value, at, ()));
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
			if H::is_in_migrate(touched, mig) {
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

/// Associate a state index for a given state reference
pub trait StateIndex<I> {
	/// Get individal state index.
	fn index(&self) -> I;
	/// Get reference to individal state index.
	fn index_ref(&self) -> &I;
}

impl<S: Clone> StateIndex<S> for Latest<S> {
	fn index(&self) -> S {
		self.latest().clone()
	}
	fn index_ref(&self) -> &S {
		self.latest()
	}
}

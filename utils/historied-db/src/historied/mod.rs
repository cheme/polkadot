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
use crate::{UpdateResult, StateIndex};
use codec::{Encode, Decode, Input};
use sp_std::ops::Range;
use crate::{Context, DecodeWithContext, Trigger};

pub mod linear;
pub mod tree;
pub mod aggregate;

/// Trait for historied data.
pub trait Data<V: Value> {
	/// State to query for this value.
	type S;

	/// Get value at this state.
	fn get(&self, at: &Self::S) -> Option<V>;

	/// Check if a value exists at this state.
	fn contains(&self, at: &Self::S) -> bool;

	/// Check if this is empty.
	fn is_empty(&self) -> bool;
}

// TODO EMCH refact with 'a for inner value
// and a get value type (see test on rust playground).
// So we only got Data type.
pub trait DataRef<V: Value>: Data<V> {
	/// Get reference to the value at this state.
	fn get_ref(&self, at: &Self::S) -> Option<&V>;
}

pub trait DataSlices<V: Value>: Data<V> {
	/// Get reference to the value at this state.
	fn get_slice(&self, at: &Self::S) -> Option<&[u8]>;
}

pub trait DataSliceRanges<S> {
	/// Get reference to the value from which this slice can be build.
	fn get_range(slice: &[u8], at: &S) -> Option<Range<usize>>;
}

/// An item of historied value.
pub trait Value: Sized {
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

pub trait ValueRef: Value {
	fn from_storage_ref(storage: &Self::Storage) -> &Self;

	fn into_storage_ref(&self) -> &Self::Storage;

	fn from_storage_ref_mut(storage: &mut Self::Storage) -> &mut Self;

	fn into_storage_ref_mut(&mut self) -> &mut Self::Storage;
}

/// Default implementation of Value for `Option`, as this
/// is a common use case.
impl<X: Eq> Value for Option<X> {
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

impl<X: Eq> ValueRef for Option<X> {
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
	impl Value for $name {
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

	impl ValueRef for $name {
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

/// Trait for mutable historied data.
pub trait DataMut<V: Value>: Data<V> + Context {
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
pub trait DataRefMut<V: Value>: DataMut<V> {
	/// Get latest value, can apply updates.
	fn get_mut(&mut self, at: &Self::SE) -> Option<&mut V>;

	/// Similar to value set but returning a pointer on replaced or deleted value.
	/// If the value is change but history is kept (new state), no pointer is returned.
	fn set_mut(&mut self, value: V, at: &Self::SE) -> UpdateResult<Option<V>>;
}

/// Same as `DataMut` but allows using unsafe index and failing if incorrect.
/// This involves some additional computation to check correctness.
/// It is also usefull when some asumption are not strong enough, for
/// instance if `DataMut` is subject to concurrent access.
/// TODO an entry api would be more proper (returning optional entry).
pub trait ConditionalDataMut<V: Value>: DataMut<V> {
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
pub trait ForceDataMut<V: Value>: DataMut<V> {
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

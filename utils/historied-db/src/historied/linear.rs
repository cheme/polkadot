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

//! Linear historied data historied db implementations.
//!
//! Current implementation is limited to a simple array indexing
//! with modification at the end only.
//! This is a sequential indexing.
//!
//! All api are assuming that the state used when modifying is indeed the latest state.

use super::{HistoriedValue, ValueRef, Value, InMemoryValueRange, InMemoryValueRef,
	InMemoryValueSlice, InMemoryValue, ConditionalValueMut, Item, ItemRef, ForceValueMut};
use crate::{UpdateResult, Latest};
use sp_std::marker::PhantomData;
use sp_std::vec::Vec;
use sp_std::ops::{SubAssign, Range};
use codec::{Encode, Decode, Input};
use crate::backend::{LinearStorage, LinearStorageMem, LinearStorageSlice, LinearStorageRange};
use crate::backend::encoded_array::EncodedArrayValue;
use crate::{Context, InitFrom, DecodeWithContext, Trigger};
use derivative::Derivative;
use crate::backend::nodes::EstimateSize;

/// Basic usage case should be integers and byte representation, but
/// only integer should really be use.
///
/// This state is a simple ordered sequence.
pub trait LinearState:
	Default
	+ Clone
	+ Ord
	+ PartialOrd
{
	// stored state and query state are
	// the same for linear state.
	/// Test if a state is valid given a current one.
	///
	/// For linear (sequential) it is true if less or
	/// equal than current state.
	fn exists(&self, at: &Self) -> bool {
		self <= at
	}
}

impl<S> LinearState for S where S:
	Default
	+ Clone
	+ Ord
	+ PartialOrd
{ }

/// Implementation of linear value history storage.
#[derive(Derivative, Debug, Encode, Decode)]
#[derivative(PartialEq(bound="D: PartialEq"))]
pub struct Linear<V, S, D>(D, PhantomData<(V, S)>);

impl<V, S, D: Trigger> Trigger for Linear<V, S, D> {
	const TRIGGER: bool = <D as Trigger>::TRIGGER;

	fn trigger_flush(&mut self) {
		if Self::TRIGGER {
			self.0.trigger_flush();
		}
	}
}

impl<V, S, D: Context> Context for Linear<V, S, D> {
	type Context = <D as Context>::Context;
}

impl<V, S, D: InitFrom> InitFrom for Linear<V, S, D> {
	fn init_from(init: Self::Context) -> Self {
		Linear(<D as InitFrom>::init_from(init), PhantomData)
	}
}

impl<V, S, D: DecodeWithContext> DecodeWithContext for Linear<V, S, D> {
	fn decode_with_context<I: Input>(input: &mut I, init: &Self::Context) -> Option<Self> {
		D::decode_with_context(input, init).map(|d| Linear(d, Default::default()))
	}
}

impl<V, S, D> Linear<V, S, D> {
	/// Access inner `LinearStorage`.
	pub fn storage(&self) -> &D {
		&self.0
	}
	/// Mutable access inner `LinearStorage`.
	pub fn storage_mut(&mut self) -> &mut D {
		&mut self.0
	}
}

impl<V, S, D: EstimateSize> EstimateSize for Linear<V, S, D> {
	fn estimate_size(&self) -> usize {
		self.0.estimate_size()
	}
}

impl<V, S, D: AsRef<[u8]>> AsRef<[u8]> for Linear<V, S, D> {
	fn as_ref(&self) -> &[u8] {
		self.0.as_ref()
	}
}

impl<V, S, D: AsMut<[u8]>> AsMut<[u8]> for Linear<V, S, D> {
	fn as_mut(&mut self) -> &mut [u8] {
		self.0.as_mut()
	}
}

impl<V, S, D: Clone> Clone for Linear<V, S, D> {
	fn clone(&self) -> Self {
		Linear(self.0.clone(), PhantomData)
	}
}

impl<V, S, D: EncodedArrayValue> EncodedArrayValue for Linear<V, S, D> {
	fn from_slice(slice: &[u8]) -> Self {
		let v = D::from_slice(slice);
		Linear(v, PhantomData)
	}
}

/// Adapter for storage (allows to factor code while keeping simple types).
/// VR is the reference to value that is used, and I the initial state.
pub trait StorageAdapter<'a, S, V, D, H> {
	fn get_adapt(inner: D, index: H) -> HistoriedValue<V, S>;
}

struct RefVecAdapter;
impl<'a, S, V, D: LinearStorageMem<V, S>> StorageAdapter<
	'a,
	S,
	&'a V,
	&'a D,
	D::Index,
> for RefVecAdapter {
	fn get_adapt(inner: &'a D, index: D::Index) -> HistoriedValue<&'a V, S> {
		inner.get_ref(index)
	}
}

struct RefVecAdapterMut;
impl<'a, S, V, D: LinearStorageMem<V, S>> StorageAdapter<
	'a,
	S,
	&'a mut V,
	&'a mut D,
	D::Index,
> for RefVecAdapterMut {
	fn get_adapt(inner: &'a mut D, index: D::Index) -> HistoriedValue<&'a mut V, S> {
		inner.get_ref_mut(index)
	}
}

struct ValueVecAdapter;
impl<'a, S, V, D: LinearStorage<V, S>> StorageAdapter<
	'a,
	S,
	V,
	&'a D,
	D::Index,
> for ValueVecAdapter {
	fn get_adapt(inner: &'a D, index: D::Index) -> HistoriedValue<V, S> {
		inner.get(index)
	}
}

struct SliceAdapter;
impl<'a, S, D: LinearStorageSlice<Vec<u8>, S>> StorageAdapter<
	'a,
	S,
	&'a [u8],
	&'a D,
	D::Index,
> for SliceAdapter {
	fn get_adapt(inner: &'a D, index: D::Index) -> HistoriedValue<&'a [u8], S> {
		inner.get_slice(index)
	}
}

impl<V: Item + Clone, S: LinearState, D: LinearStorage<V::Storage, S>> ValueRef<V> for Linear<V, S, D> {
	type S = S;

	fn get(&self, at: &Self::S) -> Option<V> {
		self.get_adapt::<_, ValueVecAdapter>(at).map(V::from_storage)
	}

	fn contains(&self, at: &Self::S) -> bool {
		self.pos_index(at).is_some()
	}

	fn is_empty(&self) -> bool {
		self.0.len() == 0
	}
}

// TODO should it be ItemRef?
impl<V: Item, S: LinearState, D: LinearStorageRange<V::Storage, S>> InMemoryValueRange<S> for Linear<V, S, D> {
	fn get_range(slice: &[u8], at: &S) -> Option<Range<usize>> {
		if let Some(inner) = D::from_slice(slice) {
			for index in inner.rev_index_iter() {
				if let Some(HistoriedValue { value, state }) = D::get_range_from_slice(slice, index) {
					if state.exists(at) {
						return Some(value);
					}
				}
			}
		}
		None
	}
}

impl<V: Item, S: LinearState, D: LinearStorage<V::Storage, S>> Linear<V, S, D> {
	fn get_adapt<'a, VR, A: StorageAdapter<'a, S, VR, &'a D, D::Index>>(&'a self, at: &S) -> Option<VR> {
		for index in self.0.rev_index_iter() {
			let HistoriedValue { value, state } = A::get_adapt(&self.0, index);
			if state.exists(at) {
				return Some(value);
			}
		}
		None
	}

	// TODO use only once, consider removal
	fn get_adapt_mut<
		'a,
		VR,
		A: StorageAdapter<'a, S, VR, &'a mut D, D::Index>,
	>(&'a mut self, at: &S)	-> Option<HistoriedValue<VR, S>> {
		if let Some(index) = self.pos_index(at) {
			Some(A::get_adapt(&mut self.0, index))
		} else {
			None
		}
	}
}

impl<V: Item + Eq, S: LinearState, D: LinearStorage<V::Storage, S>> Linear<V, S, D> {
	fn set_inner(&mut self, value: V, at: &Latest<S>) -> UpdateResult<Option<V>> {
		let at = at.latest();
		loop {
			if let Some(index) = self.0.last() {
				let last = self.0.get_state(index);
				if &last > at {
					self.0.pop();
					continue;
				}
				if at == &last {
					let mut last = self.0.get(index);
					let value = value.into_storage();
					if last.value == value {
						return UpdateResult::Unchanged;
					}
					let result = sp_std::mem::replace(&mut last.value, value);
					self.0.emplace(index, last);
					return UpdateResult::Changed(Some(V::from_storage(result)));
				}
			}
			break;
		}
		self.0.push(HistoriedValue {value: value.into_storage(), state: at.clone()});
		UpdateResult::Changed(None)
	}

	fn force_set(&mut self, value: V, at: &S) -> UpdateResult<()> {
		let mut position = self.0.last();
		let mut insert_index =  None;
		while let Some(index) = position {
			let last = self.0.get_state(index);
			if at > &last {
				break;
			}
			if at == &last {
				let mut last = self.0.get(index);
				let value = value.into_storage();
				if last.value == value {
					return UpdateResult::Unchanged;
				}
				last.value = value;
				self.0.emplace(index, last);
				return UpdateResult::Changed(());
			}
			insert_index = Some(index);
			position = self.0.previous_index(index);
		}
		let value = value.into_storage();
		if let Some(index) = insert_index {
			self.0.insert(index, HistoriedValue {value, state: at.clone()});
		} else {
			self.0.push(HistoriedValue {value, state: at.clone()});
		}
		UpdateResult::Changed(())
	}

	fn set_if_inner(&mut self, value: V, at: &S, allow_overwrite: bool) -> Option<UpdateResult<()>> {
		if let Some(index) = self.0.last() {
			let last = self.0.get_state(index);
			if &last > at {
				return None;
			}
			if at == &last {
				let mut last = self.0.get(index);
				let value = value.into_storage();
				if last.value == value {
					return Some(UpdateResult::Unchanged);
				}
				if !allow_overwrite {
					return None;
				}
				last.value = value;
				self.0.emplace(index, last);
				return Some(UpdateResult::Changed(()));
			}
		}
		self.0.push(HistoriedValue {value: value.into_storage(), state: at.clone()});
		Some(UpdateResult::Changed(()))
	}
	fn can_if_inner(&self, value: Option<&V>, at: &S) -> bool {
		if let Some(index) = self.0.last() {
			let last = self.0.get_state(index);
			if &last > at {
				return false;
			}
			if at == &last {
				if let Some(overwrite) = value {
					let last = self.0.get(index);
					// Non negligeable cost in some case: TODO consider skipping this test.
					// Or use ItemRef
					let last_value = V::from_storage(last.value);
					if overwrite != &last_value {
						return false;
					}
				}
			}
		}
		true
	}
}

impl<V: Item, S: LinearState, D: LinearStorage<V::Storage, S>> Linear<V, S, D> {
	fn pos_index(&self, at: &S) -> Option<D::Index> {
		let mut pos = None;
		for index in self.0.rev_index_iter() {
			let vr = self.0.get_state(index);
			if vr.exists(at) {
				pos = Some(index);
				break;
			}
		}
		pos
	}
}

impl<V: ItemRef + Clone, S: LinearState, D: LinearStorageMem<V::Storage, S>> InMemoryValueRef<V> for Linear<V, S, D> {
	fn get_ref(&self, at: &Self::S) -> Option<&V> {
		self.get_adapt::<_, RefVecAdapter>(at).map(ItemRef::from_storage_ref)
	}
}

impl<S: LinearState, D: LinearStorageSlice<Vec<u8>, S>> InMemoryValueSlice<Vec<u8>> for Linear<Vec<u8>, S, D> {
	fn get_slice(&self, at: &Self::S) -> Option<&[u8]> {
		self.get_adapt::<_, SliceAdapter>(at)
	}
}

impl<V: Item + Clone + Eq, S: LinearState + SubAssign<S>, D: LinearStorage<V::Storage, S>> Value<V> for Linear<V, S, D> {
	type SE = Latest<S>;
	type Index = S;
	type GC = LinearGC<S>;
	/// Migrate will act as GC but also align state to 0.
	/// The index index in second position is the old start state
	/// number that is now 0 (usually the state as gc new_start).
	type Migrate = (Self::GC, Self::S);

	fn new(value: V, at: &Self::SE, init: Self::Context) -> Self {
		let mut v = D::init_from(init);
		let state = at.latest().clone();
		v.push(HistoriedValue{ value: value.into_storage(), state });
		Linear(v, PhantomData)
	}

	fn set(&mut self, value: V, at: &Self::SE) -> UpdateResult<()> {
		self.set_inner(value, at).map(|_| ())
	}

	// TODO not sure discard is of any use (revert is most likely
	// using some migrate as it breaks expectations).
	fn discard(&mut self, at: &Self::SE) -> UpdateResult<Option<V>> {
		let at = at.latest();
		if let Some(last) = self.0.last() {
			let last = self.0.get(last);
			debug_assert!(&last.state <= at); 
			if at == &last.state {
				if self.0.len() == 1 {
					return UpdateResult::Cleared(self.0.pop().map(|v| V::from_storage(v.value)));
				} else {
					return UpdateResult::Changed(self.0.pop().map(|v| V::from_storage(v.value)));
				}
			}
		}
		UpdateResult::Unchanged
	}

	fn gc(&mut self, gc: &Self::GC) -> UpdateResult<()> {
		if gc.new_start.is_some() && gc.new_start == gc.new_end {
			self.0.clear();
			return UpdateResult::Cleared(());
		}

		let mut end_result = UpdateResult::Unchanged;
		if let Some(new_end) = gc.new_end.as_ref() {

			let mut index = self.0.len();
			for handle in self.0.rev_index_iter() { 
				let state = self.0.get_state(handle);
				if &state < new_end {
					break;
				}
				index -= 1;
			}

			if index == 0 {
				self.0.clear();
				return UpdateResult::Cleared(());
			} else if index != self.0.len() {
				// TODO could use handle here
				self.0.truncate(index);
				end_result = UpdateResult::Changed(());
			}
		}

		if let Some(start_treshold) = gc.new_start.as_ref() {
			let mut index = self.0.len();
			if index == 0 {
				return end_result;
			}
			for handle in self.0.rev_index_iter() { 
				let state = self.0.get_state(handle);
				index -= 1;
				if state.exists(start_treshold) {
					// This does not handle consecutive neutral element, but
					// it is considered marginal and bad usage (in theory one
					// should not push two consecutive identical values).
					if V::NEUTRAL {
						if V::is_storage_neutral(&self.0.get(handle).value) {
							index += 1;
						}
					}
					break;
				}
			}

			if index == 0 {
				return end_result;
			}
			if index == self.0.len() {
				self.0.clear();
				return UpdateResult::Cleared(());
			}
			// TODO could use handle here
			self.0.truncate_until(index);
			return UpdateResult::Changed(())
		}
		end_result
	}

	fn migrate(&mut self, (gc, mig): &Self::Migrate) -> UpdateResult<()> {
		let res = self.gc(gc);
		let mut next_index = self.0.last();
		let result = if next_index.is_some() {
			UpdateResult::Changed(())
		} else {
			res
		};
		while let Some(index) = next_index {
			let mut h = self.0.get(index);
			if &h.state > mig {
				h.state -= mig.clone();
			} else {
				h.state = Default::default();
			}
			self.0.emplace(index, h);

			next_index = self.0.previous_index(index);
		}
		result
	}

	fn is_in_migrate(index: &Self::Index, gc: &Self::Migrate) -> bool {
		gc.1 > Self::Index::default()
			|| gc.0.new_start.as_ref().map(|s| index < s).unwrap_or(false)
			|| gc.0.new_end.as_ref().map(|s| index >= s).unwrap_or(false)
	}
}

impl<V: ItemRef + Clone + Eq, S: LinearState + SubAssign<S>, D: LinearStorageMem<V::Storage, S>> InMemoryValue<V> for Linear<V, S, D> {
	fn get_mut(&mut self, at: &Self::SE) -> Option<&mut V> {
		let at = at.latest();
		self.get_adapt_mut::<_, RefVecAdapterMut>(at).map(|h| V::from_storage_ref_mut(h.value))
	}

	fn set_mut(&mut self, value: V, at: &Self::SE) -> UpdateResult<Option<V>> {
		self.set_inner(value, at)
	}
}

impl<V: Item + Clone + Eq, S: LinearState + SubAssign<S>, D: LinearStorage<V::Storage, S>> ConditionalValueMut<V> for Linear<V, S, D> {
	type IndexConditional = Self::Index;
	fn can_set(&self, no_overwrite: Option<&V>, at: &Self::IndexConditional) -> bool {
		self.can_if_inner(no_overwrite, at)
	}
	fn set_if_possible(&mut self, value: V, at: &Self::IndexConditional) -> Option<UpdateResult<()>> {
		self.set_if_inner(value, at, true)
	}

	fn set_if_possible_no_overwrite(&mut self, value: V, at: &Self::IndexConditional) -> Option<UpdateResult<()>> {
		self.set_if_inner(value, at, false)
	}
}

impl<V: Item + Clone + Eq, S: LinearState + SubAssign<S>, D: LinearStorage<V::Storage, S>> ForceValueMut<V> for Linear<V, S, D> {
	type IndexForce = Self::Index;

	fn force_set(&mut self, value: V, at: &Self::IndexForce) -> UpdateResult<()> {
		self.force_set(value, at)
	}
}


#[derive(Debug, Clone, Encode, Decode)]
#[cfg_attr(test, derive(PartialEq, Eq))]
pub struct LinearGC<S> {
	// inclusive
	pub(crate) new_start: Option<S>,
	// exclusive
	pub(crate) new_end: Option<S>,
}

impl Linear<Option<Vec<u8>>, u32, crate::backend::in_memory::MemoryOnly<Option<Vec<u8>>, u32>> {
	/// Temporary function to get occupied stage.
	/// TODO replace by heapsizeof
	pub fn temp_size(&self) -> usize {
		let mut size = 0;
		for h in (self.0).0.iter() {
			size += 4; // usize as u32 for index
			size += 1; // optional
			size += h.value.as_ref().map(|v| v.len()).unwrap_or(0);
		}
		size
	}
}

#[cfg(test)]
mod test {
	use super::*;
	use crate::backend::{LinearStorage, in_memory::MemoryOnly};

	#[repr(transparent)]
	#[derive(Clone, PartialEq, Eq)]
	/// Bytes with neutral item.
	struct BytesNeutral(Vec<u8>); 

	impl Item for BytesNeutral {
		const NEUTRAL: bool = true;

		type Storage = Vec<u8>;

		#[inline(always)]
		fn is_neutral(&self) -> bool {
			self.0.as_slice() == &[0]
		}

		#[inline(always)]
		fn is_storage_neutral(storage: &Self::Storage) -> bool {
			storage.as_slice() == &[0]
		}

		#[inline(always)]
		fn from_storage(storage: Self::Storage) -> Self {
			BytesNeutral(storage)
		}

		#[inline(always)]
		fn into_storage(self) -> Self::Storage {
			self.0
		}
	}

	#[test]
	fn test_gc() {
		// TODO non consecutive state.
		// [1, 2, 3, 4]
		let mut first_storage = MemoryOnly::<Vec<u8>, u32>::default();
		for i in 1..5 {
			first_storage.push((vec![i as u8], i).into());
		}
		// [1, ~, 3, ~]
		let mut second_storage = MemoryOnly::<Vec<u8>, u32>::default();
		for i in 1..5 {
			if i % 2 == 0 {
				second_storage.push((vec![0u8], i).into());
			} else {
				second_storage.push((vec![i as u8], i).into());
			}
		}
		let result_first = [
			[None, None, None, None],
			[Some(1), None, None, None],
			[Some(1), Some(2), None, None],
			[Some(1), Some(2), Some(3), None],
			[Some(1), Some(2), Some(3), Some(4)],
		];
		for i in 1..5 {
			let gc = LinearGC {
				new_start: None,
				new_end: Some(i as u32),
			};
			let mut first = Linear::<Vec<u8>, _, _>(first_storage.clone(), Default::default());
			first.gc(&gc);
			let mut second = Linear::<Vec<u8>, _, _>(second_storage.clone(), Default::default());
			second.gc(&gc);
			for j in 0..4 {
				assert_eq!(first.0.get_state_lookup(j), result_first[i - 1][j]);
				assert_eq!(second.0.get_state_lookup(j), result_first[i - 1][j]);
			}
			let mut first = Linear::<BytesNeutral, _, _>(first_storage.clone(), Default::default());
			first.gc(&gc);
			let mut second = Linear::<BytesNeutral, _, _>(second_storage.clone(), Default::default());
			second.gc(&gc);
			for j in 0..4 {
				assert_eq!(first.0.get_state_lookup(j), result_first[i - 1][j]);
				assert_eq!(second.0.get_state_lookup(j), result_first[i - 1][j]);
			}
		}
		let result_first = [
			[Some(1), Some(2), Some(3), Some(4)],
			[Some(2), Some(3), Some(4), None],
			[Some(3), Some(4), None, None],
			[Some(4), None, None, None],
			[None, None, None, None],
		];
		let result_second = [
			[Some(1), Some(2), Some(3), Some(4)],
			[Some(3), Some(4), None, None],
			[Some(3), Some(4), None, None],
			[None, None, None, None],
			[None, None, None, None],
		];
		for i in 1..5 {
			let gc = LinearGC {
				new_start: Some(i as u32),
				new_end: None,
			};
			let mut first = Linear::<Vec<u8>, _, _>(first_storage.clone(), Default::default());
			first.gc(&gc);
			let mut second = Linear::<Vec<u8>, _, _>(second_storage.clone(), Default::default());
			second.gc(&gc);
			for j in 0..4 {
				assert_eq!(first.0.get_state_lookup(j), result_first[i - 1][j]);
				assert_eq!(second.0.get_state_lookup(j), result_first[i - 1][j]);
			}
			let mut first = Linear::<BytesNeutral, _, _>(first_storage.clone(), Default::default());
			first.gc(&gc);
			let mut second = Linear::<BytesNeutral, _, _>(second_storage.clone(), Default::default());
			second.gc(&gc);
			for j in 0..4 {
				assert_eq!(first.0.get_state_lookup(j), result_first[i - 1][j]);
				assert_eq!(second.0.get_state_lookup(j), result_second[i - 1][j]);
			}
		}
	}
}

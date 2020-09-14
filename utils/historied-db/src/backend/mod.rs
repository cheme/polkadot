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

//! Linear backend structures for historied data storage.

use crate::historied::HistoriedValue;
use crate::rstd::ops::Range;
use crate::InitFrom;

/// Data stored as rust structs in memory.
pub mod in_memory;

/// Data encoded in a byte buffer, no unserialized
/// stractures.
pub mod encoded_array;

/// Content can be split between multiple nodes.
pub mod nodes;

// TODO this implementation uses a index and does not allow
// performant implementation, it should (at least when existing
// value) use a associated type handle depending on backend
// (slice index of encoded array, pointer of in_memory, pointer
// of node inner value for nodes). Also not puting value in memory.
pub struct Entry<'a, V, S, D: LinearStorage<V, S>> {
	value: Option<HistoriedValue<V, S>>,
	index: usize,
	storage: &'a mut D,
	changed: bool,
	insert: bool,
}

impl<'a, V, S, D: LinearStorage<V, S>> Entry<'a, V, S, D> {
	/// ~ Vaccant enum of rust std lib.
	/// Occupied is the negation of this.
	pub fn is_vaccant(&self) -> bool {
		self.insert
	}
	/// Access current value
	pub fn value(&self) -> Option<&HistoriedValue<V, S>> {
		self.value.as_ref()
	}
	/// Change value.
	pub fn and_modify<F>(mut self, f: impl FnOnce(&mut HistoriedValue<V, S>)) -> Self {
		self.value.as_mut().map(f);
		self.changed |= self.value.is_some();
		self
	}
	/// Init a value for vaccant entry.
	pub fn or_insert(mut self, default: HistoriedValue<V, S>) -> Self {
		if self.value.is_none() {
			self.changed = true;
			self.value = Some(default);
		}
		self
	}
	/// Lazy `or_insert`.
	pub fn or_insert_with(mut self, default: impl FnOnce() -> HistoriedValue<V, S>) -> Self {
		if self.value.is_none() {
			self.changed = true;
			self.value = Some(default());
		}
		self
	}
	/// Remove entry.
	pub fn and_delete(mut self) -> Self {
		if self.value.is_some() {
			self.changed = true;
			self.value = None;
		}
		self
	}
}

impl<'a, V, S, D: LinearStorage<V, S>> Drop for Entry<'a, V, S, D>
{
	fn drop(&mut self) {
		if self.changed {
			if let Some(change) = self.value.take() {
				if self.insert {
					self.storage.insert(self.index, change);
				} else {
					self.storage.emplace(self.index, change);
				}
			} else {
				if self.changed && !self.insert {
					self.storage.remove(self.index);
				}
			}
		}
	}
}

/// Backend for linear storage.
pub trait LinearStorage<V, S>: InitFrom {
	/// This does not need to be very efficient as it is mainly for
	/// garbage collection.
	fn truncate_until(&mut self, split_off: usize);
	/// Number of element for different S.
	fn len(&self) -> usize;
	/// Array like get.
	fn st_get(&self, index: usize) -> Option<HistoriedValue<V, S>>;
	/// Entry.
	fn entry<'a>(&'a mut self, index: usize) -> Entry<'a, V, S, Self> {
		let value = self.st_get(index);
		let insert = value.is_none();
		Entry {
			value,
			index,
			storage: self,
			changed: false,
			insert,
		}
	}
	/// Array like get.
	fn get_state(&self, index: usize) -> Option<S>;
	/// Vec like push.
	fn push(&mut self, value: HistoriedValue<V, S>);
	/// Vec like insert, this is mainly use in tree implementation.
	/// So when used as tree branch container, a efficient implementation
	/// shall be use.
	fn insert(&mut self, index: usize, value: HistoriedValue<V, S>);
	/// Vec like remove, this is mainly use in tree branch implementation.
	/// TODO ensure remove last is using pop implementation.
	fn remove(&mut self, index: usize);
	/// TODO put 'a and return read type that can be &'a S and where S is AsRef<S>.
	/// TODO put 'a and return read type that can be &'a [u8] and where Vec<u8> is AsRef<[u8]>.
	fn last(&self) -> Option<HistoriedValue<V, S>> {
		if self.len() > 0 {
			self.st_get(self.len() - 1)
		} else {
			None
		}
	}
	fn pop(&mut self) -> Option<HistoriedValue<V, S>>;
	fn clear(&mut self);
	fn truncate(&mut self, at: usize);
	/// This can be slow, only define in migrate.
	/// TODO consider renaming. TODO optimize the implementations to ensure emplace latest is
	/// as/more efficient than pop and push.
	fn emplace(&mut self, at: usize, value: HistoriedValue<V, S>);
	// TODO implement and replace in set function of linear (avoid some awkward possible
	// side effect of pop then push)
	//	fn emplace_last(&mut self, at: usize, value: HistoriedValue<V, S>);
}

/// Backend for linear storage with inmemory reference.
pub trait LinearStorageSlice<V: AsRef<[u8]> + AsMut<[u8]>, S>: LinearStorage<V, S> {
	/// Array like get.
	fn get_slice(&self, index: usize) -> Option<HistoriedValue<&[u8], S>>;
	fn last_slice(&self) -> Option<HistoriedValue<&[u8], S>> {
		if self.len() > 0 {
			self.get_slice(self.len() - 1)
		} else {
			None
		}
	}
	/// Array like get mut.
	fn get_slice_mut(&mut self, index: usize) -> Option<HistoriedValue<&mut [u8], S>>;
}

/// Backend for linear storage with inmemory reference.
pub trait LinearStorageMem<V, S>: LinearStorage<V, S> {
	/// Array like get.
	fn get_ref(&self, index: usize) -> Option<HistoriedValue<&V, S>>;
	fn last_ref(&self) -> Option<HistoriedValue<&V, S>> {
		if self.len() > 0 {
			self.get_ref(self.len() - 1)
		} else {
			None
		}
	}
	/// Array like get mut.
	fn get_ref_mut(&mut self, index: usize) -> Option<HistoriedValue<&mut V, S>>;
}

pub trait LinearStorageRange<V, S>: LinearStorage<V, S> {
	/// Array like get. TODO consider not returning option (same for from_slice), inner
	/// implementation being unsafe.
	fn get_range(slice: &[u8], index: usize) -> Option<HistoriedValue<Range<usize>, S>>;

	fn from_slice(slice: &[u8]) -> Option<Self>;
}

#[cfg(test)]
mod test {
	use super::*;
	pub(crate) type State = u32;
	pub(crate) type Value = Vec<u8>;

	// basic test for linear storage usage
	pub(crate) fn test_linear_storage<L: LinearStorage<Value, State>>(storage: &mut L) {
		// empty storage
		assert!(storage.pop().is_none());
		assert!(storage.get_state(0).is_none());
		assert!(storage.get_state(10).is_none());
		assert!(storage.st_get(0).is_none());
		assert!(storage.st_get(10).is_none());
		assert!(storage.len() == 0);
		storage.truncate(0);
		storage.truncate(10);
		storage.truncate_until(0);
		storage.truncate_until(10);
		// single element
		let h: HistoriedValue<Value, State> = (vec![5], 5).into();
		storage.push(h.clone());
		assert_eq!(storage.get_state(0), Some(5));
		assert_eq!(storage.st_get(0), Some(h.clone()));
		assert!(storage.st_get(1).is_none());
		let h: HistoriedValue<Value, State> = (vec![2], 2).into();
		storage.insert(0, h);
		assert_eq!(storage.get_state(0), Some(2));
		assert_eq!(storage.get_state(1), Some(5));
		storage.remove(0);
		assert_eq!(storage.get_state(0), Some(5));
		assert!(storage.st_get(1).is_none());
		storage.clear();
		for i in 0usize..30 {
			let h: HistoriedValue<Value, State> = (vec![i as u8], i as State).into();
			storage.push(h);
		}
		for i in 0usize..30 {
			assert_eq!(storage.get_state(i), Some(i as State));
		}
		storage.truncate_until(5);
		for i in 0usize..25 {
			assert_eq!(storage.get_state(i), Some(i as State + 5));
		}
		assert!(storage.st_get(25).is_none());
		storage.truncate(20);
		for i in 0usize..20 {
			assert_eq!(storage.get_state(i), Some(i as State + 5));
		}
		assert!(storage.st_get(20).is_none());
		storage.remove(10);
		for i in 0usize..10 {
			assert_eq!(storage.get_state(i), Some(i as State + 5));
		}
		for i in 10usize..19 {
			assert_eq!(storage.get_state(i), Some(i as State + 6));
		}
		assert!(storage.st_get(19).is_none());
		storage.emplace(18, (vec![1], 1).into());
		storage.emplace(17, (vec![2], 2).into());
		storage.emplace(0, (vec![3], 3).into());
		assert_eq!(storage.get_state(18), Some(1 as State));
		assert_eq!(storage.get_state(17), Some(2 as State));
		assert_eq!(storage.get_state(0), Some(3 as State));
	}
}

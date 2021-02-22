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

//! Historied data that can aggregate their inner values.

use super::*;

/// Result of values aggregation.
///
/// This is a supertrait for historied data build from
/// adding multiple sequentially historied item together.
pub trait Sum<V: SummableValue>: Data<V::Value> {
	/// Get value at this state.
	fn get_sum(&self, at: &Self::S) -> Option<V> {
		let mut builder = V::new_builder();
		let mut changes = Vec::new();
		if !self.get_sum_values(at, &mut changes) {
			debug_assert!(changes.len() == 0); // Incoherent state no origin for diff
		}
		if changes.len() == 0 {
			return None;
		}
		for change in changes.into_iter().rev() {
			builder.add(change);
		}
		Some(builder.result())
	}

	/// Accumulate all changes for this state.
	///
	/// Changes are written in reverse order into `changes`.
	/// Return `true` if the changes fetched for this state can build a
	/// sum.
	fn get_sum_values(&self, at: &Self::S, changes: &mut Vec<V::Value>) -> bool;
}

/// An item that can be build from consecutives
/// diffs.
pub trait SummableValue: Sized {
	/// Change item to use.
	type Value: Value;

	/// Internal type to build items.
	type SumBuilder;

	/// Get a new builder item.
	fn new_builder() -> SumBuilder<Self>;

	/// Check if the item can be a building source,
	/// one that does not require to fetch previous states.
	fn is_complete(diff: &Self::Value) -> bool;


	/// Append a new item with builder, this is should not be use directly.
	fn builder_add(builder: &mut Self::SumBuilder, diff: Self::Value);

	/// Builder result building, this is should not be use directly.
	fn builder_result(builder: &mut Self::SumBuilder) -> Self;
}

/// Trait with logic implementation for the aggregation.
///
/// This is only intended to be use with buildable sequence
/// (starting with a `is_complete` `SummableValue`).
///
/// This trait is not part of `SummableValue` only to allow
/// using `self` from builder.
pub struct SumBuilder<V: SummableValue>(V::SumBuilder);

impl<V: SummableValue> SumBuilder<V> {
	/// Instantiate a new builder.
	fn new(inner_builder: V::SumBuilder) -> Self {
		SumBuilder(inner_builder)
	}

	/// Append a new item.
	fn add(&mut self, diff: V::Value) {
		V::builder_add(&mut self.0, diff)
	}

	/// Build result.
	fn result(&mut self) -> V {
		V::builder_result(&mut self.0)
	}
}

#[cfg(feature = "xdelta3-diff")]
/// Diff using xdelta 3 lib.
///
/// This is mainly experimental and would require some benchmarking.
/// It uses external C dependency and is not no_std compatible.
pub mod xdelta {
	use super::*;

	/// Aggregate sum for optional byte value that
	/// uses xdelta 3 to produce diff as changes to aggregate
	/// a byte value.
	#[derive(Clone, PartialEq, Eq, Debug, Default)]
	pub struct BytesDelta(Option<Vec<u8>>);

	impl std::ops::Deref for BytesDelta {
		type Target = Option<Vec<u8>>;
		fn deref(&self) -> &Self::Target {
			&self.0
		}
	}

	impl std::ops::DerefMut for BytesDelta {
		fn deref_mut(&mut self) -> &mut Self::Target {
			&mut self.0
		}
	}

	impl From<Option<Vec<u8>>> for BytesDelta {
		fn from(v: Option<Vec<u8>>) -> Self {
			BytesDelta(v)
		}
	}

	impl Into<Option<Vec<u8>>> for BytesDelta {
		fn into(self) -> Option<Vec<u8>> {
			self.0
		}
	}

	impl<'a> From<Option<&'a [u8]>> for BytesDelta {
		fn from(v: Option<&'a [u8]>) -> Self {
			BytesDelta(v.map(|v| v.to_vec()))
		}
	}

	#[derive(Clone, Eq, Ord, PartialEq, PartialOrd, Debug)]
	/// Different state of diff that can be seen.
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

	impl BytesDiff {
		pub fn len(&self) -> usize {
			1 + match self {
				BytesDiff::None => 0,
				BytesDiff::VcDiff(b) => b.len(),
				BytesDiff::Value(b) => b.len(),
			}
		}
	}

	impl Value for BytesDiff {
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

		fn from_storage(mut storage: Self::Storage) -> Self {
			match storage.pop() {
				Some(0u8) => {
					debug_assert!(storage.len() == 0);
					BytesDiff::None
				},
				Some(1u8) => BytesDiff::Value(storage),
				Some(2u8) => BytesDiff::VcDiff(storage),
				_ => unreachable!("Value trait does not allow undefined content"),
			}
		}

		fn into_storage(self) -> Self::Storage {
			match self {
				BytesDiff::Value(mut storage) => {
					storage.push(1u8);
					storage
				},
				BytesDiff::VcDiff(mut storage) => {
					storage.push(2u8);
					storage
				},
				BytesDiff::None => vec![0], 
			}
		}
	}

	/// Get a change from two different builded state.
	pub fn substract(
		previous: &BytesDelta,
		target: &BytesDelta,
	) -> <BytesDelta as SummableValue>::Value {
		match (target.0.as_ref(), previous.0.as_ref()) {
			(None, _) => BytesDiff::None,
			(Some(target), None) => BytesDiff::Value(target.clone()),
			(Some(target), Some(previous)) => {
				if let Some(result) = xdelta3::encode(target.as_slice(), previous.as_slice()) {
					if result.len() < target.len() {
						BytesDiff::VcDiff(result)
					} else {
						BytesDiff::Value(target.clone())
					}
				} else {
					// write as standalone
					BytesDiff::Value(target.clone())
				}
			},
		}
	}

	impl SummableValue for BytesDelta {
		type Value = BytesDiff;

		type SumBuilder = Option<Vec<u8>>;

		fn is_complete(diff: &Self::Value) -> bool {
			match diff {
				BytesDiff::VcDiff(_) => false,
				BytesDiff::Value(_)
				| BytesDiff::None => true,
			}
		}

		fn new_builder() -> SumBuilder<Self> {
			SumBuilder::new(None)
		}

		fn builder_add(builder: &mut Self::SumBuilder, diff: Self::Value) {
			match diff {
				BytesDiff::Value(val) => {
					*builder = Some(val);
				},
				BytesDiff::None => {
					*builder = None;
				},
				BytesDiff::VcDiff(diff) => {
					*builder = Some(
						xdelta3::decode(&diff[..], builder.as_ref().map(|v| v.as_slice()).unwrap_or(&[]))
							.expect("diff build only from diff builder")
					);
				}
			}
		}

		fn builder_result(builder: &mut Self::SumBuilder) -> Self {
			BytesDelta(sp_std::mem::replace(builder, None))
		}
	}

	impl crate::backend::nodes::EstimateSize for BytesDiff {
		fn estimate_size(&self) -> usize {
			match self {
				BytesDiff::None => 1,
				BytesDiff::VcDiff(v) => 1 + v.estimate_size(),
				BytesDiff::Value(v) => 1 + v.estimate_size(),
			}
		}
	}

	impl crate::Context for BytesDiff {
		type Context = ();
	}

	impl crate::Trigger for BytesDiff {
		const TRIGGER: bool = false;

		fn trigger_flush(&mut self) { }
	}
}

/// Set delta.
///
/// Example of an aggregate for a structured data.
/// Here a simple key value map.
pub mod map_delta {
	use super::*;
	use codec::Codec;
	use sp_std::collections::btree_map::BTreeMap;
	use sp_std::vec::Vec;

	#[derive(Clone, PartialEq, Eq, Debug, Default)]
	/// Aggregate map, we only store delta (see `MapDiff`) between two states.
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
	/// Possible changes between two states.
	pub enum MapDiff<K, V> {
		Reset(Vec<(K, V)>),
		Changes(Vec<UnitDiff<K, V>>),
	}

	#[derive(Encode, Decode, Clone, Debug, PartialEq, Eq)]
	/// A unit change between two states (partial).
	pub enum UnitDiff<K, V> {
		Insert(K, V),
		Remove(K),
	}

	impl<K, V> Default for MapDiff<K, V> {
		fn default() -> Self {
			MapDiff::Reset(Vec::new())
		}
	}

	impl<K: Codec, V: Codec> Value for MapDiff<K, V> {
		const NEUTRAL: bool = true;
		type Storage = Vec<u8>;

		fn is_neutral(&self) -> bool {
			if let MapDiff::Reset(values) = self {
				values.is_empty()
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

	impl<K: Ord + Codec, V: Codec> SummableValue for MapDelta<K, V> {
		type Value = MapDiff<K, V>;
		type SumBuilder = BTreeMap<K, V>;

		fn is_complete(diff: &Self::Value) -> bool {
			match diff {
				MapDiff::Reset(..) => true,
				MapDiff::Changes(..) => false,
			}
		}

		fn new_builder() -> SumBuilder<Self> {
			SumBuilder::new(BTreeMap::new())
		}

		fn builder_add(builder: &mut Self::SumBuilder, diff: Self::Value) {
			match diff {
				MapDiff::Changes(changes) => {
					for change in changes.into_iter() {
						match change {
							UnitDiff::Insert(k, v) => {
								builder.insert(k, v);
							},
							UnitDiff::Remove(k) => {
								builder.remove(&k);
							},
						}
					}
				},
				MapDiff::Reset(content) => {
					let state: BTreeMap<K, V> = content.into_iter().collect();
					*builder = state;
				},
			}
		}

		fn builder_result(builder: &mut Self::SumBuilder) -> Self {
			MapDelta(sp_std::mem::replace(builder, BTreeMap::new()))
		}
	}
}

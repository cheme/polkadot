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
	/// Internal Value stored in the historied data.
	type Value: Value;

	/// Internal type to build items.
	type SumBuilder: SumBuilder<SummableValue = Self>;

	/// Get a new builder item.
	fn new_builder() -> Self::SumBuilder {
		Self::SumBuilder::new()
	}

	/// Check if the item can be a building source,
	/// one that does not require to fetch previous states.
	fn is_complete(diff: &Self::Value) -> bool;
}

/// Trait with logic implementation for the aggregation.
pub trait SumBuilder {
	type SummableValue: SummableValue;

	/// Instantiate a new builder.
	fn new() -> Self;

	/// Append a new item.
	fn add(&mut self, diff: <Self::SummableValue as SummableValue>::Value);

	/// Build result.
	fn result(&mut self) -> Self::SummableValue;
}

/// TODO rewrite comment (renamed)
/// This is a different trait than item diff, because usually
/// we are able to set the diff directly.
/// Eg if we manage a list, our diff will be index and new item.
/// If a vcdiff, it will be vcdiff calculated from a previous call to
/// get.
/// This usually means that we need to fetch item before modifying,
/// at this point this is how we should proceed (even if it means
/// a redundant query for modifying.
///
/// We could consider merging this trait with `SummableValue`, and
/// have an automated update for the case where we did not fetch
/// the value first.
pub trait Substract {
	type SummableValue: SummableValue;

	fn new() -> Self;
	fn substract(
		&mut self,
		previous: &Self::SummableValue,
		target: &Self::SummableValue,
	) -> <Self::SummableValue as SummableValue>::Value;
}

#[cfg(feature = "xdelta3-diff")]
/// Diff using xdelta 3 lib
pub mod xdelta {
	use super::*;

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

	pub struct BytesSubstract;

	impl Substract for BytesSubstract {
		type SummableValue = BytesDelta;

		fn new() -> Self {
			BytesSubstract
		}
		fn substract(
			&mut self,
			previous: &Self::SummableValue,
			target: &Self::SummableValue,
		) -> <Self::SummableValue as SummableValue>::Value {
			match (target.0.as_ref(), previous.0.as_ref()) {
				(None, _) => BytesDiff::None,
				(Some(target), None) => BytesDiff::Value(target.clone()),
				(Some(target), Some(previous)) => {
					if let Some(mut result) = xdelta3::encode(target.as_slice(), previous.as_slice()) {
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
	}

	pub struct BytesSumBuilder(Option<Vec<u8>>);

	impl SumBuilder for BytesSumBuilder {
		type SummableValue = BytesDelta;

		fn new() -> Self {
			BytesSumBuilder(Default::default())
		}
		fn add(&mut self, diff: <Self::SummableValue as SummableValue>::Value) {
			match diff {
				BytesDiff::Value(mut val) => {
					self.0 = Some(val);
				},
				BytesDiff::None => {
					self.0 = None;
				},
				BytesDiff::VcDiff(diff) => {
					self.0 = Some(
						xdelta3::decode(&diff[..], self.0.as_ref().map(|v| v.as_slice()).unwrap_or(&[]))
							.expect("diff build only from diff builder")
					);
				}
			}
		}
		fn result(&mut self) -> Self::SummableValue {
			BytesDelta(sp_std::mem::replace(&mut self.0, None))
		}
	}

	impl SummableValue for BytesDelta {
		type Value = BytesDiff;
		type SumBuilder = BytesSumBuilder;

		fn is_complete(diff: &Self::Value) -> bool {
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
pub mod map_delta {
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

	impl<K: Codec, V: Codec> Value for MapDiff<K, V> {
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

	pub struct MapSumBuilder<K, V>(BTreeMap<K, V>);

	impl<K: Ord + Codec, V: Codec> SumBuilder for MapSumBuilder<K, V> {
		type SummableValue = MapDelta<K, V>;

		fn new() -> Self {
			MapSumBuilder(BTreeMap::default())
		}
		fn add(&mut self, diff: <Self::SummableValue as SummableValue>::Value) {
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
		fn result(&mut self) -> Self::SummableValue {
			MapDelta(sp_std::mem::replace(&mut self.0, BTreeMap::new()))
		}
	}

	impl<K: Ord + Codec, V: Codec> SummableValue for MapDelta<K, V> {
		type Value = MapDiff<K, V>;
		type SumBuilder = MapSumBuilder<K, V>;

		fn is_complete(diff: &Self::Value) -> bool {
			match diff {
				MapDiff::Reset => true,
				MapDiff::Insert(..)
				| MapDiff::Remove(_) => false,
			}
		}
	}
}

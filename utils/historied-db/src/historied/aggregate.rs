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
//! Trait `Sum` is the result of this values aggragation,
//! while the general data structure is a regular one
//! containing the associated `Value` type for a `SummableValue`.

use super::*;

/// Trait for historied value build from
/// adding multiple item together.
pub trait Sum<V: SumValue>: Data<V::Value> {
	/// Get value at this state.
	fn get_sum(&self, at: &Self::S) -> Option<V> {
		let mut builder = V::new();
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
	/// Changes are written in reverse order into `changes`.
	/// Return `true` if a complete change was written.
	fn get_sum_values(&self, at: &Self::S, changes: &mut Vec<V::Value>) -> bool;
}

/// An item that can be build from consecutives
/// diffs. TODO rename (itemDiff should be the inner type)
pub trait SumValue: Sized {
	/// Internal Value stored.
	/// Default is the empty value (a neutral value
	/// indicating that there is no content).
	type Value: Value + Default;

	/// Internal type to build items.
	type SumBuilder: SumBuilder<SumValue = Self>;

	fn new() -> Self::SumBuilder {
		Self::SumBuilder::new()
	}

	/// Check if the item can be a building source for 
	/// TODO consider a trait specific to diff inner item.
	fn is_complete(diff: &Self::Value) -> bool;
}

pub trait SumBuilder {
	type SumValue: SumValue;

	fn new() -> Self;
	fn add(&mut self, diff: <Self::SumValue as SumValue>::Value);
	fn result(&mut self) -> Self::SumValue;
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
/// We could consider merging this trait with `SumValue`, and
/// have an automated update for the case where we did not fetch
/// the value first.
pub trait Substract {
	type SumValue: SumValue;

	fn new() -> Self;
	fn substract(
		&mut self,
		previous: &Self::SumValue,
		target: &Self::SumValue,
	) -> <Self::SumValue as SumValue>::Value;
}

#[cfg(feature = "xdelta3-diff")]
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

	impl Into<Vec<u8>> for BytesDelta {
		fn into(self) -> Vec<u8> {
			self.0
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
		type SumValue = BytesDelta;

		fn new() -> Self {
			BytesSubstract
		}
		fn substract(
			&mut self,
			previous: &Self::SumValue,
			target: &Self::SumValue,
		) -> <Self::SumValue as SumValue>::Value {
			if target.0.len() == 0 {
				return BytesDiff::None;
			}
			if previous.0.len() == 0 {
				return BytesDiff::Value(target.0.clone());
			}
			if let Some(mut result) = xdelta3::encode(target.0.as_slice(), previous.0.as_slice()) {
				if result.len() < target.len() {
					BytesDiff::VcDiff(result)
				} else {
					BytesDiff::Value(target.0.clone())
				}
			} else {
				// write as standalone
				BytesDiff::Value(target.0.clone())
			}
		}
	}

	pub struct BytesSumBuilder(Vec<u8>);

	impl SumBuilder for BytesSumBuilder {
		type SumValue = BytesDelta;

		fn new() -> Self {
			BytesSumBuilder(Default::default())
		}
		fn add(&mut self, diff: <Self::SumValue as SumValue>::Value) {
			match diff {
				BytesDiff::Value(mut val) => { self.0 = val;
				},
				BytesDiff::None => {
					self.0.clear();
				},
				BytesDiff::VcDiff(diff) => {
					self.0 = xdelta3::decode(&diff[..], self.0.as_slice())
						.expect("diff build only from diff builder");
				}
			}
		}
		fn result(&mut self) -> Self::SumValue {
			BytesDelta(sp_std::mem::replace(&mut self.0, Vec::new()))
		}
	}

	impl SumValue for BytesDelta {
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
		type SumValue = MapDelta<K, V>;

		fn new() -> Self {
			MapSumBuilder(BTreeMap::default())
		}
		fn add(&mut self, diff: <Self::SumValue as SumValue>::Value) {
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
		fn result(&mut self) -> Self::SumValue {
			MapDelta(sp_std::mem::replace(&mut self.0, BTreeMap::new()))
		}
	}

	impl<K: Ord + Codec, V: Codec> SumValue for MapDelta<K, V> {
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

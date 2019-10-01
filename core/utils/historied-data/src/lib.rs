// Copyright 2017-2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! History driven data storage.
//! Useful to store information with history
//! on a per item basis.

#![cfg_attr(not(feature = "std"), no_std)]

use rstd::convert::{TryFrom, TryInto};

pub mod tree;
pub mod linear;

/// An entry at a given history index.
#[derive(Debug, Clone)]
#[cfg_attr(any(test, feature = "test"), derive(PartialEq))]
pub struct HistoriedValue<V, I> {
	/// The stored value.
	pub value: V,
	/// The moment in history when the value got set.
	pub index: I,
}

impl<V, I> From<(V, I)> for HistoriedValue<V, I> {
	fn from(input: (V, I)) -> HistoriedValue<V, I> {
		HistoriedValue { value: input.0, index: input.1 }
	}
}

impl<V, I: Copy> HistoriedValue<V, I> {
	fn as_ref(&self) -> HistoriedValue<&V, I> {
		HistoriedValue {
			value: &self.value,
			index: self.index,
		}
	}

	fn as_mut(&mut self) -> HistoriedValue<&mut V, I> {
		HistoriedValue {
			value: &mut self.value,
			index: self.index,
		}
	}

	fn map<R, F: FnOnce(V) -> R>(self, f: F) -> HistoriedValue<R, I> {
		HistoriedValue {
			value: f(self.value),
			index: self.index,
		}
	}

}

#[derive(Debug, Clone, PartialEq, Copy)]
/// State of a data.
pub enum TransactionState {
	/// Data is under change and can still be dropped.
	Pending,
	/// Data is under change and can still be dropped.
	/// This also mark the start of a transaction.
	TxPending,
	/// Data is committed, but can still be dropped
	/// using `discard_prospective` or `discard_transaction`
	/// from a parent transaction state.
	Prospective,
	/// Committed is data that cannot be dropped.
	Committed,
	/// Data pointing to this indexed historic state should
	/// not be returned and can be removed.
	Dropped,
}

pub const DEFAULT_GC_CONF: GCConfiguration = GCConfiguration {
	trigger_transaction_gc: 100_000,
	trigger_commit_gc: 10_000,
	add_content_size_unit: 64,
};

pub struct GCConfiguration {
	/// Treshold in number of operation before running a garbage collection.
	///
	/// Should be same as `TRIGGER_COMMIT_GC` or higher
	/// (we most likely do not want lower as transaction are
	/// possibly more frequent than commit).
	pub trigger_transaction_gc: usize,

	/// Treshold in number of infooperation before running a garbage colletion
	/// on a commit operation.
	///
	/// We may want a lower value than for a transaction, even
	/// a 1 if we want to do it between every operation.
	pub trigger_commit_gc: usize,

	/// Used to count big content as multiple operations.
	/// This is a number of octet.
	/// Set to 0 to ignore.
	pub add_content_size_unit: usize,
}

impl GCConfiguration {
	/// Cost depending on value if any.
	pub fn operation_cost(&self, val: Option<&rstd::vec::Vec<u8>>) -> usize {
		let additional_cost = if self.add_content_size_unit > 0 {
			if let Some(s) = val.as_ref() {
				s.len() / self.add_content_size_unit
			} else {
				0
			}
		} else { 0 };
		1 + additional_cost
	}

}

// utility function for panicking cast (similar as `as` cas with number
fn as_usize<I: TryInto<usize>>(i: I) -> usize {
	match i.try_into() {
		Ok(index) => index,
		Err(_) => panic!("historied value index overflow"),
	}
}

// utility function for panicking cast (similar as `as` cas with number
fn as_i<I: TryFrom<usize>>(i: usize) -> I {
	match i.try_into() {
		Ok(index) => index,
		Err(_) => panic!("historied value index underflow"),
	}
}

/*
//pub trait HistoriedData<I, V, VRef, VRefMut, State, StateRef, StatePruning> {
pub trait HistoriedData<V, State> {

	fn get_trait(self, history: State) -> Option<V>;

}

pub trait HistoriedDataMut<I, V, VRef, State, StatePruning> {

	fn set_trait(self, history: State, value: V);

	fn get_mut_trait(self, history: State) -> Option<HistoriedValue<VRef, I>>;

	fn get_mut_pruning_trait(
		self,
		history: State,
		pruning_infos: StatePruning,
	) -> Option<HistoriedValue<VRef, I>>;

}*/

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

//! Transactional overlay implementation.
//!
//! This follows a linear succession of states.
//! This contains multiple unbounded transaction layer
//! and an additional top level 'prospective' layer.
//! It only allows linear history (no branch so
//! inner storage is only an array of element).

use crate::State as TransactionState;
use rstd::vec::Vec;
use rstd::vec;
use rstd::borrow::Cow;

/// An entry at a given history height.
#[derive(Debug, Clone)]
#[cfg_attr(any(test, feature = "test"), derive(PartialEq))]
pub struct HistoriedValue<V> {
	/// The stored value.
	pub value: V,
	/// The moment in history when the value got set.
	pub index: usize,
}

impl<V> From<(V, usize)> for HistoriedValue<V> {
	fn from(input: (V, usize)) -> HistoriedValue<V> {
		HistoriedValue { value: input.0, index: input.1 }
	}
}

impl<V> HistoriedValue<V> {
	fn as_ref(&self) -> HistoriedValue<&V> {
		HistoriedValue {
			value: &self.value,
			index: self.index,
		}
	}

	fn as_mut(&mut self) -> HistoriedValue<&mut V> {
		HistoriedValue {
			value: &mut self.value,
			index: self.index,
		}
	}

	fn map<R, F: FnOnce(V) -> R>(self, f: F) -> HistoriedValue<R> {
		HistoriedValue {
			value: f(self.value),
			index: self.index,
		}
	}

}

/// Array like buffer for in memory storage.
/// By in memory we expect that this will
/// not required persistence and is not serialized.
#[cfg(not(feature = "std"))]
pub(crate) type MemoryOnly<V> = Vec<HistoriedValue<V>>;

/// Array like buffer for in memory storage.
/// By in memory we expect that this will
/// not required persistence and is not serialized.
#[cfg(feature = "std")]
pub(crate) type MemoryOnly<V> = smallvec::SmallVec<[HistoriedValue<V>; ALLOCATED_HISTORY]>;

/// Size of preallocated history per element.
/// Currently at two for committed and prospective only.
/// It means that using transaction in a module got a direct allocation cost.
#[cfg(feature = "std")]
const ALLOCATED_HISTORY: usize = 2;

/// History of value that are related to a state history (eg field `history` of
/// an `OverlayedChangeSet`).
///
/// Values are always paired with a state history index.
#[derive(Debug, Clone)]
#[cfg_attr(any(test, feature = "test"), derive(PartialEq))]
pub struct History<V>(MemoryOnly<V>);

impl<V> Default for History<V> {
	fn default() -> Self {
		History(Default::default())
	}
}

// Following implementation are here to isolate
// buffer specific functions.
impl<V> History<V> {

	fn get_state(&self, index: usize) -> HistoriedValue<&V> {
		self.0[index].as_ref()
	}

	#[cfg(any(test, feature = "test"))]
	/// Create an history from an existing history.
	pub fn from_iter(input: impl IntoIterator<Item = HistoriedValue<V>>) -> Self {
		let mut history = History::default();
		for v in input {
			history.push_unchecked(v);
		}
		history
	}

	#[cfg(any(test, feature = "test"))]
	pub fn len(&self) -> usize {
		self.0.len()
	}

	#[cfg(not(any(test, feature = "test")))]
	fn len(&self) -> usize {
		self.0.len()
	}

	fn truncate(&mut self, index: usize) {
		self.0.truncate(index)
	}

	fn pop(&mut self) -> Option<HistoriedValue<V>> {
		self.0.pop()
	}

	fn remove(&mut self, index: usize) {
		let _ = self.0.remove(index);
	}

	/// Append without checking if a value already exist.
	/// If a value already exists, the history will be broken.
	/// This method shall only be call after a `get_mut` where
	/// the returned index indicate that a `set` will result
	/// in appending a value.
	pub fn push_unchecked(&mut self, value: HistoriedValue<V>) {
		self.0.push(value)
	}

	/// Set a value, it uses a state history as parameter.
	/// This method uses `get_mut` and do remove pending
	/// dropped value.
	pub fn set(&mut self, history: &[TransactionState], value: V) {
		if let Some(v) = self.get_mut(history) {
			if v.index == history.len() - 1 {
				*v.value = value;
				return;
			}
		}
		self.push_unchecked(HistoriedValue {
			value,
			index: history.len() - 1,
		});
	}

	fn mut_ref(&mut self, index: usize) -> &mut V {
		&mut self.0[index].value
	}

}

#[derive(Debug, Clone)]
#[cfg_attr(any(test, feature = "test"), derive(PartialEq))]
pub struct States(Vec<TransactionState>);

impl Default for States {
	fn default() -> Self {
		States(vec![TransactionState::Pending])
	}
}

impl States {
	pub fn as_ref(&self) -> &[TransactionState] {
		self.0.as_ref()
	}

	pub fn iter<'a>(&'a self) -> impl Iterator<Item = (usize, TransactionState)> + 'a {
		self.0.iter().map(Clone::clone).enumerate()
	}
}

impl States {

	/// Build any state for testing only.
	#[cfg(any(test, feature = "test"))]
	pub fn test_vector(test_states: Vec<TransactionState>) -> Self {
		States(test_states)
	}

	/// Discard prospective changes to state.
	pub fn discard_prospective(&mut self) {
		let mut i = self.0.len();
		while i > 0 {
			i -= 1;
			match self.0[i] {
				TransactionState::Dropped => (),
				TransactionState::Pending
				| TransactionState::TxPending
				| TransactionState::Prospective => self.0[i] = TransactionState::Dropped,
				TransactionState::Committed => break,
			}
		}
		self.0.push(TransactionState::Pending);
	}

	/// Commit prospective changes to state.
	pub fn commit_prospective(&mut self) {
		debug_assert!(self.0.len() > 0);
		let mut i = self.0.len();
		while i > 0 {
			i -= 1;
			match self.0[i] {
				TransactionState::Dropped => (),
				TransactionState::Prospective
				| TransactionState::TxPending
				| TransactionState::Pending => self.0[i] = TransactionState::Committed,
				| TransactionState::Committed => break,
			}
		}
		self.0.push(TransactionState::Pending);
	}

	/// Create a new transactional layer.
	pub fn start_transaction(&mut self) {
		self.0.push(TransactionState::TxPending);
	}

	/// Discard a transactional layer.
	/// A transaction is always running (history always end with pending).
	pub fn discard_transaction(&mut self) {
		let mut i = self.0.len();
		while i > 0 {
			i -= 1;
			match self.0[i] {
				TransactionState::Dropped => (),
				TransactionState::Prospective
				| TransactionState::Pending => self.0[i] = TransactionState::Dropped,
				TransactionState::TxPending => {
					self.0[i] = TransactionState::Dropped;
					break;
				},
				TransactionState::Committed => break,
			}
		}
		self.0.push(TransactionState::Pending);
	}

	/// Commit a transactional layer.
	pub fn commit_transaction(&mut self) {
		let mut i = self.0.len();
		while i > 0 {
			i -= 1;
			match self.0[i] {
				TransactionState::Prospective
				| TransactionState::Dropped => (),
				TransactionState::Pending => self.0[i] = TransactionState::Prospective,
				TransactionState::TxPending => {
					self.0[i] = TransactionState::Prospective;
					break;
				},
				TransactionState::Committed => break,
			}
		}
		self.0.push(TransactionState::Pending);
	}

	/// Return array of `TxPending` indexes in state.
	/// This is use as an input for garbage collection.
	pub fn transaction_indexes(&self) -> Vec<usize> {
		let mut transaction_index = Vec::new();
		for (i, state) in self.0.iter().enumerate() {
			if &TransactionState::TxPending == state {
				transaction_index.push(i);
			}
		}
		transaction_index
	}


}

#[derive(Debug, Clone)]
#[cfg_attr(any(test, feature = "test"), derive(PartialEq))]
/// Arraylike buffer with in place byte data.
/// Can be written as is in underlying
/// storage.
/// Could be use for direct access memory to.
pub struct Serialized<'a>(Cow<'a, [u8]>);


// Basis implementation to be on par with implementation using
// vec like container. Those method could be move to a trait
// implementation.
// Those function requires checked index.
impl<'a> Serialized<'a> {

	fn into_owned(self) -> Serialized<'static> {
    Serialized(Cow::from(self.0.into_owned()))
  }

	fn len(&self) -> usize {
		let len = self.0.len();
		self.read_le_usize(len - 4)
	}

	fn clear(&mut self) {
		self.write_le_usize(0, 0);
		self.0.to_mut().truncate(4);
	}

	fn truncate(&mut self, index: usize) {
		if index == 0 {
			self.clear();
			return;
		}
		let len = self.len();
		if index >= len {
			return;
		}
		let start_ix = self.index_start();
		let new_start = self.index_element(index);
		let len_ix = index * 4;
		self.slice_copy(start_ix, new_start, len_ix);
		self.write_le_usize(new_start + len_ix - 4, index);
		self.0.to_mut().truncate(new_start + len_ix);
	}

	fn pop(&mut self) -> Option<HistoriedValue<Vec<u8>>> {
		let len = self.len();
		if len == 0 {
			return None;
		}
		let start_ix = self.index_element(len - 1);
		let end_ix = self.index_start();
		let state = self.read_le_usize(start_ix);
		let value = self.0[start_ix + 4..end_ix].to_vec();
		if len - 1 == 0 {
			self.clear();
			return Some(HistoriedValue { value, index: state })	
		} else {
			self.write_le_usize(self.0.len() - 8, len - 1);
		};
		let ix_size = (len * 4) - 4;
		self.slice_copy(end_ix, start_ix, ix_size);
		self.0.to_mut().truncate(start_ix + ix_size);
		Some(HistoriedValue { value, index: state })
	}

	fn push(&mut self, val: (&[u8], usize)) {
		let len = self.len();
		let start_ix = self.index_start();
		let end_ix = self.0.len();
		// A sized buffer and multiple index to avoid to big copy
		// should be use here.
		let mut new_ix = self.0[start_ix..end_ix].to_vec();
		// truncate here can be bad
		self.0.to_mut().truncate(start_ix + 4);
		self.write_le_usize(start_ix, val.1);
		self.0.to_mut().extend_from_slice(val.0);
		self.0.to_mut().append(&mut new_ix);
		if len > 0 {
			self.write_le_usize(self.0.len() - 4, start_ix);
			self.append_le_usize(len + 1);
		} else {
			self.write_le_usize(self.0.len() - 4, 1);
		}
	}

	fn remove(&mut self, index: usize) {
		let len = self.len();
		if len == 1 && index == 0 {
			self.clear();
			return;
		}
		// eager removal is costy, running some gc impl
		// can be interesting (would be malleable serializing).
		let elt_start = self.index_element(index);
		let start_ix = self.index_start();
		let elt_end = if index == len - 1 {
			start_ix
		} else {
			self.index_element(index + 1) 
		};
		let delete_size = elt_end - elt_start;
		for _ in elt_start..elt_end {
			let _ = self.0.to_mut().remove(elt_start);
		}
		let start_ix = start_ix - delete_size;
		for i in 1..len - index - 1 {
			let old_value = self.read_le_usize(start_ix + i * 4);
			self.write_le_usize(start_ix + (i - 1) * 4, old_value - delete_size);
		}
		let len = len - 1;
		let end_index = start_ix + len * 4;
		self.write_le_usize(end_index - 4, len);
		self.0.to_mut().truncate(end_index);

	}

	fn get_state(&self, index: usize) -> HistoriedValue<&[u8]> {
		let start_ix = self.index_element(index);
		let len = self.len();
		let end_ix = if index == len - 1 {
			self.index_start()
		} else {
			self.index_element(index + 1)
		};
		let state = self.read_le_usize(start_ix);
		HistoriedValue {
			value: &self.0[start_ix + 4..end_ix],
			index: state,
		}
	}

}

impl<'a> Default for Serialized<'a> {
	fn default() -> Self {
		Serialized(Cow::Borrowed(&[0u8; 4][..]))
	}
}

// Utility function for basis implementation.
impl<'a> Serialized<'a> {
	
	// Index at end, also contains the encoded size
	fn index_start(&self) -> usize {
		let nb_ix = self.len();
		if nb_ix ==0 { return 0; }
		let end = self.0.len();
		end - (nb_ix * 4)
	}

	fn index_element(&self, position: usize) -> usize {
		if position == 0 {
			return 0;
		}
		let i = self.index_start() + (position - 1) * 4;
		self.read_le_usize(i)
	}

	// move part of array that can overlap
	// This is a memory inefficient implementation.
	fn slice_copy(&mut self, start_from: usize, start_to: usize, size: usize) {
		let buffer = self.0[start_from..start_from + size].to_vec();
		self.0.to_mut()[start_to..start_to + size].copy_from_slice(&buffer[..]);
	}

	// Usize encoded as le u32.
	fn read_le_usize(&self, pos: usize) -> usize {
		let mut buffer = [0u8; 4];
		buffer.copy_from_slice(&self.0[pos..pos + 4]);
		u32::from_le_bytes(buffer) as usize
	}

	// Usize encoded as le u32.
	fn write_le_usize(&mut self, pos: usize, value: usize) {
		let buffer = (value as u32).to_le_bytes();
		self.0.to_mut()[pos..pos + 4].copy_from_slice(&buffer[..]);
	}

	// Usize encoded as le u32.
	fn append_le_usize(&mut self, value: usize) {
		let buffer = (value as u32).to_le_bytes();
		self.0.to_mut().extend_from_slice(&buffer[..]);
	}

}

impl<'a> Serialized<'a> {

	/// Set a value, it uses a state history as parameter.
	/// This method uses `get_mut` and do remove pending
	/// dropped value.
	pub fn set(&mut self, history: &[TransactionState], val: &[u8]) {
		if let Some(v) = self.get_mut(history) {
			if v.index == history.len() - 1 {
				self.pop();
				self.push((val, v.index));
				return;
			}
		}
		self.push((val, history.len() - 1));
	}

	fn mut_ref(&mut self, _index: usize) -> () {
		()
	}

}


// share implementation, trait would be better.
macro_rules! history_impl(( $read: ty, $owned: ty, $mut: ty ) => {

	/// Access to latest pending value (non dropped state in history).
	/// When possible please prefer `get_mut` as it can free
	/// some memory.
	pub fn get(&self, history: &[TransactionState]) -> Option<$read> {
		// index is never 0,
		let mut index = self.len();
		if index == 0 {
			return None;
		}
		debug_assert!(history.len() >= index);
		while index > 0 {
			index -= 1;
			let HistoriedValue { value, index: history_index } = self.get_state(index);
			match history[history_index] {
				TransactionState::Dropped => (),
				TransactionState::Pending
				| TransactionState::TxPending
				| TransactionState::Prospective
				| TransactionState::Committed =>
					return Some(value),
			}
		}
		None
	}

	/// Get latest value, consuming the historied data.
	pub fn into_pending(mut self, history: &[TransactionState]) -> Option<$owned> {
		let mut index = self.len();
		if index == 0 {
			return None;
		}
		debug_assert!(history.len() >= index);
		while index > 0 {
			index -= 1;
			let history_index = self.get_state(index).index;
			match history[history_index] {
				TransactionState::Dropped => (),
				TransactionState::Pending
				| TransactionState::TxPending
				| TransactionState::Prospective
				| TransactionState::Committed => {
					self.truncate(index + 1);
					return self.pop().map(|v| v.value);
				},
			}
		}
		None
	}

	#[cfg(any(test, feature = "test"))]
	pub fn get_prospective(&self, history: &[TransactionState]) -> Option<$read> {
		// index is never 0,
		let mut index = self.len();
		if index == 0 {
			return None;
		}
		debug_assert!(history.len() >= index);
		while index > 0 {
			index -= 1;
			let HistoriedValue { value, index: history_index } = self.get_state(index);
			match history[history_index] {
				TransactionState::Pending
				| TransactionState::TxPending
				| TransactionState::Prospective =>
					return Some(value),
				TransactionState::Committed
				| TransactionState::Dropped => (),
			}
		}
		None
	}

	#[cfg(any(test, feature = "test"))]
	pub fn get_committed(&self, history: &[TransactionState]) -> Option<$read> {
		// index is never 0,
		let mut index = self.len();
		if index == 0 {
			return None;
		}
		debug_assert!(history.len() >= index);
		while index > 0 {
			index -= 1;
			let HistoriedValue { value, index: history_index } = self.get_state(index);
			match history[history_index] {
				TransactionState::Committed => return Some(value),
				TransactionState::Pending
				| TransactionState::TxPending
				| TransactionState::Prospective
				| TransactionState::Dropped => (),
			}
		}
		None
	}

	pub fn into_committed(mut self, history: &[TransactionState]) -> Option<$owned> {
		// index is never 0,
		let mut index = self.len();
		if index == 0 {
			return None;
		}
		// internal method: should be use properly
		// (history of the right overlay change set
		// is size aligned).
		debug_assert!(history.len() >= index);
		while index > 0 {
			index -= 1;
			let history_index = self.get_state(index).index;
			match history[history_index] {
				TransactionState::Committed => {
					self.truncate(index + 1);
					return self.pop().map(|v| v.value);
				},
				TransactionState::Pending
				| TransactionState::TxPending
				| TransactionState::Prospective
				| TransactionState::Dropped => (),
			}
		}
		None
	}

	/// Access to latest pending value (non dropped state in history).
	///
	/// This method removes latest dropped values up to the latest valid value.
	pub fn get_mut(&mut self, history: &[TransactionState]) -> Option<HistoriedValue<$mut>> {

		let mut index = self.len();
		if index == 0 {
			return None;
		}
		// internal method: should be use properly
		// (history of the right overlay change set
		// is size aligned).
		debug_assert!(history.len() >= index);
		while index > 0 {
			index -= 1;
			let history_index = self.get_state(index).index;
			match history[history_index] {
				TransactionState::Committed => {
					// here we could gc all preceding values but that is additional cost
					// and get_mut should stop at pending following committed.
					return Some((self.mut_ref(index), history_index).into())
				},
				TransactionState::Pending
				| TransactionState::TxPending
				| TransactionState::Prospective => {
					return Some((self.mut_ref(index), history_index).into())
				},
				TransactionState::Dropped => { let _ = self.pop(); },
			}
		}
		None
	}


	/// Garbage collect the history, act as a `get_mut` with additional cost.
	/// To run `eager`, a `transaction_index` parameter of all `TxPending` states
	/// must be provided, then all dropped value are removed even if it means shifting
	/// array byte. Otherwhise we mainly garbage collect up to last Commit state
	/// (truncate left size).
	pub fn get_mut_pruning(
		&mut self,
		history: &[TransactionState],
		transaction_index: Option<&[usize]>,
	) -> Option<HistoriedValue<$mut>> {
		if let Some(mut transaction_index) = transaction_index {
			let mut index = self.len();
			if index == 0 {
				return None;
			}
			// indicates that we got a value to return up to previous
			// `TxPending` so values in between can be dropped.
			let mut below_value = usize::max_value();
			let mut result: Option<(usize, usize)> = None;
			// internal method: should be use properly
			// (history of the right overlay change set
			// is size aligned).
			debug_assert!(history.len() >= index);
			while index > 0 {
				index -= 1;
				let history_index = self.get_state(index).index;
				match history[history_index] {
					TransactionState::Committed => {
						for _ in 0..index {
							self.remove(0);
						}
						result = Some(result.map(|(i, history_index)| (i - index, history_index))
							.unwrap_or((0, history_index)));
						break;
					},
					TransactionState::Pending
					| TransactionState::Prospective => {
						if history_index >= below_value {
							self.remove(index);
							result.as_mut().map(|(i, _)| *i = *i - 1);
						} else {
							if result.is_none() {
								result = Some((index, history_index));
							}
							// move to next previous `TxPending`
							while below_value > history_index {
								// mut slice pop
								let split = transaction_index.split_last()
									.map(|(v, sl)| (*v, sl))
									.unwrap_or((0, &[]));
								below_value = split.0;
								transaction_index = split.1;
							}
						}
					},
					TransactionState::TxPending => {
						if history_index >= below_value {
							self.remove(index);
							result.as_mut().map(|(i, _)| *i = *i - 1);
						} else {
							if result.is_none() {
								result = Some((index, history_index));
							}
						}
						below_value = usize::max_value();
					},
					TransactionState::Dropped => {
						self.remove(index);
					},
				}
			}
			if let Some((index, history_index)) = result {
				Some((self.mut_ref(index), history_index).into())
			} else { None }

		} else {
			self.get_mut(history)
		}
	}
});

impl<'a> Serialized<'a> {
	history_impl!(&[u8], Vec<u8>, ());
}

impl<V> History<V> {
	history_impl!(&V, V, &mut V);
}

#[cfg(test)]
mod test {
	use super::*;

	#[test]
	fn serialized_basis() {
		// test basis unsafe function similar to a simple vec
		// without index checking.
		let v1 = &b"val1"[..];
		let v2 = &b"value_2"[..];
		let v3 = &b"a third value 3"[..];
		let mut ser = Serialized::default();
		assert_eq!(ser.len(), 0);
		assert_eq!(ser.pop(), None);
		ser.push((v1, 1));
		assert_eq!(ser.get_state(0), (v1, 1).into());
		assert_eq!(ser.pop(), Some((v1.to_vec(), 1).into()));
		assert_eq!(ser.len(), 0);
		ser.push((v1, 1));
		ser.push((v2, 2));
		ser.push((v3, 3));
 		assert_eq!(ser.get_state(0), (v1, 1).into());
		assert_eq!(ser.get_state(1), (v2, 2).into());
		assert_eq!(ser.get_state(2), (v3, 3).into());
		assert_eq!(ser.pop(), Some((v3.to_vec(), 3).into()));
		assert_eq!(ser.len(), 2);
		ser.push((v3, 3));
		assert_eq!(ser.get_state(2), (v3, 3).into());
		ser.remove(0);
		assert_eq!(ser.len(), 2);
		assert_eq!(ser.get_state(0), (v2, 2).into());
		assert_eq!(ser.get_state(1), (v3, 3).into());
		ser.push((v1, 1));
		ser.remove(1);
		assert_eq!(ser.len(), 2);
		assert_eq!(ser.get_state(0), (v2, 2).into());
		assert_eq!(ser.get_state(1), (v1, 1).into());
		ser.push((v1, 1));
		ser.truncate(1);
		assert_eq!(ser.len(), 1);
		assert_eq!(ser.get_state(0), (v2, 2).into());
	}
}

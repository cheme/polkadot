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

//! Children storage related traits and implementations.

use core::fmt::Debug;
use core::mem::replace;
use derivative::Derivative;
use crate::radix::RadixConf;
use alloc::boxed::Box;

/// Children node index, depending on the radix use
/// different type can be use.
pub trait NodeIndex: Clone + Copy + Debug + PartialEq {
	fn zero() -> Self;
	fn next(&self) -> Option<Self>;
}

mod node_indexes_impls {
	use super::*;

	impl NodeIndex for bool {
		fn zero() -> Self {
			false
		}
		fn next(&self) -> Option<Self> {
			if *self {
				None
			} else {
				Some(true)
			}
		}
	}

	impl NodeIndex for u8 {
		fn zero() -> Self {
			0
		}
		fn next(&self) -> Option<Self> {
			if *self == 255 {
				None
			} else {
				Some(*self + 1)
			}
		}
	}
}

/// A children node container.
pub trait Children: Clone + Debug {
	type Radix: RadixConf;
	type Node;

	fn empty() -> Self;

	fn set_child(
		&mut self,
		index: <Self::Radix as RadixConf>::KeyIndex,
		child: Box<Self::Node>,
	) -> Option<Box<Self::Node>>;

	fn remove_child(
		&mut self,
		index: <Self::Radix as RadixConf>::KeyIndex,
	) -> Option<Box<Self::Node>>;

	fn number_child(
		&self,
	) -> usize;

	fn has_child(
		&self,
		index: <Self::Radix as RadixConf>::KeyIndex,
	) -> bool {
		self.get_child(index).is_some()
	}

	fn get_child(
		&self,
		index: <Self::Radix as RadixConf>::KeyIndex,
	) -> Option<&Self::Node>;

	fn get_child_mut(
		&mut self,
		index: <Self::Radix as RadixConf>::KeyIndex,
	) -> Option<&mut Self::Node>;

	fn first_child_index(
		&self,
	) -> Option<<Self::Radix as RadixConf>::KeyIndex> {
		let mut ix = <Self::Radix as RadixConf>::KeyIndex::zero();
		loop {
			// TODO avoid this double query? (need unsafe)
			// at least make a contains_child fn.
			let result = self.get_child(ix);
			if result.is_some() {
				return Some(ix)
			}

			ix = if let Some(ix) = ix.next() {
				ix
			} else {
				break;
			};
		}
		None
	}
}

#[derive(Derivative)]
#[derivative(Clone)]
#[derivative(Debug)]
struct Children2<N> (
	Option<(Option<Box<N>>, Option<Box<N>>)>
);

impl<N: Debug + Clone> Children for Children2<N> {
	type Radix = crate::radix::impls::Radix2Conf;

	type Node = N;

	fn empty() -> Self {
		Children2(None)
	}

	fn set_child(
		&mut self,
		index: <Self::Radix as RadixConf>::KeyIndex,
		child: Box<N>,
	) -> Option<Box<N>> {
		if self.0.is_none() {
			self.0 = Some((None, None));
		}
		let children = self.0.as_mut()
			.expect("Lazy init above");
		if index {
			replace(&mut children.0, Some(child))
		} else {
			replace(&mut children.1, Some(child))
		}
	}

	fn remove_child(
		&mut self,
		index: <Self::Radix as RadixConf>::KeyIndex,
	) -> Option<Box<N>> {
		if let Some(children) = self.0.as_mut() {
			if index {
				replace(&mut children.0, None)
			} else {
				replace(&mut children.1, None)
			}
		} else {
			None
		}
	}

	fn number_child(
		&self,
	) -> usize {
		match self.0.as_ref() {
			Some(b) => match &b {
				(Some(_), Some(_)) => 2,
				(None, Some(_)) => 1,
				(Some(_), None) => 1,
				(None, None) => 0,
			},
			None => 0,
		}
	}

	fn get_child(
		&self,
		index: <Self::Radix as RadixConf>::KeyIndex,
	) -> Option<&N> {
		self.0.as_ref().and_then(|b| if index {
			b.0.as_ref().map(AsRef::as_ref)
		} else {
			b.1.as_ref().map(AsRef::as_ref)
		})
	}

	fn get_child_mut(
		&mut self,
		index: <Self::Radix as RadixConf>::KeyIndex,
	) -> Option<&mut N> {
		self.0.as_mut().and_then(|b| if index {
			b.0.as_mut().map(AsMut::as_mut)
		} else {
			b.1.as_mut().map(AsMut::as_mut)
		})
	}
}

#[derive(Derivative)]
#[derivative(Clone)]
pub struct Children256<N> (
	// 256 array is to big but ok for initial implementation
	Option<[Option<Box<N>>; 256]>,
	u8,
);

/// 48 children for art tree.
#[derive(Derivative)]
#[derivative(Clone)]
pub struct Children48<N> (
	Option<([u8; 256], [Option<Box<N>>; 48])>,
	u8,
);

/// 16 children for art tree.
#[derive(Derivative)]
#[derivative(Clone)]
pub struct Children16<N> (
	Option<([u8; 16], [Option<Box<N>>; 16])>,
	u8,
);

/// 4 children for art tree.
#[derive(Derivative)]
#[derivative(Clone)]
pub struct Children4<N> (
	Option<([u8; 4], [Option<Box<N>>; 4])>,
	u8,
);

/// Adaptative only between 48 and 256.
#[derive(Derivative)]
#[derivative(Clone)]
pub enum ART48_256<N> {
	ART4(Children4<N>),
	ART16(Children16<N>),
	ART48(Children48<N>),
	ART256(Children256<N>),
}

const fn empty_4_children<N>() -> [Option<N>; 4] {
	// TODO copy tree crate macro
	[
		None, None, None, None,
	]
}

const fn empty_16_children<N>() -> [Option<N>; 16] {
	// TODO copy tree crate macro
	[
		None, None, None, None, None, None, None, None,
		None, None, None, None, None, None, None, None,
	]
}

const fn empty_48_children<N>() -> [Option<N>; 48] {
	// TODO copy tree crate macro
	[
		None, None, None, None, None, None, None, None,
		None, None, None, None, None, None, None, None,
		None, None, None, None, None, None, None, None,
		None, None, None, None, None, None, None, None,
		None, None, None, None, None, None, None, None,
		None, None, None, None, None, None, None, None,
	]
}

const fn empty_256_children<N>() -> [Option<N>; 256] {
	// TODO copy tree crate macro
	[
		None, None, None, None, None, None, None, None,
		None, None, None, None, None, None, None, None,
		None, None, None, None, None, None, None, None,
		None, None, None, None, None, None, None, None,
		None, None, None, None, None, None, None, None,
		None, None, None, None, None, None, None, None,
		None, None, None, None, None, None, None, None,
		None, None, None, None, None, None, None, None,
		None, None, None, None, None, None, None, None,
		None, None, None, None, None, None, None, None,
		None, None, None, None, None, None, None, None,
		None, None, None, None, None, None, None, None,
		None, None, None, None, None, None, None, None,
		None, None, None, None, None, None, None, None,
		None, None, None, None, None, None, None, None,
		None, None, None, None, None, None, None, None,
		None, None, None, None, None, None, None, None,
		None, None, None, None, None, None, None, None,
		None, None, None, None, None, None, None, None,
		None, None, None, None, None, None, None, None,
		None, None, None, None, None, None, None, None,
		None, None, None, None, None, None, None, None,
		None, None, None, None, None, None, None, None,
		None, None, None, None, None, None, None, None,
		None, None, None, None, None, None, None, None,
		None, None, None, None, None, None, None, None,
		None, None, None, None, None, None, None, None,
		None, None, None, None, None, None, None, None,
		None, None, None, None, None, None, None, None,
		None, None, None, None, None, None, None, None,
		None, None, None, None, None, None, None, None,
		None, None, None, None, None, None, None, None,
	]
}

impl<N: Debug> Debug for Children256<N> {
	fn fmt(&self, f: &mut core::fmt::Formatter) -> core::result::Result<(), core::fmt::Error> {
		if let Some(children) = self.0.as_ref() {
			children[..].fmt(f)
		} else {
			let empty: &[N] = &[]; 
			empty.fmt(f)
		}
	}
}

impl<N: Debug> Debug for Children48<N> {
	fn fmt(&self, f: &mut core::fmt::Formatter) -> core::result::Result<(), core::fmt::Error> {
		"unimplemented children 48".fmt(f)
	}
}

impl<N: Debug> Debug for Children16<N> {
	fn fmt(&self, f: &mut core::fmt::Formatter) -> core::result::Result<(), core::fmt::Error> {
		"unimplemented children 16".fmt(f)
	}
}

impl<N: Debug> Debug for Children4<N> {
	fn fmt(&self, f: &mut core::fmt::Formatter) -> core::result::Result<(), core::fmt::Error> {
		"unimplemented children 4".fmt(f)
	}
}

impl<N: Debug> Debug for ART48_256<N> {
	fn fmt(&self, f: &mut core::fmt::Formatter) -> core::result::Result<(), core::fmt::Error> {
		"unimplemented art children format".fmt(f)
	}
}

impl<N: Debug + Clone> Children for Children256<N> {
	type Radix = crate::radix::impls::Radix256Conf;

	type Node = N;

	fn empty() -> Self {
		Children256(None, 0)
	}

	fn set_child(
		&mut self,
		index: <Self::Radix as RadixConf>::KeyIndex,
		child: Box<N>,
	) -> Option<Box<N>> {
		if self.0.is_none() {
			self.0 = Some(empty_256_children());
		}
		let children = self.0.as_mut()
			.expect("Lazy init above");
		let result = replace(&mut children[index as usize], Some(child));
		if result.is_none() {
			self.1 += 1;
		}
		result
	}

	fn remove_child(
		&mut self,
		index: <Self::Radix as RadixConf>::KeyIndex,
	) -> Option<Box<N>> {
		if let Some(children) = self.0.as_mut() {
			let result = replace(&mut children[index as usize], None);
			if result.is_some() {
				self.1 -= 1;
			}
			result
		} else {
			None
		}
	}

	fn number_child(
		&self,
	) -> usize {
		self.1 as usize
	}

	fn get_child(
		&self,
		index: <Self::Radix as RadixConf>::KeyIndex,
	) -> Option<&N> {
		self.0.as_ref().and_then(|b| b[index as usize].as_ref())
			.map(AsRef::as_ref)
	}

	fn get_child_mut(
		&mut self,
		index: <Self::Radix as RadixConf>::KeyIndex,
	) -> Option<&mut N> {
		self.0.as_mut().and_then(|b| b[index as usize].as_mut())
			.map(AsMut::as_mut)
	}
}

impl<N: Debug + Clone> Children256<N> {
	fn need_reduce(
		&self,
	) -> bool {
		self.1 <= REM_TRESHOLD48
	}

	fn reduce_node(&mut self) -> Children48<N> {
		debug_assert!(self.1 <= 48);
		let mut result = Children48::empty();
		for i in 0..=255 {
			if let Some(child) = self.remove_child(i) {
				result.set_child(i, child);
			}
		}
		result
	}
}

const UNSET48: u8 = 49u8;

// we cannot really change this or at least I see no use
// in anticipating a node switch when growing
const ADD_TRESHOLD48: u8 = 48u8;
const ADD_TRESHOLD16: u8 = 16u8;
const ADD_TRESHOLD4: u8 = 4u8;

// using smaller that 48 to avoid add-remove-add-remove...
// situation
const REM_TRESHOLD48: u8 = 40u8;
const REM_TRESHOLD16: u8 = 16u8;
const REM_TRESHOLD4: u8 = 4u8;

use crate::radix::impls::Radix256Conf;

impl<N: Debug + Clone> Children48<N> {
	fn empty() -> Self {
		Children48(None, 0)
	}

	fn need_reduce(
		&self,
	) -> bool {
		self.1 <= REM_TRESHOLD16
	}

	fn reduce_node(&mut self) -> Children16<N> {
		debug_assert!(self.1 <= 16);
		let mut result = Children16::empty();
		if let Some((indexes, values)) = self.0.as_mut() {
			for i in 0..=255 {
				let index = indexes[i as usize];
				if index != UNSET48 {
					if let Some(value) = values[index as usize].take() {
						result.set_child(i, value);
					}
				}
			}
		}
		result
	}

	fn grow_node(&mut self) -> Children256<N> {
		if self.0.is_none() || self.1 == 0 {
			return Children256::empty();
		}
		let mut result = Children256::empty();
		if let Some((indexes, values)) = self.0.as_mut() {
			for i in 0..=255 {
				let ix = indexes[i];
				if ix != UNSET48 {
					let value = values[ix as usize].take()
						.expect("Not unset");
					result.set_child(i as u8, value);
				}
			}
		}
		result
	}

	fn can_set_child(
		&mut self,
		index: <Radix256Conf as RadixConf>::KeyIndex,
	) -> bool {
		if self.0.is_none() || self.1 < ADD_TRESHOLD48{
			return true;
		}
		let (indexes, _values) = self.0.as_ref()
			.expect("Lazy init above");
		let is_new = indexes[index as usize] == UNSET48;
		if is_new && self.1 >= ADD_TRESHOLD48 {
			return false;
		}
		true
	}

	fn set_child(
		&mut self,
		index: <Radix256Conf as RadixConf>::KeyIndex,
		child: Box<N>,
	) -> Option<Option<Box<N>>> {
		if self.0.is_none() {
			self.0 = Some(([UNSET48; 256], empty_48_children()));
		}
		let (indexes, values) = self.0.as_mut()
			.expect("Lazy init above");
		let is_new = indexes[index as usize] == UNSET48;
		if is_new && self.1 >= ADD_TRESHOLD48 {
			return None;
		}
		let result = if is_new {
			indexes[index as usize] = self.1;
			values[self.1 as usize] = Some(child);
			self.1 += 1;
			None
		} else {
			let ix = indexes[index as usize];
			replace(&mut values[ix as usize], Some(child))
		};
		Some(result)
	}

	fn remove_child(
		&mut self,
		index: <Radix256Conf as RadixConf>::KeyIndex,
	) -> Option<Box<N>> {
		if self.1 == 0 {
			return None;
		}
		if let Some((indexes, values)) = self.0.as_mut() {
			if indexes[index as usize] != UNSET48 {
				let old_index = indexes[index as usize];
				let result = replace(&mut values[old_index as usize], None);
				indexes[index as usize] = UNSET48;
				self.1 -= 1;
				if old_index != self.1 {
					// slow removal implementation (may do something here with u128 bit ops.
					let mut found = None;
					for (ix, value_ix) in indexes.iter().enumerate() {
						if *value_ix == self.1 {
							found = Some(ix);
							break;
						}
					}
					if let Some(ix) = found {
						let v = values[indexes[ix] as usize].take();
						values[old_index as usize] = v;
						indexes[ix] = old_index;
					}
				}
				result
			} else {
				None
			}
		} else {
			None
		}
	}

	fn number_child(
		&self,
	) -> usize {
		self.1 as usize
	}

	fn get_child(
		&self,
		index: <Radix256Conf as RadixConf>::KeyIndex,
	) -> Option<&N> {
		if self.1 == 0 {
			return None;
		}
		if let Some((indexes, values)) = self.0.as_ref() {
			let index = indexes[index as usize];
			if index == UNSET48 {
				return None;
			}
			values[index as usize].as_ref().map(AsRef::as_ref)
		} else {
			None
		}
	}

	fn get_child_mut(
		&mut self,
		index: <Radix256Conf as RadixConf>::KeyIndex,
	) -> Option<&mut N> {
		if self.1 == 0 {
			return None;
		}
		if let Some((indexes, values)) = self.0.as_mut() {
			let index = indexes[index as usize];
			if index == UNSET48 {
				return None;
			}
			values[index as usize].as_mut().map(AsMut::as_mut)
		} else {
			None
		}
	}
}

impl<N: Debug + Clone> Children16<N> {
	fn empty() -> Self {
		Children16(None, 0)
	}

	fn grow_node(&mut self) -> Children48<N> {
		if self.0.is_none() || self.1 == 0 {
			return Children48::empty();
		}
		let mut result = Children48::empty();
		if let Some((indexes, values)) = self.0.as_mut() {
			for i in 0..self.1 {
				let ix = indexes[i as usize];
				let value = values[i as usize].take()
					.expect("Restricted by size");
				result.set_child(ix, value);
			}
		}
		result
	}

	fn need_reduce(
		&self,
	) -> bool {
		self.1 <= REM_TRESHOLD4
	}

	fn reduce_node(&mut self) -> Children4<N> {
		debug_assert!(self.1 <= 4);
		let mut result = Children4::empty();
		if let Some((indexes, values)) = self.0.as_mut() {
			for i in 0..self.1 {
				let index = indexes[i as usize];
				if let Some(value) = values[i as usize].take() {
					result.set_child(index, value);
				}
			}
		}
		result
	}

	// Returns either the old value or the value to set after growth.
	fn set_child(
		&mut self,
		index: <Radix256Conf as RadixConf>::KeyIndex,
		child: Box<N>,
	) -> (Option<Option<Box<N>>>, Option<Box<N>>) {
		if self.0.is_none() {
			self.0 = Some(([0u8; 16], empty_16_children()));
		}
		let (indexes, values) = self.0.as_mut()
			.expect("Lazy init above");
		let mut existing_index = None;
		// TODO something to do with bit expr
		for i in 0..self.1 {
			if indexes[i as usize] == index {
				existing_index = Some(i);
			}
		}
		if existing_index.is_none() && self.1 >= ADD_TRESHOLD16 {
			return (None, Some(child));
		}
		let result = if let Some(i) = existing_index {
			indexes[i as usize] = index;
			replace(&mut values[i as usize], Some(child))
		} else {
			indexes[self.1 as usize] = index;
			values[self.1 as usize] = Some(child);
			self.1 += 1;
			None
		};
		(Some(result), None)
	}

	fn remove_child(
		&mut self,
		index: <Radix256Conf as RadixConf>::KeyIndex,
	) -> Option<Box<N>> {
		if self.1 == 0 {
			return None;
		}
		if let Some((indexes, values)) = self.0.as_mut() {
			let mut existing_index = None;
			// TODO something to do with bit expr
			for i in 0..self.1 {
				if indexes[i as usize] == index {
					existing_index = Some(i);
				}
			}
			if let Some(ix) = existing_index {
				self.1 -= 1;
				if ix == self.1 {
					replace(&mut values[ix as usize], None)
				} else {
					let result = replace(&mut values[ix as usize], None);
					values[ix as usize] = values[self.1 as usize].take();
					indexes[ix as usize] = indexes[self.1 as usize];
					result
				}
			} else {
				None
			}
		} else {
			None
		}
	}

	fn number_child(
		&self,
	) -> usize {
		self.1 as usize
	}

	fn get_child(
		&self,
		index: <Radix256Conf as RadixConf>::KeyIndex,
	) -> Option<&N> {
		if self.1 == 0 {
			return None;
		}
		if let Some((indexes, values)) = self.0.as_ref() {
			for i in 0..self.1 {
				if indexes[i as usize] == index {
					return values[i as usize].as_ref().map(AsRef::as_ref)
				}
			}
		}
		None
	}

	fn get_child_mut(
		&mut self,
		index: <Radix256Conf as RadixConf>::KeyIndex,
	) -> Option<&mut N> {
		if self.1 == 0 {
			return None;
		}
		if let Some((indexes, values)) = self.0.as_mut() {
			for i in 0..self.1 {
				if indexes[i as usize] == index {
					return values[i as usize].as_mut().map(AsMut::as_mut)
				}
			}
		}
		None
	}
}

impl<N: Debug + Clone> Children4<N> {
	fn empty() -> Self {
		Children4(None, 0)
	}

	fn grow_node(&mut self) -> Children16<N> {
		if self.0.is_none() || self.1 == 0 {
			return Children16::empty();
		}
		let mut result = Children16::empty();
		if let Some((indexes, values)) = self.0.as_mut() {
			for i in 0..self.1 {
				let ix = indexes[i as usize];
				let value = values[i as usize].take()
					.expect("Restricted by size");
				result.set_child(ix, value);
			}
		}
		result
	}

	// Returns either the old value or the value to set after growth.
	fn set_child(
		&mut self,
		index: <Radix256Conf as RadixConf>::KeyIndex,
		child: Box<N>,
	) -> (Option<Option<Box<N>>>, Option<Box<N>>) {
		if self.0.is_none() {
			self.0 = Some(([0u8; 4], empty_4_children()));
		}
		let (indexes, values) = self.0.as_mut()
			.expect("Lazy init above");
		let mut existing_index = None;
		// TODO something to do with bit expr
		for i in 0..self.1 {
			if indexes[i as usize] == index {
				existing_index = Some(i);
			}
		}
		if existing_index.is_none() && self.1 >= ADD_TRESHOLD4 {
			return (None, Some(child));
		}
		let result = if let Some(i) = existing_index {
			indexes[i as usize] = index;
			replace(&mut values[i as usize], Some(child))
		} else {
			indexes[self.1 as usize] = index;
			values[self.1 as usize] = Some(child);
			self.1 += 1;
			None
		};
		(Some(result), None)
	}

	fn remove_child(
		&mut self,
		index: <Radix256Conf as RadixConf>::KeyIndex,
	) -> Option<Box<N>> {
		if self.1 == 0 {
			return None;
		}
		if let Some((indexes, values)) = self.0.as_mut() {
			let mut existing_index = None;
			// TODO something to do with bit expr
			for i in 0..self.1 {
				if indexes[i as usize] == index {
					existing_index = Some(i);
				}
			}
			if let Some(ix) = existing_index {
				self.1 -= 1;
				if ix == self.1 {
					replace(&mut values[ix as usize], None)
				} else {
					let result = replace(&mut values[ix as usize], None);
					values[ix as usize] = values[self.1 as usize].take();
					indexes[ix as usize] = indexes[self.1 as usize];
					result
				}
			} else {
				None
			}
		} else {
			None
		}
	}

	fn number_child(
		&self,
	) -> usize {
		self.1 as usize
	}

	fn get_child(
		&self,
		index: <Radix256Conf as RadixConf>::KeyIndex,
	) -> Option<&N> {
		if self.1 == 0 {
			return None;
		}
		if let Some((indexes, values)) = self.0.as_ref() {
			for i in 0..self.1 {
				if indexes[i as usize] == index {
					return values[i as usize].as_ref().map(AsRef::as_ref)
				}
			}
		}
		None
	}

	fn get_child_mut(
		&mut self,
		index: <Radix256Conf as RadixConf>::KeyIndex,
	) -> Option<&mut N> {
		if self.1 == 0 {
			return None;
		}
		if let Some((indexes, values)) = self.0.as_mut() {
			for i in 0..self.1 {
				if indexes[i as usize] == index {
					return values[i as usize].as_mut().map(AsMut::as_mut)
				}
			}
		}
		None
	}
}

impl<N> ART48_256<N> {
	pub fn len(&self) -> u8 {
		match self {
			ART48_256::ART4(inner) => inner.1,
			ART48_256::ART16(inner) => inner.1,
			ART48_256::ART48(inner) => inner.1,
			ART48_256::ART256(inner) => inner.1,
		}
	}
}

impl<N: Debug + Clone> Children for ART48_256<N> {
	type Radix = Radix256Conf;
	type Node = N;

	fn empty() -> Self {
		ART48_256::ART4(Children4::empty())
	}

	fn set_child(
		&mut self,
		index: <Self::Radix as RadixConf>::KeyIndex,
		mut child: Box<N>,
	) -> Option<Box<N>> {
		let mut new_256 = match self {
			ART48_256::ART4(inner) => {
				match inner.set_child(index, child) {
					(Some(result), None) => return result,
					(None, Some(value)) => {
						child = value;
						ART48_256::ART16(inner.grow_node())
					},
					_ => unreachable!(),
				}
			},
			ART48_256::ART16(inner) => {
				match inner.set_child(index, child) {
					(Some(result), None) => return result,
					(None, Some(value)) => {
						child = value;
						ART48_256::ART48(inner.grow_node())
					},
					_ => unreachable!(),
				}
			},
			ART48_256::ART48(inner) => {
				if inner.can_set_child(index) {
					return inner.set_child(index, child)
						.expect("checked above");
				} else {
					ART48_256::ART256(inner.grow_node())
				}
			},
			ART48_256::ART256(inner) => {
				return inner.set_child(index, child);
			},
		};
		let result = new_256.set_child(index, child);
		*self = new_256;
		result
	}

	fn remove_child(
		&mut self,
		index: <Self::Radix as RadixConf>::KeyIndex,
	) -> Option<Box<N>> {
		let (result, do_reduce) = match self {
			ART48_256::ART256(inner) => {
				let result = inner.remove_child(index);
				if result.is_some() && inner.need_reduce() {
					(result, Some(ART48_256::ART48(inner.reduce_node())))
				} else {
					(result, None)
				}
			},
			ART48_256::ART48(inner) => {
				let result = inner.remove_child(index);
				if result.is_some() && inner.need_reduce() {
					(result, Some(ART48_256::ART16(inner.reduce_node())))
				} else {
					(result, None)
				}
			},
			ART48_256::ART16(inner) => {
				let result = inner.remove_child(index);
				if result.is_some() && inner.need_reduce() {
					(result, Some(ART48_256::ART4(inner.reduce_node())))
				} else {
					(result, None)
				}
			},
			ART48_256::ART4(inner) => {
				(inner.remove_child(index), None)
			},
		};
		if let Some(do_reduce) = do_reduce {
			*self = do_reduce;
		}
		result
	}

	fn number_child(
		&self,
	) -> usize {
		match self {
			ART48_256::ART256(inner) => inner.number_child(),
			ART48_256::ART48(inner) => inner.number_child(),
			ART48_256::ART16(inner) => inner.number_child(),
			ART48_256::ART4(inner) => inner.number_child(),
		}
	}

	fn get_child(
		&self,
		index: <Self::Radix as RadixConf>::KeyIndex,
	) -> Option<&N> {
		match self {
			ART48_256::ART256(inner) => inner.get_child(index),
			ART48_256::ART48(inner) => inner.get_child(index),
			ART48_256::ART16(inner) => inner.get_child(index),
			ART48_256::ART4(inner) => inner.get_child(index),
		}
	}

	fn get_child_mut(
		&mut self,
		index: <Self::Radix as RadixConf>::KeyIndex,
	) -> Option<&mut N> {
		match self {
			ART48_256::ART256(inner) => inner.get_child_mut(index),
			ART48_256::ART48(inner) => inner.get_child_mut(index),
			ART48_256::ART16(inner) => inner.get_child_mut(index),
			ART48_256::ART4(inner) => inner.get_child_mut(index),
		}
	}
}

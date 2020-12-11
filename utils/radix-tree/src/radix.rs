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

//! Radix related variants for keys and children.

use crate::{PrefixKey, NodeKeyBuff};
use core::fmt::Debug;
use core::cmp::Ordering;
use alloc::borrow::Borrow;
use derivative::Derivative;
use crate::children::{NodeIndex};

/// Masking operation for unaliged prefix key.
///
/// Note that no configuration of `MaskKeyByte` should result
/// in an empty byte. Instead of an empty byte we should use
/// the full byte configuration (`last`) at the previous index.
pub trait MaskKeyByte: Clone + Copy + PartialEq + Debug {
	/// Mask left part of a byte.
	fn mask(&self, byte: u8) -> u8;
	/// Mask right part of a byte.
	fn mask_end(&self, byte: u8) -> u8;
	/// Extract u8 index from this byte.
	fn index(&self, byte: u8) -> u8;
	/// Insert u8 index into this byte.
	fn set_index(&self, byte: u8, index: u8) -> u8;
//	fn mask_mask(&self, other: Self) -> Self;
	/// TODO use constant
	fn first() -> Self;
	/// TODO use constant
	fn last() -> Self;
	/// cmp
	fn cmp(&self, other: Self) -> Ordering;
}

/// Definition of prefix key.
pub trait PrefixKeyConf {
	/// Is key byte align using this definition.
	const ALIGNED: bool;
	/// Default mask value for aligned.
	const DEFAULT: Option<Self::Mask>;
	/// Either u8 or () depending on wether
	/// we use aligned key.
	type Mask: MaskKeyByte;
	/// Encode the byte mask, it needs to be ordered when encoded.
	fn encode_mask(mask: Self::Mask) -> u8;
	/// Decode the byte mask.
	fn decode_mask(mask: u8) -> Self::Mask;
}

mod prefix_key_confs_impls {
	use super::*;

	impl PrefixKeyConf for () {
		const ALIGNED: bool = true;
		const DEFAULT: Option<Self::Mask> = Some(());
		type Mask = ();
		fn encode_mask(_mask: Self::Mask) -> u8 {
			0
		}
		fn decode_mask(_mask: u8) -> Self::Mask {
			()
		}
	}

	impl PrefixKeyConf for bool {
		const ALIGNED: bool = false;
		const DEFAULT: Option<Self::Mask> = None;
		type Mask = bool;
		fn encode_mask(mask: Self::Mask) -> u8 {
			if mask {
				1
			} else {
				0
			}
		}
		fn decode_mask(mask: u8) -> Self::Mask {
			mask == 1
		}
	}

	impl PrefixKeyConf for u8 {
		const ALIGNED: bool = false;
		const DEFAULT: Option<Self::Mask> = None;
		type Mask = u8;
		fn encode_mask(mask: Self::Mask) -> u8 {
			mask
		}
		fn decode_mask(mask: u8) -> Self::Mask {
			mask
		}
	}

	impl MaskKeyByte for () {
		fn mask(&self, byte: u8) -> u8 {
			byte
		}
		fn mask_end(&self, byte: u8) -> u8 {
			byte
		}
	/*	fn mask_mask(&self, other: Self) -> Self {
			()
		}*/
		fn first() -> Self {
			()
		}
		fn last() -> Self {
			()
		}
		fn index(&self, byte: u8) -> u8 {
			byte
		}
		fn set_index(&self, _byte: u8, index: u8) -> u8 {
			index
		}
		fn cmp(&self, _other: Self) -> Ordering {
			Ordering::Equal
		}
	}

	impl MaskKeyByte for bool {
		fn mask(&self, byte: u8) -> u8 {
			if *self {
				byte & 0x0f
			} else {
				byte
			}
		}
		fn mask_end(&self, byte: u8) -> u8 {
			if *self {
				byte & 0xf0
			} else {
				byte
			}
		}

		fn index(&self, byte: u8) -> u8 {
			if *self {
				(byte & 0xf0) >> 4
			} else {
				byte & 0x0f
			}
		}
		fn set_index(&self, byte: u8, index: u8) -> u8 {
			if *self {
				(byte & 0x0f) | (index << 4)
			} else {
				(byte & 0xf0) | index
			}
		}
		fn first() -> Self {
			true
		}
		fn last() -> Self {
			false
		}
		fn cmp(&self, other: Self) -> Ordering {
			match (*self, other) {
				(true, false) => Ordering::Less,
				(false, true) => Ordering::Greater,
				(true, true)
					| (false, false) => Ordering::Equal,
			}
		}
	}

	impl MaskKeyByte for u8 {
		fn mask(&self, byte: u8) -> u8 {
			byte & (0b11111111 >> self)
		}
		fn mask_end(&self, byte: u8) -> u8 {
			byte & (0b11111111 << (7 - self) )
		}
		fn index(&self, byte: u8) -> u8 {
			(byte & (0b10000000 >> self)) >> (7 - self)
		}
		fn set_index(&self, byte: u8, index: u8) -> u8 {
			(byte & !(0b10000000 >> self)) | (index << (7 - self))
		}
	/*	fn mask_mask(&self, other: Self) -> Self {
			self & other
		}*/
		fn first() -> Self {
			0
		}
		fn last() -> Self {
			7
		}
		fn cmp(&self, other: Self) -> Ordering {
			<u8 as core::cmp::Ord>::cmp(self, &other)
		}
	}
}

/// Definition of the tree node structure.
pub trait RadixConf {
	/// Prefix alignement and mask.
	type Alignment: PrefixKeyConf;
	/// Index for a given `NodeChildren`.
	type KeyIndex: NodeIndex;
	/// Maximum number of children per item.
	/// Corresponding node depth (not counting partial key)
	/// in bits is therefore Log2(CHILDREN_CAPACITY).
	const CHILDREN_CAPACITY: usize;
	/// Advance one item in depth.
	/// Return next mask and number of incremented bytes.
	fn advance(previous_mask: MaskFor<Self>) -> (MaskFor<Self>, usize);
	/// Advance with multiple depth steps.
	fn advance_by(mut previous_mask: MaskFor<Self>, nb: usize) -> (MaskFor<Self>, usize) {
		let mut bytes = 0;
		for _i in 0..nb {
			let (new_mask, b) = Self::advance(previous_mask);
			previous_mask = new_mask;
			bytes += b;
		}
		(previous_mask, bytes)
	}
	/// Get child node index for a given position (depth) of a key.
	fn index(key: &[u8], at: Position<Self::Alignment>) -> Option<Self::KeyIndex>;
	/// Set index at a given position in a key.
	fn set_index(key: &mut NodeKeyBuff, at: Position<Self::Alignment>, index: Self::KeyIndex);
	/// Get mask from the delta of two byte, the delta is obtain by using xor, so 255
	/// if no common bytes and 0 if all common.
	/// This is mask for a start byte in the case of common prefix calculation.
	fn mask_from_delta(delta: u8) -> MaskFor<Self>;
}

pub(crate) type MaskFor<N> = <<N as RadixConf>::Alignment as PrefixKeyConf>::Mask;

/// Different tree radix confs implementations.
pub mod impls {
	use super::*;

	pub struct Radix256Conf;
	pub struct Radix2Conf;
	pub struct Radix16Conf;

	impl RadixConf for Radix16Conf {
		type Alignment = bool;
		type KeyIndex = u8;
		const CHILDREN_CAPACITY: usize = 16;
		fn advance(previous_mask: MaskFor<Self>) -> (MaskFor<Self>, usize) {
			if previous_mask {
				(false, 1)
			} else {
				(true, 0)
			}
		}
		fn advance_by(_previous_mask: MaskFor<Self>, _nb: usize) -> (MaskFor<Self>, usize) {
			unimplemented!("TODO or default one")
		}
		fn mask_from_delta(delta: u8) -> MaskFor<Self> {
			delta < 16
		}
		fn index(key: &[u8], at: Position<Self::Alignment>) -> Option<Self::KeyIndex> {
			key.get(at.index).map(|byte| {
				at.mask.index(*byte)
			})
		}
		fn set_index(key: &mut NodeKeyBuff, at: Position<Self::Alignment>, index: Self::KeyIndex) {
			if key.len() <= at.index {
				key.resize(at.index + 1, 0);
			}
			key.get_mut(at.index).map(|byte| {
				*byte = at.mask.set_index(*byte, index)
			});
		}
	}

	impl RadixConf for Radix256Conf {
		type Alignment = ();
		type KeyIndex = u8;
		const CHILDREN_CAPACITY: usize = 256;
		fn advance(_previous_mask: MaskFor<Self>) -> (MaskFor<Self>, usize) {
			((), 1)
		}
		fn advance_by(_previous_mask: MaskFor<Self>, nb: usize) -> (MaskFor<Self>, usize) {
			((), nb)
		}
		fn mask_from_delta(_delta: u8) -> MaskFor<Self> {
			()
		}
		fn index(key: &[u8], at: Position<Self::Alignment>) -> Option<Self::KeyIndex> {
			key.get(at.index).map(|byte| {
				at.mask.index(*byte)
			})
		}
		fn set_index(key: &mut NodeKeyBuff, at: Position<Self::Alignment>, index: Self::KeyIndex) {
			if key.len() <= at.index {
				key.resize(at.index + 1, 0);
			}
			key.get_mut(at.index).map(|byte| {
				*byte = at.mask.set_index(*byte, index) // TODO no need to call function here (aligned)
			});
		}
	}

	impl RadixConf for Radix2Conf {
		type Alignment = u8;
		type KeyIndex = bool;
		const CHILDREN_CAPACITY: usize = 2;
		fn advance(previous_mask: MaskFor<Self>) -> (MaskFor<Self>, usize) {
			if previous_mask < 255 {
				(previous_mask + 1, 0)
			} else {
				(0, 1)
			}
		}
		fn advance_by(_previous_mask: MaskFor<Self>, _nb: usize) -> (MaskFor<Self>, usize) {
			unimplemented!("TODO implement or default")
		}
		fn mask_from_delta(delta: u8) -> MaskFor<Self> {
			255 >> (delta.leading_zeros())
		}
		fn index(key: &[u8], at: Position<Self::Alignment>) -> Option<Self::KeyIndex> {
			key.get(at.index).map(|byte| {
				at.mask.index(*byte) > 0
			})
		}
		fn set_index(key: &mut NodeKeyBuff, at: Position<Self::Alignment>, index: Self::KeyIndex) {
			if key.len() <= at.index {
				key.resize(at.index + 1, 0);
			}
			key.get_mut(at.index).map(|byte| {
				*byte = at.mask.set_index(*byte, if index {
					0
				} else {
					1
				})
			});
		}
	}
}


impl<D1, D2, P> PartialEq<PrefixKey<D2, P>> for PrefixKey<D1, P>
	where
		D1: Borrow<[u8]>,
		D2: Borrow<[u8]>,
		P: PrefixKeyConf,
{
	fn eq(&self, other: &PrefixKey<D2, P>) -> bool {
		// !! this means either 255 or 0 mask
		// is forbidden!!
		// 0 should be forbidden, 255 when full byte
		// eg 1 byte slice is 255 and empty is always
		// same as a -1 byte so 255 mask
		let left = self.data.borrow();
		let right = other.data.borrow();
		left.len() == right.len()
			&& self.start == other.start
			&& self.end == other.end
			&& (left.len() == 0
				|| left.len() == 1 && self.unchecked_single_byte() == other.unchecked_single_byte()
				|| (self.unchecked_first_byte() == other.unchecked_first_byte()
					&& self.unchecked_last_byte() == other.unchecked_last_byte()
					&& left[1..left.len() - 1]
						== right[1..right.len() - 1]
			))
	}
}

impl<D, P> Eq for PrefixKey<D, P>
	where
		D: Borrow<[u8]>,
		P: PrefixKeyConf,
{ }

/// Position in a key.
#[derive(Derivative)]
#[derivative(Clone)]
#[derivative(Copy)]
#[derivative(PartialEq)]
pub struct Position<P>
	where
		P: PrefixKeyConf,
{
	pub(crate) index: usize,
	pub(crate) mask: P::Mask,
}

impl<P> Position<P>
	where
		P: PrefixKeyConf,
{
	pub(crate) fn zero() -> Self {
		Position {
			index: 0,
			mask: P::Mask::first(),
		}
	}
	pub(crate) fn next<R: RadixConf<Alignment = P>>(&self) -> Self {
		let (mask, increment) = R::advance(self.mask);
		Position {
			index: self.index + increment,
			mask,
		}
	}
	pub(crate) fn next_by<R: RadixConf<Alignment = P>>(&self, nb: usize) -> Self {
		let (mask, increment) = R::advance_by(self.mask, nb);
		Position {
			index: self.index + increment,
			mask,
		}
	}
	pub(crate) fn index<R: RadixConf<Alignment = P>>(&self, key: &[u8]) -> Option<R::KeyIndex> {
		R::index(key, *self)
	}
	pub(crate) fn set_index<R: RadixConf<Alignment = P>>(&self, key: &mut NodeKeyBuff, index: R::KeyIndex) {
		R::set_index(key, *self, index)
	}

	// TODO could derive Ord
	pub(crate) fn cmp(&self, other: Position<P>) -> Ordering {
		match self.index.cmp(&other.index) {
			Ordering::Equal => {
				self.mask.cmp(other.mask)
			},
			r => r,
		}
	}
}

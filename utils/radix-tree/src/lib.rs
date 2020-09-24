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

#![cfg_attr(not(feature = "std"), no_std)]

// rawvec api handling alloc is quite nice -> TODO manage alloc the same way,
// for now just using vec with usize as ptr
//#![feature(allow_internal_unstable)] 

//! Ordered tree with prefix iterator.
//!
//! Allows iteration over a key prefix.
//! No concern about deletion performance.

// mask cannot be 0 !!! TODO move this in key impl documentation
extern crate alloc;

//use alloc::raw_vec::RawVec;
use derivative::Derivative;
use alloc::vec::Vec;
use alloc::boxed::Box;
use alloc::borrow::Borrow;
use core::cmp::{min, Ordering};
use core::fmt::Debug;
use core::mem::replace;

/*#[cfg(not(feature = "std"))]
extern crate alloc; // TODO check if needed in 2018 and if needed at all

#[cfg(feature = "std")]
mod core_ {
	use alloc::raw_vec::RawVec
}

#[cfg(not(feature = "std"))]
mod core_ {
	pub use core::{borrow, convert, cmp, iter, fmt, hash, marker, mem, ops, result};
	pub use core::iter::Empty as EmptyIter;
	pub use alloc::{boxed, rc, vec};
	pub use alloc::collections::VecDeque;
	pub trait Error {}
	impl<T> Error for T {}
}

#[cfg(feature = "std")]
use self::rstd::{fmt, Error};

use hash_db::MaybeDebug;
use self::rstd::{boxed::Box, vec::Vec};
*/

// TODO consider removal
#[derive(Derivative)]
#[derivative(Clone)]
#[derivative(Debug)]
struct PrefixKey<D, P>
	where
		P: PrefixKeyConf,
//		D: Borrow<[u8]>,
{
	// ([u8; size], next_slice)
	start: P::Mask, // mask of first byte
	end: P::Mask, // mask of last byte
	data: D,
}

/// Definition of prefix handle.
pub trait PrefixKeyConf {
	/// Is key byte align using this definition.
	const ALIGNED: bool;
	/// Either u8 or () depending on wether
	/// we use aligned key.
	type Mask: MaskKeyByte;
}

impl PrefixKeyConf for () {
	const ALIGNED: bool = true;
	type Mask = ();
}

impl PrefixKeyConf for bool {
	const ALIGNED: bool = false;
	type Mask = bool;
}

impl PrefixKeyConf for u8 {
	const ALIGNED: bool = false;
	type Mask = u8;
}

type MaskFor<N> = <<N as RadixConf>::Alignment as PrefixKeyConf>::Mask;

/// Definition of node handle.
pub trait RadixConf {
	/// Prefix alignement and mask.
	type Alignment: PrefixKeyConf;
	/// Index for a given `NodeChildren`.
	type KeyIndex: NodeIndex;
	/// Maximum number of children per item.
	const CHILDREN_CAPACITY: usize;
	/// DEPTH in byte when aligned or in bit (2^DEPTH == NUMBER_CHILDREN).
	/// TODO is that of any use?
	const DEPTH: usize;
	/// Advance one item in depth.
	/// Return next mask and number of incremented bytes.
	fn advance(previous_mask: MaskFor<Self>) -> (MaskFor<Self>, usize);
	/// Advance with multiple steps.
	fn advance_by(mut previous_mask: MaskFor<Self>, nb: usize) -> (MaskFor<Self>, usize) {
		let mut bytes = 0;
		for _i in 0..nb {
			let (new_mask, b) = Self::advance(previous_mask);
			previous_mask = new_mask;
			bytes += b;
		}
		(previous_mask, bytes)
	}
	/// Get index at a given position.
	fn index(key: &[u8], at: Position<Self::Alignment>) -> Option<Self::KeyIndex>;
	/// Set index at a given position.
	fn set_index(key: &mut Vec<u8>, at: Position<Self::Alignment>, index: Self::KeyIndex);
	/// (get a mask corresponding to a end position).
	// let mask = !(255u8 >> delta.leading_zeros()); + TODO round to nibble
	fn mask_from_delta(delta: u8) -> MaskFor<Self>;
}

type PositionFor<N> = Position<<<N as Node>::Radix as RadixConf>::Alignment>;
type KeyIndexFor<N> = <<N as Node>::Radix as RadixConf>::KeyIndex;

pub trait Node: Clone + PartialEq + Debug {
	type Radix: RadixConf;
	type InitFrom: Clone;

	fn new(
		key: &[u8],
		start_position: PositionFor<Self>,
		end_position: PositionFor<Self>,
		value: Option<Vec<u8>>,
		init: Self::InitFrom,
	) -> Self;
	fn descend(
		&self,
		key: &[u8],
		node_position: PositionFor<Self>,
		// exclusive
		dest_position: PositionFor<Self>,
	) -> Descent<Self::Radix>;
	fn depth(
		&self,
	) -> usize;
	fn value(
		&self,
	) -> Option<&[u8]>; // TODO parameterized with V
	fn value_mut(
		&mut self,
	) -> Option<&mut Vec<u8>>; // TODO parameterized with V
	fn set_value(
		&mut self,
		value: Vec<u8>,
	) -> Option<Vec<u8>>; // TODO parameterized with V
	fn remove_value(
		&mut self,
	) -> Option<Vec<u8>>; // TODO parameterized with V
	fn number_child(
		&self,
	) -> usize;
	fn get_child(
		&self,
		index: KeyIndexFor<Self>,
	) -> Option<&Self>;
	fn set_child(
		&mut self,
		index: KeyIndexFor<Self>,
		child: Self,
	) -> Option<Self>;
	fn remove_child(
		&mut self,
		index: KeyIndexFor<Self>,
	) -> Option<Self>;
	fn fuse_child(
		&mut self,
		key: &[u8],
	);
	fn split_off(
		&mut self,
		position: PositionFor<Self>,
		at: PositionFor<Self>,
	);
	fn change_start(
		&mut self,
		key: &[u8],
		new_start: PositionFor<Self>,
	);
	fn get_child_mut(
		&mut self,
		index: KeyIndexFor<Self>,
	) -> Option<&mut Self>;
	/// utility to stack the prefix of the node.
	/// It truncate end of stack or can extend with 0.
	fn new_end(&self, stack: &mut Vec<u8>, node_position: PositionFor<Self>);
}

pub struct Radix256Conf;
pub struct Radix2Conf;
pub struct Radix16Conf;

impl RadixConf for Radix16Conf {
	type Alignment = bool;
	type KeyIndex = u8;
	const CHILDREN_CAPACITY: usize = 16;
	const DEPTH: usize = 4;
	fn advance(previous_mask: MaskFor<Self>) -> (MaskFor<Self>, usize) {
		if previous_mask {
			(false, 1)
		} else {
			(true, 0)
		}
	}
	fn advance_by(_previous_mask: MaskFor<Self>, nb: usize) -> (MaskFor<Self>, usize) {
		unimplemented!()
	}
	fn mask_from_delta(_delta: u8) -> MaskFor<Self> {
		unimplemented!()
	}
	fn index(key: &[u8], at: Position<Self::Alignment>) -> Option<Self::KeyIndex> {
		key.get(at.index).map(|byte| {
			at.mask.index(*byte)
		})
	}
	fn set_index(key: &mut Vec<u8>, at: Position<Self::Alignment>, index: Self::KeyIndex) {
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
	const DEPTH: usize = 1;
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
	fn set_index(key: &mut Vec<u8>, at: Position<Self::Alignment>, index: Self::KeyIndex) {
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
	const DEPTH: usize = 1;
	fn advance(previous_mask: MaskFor<Self>) -> (MaskFor<Self>, usize) {
		if previous_mask < 255 {
			(previous_mask + 1, 0)
		} else {
			(0, 1)
		}
	}
	fn advance_by(_previous_mask: MaskFor<Self>, nb: usize) -> (MaskFor<Self>, usize) {
		unimplemented!()
	}
	fn mask_from_delta(_delta: u8) -> MaskFor<Self> {
		unimplemented!()
	}
	fn index(key: &[u8], at: Position<Self::Alignment>) -> Option<Self::KeyIndex> {
		key.get(at.index).map(|byte| {
			at.mask.index(*byte) > 0
		})
	}
	fn set_index(key: &mut Vec<u8>, at: Position<Self::Alignment>, index: Self::KeyIndex) {
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

/// Mask a byte for unaligned prefix key.
/// Note that no configuration of `MaskKeyByte` should result
/// in an empty byte. Instead of an empty byte we should use
/// the full byte configuration (`last`) at the previous index.
/// TODO consider merging with RadixConf.
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
	fn set_index(&self, byte: u8, index: u8) -> u8 {
		index
	}
	fn cmp(&self, other: Self) -> Ordering {
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

#[derive(Derivative)]
#[derivative(Clone)]
#[derivative(Copy)]
#[derivative(PartialEq)]
pub struct Position<P>
	where
		P: PrefixKeyConf,
{
	index: usize,
	mask: P::Mask,
}

impl<P> Position<P>
	where
		P: PrefixKeyConf,
{
	fn zero() -> Self {
		Position {
			index: 0,
			mask: P::Mask::first(),
		}
	}
	fn next<R: RadixConf<Alignment = P>>(&self) -> Self {
		let (mask, increment) = R::advance(self.mask);
		Position {
			index: self.index + increment,
			mask,
		}
	}
	fn next_by<R: RadixConf<Alignment = P>>(&self, nb: usize) -> Self {
		let (mask, increment) = R::advance_by(self.mask, nb);
		Position {
			index: self.index + increment,
			mask,
		}
	}
	fn index<R: RadixConf<Alignment = P>>(&self, key: &[u8]) -> Option<R::KeyIndex> {
		R::index(key, *self)
	}
	fn set_index<R: RadixConf<Alignment = P>>(&self, key: &mut Vec<u8>, index: R::KeyIndex) {
		R::set_index(key, *self, index)
	}

	// TODO could derive
	fn cmp(&self, other: Position<P>) -> Ordering {
		match self.index.cmp(&other.index) {
			Ordering::Equal => {
				self.mask.cmp(other.mask)
			},
			r => r,
		}
	}
}

impl<D, P> PrefixKey<D, P>
	where
		D: Borrow<[u8]> + Default,
		P: PrefixKeyConf,
{
	fn empty() -> Self {
		PrefixKey {
			start: P::Mask::first(),
			end: P::Mask::first(),
			data: Default::default(),
		}
	}
}

impl<D, P> PrefixKey<D, P>
	where
		D: Borrow<[u8]>,
		P: PrefixKeyConf,
{

	fn unchecked_first_byte(&self) -> u8 {
		self.start.mask(self.data.borrow()[0])
	}
	fn unchecked_last_byte(&self) -> u8 {
		self.end.mask_end(self.data.borrow()[self.data.borrow().len() - 1])
	}
	fn unchecked_single_byte(&self) -> u8 {
		self.start.mask(self.end.mask_end(self.data.borrow()[0]))
	}

/*	fn pos_start(&self) -> Position<P> {
		Position {
			index: 0,
			mask: self.start,
		}
	}

	fn pos_end(&self) -> Position {
		Position {
			index: self.data.borrow().len(),
			mask: self.end,
		}
	}
*/

	fn index<R: RadixConf<Alignment = P>>(&self, position: Position<P>) -> R::KeyIndex {
		position.index::<R>(self.data.borrow())
			.expect("TODO consider safe api here")
	}
	fn depth(&self) -> usize {
		if P::ALIGNED {
			self.data.borrow().len()
		} else {
			let mut len = self.data.borrow().len() * 8;
			// TODO consider a const value for getting bit mask.
			len -= self.start.mask(255).leading_zeros() as usize;
			len -= self.end.mask_end(255).trailing_zeros() as usize;
			len
		}
	}
}
impl<P> PrefixKey<Vec<u8>, P>
	where
		P: PrefixKeyConf,
{
	// TODO consider returning the skipped byte aka key index (avoid fetching it before split_off)
	fn split_off<R: RadixConf<Alignment = P>>(&mut self, position: Position<P>) -> Self {
		let split_end = self.end;
		let mut split = if position.mask == MaskFor::<R>::first() {
			let split = self.data.split_off(position.index);
			self.end = position.mask;
			split
		} else {
			let split = self.data.split_off(position.index + 1);
			self.end = position.mask;
			split
		};
		let (split_start, increment) = R::advance(position.mask);
		if increment > 0 {
			split = split.split_off(increment);
		}
		PrefixKey {
			data: split,
			start: split_start,
			end: split_end,
		}
	}
}


// TODO remove that??
// Return first differing position. (TODO rename?)
fn common_depth<D1, D2, N>(one: &PrefixKey<D1, N::Alignment>, other: &PrefixKey<D2, N::Alignment>) -> Position<N::Alignment>
	where
		D1: Borrow<[u8]>,
		D2: Borrow<[u8]>,
		N: RadixConf,
{
		if N::Alignment::ALIGNED {
			let mut index = 0;
			let left = one.data.borrow();
			let right = other.data.borrow();
			let upper_bound = min(left.len(), right.len());
			for index in 0..upper_bound {
				if left[index] != right[index] {
					return Position {
						index,
						mask: MaskFor::<N>::first(),
					}
				}
			}
			return Position {
				index: upper_bound,
				mask: MaskFor::<N>::first(),
			}
		}
		if one.start != other.start {
			return Position::zero();
		}
		let left = one.data.borrow();
		let right = other.data.borrow();
		if left.len() == 0 || right.len() == 0 {
			return Position::zero();
		}
		let mut index = 0;
		let mut delta = one.unchecked_first_byte() ^ other.unchecked_first_byte();
		if delta == 0 {
			let upper_bound = min(left.len(), right.len());
			for i in 1..(upper_bound - 1) {
				if left[i] != right[i] {
					index = i;
					break;
				}
			}
			if index == 0 {
				index = upper_bound - 1;
					/*
				delta = if left.len() == upper_bound {
					one.unchecked_last_byte() ^ right[index]
						& !one.end.mask(255)
				} else {
					left[index] ^ other.unchecked_last_byte()
						& !other.end.mask(255)
				};
					i*/
					unimplemented!("TODO do with a mask_end function.");
			} else {
				delta = left[index] ^ right[index];
			}
		}
		if delta == 0 {
			Position {
				index: index,
				mask: MaskFor::<N>::last(),
			}
		} else {
			//let mask = 255u8 >> delta.leading_zeros();
			let mask = N::mask_from_delta(delta);
/*			let mask = if index == 0 {
				self.start.mask_mask(mask)
			} else {
				mask
			};*/
			Position {
				index,
				mask,
			}
		}
	}


//	fn common_depth_next(&self, other: &Self) -> Descent<P> {
/*		// key must be aligned.
		assert!(self.start == other.start);
		let left = self.data.borrow();
		let right = other.data.borrow();
		assert!(self.start == other.start);
		if left.len() == 0 {
			if right.len() == 0 {
				return Descent::Match(Position::zero());
			} else {
				return Descent::Middle(Position::zero(), other.index(Position::zero()));
			}
		} else if right.len() == 0 {
			return Descent::Child(Position::zero(), self.index(Position::zero()));
		}
		let mut index = 0;
		let mut delta = self.unchecked_first_byte() ^ other.unchecked_last_byte();
		if delta == 0 {
			let upper_bound = min(left.len(), right.len());
			for i in 1..(upper_bound - 1) {
				if left[i] != right[i] {
					index = i;
					break;
				}
			}
			if index == 0 {
				index = upper_bound - 1;
				delta = if left.len() == upper_bound {
					self.unchecked_last_byte() ^ right[index]
				} else {
					left[index] ^ other.unchecked_last_byte()
				};
			} else {
				delta = left[index] ^ right[index];
			}
		}
		if delta == 0 {
			Position {
				index: index + 1,
				mask: 0,
			}
		} else {
			let mask = 255u8 >> delta.leading_zeros();
			Position {
				index,
				mask,
			}
		}*/
//	}
/*
	// TODO remove that??
	fn index(&self, ix: Position<P>) -> P::KeyIndex {
		let mask = 128u8 >> ix.mask.leading_zeros();
		if (self.data.borrow()[ix.index] & mask) == 0 {
			KeyIndex {
				right: false,
			}
		} else {
			KeyIndex {
				right: true,
			}
		}
	}
*/

impl<P> PrefixKey<Vec<u8>, P>
	where
		P: PrefixKeyConf,
{
	/// start is inclusive, end is exclusive, this function cannot build an empty `PrefixKey`
	/// `empty` should be use.
	fn new_offset<Q: Borrow<[u8]>>(key: Q, start: Position<P>, end: Position<P>) -> Self {
		let data = if end.mask == P::Mask::first() {
			key.borrow()[start.index..end.index].to_vec()
		} else {
			key.borrow()[start.index..end.index + 1].to_vec()
		};

/*		if data.len() > 0 {
			data[0] &= start.mask; // this update is for Eq implementation
		}*/
		PrefixKey {
			start: start.mask,
			end: end.mask,
			data,
		}
	}
}
impl<'a, P> PrefixKey<&'a [u8], P>
	where
		P: PrefixKeyConf,
{
	/// start is inclusive, end is exclusive.
	fn new_offset_ref(key: &'a [u8], start: Position<P>, end: Position<P>) -> Self {
		let data = if end.mask == P::Mask::first() {
			&key[start.index..end.index]
		} else {
			&key[start.index..end.index + 1]
		};
		PrefixKey {
			start: start.mask,
			end: end.mask,
			data,
		}
	}
}


#[derive(Derivative)]
#[derivative(Clone)]
#[derivative(Debug)]
#[derivative(PartialEq)]
struct NodeOld<P, C>
	where
		P: RadixConf,
//		C: Children<Self, Radix = P>,
{
	// TODO this should be able to use &'a[u8] for iteration
	// and querying.
	pub key: PrefixKey<Vec<u8>, P::Alignment>,
	//pub value: usize,
	pub value: Option<Vec<u8>>,
	//pub left: usize,
	//pub right: usize,
	// TODO if backend behind, then Self would neeed to implement a Node trait with lazy loading...
	pub children: C,
}
/*
impl<P, C> NodeOld<P, C>
	where
		P: RadixConf,
		C: Children<Self, Radix = P>,
{
	fn leaf(key: &[u8], start: Position<P::Alignment>, value: Vec<u8>) -> Self {
		NodeOld {
			key: PrefixKey::new_offset(key, start),
			value: Some(value),
			children: C::empty(),
		}
	}
}
*/

impl<P, C> Node for NodeOld<P, C>
	where
		P: RadixConf,
		C: Children<Self, Radix = P>,
{
	type Radix = P;
	type InitFrom = ();
	fn new(
		key: &[u8],
		start_position: PositionFor<Self>,
		end_position: PositionFor<Self>,
		value: Option<Vec<u8>>,
		_init: Self::InitFrom,
	) -> Self {
		NodeOld {
			key: PrefixKey::new_offset(key, start_position, end_position),
			value,
			children: C::empty(),
		}
	}
	fn descend(
		&self,
		key: &[u8],
		node_position: PositionFor<Self>,
		dest_position: PositionFor<Self>,
	) -> Descent<Self::Radix> {
		let ref_prefix = PrefixKey::<_, P::Alignment>::new_offset_ref(key, node_position, dest_position);
		let mut common = common_depth::<_, _, Self::Radix>(&self.key, &ref_prefix);
		let dest_position_next = dest_position;
		common.index += node_position.index;
		match common.cmp(dest_position_next) {
			Ordering::Equal => Descent::Match(common),
			Ordering::Greater => {
				let ix = common.index::<Self::Radix>(key)
					.expect("child");
				Descent::Child(common, ix)
			},
			Ordering::Less => {
				// TODO consider storing or direct function for next by child depth
				// to access value index.
				let node_end_index = node_position.next_by::<Self::Radix>(self.depth());
				if common == node_end_index {
					let ix = common.index::<Self::Radix>(key)
						.expect("child");
					Descent::Child(common, ix)
				} else if common == dest_position_next {
					Descent::Middle(common, None)
				} else {
					let ix = common.index::<Self::Radix>(key);
					Descent::Middle(common, ix)
				}
			},
		}
	}
	fn depth(
		&self,
	) -> usize {
		self.key.depth()
	}
	fn value(
		&self,
	) -> Option<&[u8]> {
		self.value.as_ref().map(|v| v.as_slice())
	}
	fn value_mut(
		&mut self,
	) -> Option<&mut Vec<u8>> {
		self.value.as_mut()
	}
	fn set_value(
		&mut self,
		value: Vec<u8>,
	) -> Option<Vec<u8>> {
		replace(&mut self.value, Some(value))
	}
	fn remove_value(
		&mut self,
	) -> Option<Vec<u8>> {
		replace(&mut self.value, None)
	}
	fn number_child(
		&self,
	) -> usize {
		self.children.number_child()
	}
	fn get_child(
		&self,
		index: KeyIndexFor<Self>,
	) -> Option<&Self> {
		self.children.get_child(index)
	}
	fn get_child_mut(
		&mut self,
		index: KeyIndexFor<Self>,
	) -> Option<&mut Self> {
		self.children.get_child_mut(index)
	}
	fn set_child(
		&mut self,
		index: KeyIndexFor<Self>,
		child: Self,
	) -> Option<Self> {
		self.children.set_child(index, child)
	}
	fn remove_child(
		&mut self,
		index: KeyIndexFor<Self>,
	) -> Option<Self> {
		self.children.remove_child(index)
	}
	fn split_off(
		&mut self,
		position: PositionFor<Self>,
		mut at: PositionFor<Self>,
	) {
		at.index -= position.index;
		let index = self.key.index::<P>(at);
		let child_prefix = self.key.split_off::<P>(at);
		let child_value = self.value.take();
		let child_children = replace(&mut self.children, C::empty());
		let child = NodeOld {
			key: child_prefix,
			value: child_value,
			children: child_children,
		};
		self.set_child(index, child);
	}
	fn fuse_child(
		&mut self,
		key: &[u8],
	) {
		if let Some(index) = self.children.first() {
			if let Some(mut child) = self.children.remove_child(index) {
				let position = PositionFor::<Self> {
					index: 0,
					mask: self.key.start,
				};
				let position_start = position.next_by::<P>(self.depth());
				position_start.set_index::<P>(&mut self.key.data, index);
				let position_cat = position.next::<P>();
				child.new_end(&mut self.key.data, position_cat);
				self.key.end = child.key.end;
				self.value = child.value;
				self.children = child.children;
			} else {
				unreachable!("fuse condition checked");
			}
		} else {
			unreachable!("fuse condition checked");
		}
	}
	fn change_start(
		&mut self,
		key: &[u8],
		new_start: PositionFor<Self>,
	) {
		unimplemented!()
	}

	// TODO make it a trait function?
	fn new_end(&self, stack: &mut Vec<u8>, node_position: PositionFor<Self>) {
		let depth = self.depth();
		if depth == 0 {
			return;
		}
		if P::Alignment::ALIGNED {
			let new_len = node_position.index + depth;
			stack.resize(new_len, 0);
			&mut stack[node_position.index..new_len].copy_from_slice(self.key.data.borrow());
		} else {
			let node_position_end = node_position.next_by::<P>(depth);

			let (start, end) = if node_position.index == node_position_end.index {
				let start = stack[node_position.index] & !self.key.start.mask(255) & self.key.end.mask(255)
					& self.key.unchecked_single_byte();
				(start, start)
			} else {
				let start = stack[node_position.index] & !self.key.start.mask(255) & self.key.unchecked_first_byte();
				let end = stack[node_position_end.index] & self.key.end.mask(255) & self.key.unchecked_last_byte();
				(start, end)
			};
			&mut stack[node_position.index..node_position_end.index].copy_from_slice(self.key.data.borrow());
			stack[node_position.index] = start;
			stack[node_position_end.index] = end;
		}
	}
}

#[derive(Derivative)]
#[derivative(Clone(bound=""))]
#[derivative(Debug(bound=""))]
#[derivative(PartialEq(bound=""))]
pub struct Tree<N>
	where
		N: Node,
{
	//tree: Vec<Node>,
	tree: Option<N>,
	//values: Vec<Vec<u8>>,
	//keys: Vec<u8>,
	#[derivative(Debug="ignore")]
	#[derivative(PartialEq="ignore")]
	init: N::InitFrom,
}

impl<N> Tree<N>
	where
		N: Node,
{
	pub fn new(init: N::InitFrom) -> Self {
		Tree {
			tree: None,
			init,
		}
	}
}

pub trait Children<N>: Clone + Debug + PartialEq {
	type Radix: RadixConf;

	fn empty() -> Self;
	fn set_child(
		&mut self,
		index: <Self::Radix as RadixConf>::KeyIndex,
		child: N,
	) -> Option<N>;
	fn remove_child(
		&mut self,
		index: <Self::Radix as RadixConf>::KeyIndex,
	) -> Option<N>;
	fn number_child(
		&self,
	) -> usize;
	fn get_child(
		&self,
		index: <Self::Radix as RadixConf>::KeyIndex,
	) -> Option<&N>;
	fn get_child_mut(
		&mut self,
		index: <Self::Radix as RadixConf>::KeyIndex,
	) -> Option<&mut N>;
	fn first(
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

pub trait NodeIndex: Clone + Copy + Debug + PartialEq {
	fn zero() -> Self;
	fn next(&self) -> Option<Self>;
}

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


#[derive(Derivative)]
#[derivative(Clone)]
#[derivative(Debug)]
#[derivative(PartialEq)]
struct Children2<N> (
	Option<Box<(Option<N>, Option<N>)>>
);

impl<N: Node> Children<N> for Children2<N> {
	type Radix = Radix2Conf;

	fn empty() -> Self {
		Children2(None)
	}
	fn set_child(
		&mut self,
		index: <Self::Radix as RadixConf>::KeyIndex,
		child: N,
	) -> Option<N> {
		if self.0.is_none() {
			self.0 = Some(Box::new((None, None)));
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
	) -> Option<N> {
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
			Some(b) => match b.as_ref() {
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
			b.0.as_ref()
		} else {
			b.1.as_ref()
		})
	}
	fn get_child_mut(
		&mut self,
		index: <Self::Radix as RadixConf>::KeyIndex,
	) -> Option<&mut N> {
		self.0.as_mut().and_then(|b| if index {
			b.0.as_mut()
		} else {
			b.1.as_mut()
		})
	}
}

#[derive(Derivative)]
#[derivative(Clone)]
struct Children256<N> (
	// 256 array is to big but ok for initial implementation
	Option<Box<[Option<N>; 256]>>,
	usize,
);

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

impl<N: PartialEq> PartialEq for Children256<N> {
	fn eq(&self, other: &Self) -> bool {
		match (self.0.as_ref(), other.0.as_ref()) {
			(Some(self_children), Some(other_children)) =>  {
				for i in 0..256 {
					if self_children[i] != other_children[i] {
						return false;
					}
				}
				true
			},
			(None, None) => true,
			_ => false,
		}
	}
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

impl<N: Node> Children<N> for Children256<N> {
	type Radix = Radix256Conf;

	fn empty() -> Self {
		Children256(None, 0)
	}
	fn set_child(
		&mut self,
		index: <Self::Radix as RadixConf>::KeyIndex,
		child: N,
	) -> Option<N> {
		if self.0.is_none() {
			self.0 = Some(Box::new(empty_256_children()));
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
	) -> Option<N> {
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
		self.1
	}
	fn get_child(
		&self,
		index: <Self::Radix as RadixConf>::KeyIndex,
	) -> Option<&N> {
		self.0.as_ref().and_then(|b| b[index as usize].as_ref())
	}
	fn get_child_mut(
		&mut self,
		index: <Self::Radix as RadixConf>::KeyIndex,
	) -> Option<&mut N> {
		self.0.as_mut().and_then(|b| b[index as usize].as_mut())
	}
}

/// Flatten type for children of a given node type.
/// `inner_node_type` is expected to be parametered by a `Children` type
/// and a `RadixConf` type.
macro_rules! flatten_children {
	($type_alias: ident, $inner_children_type: ident, $inner_node_type: ident, $inner_type: ident, $inner_radix: ident) => {
		type $inner_children_type = $inner_node_type<$inner_radix, $type_alias>;
		#[derive(Derivative)]
		#[derivative(Clone)]
		#[derivative(PartialEq)]
		#[derivative(Debug)]
		struct $type_alias($inner_type<$inner_children_type>);

		impl Children<$inner_children_type> for $type_alias {
			type Radix = $inner_radix;

			fn empty() -> Self {
				$type_alias($inner_type::empty())
			}
			fn set_child(
				&mut self,
				index: <Self::Radix as RadixConf>::KeyIndex,
				child: $inner_children_type,
			) -> Option<$inner_children_type> {
				self.0.set_child(index, child)
			}
			fn remove_child(
				&mut self,
				index: <Self::Radix as RadixConf>::KeyIndex,
			) -> Option<$inner_children_type> {
				self.0.remove_child(index)
			}
			fn number_child(
				&self,
			) -> usize {
				self.0.number_child()
			}
			fn get_child(
				&self,
				index: <Self::Radix as RadixConf>::KeyIndex,
			) -> Option<&$inner_children_type> {
				self.0.get_child(index)
			}
			fn get_child_mut(
				&mut self,
				index: <Self::Radix as RadixConf>::KeyIndex,
			) -> Option<&mut $inner_children_type> {
				self.0.get_child_mut(index)
			}
		}
	}
}
flatten_children!(Children256Flatten, Node256Flatten, NodeOld, Children256, Radix256Conf);

#[derive(Derivative)]
#[derivative(Clone)]
#[derivative(Copy)]
pub enum Descent<P>
	where
		P: RadixConf,
{
	// index in input key
	/// Position is child is at position + 1 of the branch.
	/// Index is index for the child at position.
	Child(Position<P::Alignment>, P::KeyIndex),
	/// Position is the position of the child of the middle branch.
	/// Index is the index where existing child will be inserted.
	/// (if None, then the key is on the existing node).
	Middle(Position<P::Alignment>, Option<P::KeyIndex>),
	/// Position is child is at position + 1 of the branch.
	/// TODO is position of any use (it is dest position of descent)
	Match(Position<P::Alignment>),
//	// position mask left of this node
//	Middle(usize, u8),
}

impl<P, C> NodeOld<P, C>
	where
		P: RadixConf,
		C: Children<Self, Radix = P>,
{
	fn prefix_node(&self, key: &[u8]) -> (&Self, Descent<P>) {
		unimplemented!()
	}
	fn prefix_node_mut(&mut self, key: &[u8]) -> (&mut Self, Descent<P>) {
		unimplemented!()
	}
}

/// Stack of Node to reach a position.
struct NodeStack<'a, N: Node> {
	// TODO use smallvec instead
	stack: Vec<(PositionFor<N>, &'a N)>,
	// The key used with the stack.
	// key: Vec<u8>,
}

// TODO put pointers in node stack.
impl<'a, N: Node> NodeStack<'a, N> {
	fn new() -> Self {
		NodeStack {
			stack: Vec::new(),
		}
	}
}
impl<'a, N: Node> NodeStack<'a, N> {
	fn descend(&self, key: &[u8], dest_position: PositionFor<N>) -> Descent<N::Radix> {
		if let Some(top) = self.stack.last() {
			top.1.descend(key, top.0, dest_position)
		} else {
			// using a random key index for root element
			Descent::Child(PositionFor::<N>::zero(), KeyIndexFor::<N>::zero())
		}
	}
}
/// Stack of Node to reach a position.
struct NodeStackMut<N: Node> {
	// TODO use smallvec instead
	stack: Vec<(PositionFor<N>, *mut N)>,
	// The key used with the stack.
	// key: Vec<u8>,
}

// TODO put pointers in node stack.
impl<N: Node> NodeStackMut<N> {
	fn new() -> Self {
		NodeStackMut {
			stack: Vec::new(),
		}
	}
}
impl<N: Node> NodeStackMut<N> {
	fn descend(&self, key: &[u8], dest_position: PositionFor<N>) -> Descent<N::Radix> {
		if let Some(top) = self.stack.last() {
			unsafe {
				top.1.as_mut().unwrap().descend(key, top.0, dest_position)
			}
		} else {
			// using a random key index for root element
			Descent::Child(PositionFor::<N>::zero(), KeyIndexFor::<N>::zero())
		}
	}
}

pub struct SeekIter<'a, N: Node> {
	tree: &'a Tree<N>,
	dest: &'a [u8],
	dest_position: PositionFor<N>,
	// TODO seekiter could be lighter and not stack, 
	// just keep latest: a stack trait could be use.
	stack: NodeStack<'a, N>,
	reach_dest: bool,
	next: Descent<N::Radix>,
}
pub struct SeekValueIter<'a, N: Node>(SeekIter<'a, N>);

impl<N: Node> Tree<N> {
	pub fn seek_iter<'a>(&'a self, key: &'a [u8]) -> SeekIter<'a, N> {
		let dest_position = Position {
			index: key.len(),
			mask: MaskFor::<N::Radix>::last(),
		};
		self.seek_iter_at(key, dest_position)
	}
	/// Seek non byte aligned nodes.
	pub fn seek_iter_at<'a>(&'a self, key: &'a [u8], dest_position: PositionFor<N>) -> SeekIter<'a, N> {
		let stack = NodeStack::new();
		let reach_dest = false;
		let next = stack.descend(key, dest_position);
		SeekIter {
			tree: self,
			dest: key,
			dest_position,
			stack,
			reach_dest,
			next,
		}
	}
}


impl<'a, N: Node> SeekIter<'a, N> {
	pub fn iter(self) -> Iter<'a, N> {
		let dest = self.dest;
		let stack = self.stack.stack.into_iter().map(|(pos, node)| {
			let key = pos.index::<N::Radix>(dest)
				.expect("build from existing data struct");
			(pos, node, key)
		}).collect();
		Iter {
			tree: self.tree,
			stack: IterStack {
				stack,
				key: self.dest.to_vec(),
			},
			finished: false,
		}
	}
	pub fn iter_prefix(mut self) -> Iter<'a, N> {
		let dest = self.dest;
		let stack = self.stack.stack.pop().map(|(pos, node)| {
			let key = pos.index::<N::Radix>(dest)
				.expect("build from existing data struct");
			(pos, node, key)
		}).into_iter().collect();
		Iter {
			tree: self.tree,
			stack: IterStack {
				stack,
				key: self.dest.to_vec(),
			},
			finished: false,
		}
	}
	pub fn value_iter(self) -> SeekValueIter<'a, N> {
		SeekValueIter(self)
	}
	fn next_node(&mut self) -> Option<(PositionFor<N>, &'a N)> {
		if self.reach_dest {
			return None;
		}
		match self.next {
			Descent::Child(position, index) => {
				if let Some(parent) = self.stack.stack.last() {
					// TODO stack child
					if let Some(child) = parent.1.get_child(index) {
						//let position = position.next::<N::Radix>();
						self.stack.stack.push((position, child));
					} else {
						self.reach_dest = true;
						return None;
					}
				} else {
					// empty tree
					//		// TODO put ref in stack.
					if let Some(node) = self.tree.tree.as_ref() {
						let zero = PositionFor::<N>::zero();
						self.stack.stack.push((zero, node));
					} else {
						self.reach_dest = true;
					}
				}
			},
			Descent::Middle(_position, _index) => {
				self.reach_dest = true;
				return None;
			},
			Descent::Match(_position) => {
				self.reach_dest = true;
			},
		}
		if !self.reach_dest {
			self.next = self.stack.descend(&self.dest, self.dest_position);
		}
		self.stack.stack.last().map(|last| (last.0, last.1))
	}
}

impl<'a, N: Node> Iterator for SeekIter<'a, N> {
	type Item = (&'a [u8], PositionFor<N>, &'a N);
	fn next(&mut self) -> Option<Self::Item> {
		self.next_node().map(|(pos, node)| (self.dest, pos, node))
	}
}

impl<'a, N: Node> Iterator for SeekValueIter<'a, N> {
	type Item = (&'a [u8], &'a [u8]);
	fn next(&mut self) -> Option<Self::Item> {
		loop {
			if let Some((key, _pos, node)) = self.0.next() {
				if let Some(v) = node.value() {
					return Some((key, v))
				}
			} else {
				return None;
			}
		}
	}
}
pub struct SeekIterMut<'a, N: Node> {
	tree: &'a mut Tree<N>,
	dest: &'a [u8],
	dest_position: PositionFor<N>,
	// Here NodeStackMut will be used through unsafe
	// calls, so it should always be 'a with
	// content comming only form tree field.
	stack: NodeStackMut<N>,
	reach_dest: bool,
	next: Descent<N::Radix>,
}
pub struct SeekValueIterMut<'a, N: Node>(SeekIterMut<'a, N>);
	
impl<N: Node> Tree<N> {
	pub fn seek_iter_mut<'a>(&'a mut self, key: &'a [u8]) -> SeekIterMut<'a, N> {
		let dest_position = Position {
			index: key.len(),
			mask: MaskFor::<N::Radix>::last(),
		};
		self.seek_iter_at_mut(key, dest_position)
	}
	/// Seek non byte aligned nodes.
	pub fn seek_iter_at_mut<'a>(&'a mut self, key: &'a [u8], dest_position: PositionFor<N>) -> SeekIterMut<'a, N> {
		let stack = NodeStackMut::new();
		let reach_dest = false;
		let next = stack.descend(key, dest_position);
		SeekIterMut {
			tree: self,
			dest: key,
			dest_position,
			stack,
			reach_dest,
			next,
		}
	}
}


impl<'a, N: Node> SeekIterMut<'a, N> {
	pub fn value_iter(self) -> SeekValueIterMut<'a, N> {
		SeekValueIterMut(self)
	}
	fn next_node(&mut self) -> Option<(PositionFor<N>, &'a mut N)> {
		if self.reach_dest {
			return None;
		}
		match self.next {
			Descent::Child(position, index) => {
				if let Some(parent) = self.stack.stack.last_mut() {
					// TODO stack child
					if let Some(child) = unsafe {
						parent.1.as_mut().unwrap().get_child_mut(index) 
					} {
						let child = child as *mut _;
						//let position = position.next::<N::Radix>();
						self.stack.stack.push((position, child));
					} else {
						self.reach_dest = true;
						return None;
					}
				} else {
					// empty tree
					//		// TODO put ref in stack.
					if let Some(node) = self.tree.tree.as_mut() {
						let zero = PositionFor::<N>::zero();
						self.stack.stack.push((zero, node));
					} else {
						self.reach_dest = true;
					}
				}
			},
			Descent::Middle(_position, _index) => {
				self.reach_dest = true;
				return None;
			},
			Descent::Match(_position) => {
				self.reach_dest = true;
			},
		}
		if !self.reach_dest {
			self.next = self.stack.descend(&self.dest, self.dest_position);
		}
		self.stack.stack.last().map(|last| (
			last.0,
			unsafe { last.1.as_mut().unwrap() },
		))
	}
}
impl<'a, N: Node> Iterator for SeekIterMut<'a, N> {
	type Item = (&'a [u8], PositionFor<N>, &'a mut N);
	fn next(&mut self) -> Option<Self::Item> {
		self.next_node().map(|(pos, node)| (self.dest, pos, node))
	}
}

impl<'a, N: Node> Iterator for SeekValueIterMut<'a, N> {
	type Item = (&'a [u8], &'a [u8]);
	fn next(&mut self) -> Option<Self::Item> {
		loop {
			if let Some((key, _pos, node)) = self.0.next() {
				if let Some(v) = node.value() {
					return Some((key, v))
				}
			} else {
				return None;
			}
		}
	}
}

/// Stack of Node to reach a position.
struct IterStack<'a, N: Node> {
	// TODO use smallvec instead
	// The index is the current index where to descend into if going
	// downward, or where we descend from if going upward.
	stack: Vec<(PositionFor<N>, &'a N, KeyIndexFor<N>)>,
	// The key used with the stack.
	key: Vec<u8>,
}

// TODO put pointers in node stack.
impl<'a, N: Node> IterStack<'a, N> {
	fn new() -> Self {
		IterStack {
			stack: Vec::new(),
			key: Vec::new(),
		}
	}
}

pub struct Iter<'a, N: Node> {
	tree: &'a Tree<N>,
	stack: IterStack<'a, N>,
	finished: bool,
}

pub struct ValueIter<'a, N: Node>(Iter<'a, N>);

impl<N: Node> Tree<N> {
	pub fn iter<'a>(&'a self) -> Iter<'a, N> {
		Iter {
			tree: self,
			stack: IterStack::new(),
			finished: false,
		}
	}
}

impl<'a, N: Node> Iter<'a, N> {
	fn value_iter(self) -> ValueIter<'a, N> {
		ValueIter(self)
	}
	fn next_node(&mut self) -> Option<(PositionFor<N>, &'a N)> {
		if self.finished {
			return None;
		}
		let mut do_pop = false;
		loop {
			if do_pop {
				self.stack.stack.pop();
				if let Some(last) = self.stack.stack.last_mut() {
					// move cursor to next
					if let Some(next) = last.2.next() {
						last.2 = next;
					} else {
						// try descend in next from parent
						continue;
					}
				} else {
					// last pop
					self.finished = true;
					break;
				}
				do_pop = false;
			}
			if let Some(last) = self.stack.stack.last_mut() {
				// try descend
				if let Some(child) = last.1.get_child(last.2) {
					//let position = last.0.next::<N::Radix>();
					let position = last.0;
					position.set_index::<N::Radix>(&mut self.stack.key, last.2);
					let position = position.next::<N::Radix>();
					child.new_end(&mut self.stack.key, position);
					let position = position.next_by::<N::Radix>(child.depth());
					let first_key = KeyIndexFor::<N>::zero();
					self.stack.stack.push((position, child, first_key));
					break;
				}
	
				// try descend in next
				if let Some(next) = last.2.next() {
					last.2 = next;
				} else {
					// try descend in next from parent
					do_pop = true;
				}
			} else {
				// empty, this is start iteration
				if let Some(node) = self.tree.tree.as_ref() {
					let zero = PositionFor::<N>::zero();
					let first_key = KeyIndexFor::<N>::zero();
					node.new_end(&mut self.stack.key, zero);
					let zero = zero.next_by::<N::Radix>(node.depth());
					self.stack.stack.push((zero, node, first_key));
				} else {
					self.finished = true;
				}
				break;
			}
		}

		self.stack.stack.last().map(|(p, n, _i)| (*p, *n))
	}
}

impl<'a, N: Node> Iterator for Iter<'a, N> {
	// TODO key as slice, but usual lifetime issue.
	// TODO at leas use a stack type for key (smallvec).
	type Item = (Vec<u8>, PositionFor<N>, &'a N);
	fn next(&mut self) -> Option<Self::Item> {
		self.next_node().map(|(p, n)| (self.stack.key.clone(), p, n))
	}
}

impl<'a, N: Node> Iterator for ValueIter<'a, N> {
	// TODO key as slice, but usual lifetime issue.
	// TODO at leas use a stack type for key (smallvec).
	type Item = (Vec<u8>, &'a [u8]);
	fn next(&mut self) -> Option<Self::Item> {
		loop {
			if let Some((mut key, pos, node)) = self.0.next() {
				if let Some(v) = node.value() {
					key.truncate(pos.index);
					return Some((key, v))
				}
			} else {
				return None;
			}
		}
	}
}

impl<N: Node> Tree<N> {
	pub fn get(&self, key: &[u8]) -> Option<&[u8]> {
		if let Some(top) = self.tree.as_ref() {
			let mut current = top;
			if key.len() == 0 {
				return current.value();
			}
			let dest_position = Position {
				index: key.len(),
				mask: MaskFor::<N::Radix>::last(),
			};
			let mut position = PositionFor::<N>::zero();
			loop {
				match current.descend(key, position, dest_position) {
					Descent::Child(child_position, index) => {
						if let Some(child) = current.get_child(index) {
							position = child_position.next::<N::Radix>();
							//position = child_position;
							current = child;
						} else {
							return None;
						}
					},
					Descent::Middle(_position, _index) => {
						return None;
					},
					Descent::Match(_position) => {
						return current.value();
					},
				}
			}
		} else {
			None
		}
	}
	pub fn insert(&mut self, key: &[u8], value: Vec<u8>) -> Option<Vec<u8>> {
		let dest_position = PositionFor::<N> {
			index: key.len(),
			mask: MaskFor::<N::Radix>::first(),
		};
		let mut position = PositionFor::<N>::zero();
		if let Some(top) = self.tree.as_mut() {
			let mut current = top;
			if key.len() == 0 && current.depth() == 0 {
				return current.set_value(value);
			}
			loop {
				match current.descend(key, position, dest_position) {
					Descent::Child(child_position, index) => {
						if current.get_child(index).is_some() {
							if let Some(child) = current.get_child_mut(index) {
								position = child_position.next::<N::Radix>();
								//position = child_position;
								current = child;
							} else {
								unreachable!("tested above")
							}
						} else {
							let child_position = child_position.next::<N::Radix>();
							let new_child = N::new(key, child_position, dest_position, Some(value), self.init.clone());
							assert!(current.set_child(index, new_child).is_none());
							return None;
						}
					},
					Descent::Middle(middle_position, Some(index)) => {
						// insert middle node
						current.split_off(position, middle_position);
						let child_start = middle_position.next::<N::Radix>();
						let new_child = N::new(key, child_start, dest_position, Some(value), self.init.clone());
						//let child_index = middle_position.index::<N::Radix>(key)
						//	.expect("Middle resolved from key");
						assert!(current.set_child(index, new_child).is_none());
						return None;
					},
					Descent::Middle(middle_position, None) => {
						// insert middle node
						current.split_off(position, middle_position);
						current.set_value(value);
						return None;
					},
					Descent::Match(_position) => {
						return current.set_value(value);
					},
				}
			}
		} else {
			self.tree = Some(N::new(key, position, dest_position, Some(value), self.init.clone()));
			None
		}
	}
	pub fn remove(&mut self, key: &[u8]) -> Option<Vec<u8>> {
		let mut position = PositionFor::<N>::zero();
		let mut empty_tree = None;
		if let Some(top) = self.tree.as_mut() {
			let mut current: &mut N = top;
			if key.len() == 0 && current.depth() == 0 {
				let result = current.remove_value();
				if current.number_child() == 0 {
					empty_tree = Some(result);
//					self.tree = None;
				} else {
					if current.number_child() == 1 {
						current.fuse_child(key);
					}
					return result;
				}
			}
			let dest_position = Position {
				index: key.len(),
				mask: MaskFor::<N::Radix>::last(),
			};
			if let Some(result) = empty_tree {
				self.tree = None;
				return result;
			}
			let mut parent = None;
			let mut current_ptr: *mut N = current;
			loop {
				let current = unsafe { current_ptr.as_mut().unwrap() };
				match current.descend(key, position, dest_position) {
					Descent::Child(child_position, index) => {
						if let Some(child) = current.get_child_mut(index) {
							let old_position = child_position; // TODO probably incorrect
							position = child_position.next::<N::Radix>();
							current_ptr = child as *mut N;
							parent = Some((current, old_position));
						} else {
							return None;
						}
					},
					Descent::Middle(_middle_position, _index) => {
						return None;
					},
					Descent::Match(_position) => {
						let result = current.remove_value();
						if current.number_child() == 0 {
							if let Some((parent, parent_position)) = parent {
								let parent_index = parent_position.index::<N::Radix>(key)
									.expect("was resolved from key");
								parent.remove_child(parent_index);
								if parent.value().is_none() && parent.number_child() == 1 {
									parent.fuse_child(key);
								}
							} else {
								// root
//								self.tree = None;
								empty_tree = Some(result);
								break;
							}
						} else if current.number_child() == 1 {
							current.fuse_child(key)
						}

						//return current.set_value(value);
						return result;
					},
				}
			}
			if let Some(result) = empty_tree {
				self.tree = None;
				return result;
			}
		}
		None
	}
	pub fn clear(&mut self) {
		// TODO use iter mut
		let keys: Vec<_> = self.iter().value_iter().map(|v| v.0).collect();
		for key in keys {
			self.remove(key.as_slice());
		}
	}
}

#[cfg(any(test, feature = "fuzzer"))]
pub mod test_256 {
	use crate::*;
	use std::collections::btree_map::BTreeMap;

	type Node = NodeOld<Radix256Conf, Children256Flatten>;

	#[test]
	fn empty_are_equals() {
		let t1 = Tree::<Node>::new(());
		let t2 = Tree::<Node>::new(());
		assert_eq!(t1, t2);
	}

	#[test]
	fn inserts_are_equals() {
		let mut t1 = Tree::<Node>::new(());
		let mut t2 = Tree::<Node>::new(());
		let value1 = b"value1".to_vec();
		assert_eq!(None, t1.insert(b"key1", value1.clone()));
		assert_eq!(None, t2.insert(b"key1", value1.clone()));
		assert_eq!(t1, t2);
		assert_eq!(Some(value1.clone()), t1.insert(b"key1", b"value2".to_vec()));
		assert_eq!(Some(value1.clone()), t2.insert(b"key1", b"value2".to_vec()));
		assert_eq!(t1, t2);
		assert_eq!(None, t1.insert(b"key2", value1.clone()));
		assert_eq!(None, t2.insert(b"key2", value1.clone()));
		assert_eq!(t1, t2);
		assert_eq!(None, t2.insert(b"key3", value1.clone()));
		assert_ne!(t1, t2);
	}

	fn compare_iter<K: Borrow<[u8]>>(left: &Tree::<Node>, right: &BTreeMap<K, Vec<u8>>) -> bool {
		let left_node = left.iter();
		let left = left_node.value_iter();
		let mut right = right.iter();
		for l in left {
			if let Some(r) = right.next() {
				if &l.0[..] != &r.0.borrow()[..] {
					return false;
				}
				if &l.1[..] != &r.1[..] {
					return false;
				}
			} else {
				return false;
			}
		}
		if right.next().is_some() {
			return false;
		}
		true
	}

	#[test]
	fn compare_btree() {
		let mut t1 = Tree::<Node>::new(());
		let mut t2 = BTreeMap::<&'static [u8], Vec<u8>>::new();
		let value1 = b"value1".to_vec();
		assert_eq!(None, t1.insert(b"key1", value1.clone()));
		assert_eq!(None, t2.insert(b"key1", value1.clone()));
		assert!(compare_iter(&t1, &t2));
		assert_eq!(Some(value1.clone()), t1.insert(b"key1", b"value2".to_vec()));
		assert_eq!(Some(value1.clone()), t2.insert(b"key1", b"value2".to_vec()));
		assert!(compare_iter(&t1, &t2));
		assert_eq!(None, t1.insert(b"key2", value1.clone()));
		assert_eq!(None, t2.insert(b"key2", value1.clone()));
		assert!(compare_iter(&t1, &t2));
		assert_eq!(None, t2.insert(b"key3", value1.clone()));
		assert!(!compare_iter(&t1, &t2));
	}

	fn fuzz_to_data(input: &[u8]) -> Vec<(Vec<u8>,Vec<u8>)> {
		let mut result = Vec::new();
		// enc = (minkeylen, maxkeylen (min max up to 32), datas)
		// fix data len 2 bytes
		let mut minkeylen = if let Some(v) = input.get(0) {
			let mut v = *v & 31u8;
			v = v + 1;
			v
		} else { return result; };
		let mut maxkeylen = if let Some(v) = input.get(1) {
			let mut v = *v & 31u8;
			v = v + 1;
			v
		} else { return result; };

		if maxkeylen < minkeylen {
			let v = minkeylen;
			minkeylen = maxkeylen;
			maxkeylen = v;
		}
		let mut ix = 2;
		loop {
			let keylen = if let Some(v) = input.get(ix) {
				let mut v = *v & 31u8;
				v = v + 1;
				v = std::cmp::max(minkeylen, v);
				v = std::cmp::min(maxkeylen, v);
				v as usize
			} else { break };
			let key = if input.len() > ix + keylen {
				input[ix..ix+keylen].to_vec()
			} else { break };
			ix += keylen;
			let val = if input.len() > ix + 2 {
				input[ix..ix+2].to_vec()
			} else { break };
			result.push((key,val));
		}
		result
	}

	fn fuzz_removal(data: Vec<(Vec<u8>,Vec<u8>)>) -> Vec<(bool, Vec<u8>,Vec<u8>)> {
		let mut res = Vec::new();
		let mut existing = None;
		for (a, d) in data.into_iter().enumerate() {
			if existing == None {
				existing = Some(a%2);
			}
			if existing.unwrap() == 0 {
				if a % 9 == 6
				|| a % 9 == 7
				|| a % 9 == 8 {
					// a random removal some time
					res.push((true, d.0, d.1));
					continue;
				}
			}
			res.push((false, d.0, d.1));
		}
		res
	}

	pub fn fuzz_insert_remove(input: &[u8]) {
		let data = fuzz_to_data(input);
		let data = fuzz_removal(data);
		let mut a = 0;
		let mut t1 = Tree::<Node>::new(());
		let mut t2 = BTreeMap::<Vec<u8>, Vec<u8>>::new();
		while a < data.len() {
			if data[a].0 {
				// remove
				t1.remove(&data[a].1[..]);
				t2.remove(&data[a].1[..]);
			} else {
				// add
				t1.insert(&data[a].1[..], data[a].2.clone());
				t2.insert(data[a].1.clone(), data[a].2.clone());
			}
			a += 1;
		}
		assert!(compare_iter(&mut t1, &mut t2));
	}

	#[test]
	fn replay_insert_remove_fuzzing() {
		let datas = [
			vec![0, 1, 0, 45, 0, 0, 0, 0, 0, 0, 0, 0, 75, 0],
			vec![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 96, 0, 16, 96],
			vec![0, 0, 0, 0, 0, 0, 0, 195, 0, 0, 195, 0, 0, 0],
			vec![0, 0, 5, 75, 9, 1, 48, 58, 17, 9, 17, 9, 0],
			vec![0, 0, 8, 0, 0, 0, 0, 0],
			vec![0, 0, 70, 0, 3, 61, 0, 0],
			vec![0u8, 202, 1, 4, 64, 49, 0, 0],
		];
		for data in datas.iter() {
			fuzz_insert_remove(&data[..]);
		}
	}
}

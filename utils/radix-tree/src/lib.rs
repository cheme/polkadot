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

//! Ordered tree with prefix iterator.
//!
//! Allows iteration over a key prefix.
//! No concern about deletion performance.

extern crate alloc;

pub mod backends;
pub mod radix;
pub mod children;
pub mod iterators;
pub mod tests;

pub use derivative::Derivative;
use alloc::vec::Vec;
use alloc::boxed::Box;
use alloc::borrow::Borrow;
use core::cmp::{min, Ordering};
use core::fmt::Debug;
use core::mem::replace;
use codec::Codec;
use radix::{PrefixKeyConf, RadixConf, Position,
	MaskFor, MaskKeyByte};
use children::Children;
pub use backends::TreeBackend as Backend;


pub type Key = NodeKeyBuff;
//type NodeKeyBuff = smallvec::SmallVec<[u8; 64]>;
type NodeKeyBuff = Vec<u8>;
pub type NodeBox<N> = Box<Node<N>>;

/// Value trait constraints.
pub trait Value: Clone + Debug { }

impl<V: Clone + Debug> Value for V { }

/// This is a partial key.
/// It contains part of a value key.
/// For unaligned radix, mask for start
/// byte and end byte are included.
#[derive(Derivative)]
#[derivative(Clone)]
#[derivative(Debug)]
struct PrefixKey<D, P>
	where
		P: PrefixKeyConf,
{
	start: P::Mask, // mask of first byte
	end: P::Mask, // mask of last byte
	data: D,
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

impl<P> PrefixKey<NodeKeyBuff, P>
	where
		P: PrefixKeyConf,
{
	// TODO consider returning the skipped byte aka key index (avoid fetching it before split_off)
	fn split_off<R: RadixConf<Alignment = P>>(&mut self, position: Position<P>) -> Self {
		let split_end = self.end;
		let mut split: NodeKeyBuff = if position.mask == MaskFor::<R>::first() {
			// No splitoff for smallvec
			//let split = self.data[position.index..].into();
			//self.data.truncate(position.index);
			let split = self.data.split_off(position.index);
			self.end = position.mask;
			split
		} else {
			// No splitoff for smallvec
			//let split = self.data[position.index + 1..].into();
			//self.data.truncate(position.index + 1);
			let split = self.data.split_off(position.index + 1);
			self.end = position.mask;
			split
		};
		let (split_start, increment) = R::advance(position.mask);
		if increment > 0 {
			//split = split[increment..].into();
			split = split.split_off(increment);
		}
		PrefixKey {
			data: split,
			start: split_start,
			end: split_end,
		}
	}
}


/// Returns first position where position differs.
fn common_until<D1, D2, N>(one: &PrefixKey<D1, N::Alignment>, other: &PrefixKey<D2, N::Alignment>) -> Position<N::Alignment>
	where
		D1: Borrow<[u8]>,
		D2: Borrow<[u8]>,
		N: RadixConf,
{
	if N::Alignment::ALIGNED {
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
	} else {
		unimplemented!()
/*		if one.start != other.start {
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
				delta = if left.len() == upper_bound {
					one.unchecked_last_byte() ^ right[index]
						& !one.end.mask(255)
				} else {
					left[index] ^ other.unchecked_last_byte()
						& !other.end.mask(255)
				};
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
		*/
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

impl<P> PrefixKey<NodeKeyBuff, P>
	where
		P: PrefixKeyConf,
{
	/// start is inclusive, end is exclusive.
	/// This function cannot build an empty `PrefixKey`,
	/// if needed `empty` should be use.
	fn new_offset<Q: Borrow<[u8]>>(key: Q, start: Position<P>, end: Position<P>) -> Self {
		let data = if end.mask == P::Mask::first() {
			key.borrow()[start.index..end.index].into()
		} else {
			key.borrow()[start.index..end.index + 1].into()
		};

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

/// Trait with main tree configuration.
pub trait TreeConf: Debug + Clone + Sized {
	type Radix: RadixConf;
	type Value: Value;
	type Children: Children<Node = Node<Self>, Radix = Self::Radix>;
	type Backend: Backend<Self>;

	fn new_node_split(node: &Node<Self>, key: &[u8], position: PositionFor<Self>, at: PositionFor<Self>) -> Self::Backend {
		if let Some(backend) = Self::Backend::DEFAULT {
			backend
		} else {
			let mut key = key.into();
			node.new_end(&mut key, position);
			let at = at.next::<Self::Radix>();
			// TODO consider owned variant of `backend_key` !!
			let key = Self::Backend::backend_key(key.as_slice(), at);
			Self::Backend::new_node(&node.backend, key)
		}
	}

	fn new_node_contained(node: &Node<Self>, key: &[u8], position: PositionFor<Self>) -> Self::Backend {
		if let Some(backend) = Self::Backend::DEFAULT {
			backend
		} else {
			let key = Self::Backend::backend_key(key, position);
			Self::Backend::new_node(&node.backend, key)
		}
	}
	fn new_node_root(init: &BackendFor<Self>) -> Self::Backend {
		if let Some(backend) = Self::Backend::DEFAULT {
			backend
		} else {
			Self::Backend::new_root(init)
		}
	}
}

pub(crate) type PositionFor<N> = Position<<<N as TreeConf>::Radix as RadixConf>::Alignment>;
pub(crate) type AlignmentFor<N> = <<N as TreeConf>::Radix as RadixConf>::Alignment;
pub(crate) type KeyIndexFor<N> = <<N as TreeConf>::Radix as RadixConf>::KeyIndex;
pub(crate) type BackendFor<N> = <<N as TreeConf>::Backend as Backend<N>>::Backend;

#[derive(Derivative)]
#[derivative(Clone)]
pub struct Node<N>
	where
		N: TreeConf,
{
	// TODO this should be able to use &'a[u8] for iteration
	// and querying.
	key: PrefixKey<NodeKeyBuff, AlignmentFor<N>>,
	//pub value: usize,
	value: Option<N::Value>,
	//pub left: usize,
	//pub right: usize,
	// TODO if backend behind, then Self would neeed to implement a Node trait with lazy loading...
	children: N::Children,
	backend: N::Backend,
}

impl<N: TreeConf> Debug for Node<N> {
	fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
		if N::Backend::DO_DEBUG {
			"Node:".fmt(f)?;
			self.key.fmt(f)?;
			self.value.fmt(f)?;
			self.children.fmt(f)?;
		} else {
			"Non debuggable node".fmt(f)?;
		}
		Ok(())
	}
}

impl<N: TreeConf> Drop for Node<N> {
	fn drop(&mut self) {
		N::Backend::commit_change(self, false);
	}
}

/*
impl<P, C> Node<P, C>
	where
		P: RadixConf,
		C: Children<Self, Radix = P>,
{
	fn leaf(key: &[u8], start: Position<P::Alignment>, value: Vec<u8>) -> Self {
		Node {
			key: PrefixKey::new_offset(key, start),
			value: Some(value),
			children: C::empty(),
		}
	}
}
*/

impl<N: TreeConf> Node<N> {
	pub fn new_box(
		key: &[u8],
		start_position: PositionFor<N>,
		end_position: PositionFor<N>,
		value: Option<N::Value>,
		init: (),
		backend: N::Backend,
	) -> NodeBox<N> {
		Box::new(Self::new(key, start_position, end_position, value, init, backend))
	}
	pub fn new(
		key: &[u8],
		start_position: PositionFor<N>,
		end_position: PositionFor<N>,
		value: Option<N::Value>,
		_init: (),
		backend: N::Backend,
	) -> Node<N> {
		Node {
			key: PrefixKey::new_offset(key, start_position, end_position),
			value,
			children: N::Children::empty(),
			backend,
		}
	}

	fn descend(
		&self,
		key: &[u8],
		node_position: PositionFor<N>,
		dest_position: PositionFor<N>,
	) -> Descent<N::Radix> {
		let ref_prefix = PrefixKey::<_, AlignmentFor<N>>::new_offset_ref(key, node_position, dest_position);
		let mut common = common_until::<_, _, N::Radix>(&self.key, &ref_prefix);
		let dest_position_next = dest_position;
		common.index += node_position.index;
		match common.cmp(dest_position_next) {
			Ordering::Equal => Descent::Match(common),
			Ordering::Greater => {
				let ix = common.index::<N::Radix>(key)
					.expect("child");
				Descent::Child(common, ix)
			},
			Ordering::Less => {
				// TODO consider storing or direct function for next by child depth
				// to access value index.
				let node_end_index = node_position.next_by::<N::Radix>(self.depth());
				if common == node_end_index {
					let ix = common.index::<N::Radix>(key)
						.expect("child");
					Descent::Child(common, ix)
				} else if common == dest_position_next {
					Descent::Middle(common, None)
				} else {
					let ix = common.index::<N::Radix>(key);
					Descent::Middle(common, ix)
				}
			},
		}
	}
	pub fn depth(
		&self,
	) -> usize {
		self.key.depth()
	}
	pub fn value(
		&self,
	) -> Option<&N::Value> {
		self.value.as_ref()
	}
	pub fn value_mut(
		&mut self,
	) -> Option<&mut N::Value> {
		self.value.as_mut()
	}
	pub fn set_value(
		&mut self,
		value: N::Value,
	) -> Option<N::Value> {
		replace(&mut self.value, Some(value))
	}
	pub fn remove_value(
		&mut self,
	) -> Option<N::Value> {
		replace(&mut self.value, None)
	}
	pub fn number_child(
		&self,
	) -> usize {
		self.children.number_child()
	}
	pub fn get_child(
		&self,
		index: KeyIndexFor<N>,
	) -> Option<&Self> {
		//N::Backend::resolve(self);
		let result = self.children.get_child(index);
		result.as_ref().map(|c| N::Backend::resolve(c));
		result
	}
	pub fn has_child(
		&self,
		index: KeyIndexFor<N>,
	) -> bool {
		self.children.has_child(index)
	}
	pub fn get_child_mut(
		&mut self,
		index: KeyIndexFor<N>,
	) -> Option<&mut Self> {
		let mut result = self.children.get_child_mut(index);
		result.as_mut().map(|c| N::Backend::resolve_mut(c));
		result
	}
	pub fn set_child(
		&mut self,
		index: KeyIndexFor<N>,
		child: Box<Self>,
	) -> Option<Box<Self>> {
		self.backend.set_change();
		self.children.set_child(index, child)
	}
	pub fn remove_child(
		&mut self,
		index: KeyIndexFor<N>,
	) -> Option<Box<Self>> {
		let result = self.children.remove_child(index);
		if result.is_some() {
			self.backend.set_change();
		}
		result
	}
	pub fn split_off(
		&mut self,
		key: &[u8],
		position: PositionFor<N>,
		mut at: PositionFor<N>,
	) {
		at.index -= position.index;
		let index = self.key.index::<N::Radix>(at);
		let backend = N::new_node_split(self, key, position, at);

		let child_prefix = self.key.split_off::<N::Radix>(at);
		let child_value = self.value.take();
		let child_children = replace(&mut self.children, N::Children::empty());
		let child = Box::new(Node {
			key: child_prefix,
			value: child_value,
			children: child_children,
			backend, 
		});
		self.children.set_child(index, child);
		self.backend.set_change();
	}
	pub fn fuse_child(
		&mut self,
	) {
		if let Some(index) = self.children.first_child_index() {
			if let Some(mut child) = self.children.remove_child(index) {
				N::Backend::resolve_mut(&mut child);
				let position = PositionFor::<N> {
					index: 0,
					mask: self.key.start,
				};
				let position_start = position.next_by::<N::Radix>(self.depth());
				position_start.set_index::<N::Radix>(&mut self.key.data, index);
				let position_cat = position_start.next::<N::Radix>();
				child.new_end(&mut self.key.data, position_cat);
				self.key.end = child.key.end;
				self.value = child.value.take();
				self.children = replace(&mut child.children, N::Children::empty());
				N::Backend::delete(child);
			} else {
				unreachable!("fuse condition checked");
			}
		} else {
			unreachable!("fuse condition checked");
		}
	}

	// TODO make it a trait function?
	/// Realign node partial key to a given end position.
	pub fn new_end(&self, stack: &mut Key, node_position: PositionFor<N>) {
		let depth = self.depth();
		if depth == 0 {
			return;
		}
		if <N::Radix as RadixConf>::Alignment::ALIGNED {
			let new_len = node_position.index + depth;
			stack.resize(new_len, 0);
			&mut stack[node_position.index..new_len].copy_from_slice(self.key.data.borrow());
		} else {
			let node_position_end = node_position.next_by::<N::Radix>(depth);

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

	pub fn backend(
		&self,
	) -> &N::Backend {
		&self.backend
	}

	pub fn backend_mut(
		&mut self,
	) -> &mut N::Backend {
		&mut self.backend
	}
}

/// Main tree structure.
#[derive(Derivative)]
#[derivative(Clone(bound=""))]
#[derivative(Debug(bound=""))]
pub struct Tree<N>
	where
		N: TreeConf,
{
	/// A root node if any.
	tree: Option<NodeBox<N>>,

	/// A backend if needed.
	#[derivative(Debug="ignore")]
	pub init: BackendFor<N>,
}

impl<N> Tree<N>
	where
		N: TreeConf,
{
	pub fn new(init: BackendFor<N>) -> Self {
		Tree {
			tree: None,
			init,
		}
	}
	pub fn from_backend(init: BackendFor<N>) -> Self {
		if N::Backend::DEFAULT.is_some() {
			Self::new(init)
		} else {
			let tree =  N::Backend::get_root(&init);
			Tree {
				tree,
				init,
			}
		}
	}
	pub fn commit(&mut self) {
		self.tree.as_mut()
			.map(|node| N::Backend::commit_change(node, true));
	}
}

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
/*
impl<P, C> Node<P, C>
	where
		P: RadixConf,
		C: Children<Node = Self, Radix = P>,
{
	fn prefix_node(&self, key: &[u8]) -> (&Self, Descent<P>) {
		unimplemented!()
	}
	fn prefix_node_mut(&mut self, key: &[u8]) -> (&mut Self, Descent<P>) {
		unimplemented!()
	}
}
*/

impl<N: TreeConf> Tree<N> {
	pub fn get(&self, key: &[u8]) -> Option<&N::Value> {
		if let Some(top) = self.tree.as_ref() {
			let mut current = top.as_ref();
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
	pub fn get_mut(&mut self, key: &[u8]) -> Option<&mut N::Value> {
		if let Some(top) = self.tree.as_mut() {
			let mut current = top.as_mut();
			if key.len() == 0 {
				return current.value_mut();
			}
			let dest_position = Position {
				index: key.len(),
				mask: MaskFor::<N::Radix>::last(),
			};
			let mut position = PositionFor::<N>::zero();
			loop {
				match current.descend(key, position, dest_position) {
					Descent::Child(child_position, index) => {
						if let Some(child) = current.get_child_mut(index) {
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
						return current.value_mut();
					},
				}
			}
		} else {
			None
		}
	}

	pub fn insert(&mut self, key: &[u8], value: N::Value) -> Option<N::Value> {
		let dest_position = PositionFor::<N> {
			index: key.len(),
			mask: MaskFor::<N::Radix>::first(),
		};
		let mut position = PositionFor::<N>::zero();
		if let Some(top) = self.tree.as_mut() {
			let mut current = top.as_mut();
			if key.len() == 0 && current.depth() == 0 {
				return current.set_value(value);
			}
			loop {
				match current.descend(key, position, dest_position) {
					Descent::Child(child_position, index) => {
						if current.has_child(index) {
							if let Some(child) = current.get_child_mut(index) {
								position = child_position.next::<N::Radix>();
								//position = child_position;
								current = child;
							} else {
								unreachable!("tested above")
							}
						} else {
							let child_position = child_position.next::<N::Radix>();
							let new_child = Node::<N>::new_box(
								key,
								child_position,
								dest_position,
								Some(value),
								(),
								N::new_node_contained(current, key, child_position),
							);
							assert!(current.set_child(index, new_child).is_none());
							return None;
						}
					},
					Descent::Middle(middle_position, Some(index)) => {
						// insert middle node
						current.split_off(key, position, middle_position);
						let child_start = middle_position.next::<N::Radix>();
						let new_child = Node::<N>::new_box(
							key,
							child_start,
							dest_position,
							Some(value),
							(),
							N::new_node_contained(current, key, child_start),
						);
						//let child_index = middle_position.index::<N::Radix>(key)
						//	.expect("Middle resolved from key");
						assert!(current.set_child(index, new_child).is_none());
						return None;
					},
					Descent::Middle(middle_position, None) => {
						// insert middle node
						current.split_off(key, position, middle_position);
						current.set_value(value);
						return None;
					},
					Descent::Match(_position) => {
						return current.set_value(value);
					},
				}
			}
		} else {
			self.tree = Some(Node::<N>::new_box(
				key,
				position,
				dest_position,
				Some(value),
				(),
				N::new_node_root(&self.init),
			));
			None
		}
	}
	pub fn remove(&mut self, key: &[u8]) -> Option<N::Value> {
		let mut position = PositionFor::<N>::zero();
		let mut empty_tree = None;
		if let Some(top) = self.tree.as_mut() {
			let current: &mut Node<N> = top;
			if key.len() == 0 && current.depth() == 0 {
				let result = current.remove_value();
				if current.number_child() == 0 {
					empty_tree = Some(result);
//					self.tree = None;
				} else {
					if current.number_child() == 1 {
						current.fuse_child();
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
			let mut current_ptr: *mut Node<N> = current;
			loop {
				// Note that this can produce dangling pointer when removing
				// node.
				let current = unsafe { current_ptr.as_mut().unwrap() };
				match current.descend(key, position, dest_position) {
					Descent::Child(child_position, index) => {
						if let Some(child) = current.get_child_mut(index) {
							let old_position = child_position; // TODO probably incorrect
							position = child_position.next::<N::Radix>();
							current_ptr = child as *mut Node<N>;
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
									parent.fuse_child();
								}
							} else {
								// root
//								self.tree = None;
								empty_tree = Some(result);
								break;
							}
						} else if current.number_child() == 1 {
							current.fuse_child();
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

#[macro_export]
/// Flatten type for children of a given node type.
/// `inner_node_type` is expected to be parametered by a `Children` type
/// and a `RadixConf` type.
macro_rules! flatten_children {
	(
		$(!value_bound: $( $value_const: ident)*,)?
		$type_alias: ident,
		$inner_children_type: ident,
		$inner_node_type: ident,
		$inner_type: ident,
		$inner_radix: ty,
		$backend: ty,
		$($backend_gen: ident, )?
		$({ $backend_ty: ident: $backend_const: tt $(+ $backend_const2: tt)* })?
	) => {
		#[derive(Clone)]
		#[derive(Debug)]
		pub struct $inner_node_type<V: Value, $($backend_gen)?>(core::marker::PhantomData<V>, $(core::marker::PhantomData<$backend_gen>)?);
		impl<V: Value $($(+ $value_const)*)?, $($backend_gen)?> TreeConf for $inner_node_type<V, $($backend_gen)?>
			$(where $backend_ty: $backend_const $(+ $backend_const2)*)?
		{
			type Radix = $inner_radix;
			type Value = V;
			type Children = $type_alias<V, $($backend_gen)?>;
			type Backend = $backend;
		}
		type $inner_children_type<V, $($backend_gen)?> = Node<$inner_node_type<V, $($backend_gen)?>>;
		#[derive(Derivative)]
		#[derivative(Clone)]
		#[derivative(Debug)]
		pub struct $type_alias<V: Value $($(+ $value_const)*)?, $($backend_gen)?>($inner_type<$inner_children_type<V, $($backend_gen)?>>)
			$(where $backend_ty: $backend_const $(+ $backend_const2)*)?;

		impl<V: Value $($(+ $value_const)*)?, $($backend_gen)?> Children for $type_alias<V, $($backend_gen)?>
			$(where $backend_ty: $backend_const $(+ $backend_const2)*)?
		{
			type Radix = $inner_radix;
			type Node = Node<$inner_node_type<V, $($backend_gen)?>>;

			fn empty() -> Self {
				$type_alias($inner_type::empty())
			}
			fn set_child(
				&mut self,
				index: <Self::Radix as RadixConf>::KeyIndex,
				child: Box<$inner_children_type<V, $($backend_gen)?>>,
			) -> Option<Box<$inner_children_type<V, $($backend_gen)?>>> {
				self.0.set_child(index, child)
			}
			fn remove_child(
				&mut self,
				index: <Self::Radix as RadixConf>::KeyIndex,
			) -> Option<Box<$inner_children_type<V, $($backend_gen)?>>> {
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
			) -> Option<&$inner_children_type<V, $($backend_gen)?>> {
				self.0.get_child(index)
			}
			fn get_child_mut(
				&mut self,
				index: <Self::Radix as RadixConf>::KeyIndex,
			) -> Option<&mut $inner_children_type<V, $($backend_gen)?>> {
				self.0.get_child_mut(index)
			}
		}
	}
}

use crate::children::{Children256, ART48_256};
use crate::radix::impls::Radix256Conf;

flatten_children!(
	Children256Flatten,
	Node256Flatten,
	Node256NoBackend,
	Children256,
	Radix256Conf,
	(),
);

flatten_children!(
	Children256FlattenART,
	Node256FlattenART,
	Node256NoBackendART,
	ART48_256,
	Radix256Conf,
	(),
);

flatten_children!(
	!value_bound: Codec,
	Children256Flatten2,
	Node256Flatten2,
	Node256HashBackend,
	Children256,
	Radix256Conf,
	backends::DirectBackend<
		backends::RcBackend<
			backends::MapBackend
		>
	>,
);

flatten_children!(
	!value_bound: Codec,
	Children256Flatten3,
	Node256Flatten3,
	Node256LazyHashBackend,
	Children256,
	Radix256Conf,
	backends::LazyBackend<
		backends::RcBackend<
			backends::MapBackend
		>
	>,
);

flatten_children!(
	!value_bound: Codec,
	Children256Flatten4,
	Node256Flatten4,
	Node256TxBackend,
	Children256,
	Radix256Conf,
	backends::DirectBackend<
		backends::RcBackend<
			backends::MapBackend
		>
	>,
);

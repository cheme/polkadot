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

//pub mod backends;
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
use radix::{PrefixKeyConf, RadixConf, Position,
	MaskFor, MaskKeyByte};
use children::Children;
use codec::Codec;
pub use backends::TreeBackend as Backend;

/// Alias to type of a key as used by external api.
pub type Key = NodeKeyBuff;

/// Alias type to internal byte buffer for partial key (`PrefixKey`)
/// stored in nodes.
type NodeKeyBuff = Vec<u8>;
//type NodeKeyBuff = smallvec::SmallVec<[u8; 64]>;

/// Alias to boxed nodes, tree use
/// node on heap.
pub type NodeBox<N> = Box<Node<N>>;

/// Value trait constraints.
pub trait Value: Clone + Debug { }

impl<V: Clone + Debug> Value for V { }

/// This is a partial key.
/// It contains part of a value key.
/// For unaligned radix, inclusive mask for start
/// byte and exclusive mask for end byte are included.
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
		self.start.mask_start(self.data.borrow()[0])
	}

	/*fn unchecked_last_byte(&self) -> u8 {
		self.end.mask_end_incl(self.data.borrow()[self.data.borrow().len() - 1])
	}*/

	fn unchecked_last_byte_excl(&self) -> u8 {
		self.end.mask_end_excl(self.data.borrow()[self.data.borrow().len() - 1])
	}

	fn unchecked_single_byte(&self) -> u8 {
		self.start.mask_start(self.end.mask_end_incl(self.data.borrow()[0]))
	}

	fn index<R: RadixConf<Alignment = P>>(&self, position: Position<P>) -> R::KeyIndex {
		position.index::<R>(self.data.borrow())
			.expect("TODO consider safe api here")
	}

	fn depth(&self) -> usize {
		if P::ALIGNED {
			self.data.borrow().len()
		} else {
			let nb_mask = P::Mask::LAST.to_index() + 1; // TODO associated const, but merge useless traits first
			let mut len = self.data.borrow().len() * nb_mask as usize;
			len -= self.start.to_index() as usize;
			if P::Mask::FIRST != self.end {
				len -= (nb_mask - self.end.to_index()) as usize;
			}
			len
		}
	}
}

impl<P> PrefixKey<NodeKeyBuff, P>
	where
		P: PrefixKeyConf,
{
	// TODO consider returning the skipped byte aka key index (avoid fetching it before split_off)
	fn child_split_off<R: RadixConf<Alignment = P>>(&mut self, position: Position<P>) -> Self {
		let split_end = self.end;
		let shift = if position.mask == MaskFor::<R>::FIRST {
			0
		} else {
			1
		};
		// No splitoff for smallvec(
		//let split = self.data[position.index..].into();
		//self.data.truncate(position.index);)
		let mut split = self.data.split_off(position.index + shift);
		self.end = position.mask;

		// remove one for child.
		let (split_start, increment) = R::advance(position.mask);
		debug_assert!(increment < 2);
		if shift > 0 {
			if increment == 0 {
				let last_ix = self.data.len() - 1;
				let last = self.data[last_ix];
				split.insert(0, split_start.mask_start(last));
				self.data[last_ix] = self.end.mask_end_excl(last);
			}
		} else {
			if increment > 0 {
				split = split.split_off(increment);
			}
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
					mask: MaskFor::<N>::FIRST,
				}
			}
		}
		return Position {
			index: upper_bound,
			mask: MaskFor::<N>::FIRST,
		}
	} else {
		// TODO replace by debug_assert later.
		if one.start != other.start {
			panic!("Unaligned call to common_until.");
		}

		let left = one.data.borrow();
		let right = other.data.borrow();
		if left.len() == 0 || right.len() == 0 {
			return Position::zero();
		}

		let mut index = 0;
		let mut delta = one.unchecked_first_byte() ^ other.unchecked_first_byte();
		/*if left.len() == 1 {
			one.end.mask_end_excl(one.unchecked_first_byte())
		} else {
			one.unchecked_first_byte()
		} ^ if right.len() == 1 {
			other.end.mask_end_excl(other.unchecked_first_byte())
		} else {
			other.unchecked_first_byte()
		};*/
		if delta == 0 {
			let upper_bound = min(left.len(), right.len());
			for i in 1..(upper_bound - 1) {
				delta = left[i] ^ right[i];
				if delta != 0 {
					index = i;
					break;
				}
			}
			if index == 0 {
				index = upper_bound - 1;
				let left = if left.len() == upper_bound && one.end != MaskFor::<N>::FIRST {
					one.unchecked_last_byte_excl()
				} else {
					left[index]
				};
				let right =  if right.len() == index && one.end != MaskFor::<N>::FIRST {
					other.unchecked_last_byte_excl()
				} else {
					right[index]
				};
				if index == 0 {
					// actually we double check first byte here TODO remove first byte check?
					delta = one.start.mask_start(left) ^ other.start.mask_start(right);
				} else {
					delta = left ^ right;
				}
			}
		}
		if delta == 0 {
			if one.end == MaskFor::<N>::FIRST && other.end == MaskFor::<N>::FIRST {
				Position {
					index: index + 1,
					mask: MaskFor::<N>::FIRST,
				}
			} else {
				// get max end mask (TODO refact thisexpression ?)
				let mask = if one.end == MaskFor::<N>::FIRST {
					other.end
				} else if other.end == MaskFor::<N>::FIRST {
					one.end
				} else if one.end.cmp(other.end) == Ordering::Less {
					one.end
				} else {
					other.end
				};
				Position {
					index: index,
					mask,
				}
			}
		} else {
			let mut mask = N::common_until_delta(delta);
			if index + 1 == left.len() {
				if one.end != MaskFor::<N>::FIRST && one.end.cmp(mask) == Ordering::Less {
					mask = one.end;
				}
			}
			if other.end != MaskFor::<N>::FIRST && index + 1 == right.len() {
				if other.end.cmp(mask) == Ordering::Less {
					mask = one.end;
				}
			}
			Position {
				index: index,
				mask,
			}
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

impl<P> PrefixKey<NodeKeyBuff, P>
	where
		P: PrefixKeyConf,
{
	/// start is inclusive, end is exclusive.
	/// This function cannot build an empty `PrefixKey`,
	/// if needed `empty` should be use.
	fn new_offset<Q: Borrow<[u8]>>(key: Q, start: Position<P>, end: Position<P>) -> Self {
		let data = if end.mask == P::Mask::FIRST {
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
		let data = if end.mask == P::Mask::FIRST {
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
	type Children: Children<Node = ChildFor<Self>, Radix = Self::Radix>;
	type Backend: Backend<Self>;

	fn new_node_backend(node: &Node<Self>, removed_node: &mut Vec<Self::Backend>) -> Self::Backend {
		Self::new_node_backend_root(&node.backend.backend(), removed_node)
	}

	fn new_node_backend_root(init: &BackendFor<Self>, removed_node: &mut Vec<Self::Backend>) -> Self::Backend {
		if let Some(backend) = removed_node.pop() {
			backend
		} else {
			Self::Backend::new_node_backend(init)
		}
	}
}

pub(crate) type PositionFor<N> = Position<<<N as TreeConf>::Radix as RadixConf>::Alignment>;
pub(crate) type AlignmentFor<N> = <<N as TreeConf>::Radix as RadixConf>::Alignment;
pub(crate) type KeyIndexFor<N> = <<N as TreeConf>::Radix as RadixConf>::KeyIndex;
pub(crate) type BackendFor<N> = <<N as TreeConf>::Backend as Backend<N>>::Backend;
pub(crate) type ChildFor<N> = <<N as TreeConf>::Backend as Backend<N>>::ChildState;

/// Node of a tree.
#[derive(Derivative)]
#[derivative(Clone)]
pub struct Node<N>
	where
		N: TreeConf,
{
	/// A partial key contain in this node.
	/// TODO if implementing optimisation where key is stored with
	/// value only, this will still need to contain depth info and
	/// also maybe position of the closest child value (instert
	/// will need to query in depth to resolve key position in children).
	/// Can probably be gated behind an associated type in N.
	key: PrefixKey<NodeKeyBuff, AlignmentFor<N>>,

	/// A value if a value is stored for this node.
	value: Option<N::Value>,

	/// Children of this node
	children: N::Children,

	/// A backend for serializing the tree. `()` can be used if no serializing is needed.
	backend: N::Backend,
}

impl<N: TreeConf> Debug for Node<N> {
	fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
		"Node:".fmt(f)?;
		self.key.fmt(f)?;
		self.value.fmt(f)?;
		self.children.fmt(f)?;
		Ok(())
	}
}

impl<N: TreeConf> Node<N> {
	fn new_box(
		key: &[u8],
		start_position: PositionFor<N>,
		end_position: PositionFor<N>,
		value: Option<N::Value>,
		init: (),
		backend: N::Backend,
	) -> NodeBox<N> {
		Box::new(Self::new(key, start_position, end_position, value, init, backend))
	}

	fn children_from_backend(
		backend: &mut N::Backend,
	) -> N::Children {
		let mut children = N::Children::empty(backend.fetch_nb_children().unwrap_or(0));
		if N::Backend::ACTIVE && children.need_init_unfetched() {
			use crate::children::NodeIndex;
			let mut i = KeyIndexFor::<N>::zero();
			loop {
				if let Some(_) = backend.fetch_children_index(i) {
					let child = ChildFor::<N>::from_state(ChildState::Unfetched, None);
					children.set_child(i, child);
				}

				if let Some(n) = i.next() {
					i = n;
				} else {
					break;
				}
			}
		}
		children
	}
	
	fn new(
		key: &[u8],
		start_position: PositionFor<N>,
		end_position: PositionFor<N>,
		value: Option<N::Value>,
		_init: (),
		mut backend: N::Backend,
	) -> Node<N> {
		let children = Self::children_from_backend(&mut backend);
		Node {
			key: PrefixKey::new_offset(key, start_position, end_position),
			value,
			children,
			backend,
		}
	}

	fn new_box_unfetched(
		prefix: PrefixKey<NodeKeyBuff, AlignmentFor<N>>,
		mut backend: N::Backend,
	) -> NodeBox<N> {
		let children = Self::children_from_backend(&mut backend);
		Box::new(Node {
			key: prefix,
			value: None,
			children,
			backend,
		})
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
		// TODO comment and check for more efficient compare (maybe first next_by?).
		match common.cmp(dest_position_next) {
			Ordering::Equal => {
				let node_end_index = node_position.next_by::<N::Radix>(self.depth());
				if common == node_end_index {
					Descent::Match(common)
				} else {
					let ix = common.index::<N::Radix>(key);
					Descent::Middle(common, ix)
				}
			},
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
					unreachable!(); // This indicate some possible optimization.
					//Descent::Middle(common, None)
				} else {
					let ix = common.index::<N::Radix>(key);
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
	) -> Option<&N::Value> {
		if N::Backend::ACTIVE {
			panic!("Cannot fetch");
		}
		self.value.as_ref()
	}

	fn value_mut(
		&mut self,
	) -> Option<&mut N::Value> {
		if N::Backend::ACTIVE {
			match self.backend.value_state()  {
				ValueState::Unfetched => {
					if let Some(option_value) = self.backend.fetch_value() {
						self.value = option_value;
					}
				},
				_ => (),
			}
		}
		self.value.as_mut()
	}

	fn value_no_cache(
		&self,
	) -> Option<N::Value> {
		if !N::Backend::ACTIVE {
			panic!("No backend");
		}
		self.backend.fetch_value_no_cache()
	}

	fn set_value(
		&mut self,
		value: N::Value,
	) -> Option<N::Value> {
		if N::Backend::ACTIVE {
			self.backend.set_value_state(ValueState::Modified);
		}
		replace(&mut self.value, Some(value))
	}

	fn remove_value(
		&mut self,
		with_value: bool,
	) -> Option<N::Value> {
		if N::Backend::ACTIVE {
			if with_value {
				self.backend.fetch_value();
			}
			self.backend.set_value_state(ValueState::Deleted);
		}
		replace(&mut self.value, None)
	}

	fn number_child(
		&self,
	) -> usize {
		self.children.number_child()
	}

	fn get_child(
		&self,
		index: KeyIndexFor<N>,
	) -> Option<&Self> {
		if N::Backend::ACTIVE {
			panic!("Cannot fetch");
		}
		self.children.get_child(index).and_then(|c| c.node())
	}
	fn get_child_no_cache( // TODO useless except if backend non mutable no_cache get 
		&self,
		index: KeyIndexFor<N>,
	) -> Option<NodeBox<N>> {
		if !N::Backend::ACTIVE {
			panic!("No backend");
		}
		self.backend.fetch_children_no_cache(index)
	}

	fn has_child(
		&self,
		index: KeyIndexFor<N>,
	) -> bool {
		if !N::Backend::ACTIVE {
			return self.children.get_child(index).is_some();
		}
		if let Some(children) = self.children.get_child(index) {
			match children.state() {
				ChildState::Resolved => {
					children.node().is_some()
				},
				ChildState::Unfetched => {
					// Do not resolve child, just check for existing index.
					if let Some(_) = self.backend.fetch_children_index(index) {
						// do not fetch
						true
					} else {
						false
					}
				},
			}
		} else {
			false
		}
	}

	fn has_value(
		&self,
	) -> bool {
		if !N::Backend::ACTIVE {
			return self.value.is_some()
		}
		match self.backend.value_state() {
			ValueState::Unfetched => {
				self.backend.fetch_value_index().is_some()
			},
			_ => self.value.is_some(),
		}
	}
	
	fn get_child_mut(
		&mut self,
		index: KeyIndexFor<N>,
	) -> Option<&mut Box<Self>> {
		if let Some(Some(result)) = self.backend.fetch_children(index) {
			let result = ChildFor::<N>::from_state(ChildState::Resolved, Some(result));
			self.children.set_child(index, result);
		}
		self.children.get_child_mut(index).and_then(|c| c.node_mut())
	}

	fn get_child_mut_deref(
		&mut self,
		index: KeyIndexFor<N>,
	) -> Option<&mut Self> {
		self.get_child_mut(index).map(AsMut::as_mut)
	}

	fn set_child(
		&mut self,
		index: KeyIndexFor<N>,
		child: Box<Self>,
	) -> Option<Box<Self>> {
		self.backend.set_children_change();
		let child = ChildFor::<N>::from_state(ChildState::Resolved, Some(child));
		// TODO check is none when with backend? and don't return
		let result = self.children.set_child(index, child).and_then(|c| c.extract_node());
		if result.is_none() {
			self.children.increase_number();
		} else {
			unreachable!("should not set child on existing, set value in this case");
		}
		result
	}

	fn remove_child(
		&mut self,
		index: KeyIndexFor<N>,
	) -> Option<Box<Self>> {
		let result = self.children.remove_child(index).and_then(|c| c.extract_node());
		if result.is_some() {
			self.backend.set_children_change();
			self.children.decrease_number();
		}
		result
	}
	fn split_off(
		node: &mut Box<Self>,
		position: PositionFor<N>,
		mut at: PositionFor<N>,
		removed_node: &mut Vec<N::Backend>,
	) {
		at.index -= position.index;
		let index = node.key.index::<N::Radix>(at);
		let backend = N::new_node_backend(node.as_ref(), removed_node);

		let child_prefix = node.key.child_split_off::<N::Radix>(at);
		node.backend.set_prefix_change();
		let parent_prefix = replace(&mut node.key, child_prefix);
		let parent = Box::new(Node {
			key: parent_prefix,
			value: None,
			children: N::Children::empty(0),
			backend, 
		});
		let child = replace(node, parent);
		let child = ChildFor::<N>::from_state(ChildState::Resolved, Some(child));
		assert!(node.children.set_child(index, child).is_none());
		node.children.increase_number();
		node.backend.set_children_change();
	}

	fn fuse_child(
		node: &mut Box<Self>,
		removed_node: &mut Vec<N::Backend>,
	) {
		if let Some(index) = node.first_child_index() {
			// even with backend we do a removal in this case (cannot keep deleted).
			if let Some(child) = node.children.remove_child(index) {
				node.children.decrease_number();
				let position = PositionFor::<N> {
					index: 0,
					mask: node.key.start,
				};
				let position_start = position.next_by::<N::Radix>(node.depth());
				position_start.set_index::<N::Radix>(&mut node.key.data, index);
				let position_cat = position_start.next::<N::Radix>();
				let mut child = child.extract_node().expect("resolved on remove child");
				child.new_end(&mut node.key.data, position_cat);
				node.key.end = child.key.end;
				child.key = replace(&mut node.key, child.key);
				child.backend.set_prefix_change();
				let mut parent = replace(node, child);
				if N::Backend::ACTIVE {
					parent.backend.clear_content();
					removed_node.push(parent.backend);
				}
			} else {
				unreachable!("fuse condition checked");
			}
		} else {
			unreachable!("fuse condition checked");
		}
	}

	// TODO make it a trait function for Radix_conf? TODO reverse logic (update the other way)
	/// Push node partial on the current stacked key, given the node start position.
	fn new_end(&self, stack: &mut Key, node_position: PositionFor<N>) {
		let depth = self.depth();
		if depth == 0 {
			return;
		}
		if <N::Radix as RadixConf>::Alignment::ALIGNED {
			let new_len = node_position.index + depth;
			stack.resize(new_len, 0);
			&mut stack[node_position.index..new_len].copy_from_slice(self.key.data.borrow());
		} else {
			// exclusive end.
			let node_position_end = node_position.next_by::<N::Radix>(depth);
			let shift = if node_position_end.mask == MaskFor::<N::Radix>::FIRST {
				1
			} else {
				0
			};
			stack.resize(node_position_end.index + 1 - shift, 0);

			// TODO could also directly get first byte since prefix key should be updated correctly.
			// TODO maybe change prefix key code to never update byte??
			let start: u8 = self.key.start.mask_end_excl(stack[node_position.index]);
			// end index exclusive semantic.
			&mut stack[node_position.index..node_position_end.index + 1 - shift].copy_from_slice(self.key.data.borrow());
			// this requires that the stack end position is cleared
			stack[node_position.index] = self.key.start.mask_start(stack[node_position.index]) | start;
			if node_position_end.mask != MaskFor::<N::Radix>::FIRST {
				stack[node_position_end.index] = node_position_end.mask.mask_end_excl(stack[node_position_end.index]);
			};			
		}
	}

	fn partial_index(&self, node_offset_position: PositionFor<N>, position: PositionFor<N>) -> Option<KeyIndexFor<N>> {
		let mut position = position.clone();
		position.index -= node_offset_position.index;
		position.index::<N::Radix>(self.key.data.borrow())
	}

	// TODO useless? or change to get_next_children_index as in backend?
	fn first_child_index(
		&self,
	) -> Option<KeyIndexFor<N>> {
		use crate::children::NodeIndex; // TODO inefficient have next defined children index.
		let mut ix = KeyIndexFor::<N>::zero();
		loop {
			if self.has_child(ix) {
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

	/// When using backend, removed
	/// node can be reuse, and removal is only done on commit.
	#[derivative(Debug="ignore")]
	pub removed_node: Vec<N::Backend>,
}

impl<N> Default for Tree<N>
	where
		N: TreeConf,
		BackendFor<N>: Default,
{
	fn default() -> Self {
		Tree {
			tree: None,
			init: Default::default(),
			removed_node: Vec::new(),
		}
	}
}
	
impl<N> Tree<N>
	where
		N: TreeConf,
{
	/// Create a new empty tree.
	pub fn new(init: BackendFor<N>) -> Self {
		Tree {
			tree: None,
			init,
			removed_node: Vec::new(),
		}
	}
	
	/// Instantiate an existing tree from its serializing
	/// backend.
	pub fn from_backend(init: BackendFor<N>) -> Self {
		let tree =  N::Backend::get_root(&init);
		Tree {
			tree,
			init,
			removed_node: Vec::new(),
		}
	}

	/// Commit tree changes to its underlying serializing backend.
	pub fn commit(&mut self) {
		if let Some(mut node) = self.tree.as_mut() {
			for node in self.removed_node.drain(..) {
				N::Backend::delete(node);
			}
			// TODO here could/should apply fuse_node on all node (doing it lazilly
			// is sometime better: less child access). Should be define by
			// backend constant.
			if let Some(result) = N::Backend::commit_change(&mut node) {
				use crate::backends::Backend;
				node.backend.backend().set_root(result);
			}
		}
	}
}

#[derive(Derivative)]
#[derivative(Clone)]
#[derivative(Copy)]
enum Descent<P>
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
	/// TODO looks incorrect when reading descend function: same
	/// pos as child, or at least explicit why option.
	/// TODO add index of both key and next, then audit use!!
	/// Note that the value for both should be return by common fn.
	Middle(Position<P::Alignment>, Option<P::KeyIndex>),
	/// Position is child is at position + 1 of the branch.
	/// TODO is position of any use (it is dest position of descent)
	Match(Position<P::Alignment>),
}

macro_rules! tree_get {
	(
		$fn_name: ident,
		$get_child: ident,
		$as_ref: ident,
		$value: ident,
		$( $modifier: ident, )?
	) => {


impl<N: TreeConf> Tree<N> {
	/// Get reference to a tree value for a given key.
	pub fn $fn_name(& $($modifier)? self, key: &[u8]) -> Option<& $($modifier)? N::Value> {
		if let Some(top) = self.tree.$as_ref() {
			let mut current = top.$as_ref();
			// TODO is this limit condition of any use
			if key.len() == 0 {
				if current.depth() == 0 {
					return current.$value();
				} else {
					return None;
				}
			}
			let dest_position = Position {
				index: key.len(),
				mask: MaskFor::<N::Radix>::FIRST,
			};
			let mut position = PositionFor::<N>::zero();
			loop {
				match current.descend(key, position, dest_position) {
					Descent::Child(child_position, index) => {
						if let Some(child) = current.$get_child(index) {
							position = child_position.next::<N::Radix>();
							current = child;
						} else {
							return None;
						}
					},
					Descent::Middle(_position, _index) => {
						return None;
					},
					Descent::Match(_position) => {
						return current.$value();
					},
				}
			}
		} else {
			None
		}
	}
}


}}

tree_get!(
	get,
	get_child,
	as_ref,
	value,
);

tree_get!(
	get_mut,
	get_child_mut,
	as_mut,
	value_mut,
	mut,
);

impl<N: TreeConf> Tree<N> {
	/// Get reference to a tree value for a given key, do not cache backend query.
	pub fn get_no_cache(self, key: &[u8]) -> Option<N::Value> {
		if let Some(top) = self.tree {
			let mut current = top;
			// TODO is this limit condition of any use
			if key.len() == 0 {
				if current.depth() == 0 {
					return current.value_no_cache();
				} else {
					return None;
				}
			}
			let dest_position = Position {
				index: key.len(),
				mask: MaskFor::<N::Radix>::FIRST,
			};
			let mut position = PositionFor::<N>::zero();
			loop {
				match current.descend(key, position, dest_position) {
					Descent::Child(child_position, index) => {
						if let Some(child) = current.get_child_no_cache(index) {
							position = child_position.next::<N::Radix>();
							current = child;
						} else {
							return None;
						}
					},
					Descent::Middle(_position, _index) => {
						return None;
					},
					Descent::Match(_position) => {
						return current.value_no_cache();
					},
				}
			}
		} else {
			None
		}
	}

	/// Add new key value to the tree, and return previous value if any.
	pub fn insert(&mut self, key: &[u8], value: N::Value) -> Option<N::Value> {
		let dest_position = PositionFor::<N> {
			index: key.len(),
			mask: MaskFor::<N::Radix>::FIRST,
		};
		let mut position = PositionFor::<N>::zero();
		if let Some(top) = self.tree.as_mut() {
			let mut current: &mut NodeBox<N> = top;
			if key.len() == 0 && current.depth() == 0 {
				return current.set_value(value);
			}
			loop {
				match current.descend(key, position, dest_position) {
					Descent::Child(child_position, index) => {
						if current.has_child(index) { // has child for lifetime only
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
								N::new_node_backend(current, &mut self.removed_node),
							);
							assert!(current.set_child(index, new_child).is_none());
							current.backend.set_children_change();
							return None;
						}
					},
					Descent::Middle(middle_position, Some(index)) => {
						// insert middle node
						Node::<N>::split_off(current, position, middle_position, &mut self.removed_node);
						let child_start = middle_position.next::<N::Radix>();
						let new_child = Node::<N>::new_box(
							key,
							child_start,
							dest_position,
							Some(value),
							(),
							N::new_node_backend(current, &mut self.removed_node),
						);
						//let child_index = middle_position.index::<N::Radix>(key)
						//	.expect("Middle resolved from key");
						current.set_child(index, new_child);
						return None;
					},
					Descent::Middle(middle_position, None) => {
						// insert middle node
						Node::<N>::split_off(current, position, middle_position, &mut self.removed_node);
						// TODO need to put this set_value in a test code path.
						assert!(current.set_value(value).is_none());
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
				N::new_node_backend_root(&self.init, &mut self.removed_node),
			));
			None
		}
	}

	/// Remove value at a given location.
	pub fn remove(&mut self, key: &[u8], with_value: bool) -> Option<N::Value> {
		let mut position = PositionFor::<N>::zero();
		let mut empty_tree = None;
		if let Some(top) = self.tree.as_mut() {
			let current: &mut NodeBox<N> = top;
			if key.len() == 0 && current.depth() == 0 {
				let result = current.remove_value(with_value);
				if current.number_child() == 0 {
					empty_tree = Some(result);
				} else {
					if current.number_child() == 1 {
						Node::<N>::fuse_child(current, &mut self.removed_node);
					}
					return result;
				}
			}
			let dest_position = Position {
				index: key.len(),
				mask: MaskFor::<N::Radix>::FIRST,
			};
			if let Some(result) = empty_tree {
				self.tree = None;
				return result;
			}
			let mut parent = None;
			let mut current_ptr: *mut NodeBox<N> = current;
			loop {
				// Note that this can produce dangling pointer when removing
				// node.
				let current: &mut NodeBox<N> = unsafe { current_ptr.as_mut().unwrap() };
				match current.descend(key, position, dest_position) {
					Descent::Child(child_position, index) => {
						if let Some(child) = current.get_child_mut(index) {
							let old_position = child_position;
							position = child_position.next::<N::Radix>();
							current_ptr = child as *mut NodeBox<N>;
							parent = Some((current, old_position));
						} else {
							return None;
						}
					},
					Descent::Middle(_middle_position, _index) => {
						return None;
					},
					Descent::Match(_position) => {
						let result = current.remove_value(with_value);
						if current.number_child() == 0 {
							if let Some((parent, parent_position)) = parent {
								let parent_index = parent_position.index::<N::Radix>(key)
									.expect("was resolved from key");
								if let Some(mut removed) = parent.remove_child(parent_index) {
									if N::Backend::ACTIVE {
										removed.backend.clear_content();
										self.removed_node.push(removed.backend);
									}
								} else {
									unreachable!();
								}
								if !parent.has_value() && parent.number_child() == 1 {
									Node::<N>::fuse_child(parent, &mut self.removed_node);
								}
							} else {
								// root
								empty_tree = Some(result);
								break;
							}
						} else if current.number_child() == 1 {
							Node::<N>::fuse_child(current, &mut self.removed_node);
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

	/// Empty a tree from all its key values.
	pub fn clear(&mut self) {
		// TODO use iter mut.
		// TODO might not work with backend: consider just removal.
		let keys: Vec<_> = self.iter().value_iter().map(|v| v.0).collect();
		for key in keys {
			self.remove(key.as_slice(), false);
		}
	}
}

pub trait WithChildState<N> {
	fn state(&self) -> ChildState;
	fn state_mut(&mut self) -> &mut ChildState;
	fn from_state(state: ChildState, node: Option<Box<N>>) -> Self;
	fn extract_node(self) -> Option<Box<N>>;
	fn node(&self) -> Option<&N>;
	fn node_mut(&mut self) -> Option<&mut Box<N>>;
}

/// Different possible children state.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ChildState {
	/// Fetched state.
	Resolved,
	/// When runing on backend, this child need to be resolve
	/// from backend first.
	/// Could be an existing child or not.
	Unfetched,
}

/// Different possible value state.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ValueState {
	/// Unfetched
	Unfetched,
	/// Resolved
	Resolved,
	/// Modified
	Modified,
	/// Deleted.
	Deleted,
}

impl Default for ChildState {
	fn default() -> Self {
		ChildState::Unfetched
	}
}

impl<N> WithChildState<N> for Child<N> {
	fn state(&self) -> ChildState {
		self.1
	}

	fn state_mut(&mut self) -> &mut ChildState {
		&mut self.1
	}

	fn from_state(state: ChildState, node: Option<Box<N>>) -> Self {
		Child(node, state)
	}
	fn extract_node(self) -> Option<Box<N>> {
		assert!(self.1 != ChildState::Unfetched);
		self.0
	}
	fn node(&self) -> Option<&N> {
		self.0.as_ref().map(AsRef::as_ref)
	}
	fn node_mut(&mut self) -> Option<&mut Box<N>> {
		self.0.as_mut()
	}
}

impl<N> WithChildState<N> for Box<N> {
	fn state(&self) -> ChildState {
		ChildState::Resolved
	}

	fn state_mut(&mut self) -> &mut ChildState {
		unreachable!("only for active backends");
	}

	fn from_state(state: ChildState, node: Option<Box<N>>) -> Self {
		assert!(state == ChildState::Resolved);
		node.expect("Child with node")
	}
	fn extract_node(self) -> Option<Box<N>> {
		Some(self)
	}
	fn node(&self) -> Option<&N> {
		Some(self.as_ref())
	}
	fn node_mut(&mut self) -> Option<&mut Box<N>> {
		Some(self)
	}
}

// Node with state
#[derive(Derivative)]
#[derivative(Clone)]
#[derivative(Debug)]
pub struct Child<N>(Option<Box<N>>, ChildState);

impl<N> Default for Child<N> {
	fn default() -> Self {
		Child(None, Default::default())
	}
}

use crate::children::{Children256, ART48_256, Children16, Children4};
use crate::radix::impls::{Radix256Conf, Radix16Conf, Radix4Conf};

#[derive(Derivative)]
#[derivative(Clone)]
#[derivative(Debug)]
pub struct Node256NoBackend<V>(core::marker::PhantomData<V>);
impl <V: Value> TreeConf for Node256NoBackend<V> {
    type Radix = Radix256Conf;
    type Value = V;
    type Children = Children256<ChildFor<Self>>;
    type Backend = ();
}

#[derive(Derivative)]
#[derivative(Clone)]
#[derivative(Debug)]
pub struct Node256NoBackendART<V>(core::marker::PhantomData<V>);
impl <V: Value> TreeConf for Node256NoBackendART<V> {
    type Radix = Radix256Conf;
    type Value = V;
    type Children = ART48_256<ChildFor<Self>>;
    type Backend = ();
}

#[derive(Derivative)]
#[derivative(Clone)]
#[derivative(Debug)]
pub struct Node16NoBackend<V>(core::marker::PhantomData<V>);
impl <V: Value> TreeConf for Node16NoBackend<V> {
    type Radix = Radix16Conf;
    type Value = V;
    type Children = Children16<ChildFor<Self>>;
    type Backend = ();
}

#[derive(Derivative)]
#[derivative(Clone)]
#[derivative(Debug)]
pub struct Node4NoBackend<V>(core::marker::PhantomData<V>);
impl <V: Value> TreeConf for Node4NoBackend<V> {
    type Radix = Radix4Conf;
    type Value = V;
    type Children = Children4<ChildFor<Self>>;
    type Backend = ();
}

#[derive(Derivative)]
#[derivative(Clone)]
#[derivative(Debug)]
pub struct Node256TestBackendART<V>(core::marker::PhantomData<V>);
impl <V: Value + Codec> TreeConf for Node256TestBackendART<V> {
    type Radix = Radix256Conf;
    type Value = V;
    type Children = ART48_256<ChildFor<Self>>;
    type Backend = backends::NodeTestBackend<Self>;
}

#[derive(Derivative)]
#[derivative(Clone)]
#[derivative(Debug)]
pub struct Node256TestBackend<V>(core::marker::PhantomData<V>);
impl <V: Value + Codec> TreeConf for Node256TestBackend<V> {
    type Radix = Radix256Conf;
    type Value = V;
    type Children = Children256<ChildFor<Self>>;
    type Backend = backends::NodeTestBackend<Self>;
}

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

//! Different tree iterators and implementations.

// TODO remove code redundancy.

use super::{Tree, TreeConf, Node, PositionFor, Descent, Key, KeyIndexFor};
pub use derivative::Derivative;
use alloc::vec::Vec;
use crate::radix::{Position, MaskFor, MaskKeyByte};
use crate::children::NodeIndex;

/// Stack of Node to reach a position.
struct NodeStack<'a, N: TreeConf> {
	// TODO use smallvec instead?
	stack: Vec<(PositionFor<N>, &'a Node<N>)>,
	// The key used with the stack.
	// key: Vec<u8>,
}

impl<'a, N: TreeConf> NodeStack<'a, N> {
	fn new() -> Self {
		NodeStack {
			stack: Vec::new(),
		}
	}
}

impl<'a, N: TreeConf> NodeStack<'a, N> {
	// TODO useless??
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
struct NodeStackMut<N: TreeConf> {
	// TODO use smallvec instead?
	stack: Vec<(PositionFor<N>, *mut Node<N>)>,
	// The key used with the stack.
	// key: Vec<u8>,
}

impl<N: TreeConf> NodeStackMut<N> {
	fn new() -> Self {
		NodeStackMut {
			stack: Vec::new(),
		}
	}
}

impl<N: TreeConf> NodeStackMut<N> {
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

/// Stack of Node to reach a position.
struct IterStack<'a, N: TreeConf> {
	// TODO use smallvec instead
	// The index is the current index where to descend into if going
	// downward, or where we descend from if going upward.
	stack: Vec<(PositionFor<N>, &'a Node<N>, KeyIndexFor<N>)>,
	// The key used with the stack.
	key: Key,
}

/// Stack of Node to reach a position.
struct IterStackMut<N: TreeConf> {
	// TODO use smallvec instead
	// The index is the current index where to descend into if going
	// downward, or where we descend from if going upward.
	stack: Vec<(PositionFor<N>, *mut Node<N>, KeyIndexFor<N>)>,
	// The key used with the stack.
	key: Key,
}

impl<'a, N: TreeConf> IterStack<'a, N> {
	fn new() -> Self {
		IterStack {
			stack: Vec::new(),
			key: Default::default(),
		}
	}
}

impl<N: TreeConf> IterStackMut<N> {
	fn new() -> Self {
		IterStackMut {
			stack: Vec::new(),
			key: Default::default(),
		}
	}
}

/// Iterator on nodes that follows a given key (all nodes seeked
/// on the key path).
pub struct SeekIter<'a, N: TreeConf> {
	tree: &'a Tree<N>,
	dest: &'a [u8],
	dest_position: PositionFor<N>,
	// TODO seekiter could be lighter and avoid using stack, 
	// just keep latest: a stack trait could be use.
	stack: NodeStack<'a, N>,
	// state for next iter, we calculate it before
	// just to store position with node prefix.
	// TODO this is actually always a child variant
	next: Descent<N::Radix>,
	// part of state for next iter, not an item of descent
	// to avoid
	reach_dest: bool,
}

/// Iterator on values seeked when fetching a given key.
pub struct SeekValueIter<'a, N: TreeConf>(SeekIter<'a, N>);

impl<'a, N: TreeConf> SeekValueIter<'a, N> {
	/// Get back node iterator.
	pub fn node_iter(self) -> SeekIter<'a, N> {
		self.0
	}
}

impl<N: TreeConf> Tree<N> {
	/// Seek iteration following a giving key.
	pub fn seek_iter<'a>(&'a self, key: &'a [u8]) -> SeekIter<'a, N> {
		let dest_position = Position {
			index: key.len(),
			mask: MaskFor::<N::Radix>::LAST,
		};
		self.seek_iter_at(key, dest_position)
	}

	/// Seek iteration following a giving node key, a postion on the key is used for unalingned
	/// radix.
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


impl<'a, N: TreeConf> SeekIter<'a, N> {
	/// Node iterator from a seek iterator.
	/// This allow doing seek first then iterationg nodes
	/// with the same context.
	pub fn iter(mut self) -> Iter<'a, N> {
		let dest = self.dest;
		let mut finished = false;
		// corner case where seek iter skip a stack (alloc)
		if self.stack.stack.len() == 0 && self.dest.len() > 0 {
			if let Some(node) = self.tree.tree.as_ref() {
				if let Descent::Middle(..) = self.next {
					finished = true;
				} else {
					let zero = PositionFor::<N>::zero();
					self.stack.stack.push((zero, node));
				}
			}
		}

		let stack = self.stack.stack.into_iter().map(|(pos, node)| {
			let pos = pos.next_by::<N::Radix>(node.depth());
			let key = pos.index::<N::Radix>(dest)
				// out of dest we use the first child
				.unwrap_or_else(|| KeyIndexFor::<N>::zero());
			(pos, node, key)
		}).collect();
		Iter {
			tree: self.tree,
			stack: IterStack {
				stack,
				key: self.dest.into(),
			},
			finished,
		}
	}

	/// Node iterator from a seek iterator.
	/// This differs from `iter` because the iteration
	/// will only happen on nodes starting with the prefix
	/// of the current node for the seek iterator.
	pub fn iter_prefix(mut self) -> Iter<'a, N> {
		let dest = self.dest;
		let mut finished = false;
		// corner case where seek iter skip a stack (alloc)
		if self.stack.stack.len() == 0 && self.dest.len() > 0 {
			if let Some(node) = self.tree.tree.as_ref() {
				if let Descent::Middle(..) = self.next {
					finished = true;
				} else {
					let zero = PositionFor::<N>::zero();
					self.stack.stack.push((zero, node));
				}
			}
		}
		let stack = self.stack.stack.pop().map(|(pos, node)| {
			let pos = pos.next_by::<N::Radix>(node.depth());
			let key = pos.index::<N::Radix>(dest)
				.unwrap_or_else(|| KeyIndexFor::<N>::zero());
			(pos, node, key)
		}).into_iter().collect();
		Iter {
			tree: self.tree,
			stack: IterStack {
				stack,
				key: self.dest.into(),
			},
			finished,
		}
	}

	/// Get iterator only on value from respective node iterator.
	pub fn value_iter(self) -> SeekValueIter<'a, N> {
		SeekValueIter(self)
	}

	fn next_node(&mut self) -> Option<(PositionFor<N>, &'a Node<N>)> {
		if self.reach_dest {
			return None;
		}
		match self.next {
			Descent::Child(position, index) => {
				if let Some(parent) = self.stack.stack.last() {
					if let Some(child) = parent.1.get_child(index) {
						let position = position.next::<N::Radix>();
						match child.descend(
							&self.dest,
							position,
							self.dest_position,
						) {
							Descent::Middle(..) => {
								self.reach_dest = true;
								return None;
							},
							Descent::Match(..) => {
								self.reach_dest = true;
							},
							next@Descent::Child(..) => {
								self.next = next;
							},
						}
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
						match node.descend(
							&self.dest,
							zero,
							self.dest_position,
						) {
							Descent::Middle(position, index) => {
								// use for corner case when creating iter.
								if position != self.dest_position {
									self.next = Descent::Middle(position, index);
								}
								self.reach_dest = true;
								return None;
							},
							Descent::Match(..) => {
								self.reach_dest = true;
							},
							next@Descent::Child(..) => {
								self.next = next;
							},
						}
						self.stack.stack.push((zero, node));
					} else {
						self.reach_dest = true;
					}
				}
			},
			Descent::Middle(_position, _index) => {
				unreachable!();
			},
			Descent::Match(_position) => {
				unreachable!();
			},
		}
		self.stack.stack.last().map(|last| (last.0, last.1))
	}
}

impl<'a, N: TreeConf> Iterator for SeekIter<'a, N> {
	type Item = (&'a [u8], PositionFor<N>, &'a Node<N>);

	fn next(&mut self) -> Option<Self::Item> {
		self.next_node().map(|(pos, node)| (self.dest, pos, node))
	}
}

impl<'a, N: TreeConf> Iterator for SeekValueIter<'a, N> {
	type Item = (&'a [u8], &'a N::Value);

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			if let Some((key, pos, node)) = self.0.next() {
				if let Some(v) = node.value() {
					let pos = pos.next_by::<N::Radix>(node.depth());
					return Some((&key[..pos.index], v))
				}
			} else {
				return None;
			}
		}
	}
}

/// Mutable variant of seek iterator.
pub struct SeekIterMut<'a, N: TreeConf> {
	tree: &'a mut Tree<N>,
	dest: &'a [u8],
	dest_position: PositionFor<N>,
	// Here NodeStackMut will be used through unsafe
	// calls, but it should always be 'a with
	// content comming only form tree field.
	stack: NodeStackMut<N>,
	reach_dest: bool,
	next: Descent<N::Radix>,
}

pub struct SeekValueIterMut<'a, N: TreeConf>(SeekIterMut<'a, N>);
	
impl<N: TreeConf> Tree<N> {
	/// Seek nodes iterator over a given key with mutable access.
	pub fn seek_iter_mut<'a>(&'a mut self, key: &'a [u8]) -> SeekIterMut<'a, N> {
		let dest_position = Position {
			index: key.len(),
			mask: MaskFor::<N::Radix>::LAST,
		};
		self.seek_iter_at_mut(key, dest_position)
	}

	/// Variant of `seek_iter_mut` for key using a unaligned radix.
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

impl<'a, N: TreeConf> SeekIterMut<'a, N> {
	/// Get iterator only on value from respective node iterator.
	pub fn value_iter(self) -> SeekValueIterMut<'a, N> {
		SeekValueIterMut(self)
	}

	/// Get iterator on nodes from the seek iterator context.
	pub fn iter(mut self) -> IterMut<'a, N> {
		let dest = self.dest;
		let mut finished = false;
		// corner case where seek iter skip a stack (alloc)
		if self.stack.stack.len() == 0 && self.dest.len() > 0 {
			if let Some(node) = self.tree.tree.as_mut() {
				if let Descent::Middle(..) = self.next {
					finished = true;
				} else {
					let zero = PositionFor::<N>::zero();
					self.stack.stack.push((zero, node.as_mut()));
				}
			}
		}
		let stack = self.stack.stack.into_iter().map(|(pos, node)| {
			let node_depth = unsafe { node.as_mut().unwrap().depth() };
			let pos = pos.next_by::<N::Radix>(node_depth);
			let key = pos.index::<N::Radix>(dest)
				.unwrap_or_else(|| KeyIndexFor::<N>::zero());
			(pos, node, key)
		}).collect();
		IterMut {
			tree: self.tree,
			stack: IterStackMut {
				stack,
				key: self.dest.into(),
			},
			finished,
		}
	}

	/// Get iterator on nodes from the seek iterator context,
	/// and limit iteration do the seeked prefix.
	pub fn iter_prefix(mut self) -> IterMut<'a, N> {
		let dest = self.dest;
		let mut finished = false;
		// corner case where seek iter skip a stack (alloc)
		if self.stack.stack.len() == 0 && self.dest.len() > 0 {
			if let Some(node) = self.tree.tree.as_mut() {
				if let Descent::Middle(..) = self.next {
					finished = true;
				} else {
					let zero = PositionFor::<N>::zero();
					self.stack.stack.push((zero, node.as_mut()));
				}
			}
		}
		let stack = self.stack.stack.pop().map(|(pos, node)| {
			let node_depth = unsafe { node.as_mut().unwrap().depth() };
			let pos = pos.next_by::<N::Radix>(node_depth);
			let key = pos.index::<N::Radix>(dest)
				.unwrap_or_else(|| KeyIndexFor::<N>::zero());
			(pos, node, key)
		}).into_iter().collect();
		IterMut {
			tree: self.tree,
			stack: IterStackMut {
				stack,
				key: self.dest.into(),
			},
			finished,
		}
	}

	fn next_node(&mut self) -> Option<(PositionFor<N>, &'a mut Node<N>)> {
		if self.reach_dest {
			return None;
		}
		match self.next {
			Descent::Child(position, index) => {
				if let Some(parent) = self.stack.stack.last_mut() {
					if let Some(child) = unsafe {
						parent.1.as_mut().unwrap().get_child_mut(index) 
					} {
						let position = position.next::<N::Radix>();
						match child.descend(
							&self.dest,
							position,
							self.dest_position,
						) {
							Descent::Middle(..) => {
								self.reach_dest = true;
								return None;
							},
							Descent::Match(..) => {
								self.reach_dest = true;
							},
							next@Descent::Child(..) => {
								self.next = next;
							},
						}
						let child = child as *mut _;
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
						match node.descend(
							&self.dest,
							zero,
							self.dest_position,
						) {
							Descent::Middle(position, index) => {
								// use for corner case when creating iter.
								if position != self.dest_position {
									self.next = Descent::Middle(position, index);
								}
								self.reach_dest = true;
								return None;
							},
							Descent::Match(..) => {
								self.reach_dest = true;
							},
							next@Descent::Child(..) => {
								self.next = next;
							},
						}
						self.stack.stack.push((zero, node.as_mut()));
					} else {
						self.reach_dest = true;
					}
				}
			},
			Descent::Middle(_position, _index) => {
				unreachable!();
			},
			Descent::Match(_position) => {
				unreachable!();
			},
		}
		self.stack.stack.last().map(|last| (
			last.0,
			unsafe { last.1.as_mut().unwrap() },
		))
	}
}

impl<'a, N: TreeConf> Iterator for SeekIterMut<'a, N> {
	type Item = (&'a [u8], PositionFor<N>, &'a mut Node<N>);

	fn next(&mut self) -> Option<Self::Item> {
		self.next_node().map(|(pos, node)| (self.dest, pos, node))
	}
}

impl<'a, N: TreeConf> Iterator for SeekValueIterMut<'a, N> {
	type Item = (&'a [u8], &'a N::Value);

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			if let Some((key, pos, node)) = self.0.next() {
				if let Some(v) = node.value() {
					let pos = pos.next_by::<N::Radix>(node.depth());
					return Some((&key[..pos.index], v))
				}
			} else {
				return None;
			}
		}
	}
}

/// Iterator over the nodes of a tree.
pub struct Iter<'a, N: TreeConf> {
	tree: &'a Tree<N>,
	stack: IterStack<'a, N>,
	finished: bool,
}

/// Mutable aterator over the nodes of a tree.
pub struct IterMut<'a, N: TreeConf> {
	tree: &'a mut Tree<N>,
	stack: IterStackMut<N>,
	finished: bool,
}

/// Iterator over the values of a tree.
pub struct ValueIter<'a, N: TreeConf>(Iter<'a, N>);

/// Mutable iterator over the values of a tree.
pub struct ValueIterMut<'a, N: TreeConf>(IterMut<'a, N>);

impl<N: TreeConf> Tree<N> {
	/// Get node iterator for this tree.
	pub fn iter<'a>(&'a self) -> Iter<'a, N> {
		Iter {
			tree: self,
			stack: IterStack::new(),
			finished: false,
		}
	}

	/// Get mutable node iterator for this tree.
	pub fn iter_mut<'a>(&'a mut self) -> IterMut<'a, N> {
		IterMut {
			tree: self,
			stack: IterStackMut::new(),
			finished: false,
		}
	}
}

impl<'a, N: TreeConf> Iter<'a, N> {
	/// Get value iterator from this node iterator.
	pub fn value_iter(self) -> ValueIter<'a, N> {
		ValueIter(self)
	}

	fn next_node(&mut self) -> Option<(PositionFor<N>, &'a Node<N>)> {
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

impl<'a, N: TreeConf> IterMut<'a, N> {
	/// Get value iterator from this node iterator.
	pub fn value_iter_mut(self) -> ValueIterMut<'a, N> {
		ValueIterMut(self)
	}

	fn next_node(&mut self) -> Option<(PositionFor<N>, &'a mut Node<N>)> {
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
				let last_1 = unsafe { last.1.as_mut().unwrap() };
				// try descend
				if let Some(child) = last_1.get_child_mut(last.2) {
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
				if let Some(node) = self.tree.tree.as_mut() {
					let zero = PositionFor::<N>::zero();
					let first_key = KeyIndexFor::<N>::zero();
					node.new_end(&mut self.stack.key, zero);
					let zero = zero.next_by::<N::Radix>(node.depth());
					self.stack.stack.push((zero, node.as_mut(), first_key));
				} else {
					self.finished = true;
				}
				break;
			}
		}

		self.stack.stack.last_mut().map(|(p, n, _i)| (*p, unsafe { n.as_mut().unwrap() }))
	}
}

impl<'a, N: TreeConf> Iterator for Iter<'a, N> {
	// TODO key as slice, but usual lifetime issue.
	// TODO at leas use a stack type for key (smallvec).
	type Item = (Key, PositionFor<N>, &'a Node<N>);

	fn next(&mut self) -> Option<Self::Item> {
		self.next_node().map(|(p, n)| (self.stack.key.clone(), p, n))
	}
}

impl<'a, N: TreeConf> Iterator for IterMut<'a, N> {
	// TODO key as slice, but usual lifetime issue.
	// TODO at leas use a stack type for key (smallvec).
	type Item = (Key, PositionFor<N>, &'a mut Node<N>);

	fn next(&mut self) -> Option<Self::Item> {
		self.next_node().map(|(p, n)| (self.stack.key.clone(), p, n))
	}
}

impl<'a, N: TreeConf> Iterator for ValueIter<'a, N> {
	// TODO key as slice, but usual lifetime issue.
	// TODO at leas use a stack type for key (smallvec).
	type Item = (Key, &'a N::Value);

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

impl<'a, N: TreeConf> ValueIter<'a, N> {
	/// Get back node iterator.
	pub fn node_iter(self) -> Iter<'a, N> {
		self.0
	}
}

impl<'a, N: TreeConf> Iterator for ValueIterMut<'a, N> {
	// TODO key as slice, but usual lifetime issue (key being
	// build from multiple prefixes).
	// TODO return stack of keys that would require merge?
	// TODO at leas use a stack type for key (smallvec).
	type Item = (Key, &'a mut N::Value);

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			if let Some((mut key, pos, node)) = self.0.next() {
				if let Some(v) = node.value_mut() {
					key.truncate(pos.index);
					return Some((key, v))
				}
			} else {
				return None;
			}
		}
	}
}

/// Owned tree iterator.
///
/// Should be use when we want to keep iterator context
/// but don't want to manage associated lifetime.
///
/// This is an unsafe wrapper over `ValueIterMut`
/// (we use mutable version for backend supports).
///
/// Owned iterator do not modify the inner tree,
/// and iterated content is always cloned.
pub struct OwnedIter<N: TreeConf + 'static> {
	inner: Tree<N>,
	iter: ValueIterMut<'static, N>,
}

impl<N: TreeConf + 'static> OwnedIter<N> {
	/// After iteration, we can use back the
	/// tree content back.
	pub fn extract_inner(self) -> Tree<N> {
		let OwnedIter {
			inner,
			iter,
		} = self;
		drop(iter);
		inner
	}
}

impl<N: TreeConf> Tree<N> {
	/// Use tree as a value iterator.
	pub fn owned_iter(mut self) -> OwnedIter<N> {
		let self_ptr = &mut self as *mut Self;
		let unsafe_ptr: &'static mut Self = unsafe { self_ptr.as_mut().unwrap() };
		OwnedIter {
			inner: self,
			iter: ValueIterMut (
				IterMut {
					tree: unsafe_ptr,
					stack: IterStackMut::new(),
					finished: false,
				}
			),
		}
	}

	/// Use tree as a value iterator for keys starting with a given prefix.
	pub fn owned_prefix_iter(mut self, prefix: &[u8]) -> OwnedIter<N> {
		let self_ptr = &mut self as *mut Self;
		let unsafe_ptr: &'static mut Self = unsafe { self_ptr.as_mut().unwrap() };
		let static_prefix = prefix as *const [u8];
		let static_prefix: &'static [u8] = unsafe { static_prefix.as_ref().unwrap() };
		let mut seek_iter = unsafe_ptr.seek_iter_mut(static_prefix);
		while seek_iter.next().is_some() { }
		let iter = seek_iter.iter_prefix().value_iter_mut();
		OwnedIter {
			inner: self,
			iter,
		}
	}

	/// Use tree as a value iterator for keys starting with a given key.
	pub fn owned_iter_from(mut self, start_key: &[u8]) -> OwnedIter<N> {
		let self_ptr = &mut self as *mut Self;
		let unsafe_ptr: &'static mut Self = unsafe { self_ptr.as_mut().unwrap() };
		let static_prefix = start_key as *const [u8];
		let static_prefix: &'static [u8] = unsafe { static_prefix.as_ref().unwrap() };
		let mut seek_iter = unsafe_ptr.seek_iter_mut(static_prefix);
		while seek_iter.next().is_some() { }
		let iter = seek_iter.iter().value_iter_mut();
		OwnedIter {
			inner: self,
			iter,
		}
	}
}

impl<N: TreeConf + 'static> Iterator for OwnedIter<N> {
	type Item = (Key, N::Value);

	fn next(&mut self) -> Option<Self::Item> {
		self.iter.next().map(|(key, value)| (key, value.clone()))
	}
}

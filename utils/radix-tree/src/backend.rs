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

//! Use a backend for existing nodes.

use crate::{Node, PositionFor, Descent, KeyIndexFor, MaskFor,
	Position, MaskKeyByte, NodeIndex};
use alloc::vec::Vec;
use alloc::rc::Rc;
use core::marker::PhantomData;
use hashbrown::HashMap;
use codec::{Encode, Decode, Error as CodecError};
use core::cell::RefCell;
use core::fmt::Debug;
use derivative::Derivative;

type Key = Vec<u8>;

/// The backend to use for a tree.
pub trait Backend {
	fn write(&mut self, k: Vec<u8>, v: Vec<u8>);
	fn remove(&mut self, k: &[u8]);
	fn read(&self, k: &[u8]) -> Option<Vec<u8>>;
}

impl Backend for HashMap<Vec<u8>, Vec<u8>> {
	fn write(&mut self, k: Vec<u8>, v: Vec<u8>) {
		self.insert(k, v);
	}
	fn remove(&mut self, k: &[u8]) {
		self.remove(k);
	}
	fn read(&self, k: &[u8]) -> Option<Vec<u8>> {
		self.get(k).cloned()
	}
}

pub trait NodeBackend<N>: Clone {
	fn get_node(&self, k: &[u8]) -> Option<N>;
}

#[derive(Derivative)]
#[derivative(Clone(bound=""))]
struct SingleThreadBackend<B>(Rc<RefCell<B>>);

fn key_addressed<N: Node>(
	key: &[u8],
	start_postion: PositionFor<N>,
) -> Vec<u8> {
	unimplemented!();
}

fn key_from_addressed<N: Node>(
	key: &[u8],
) -> (&[u8], PositionFor<N>) {
	unimplemented!();
}

fn decode_node<N, B: Clone>(
	key: &[u8],
	mut encoded: &[u8],
	init: N::InitFrom,
	backend: &B,
) -> core::result::Result<N, CodecError>
	where
		N: Node,
		MaskFor<N::Radix>: Decode,
{
	let mut input = &mut encoded;
	let start_mask: MaskFor<N::Radix> = Decode::decode(input)?;
	let start = PositionFor::<N> {
		index: 0,
		mask: start_mask,
	};
	let end_mask: MaskFor<N::Radix> = Decode::decode(input)?;
	let prefix: Vec<u8> = Decode::decode(input)?;
	let end = if end_mask == MaskFor::<N::Radix>::first() {
		PositionFor::<N>  {
			index: prefix.len(),
			mask: end_mask,
		}
	} else {
		PositionFor::<N>  {
			index: prefix.len() - 1,
			mask: end_mask,
		}
	};

	let value: Option<Vec<u8>> = Decode::decode(input)?;
	let mut node = N::new(
		prefix.as_slice(),
		start,
		end,
		value,
		init,	
	);

	let mut key_index = KeyIndexFor::<N>::zero();
	let mut byte_index = 0;
	let mut input_index = 0;
	let mut child_key = key.to_vec();
	let child_position = end.next::<N::Radix>();
	loop {
		if let Some(children) = input.get(input_index) {
			if children & 0b1000_0000 >> byte_index != 0 {
				child_position.set_index::<N::Radix>(&mut child_key, key_index);
				let key = key_addressed(&child_key[..], child_position);
				node.set_child(key_index, LazyNode::Unresolved(UnresolvedBackedNode {
					key,
					backend: backend.clone(),
				}))
			}

			if byte_index == 8 {
				byte_index = 0;
				input_index += 1;
			}
			if let Some(i) = key_index.next() {
				key_index = i;
			} else {
				break;
			}
		} else {
			return Err("Incomplete node".into());
		}
	}

	Ok(node)
}

impl<B, N> NodeBackend<N> for SingleThreadBackend<B>
	where
		B: Backend,
		N: Node<InitFrom = ()>,
		MaskFor<N::Radix>: Decode,
{
	fn get_node(&self, k: &[u8]) -> Option<N> {
		self.0.borrow().read(k).and_then(|encoded| {
			decode_node(k, encoded.as_slice(), (), &self).ok()
		})
	}
}

/// The backend to use for a tree.
pub struct SynchBackend<B, N> {
	nodes: B,
	_ph: PhantomData<N>,
}

/// The backend to use for a tree.
pub struct TransactionBackend<B, N> {
	inner: SynchBackend<B, N>,
	changes: HashMap<Vec<u8>, N>,
}

#[derive(Derivative)]
#[derivative(Clone)]
#[derivative(PartialEq(bound="N: PartialEq"))]
#[derivative(Debug(bound="N: Debug"))]
/// Node using a backend
pub struct BackedNode<B, N> {
	inner: N,
	key: Key,
	changed: bool,
	#[derivative(Debug="ignore")]
	#[derivative(PartialEq="ignore")]
	backend: B,
}

#[derive(Derivative)]
#[derivative(Clone)]
#[derivative(PartialEq(bound=""))]
#[derivative(Debug(bound=""))]
/// Unresolved node.
///
/// Note  that `Eq` only works when
/// using the same backend (we do
/// not do backend equality check).
/// This is also true for `LazyNode`.
pub struct UnresolvedBackedNode<B> {
	key: Key,
	#[derivative(Debug="ignore")]
	#[derivative(PartialEq="ignore")]
	backend: B,
}

#[derive(Derivative)]
#[derivative(Clone)]
#[derivative(PartialEq(bound=""))]
#[derivative(Debug(bound=""))]
pub struct DeletedBackedNode<B> {
	key: Key,
	#[derivative(Debug="ignore")]
	#[derivative(PartialEq="ignore")]
	backend: B,
}

#[derive(Derivative)]
#[derivative(Clone)]
#[derivative(PartialEq(bound="N: PartialEq"))]
#[derivative(Debug(bound="N: Debug"))]
/// Resolved from backend on 
pub enum LazyNode<B, N> {
	Unresolved(UnresolvedBackedNode<B>),
	Resolved(BackedNode<B, N>),
	Deleted(DeletedBackedNode<B>), // TODO variant can be removed as it is not usable
}

impl<B, N> LazyNode<B, N>
	where
		B: NodeBackend<N>,
		N: Node<InitFrom = ()>,
		MaskFor<N::Radix>: Decode,
{
	fn resolve(&mut self) {
		match self {
			LazyNode::Unresolved(..) => (),
			LazyNode::Resolved(..) => return,
			LazyNode::Deleted(..) => panic!("can't resolve a deleted node"),
		};

		*self = match *self {
			LazyNode::Unresolved(
				UnresolvedBackedNode { key, backend }
			) => {
				let inner = backend.get_node(key.as_slice())
					.expect("Backend corrupted, missing tree node");

				LazyNode::Resolved(BackedNode {
					inner,
					key,
					changed: false,
					backend,
				})
			},
			LazyNode::Resolved(..) => return,
			LazyNode::Deleted(..) => panic!("can't resolve a deleted node"),
		};
	}
	fn delete(self) {
		let (key, backend) = match self {
			LazyNode::Unresolved(
				UnresolvedBackedNode { key, backend }
			) => (key, backend),
			LazyNode::Resolved(
				BackedNode { key, backend, .. }
			) => (key, backend),
			LazyNode::Deleted(..) => return,
		};
		self = LazyNode::Deleted(DeletedBackedNode {key, backend});
	}
	fn delete_clone(self) -> Self {
		let result = self.clone();
		self.delete();
		result
	}
	fn key_addressed(
		key: &[u8],
		start_postion: PositionFor<N>,
	) -> Vec<u8> {
		unimplemented!();
	}
	fn inner(&self) -> &N {
		match self {
			LazyNode::Resolved(BackedNode { inner, .. }) => &inner,
			_ => unimplemented!("Backend must be use as mutable due to lazy nature"),
		}
	}
	fn inner_mut(&mut self) -> &mut N {
		match self {
			LazyNode::Unresolved(..) => self.resolve(),
			LazyNode::Resolved(..) => (),
			LazyNode::Deleted(..) => panic!("Trying to access a deleted node"),
		}
		match self {
			LazyNode::Resolved(BackedNode { inner, .. }) => &mut inner,
			_ => unreachable!(),
		}
	}
	fn set_changed(&mut self) {
		match self {
			LazyNode::Unresolved(..) => self.resolve(),
			LazyNode::Resolved(..) => (),
			LazyNode::Deleted(..) => panic!("Trying to access a deleted node"),
		}
		match self {
			LazyNode::Resolved(BackedNode { changed, .. }) => {
				*changed = true;
			},
			_ => unreachable!(),
		}
	}
}

impl<B, N> Node for LazyNode<B, N>
	where
		B: NodeBackend<N>,
		N: Node<InitFrom = ()>,
		MaskFor<N::Radix>: Decode,
{
	type Radix = <N as Node>::Radix;
	type InitFrom = B;

	fn new(
		key: &[u8],
		start_position: PositionFor<Self>,
		end_position: PositionFor<Self>,
		value: Option<Vec<u8>>,
		init: Self::InitFrom,
	) -> Self {
		let inner = N::new(key, start_position, end_position, value, ());
		let key = Self::key_addressed(key, start_position);
		LazyNode::Resolved(BackedNode {
			inner,
			key,
			changed: true,
			backend: init,
		})
	}
	fn descend(
		&self,
		key: &[u8],
		node_position: PositionFor<Self>,
		// exclusive
		dest_position: PositionFor<Self>,
	) -> Descent<Self::Radix> {
		self.inner().descend(key, node_position, dest_position)
	}
	fn depth(
		&self,
	) -> usize {
		self.inner().depth()
	}
	fn value(
		&self,
	) -> Option<&[u8]> {
		self.inner().value()
	}
	fn value_mut(
		&mut self,
	) -> Option<&mut Vec<u8>> {
		self.set_changed();
		// TODO warn or unimplement, or safer api: this can create bad
		// overwrites
		self.inner_mut().value_mut()
	}
	fn set_value(
		&mut self,
		value: Vec<u8>,
	) -> Option<Vec<u8>> {
		self.set_changed();
		self.inner_mut().set_value(value)
	}
	fn remove_value(
		&mut self,
	) -> Option<Vec<u8>> {
		if self.inner().value().is_some() {
			self.set_changed();
			self.inner_mut().remove_value()
		} else {
			None
		}
	}
	fn number_child(
		&self,
	) -> usize {
		self.inner().number_child()
	}
	fn get_child(
		&self,
		index: KeyIndexFor<Self>,
	) -> Option<&Self> {
		unimplemented!("Backend must be use as mutable due to lazy nature");
	}
	fn set_child(
		&mut self,
		index: KeyIndexFor<Self>,
		child: Self,
	) -> Option<Self> {
		self.set_changed();
		self.inner_mut().set_child(index, child)
	}
	fn remove_child(
		&mut self,
		index: KeyIndexFor<Self>,
	) -> Option<Self> {
		if self.inner_mut().get_child(index).is_some() {
			self.set_changed();
			let result = self.inner_mut().remove_child();
			result.map(|node| node.delete_clone())
		} else {
			None
		}
	}
	fn fuse_child(
		&mut self,
		key: &[u8],
	) -> Option<Self> {
		self.set_changed();
		if let Some(child) = self.inner_mut().fuse_child(key) {
			child.delete();
		}
		None
	}
	fn split_off(
		&mut self,
		position: PositionFor<Self>,
		at: PositionFor<Self>,
	) {
		self.set_changed();
		self.inner_mut().split_off(position, at);
	}
	fn change_start(
		&mut self,
		key: &[u8],
		new_start: PositionFor<Self>,
	) {
		self.set_changed();
		self.inner_mut().change_start(key, new_start);
	}
	fn get_child_mut(
		&mut self,
		index: KeyIndexFor<Self>,
	) -> Option<&mut Self> {
		self.inner_mut().get_child_mut(index)
	}
	fn new_end(
		&self,
		stack: &mut Vec<u8>,
		node_position: PositionFor<Self>,
	) {
		self.set_changed();
		self.inner().new_end(stack, node_position)
	}
}

// Copyright 2015-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Parity is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Parity is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Parity.  If not, see <http://www.gnu.org/licenses/>.

//! `NodeCodec` implementation for Substrate's trie format.

use sp_std::marker::PhantomData;
use sp_std::ops::Range;
use sp_std::vec::Vec;
use sp_std::borrow::Borrow;
use codec::{Encode, Decode, Input, Compact};
use hash_db::Hasher;
use trie_db::{self, node::{NibbleSlicePlan, NodePlan, NodeHandlePlan}, ChildReference,
	nibble_ops, Partial, NodeCodec as NodeCodecT, BinaryHasher, Bitmap, BITMAP_LENGTH,
	NodeCodecHybrid, ChildProofHeader, HashesPlan, binary_additional_hashes,
};
use crate::error::Error;
use crate::trie_constants;
use super::{node_header::{NodeHeader, NodeKind}};

/// Helper struct for trie node decoder. This implements `codec::Input` on a byte slice, while
/// tracking the absolute position. This is similar to `std::io::Cursor` but does not implement
/// `Read` and `io` is not in `sp-std`.
struct ByteSliceInput<'a> {
	data: &'a [u8],
	offset: usize,
}

impl<'a> ByteSliceInput<'a> {
	fn new(data: &'a [u8]) -> Self {
		ByteSliceInput {
			data,
			offset: 0,
		}
	}

	fn take(&mut self, count: usize) -> Result<Range<usize>, codec::Error> {
		if self.offset + count > self.data.len() {
			return Err("out of data".into());
		}

		let range = self.offset..(self.offset + count);
		self.offset += count;
		Ok(range)
	}
}

impl<'a> Input for ByteSliceInput<'a> {
	fn remaining_len(&mut self) -> Result<Option<usize>, codec::Error> {
		let remaining = if self.offset <= self.data.len() {
			Some(self.data.len() - self.offset)
		} else {
			None
		};
		Ok(remaining)
	}

	fn read(&mut self, into: &mut [u8]) -> Result<(), codec::Error> {
		let range = self.take(into.len())?;
		into.copy_from_slice(&self.data[range]);
		Ok(())
	}

	fn read_byte(&mut self) -> Result<u8, codec::Error> {
		if self.offset + 1 > self.data.len() {
			return Err("out of data".into());
		}

		let byte = self.data[self.offset];
		self.offset += 1;
		Ok(byte)
	}
}

/// Concrete implementation of a `NodeCodec` with Parity Codec encoding, generic over the `Hasher`
#[derive(Default, Clone)]
pub struct NodeCodec<H>(PhantomData<H>);

impl<H: Hasher> NodeCodec<H> {
	fn decode_plan_internal(
		data: &[u8],
		is_proof: bool,
	) -> sp_std::result::Result<(NodePlan, usize), <Self as NodeCodecT>::Error> {
		let mut result_offset = 0;
		let mut input = ByteSliceInput::new(data);
		let node = match NodeHeader::decode(&mut input)? {
			NodeHeader::Null => NodePlan::Empty,
			NodeHeader::Branch(has_value, nibble_count) => {
				let padding = nibble_count % nibble_ops::NIBBLE_PER_BYTE != 0;
				// check that the padding is valid (if any)
				if padding && nibble_ops::pad_left(data[input.offset]) != 0 {
					return Err(Error::BadFormat);
				}
				let partial = input.take(
					(nibble_count + (nibble_ops::NIBBLE_PER_BYTE - 1)) / nibble_ops::NIBBLE_PER_BYTE,
				)?;
				let partial_padding = nibble_ops::number_padding(nibble_count);
				let bitmap_range = input.take(BITMAP_LENGTH)?;
				let bitmap = Bitmap::decode(&data[bitmap_range]);
				let value = if has_value {
					let count = <Compact<u32>>::decode(&mut input)?.0 as usize;
					Some(input.take(count)?)
				} else {
					None
				};
				result_offset = input.offset;
				let mut children = [
					None, None, None, None, None, None, None, None,
					None, None, None, None, None, None, None, None,
				];
				for i in 0..nibble_ops::NIBBLE_LENGTH {
					if bitmap.value_at(i) {
						if is_proof {
							children[i] = Some(NodeHandlePlan::Inline(Range { start: 0, end: 0 }));
						} else {
							let count = <Compact<u32>>::decode(&mut input)?.0 as usize;
							let range = input.take(count)?;
							children[i] = Some(if count == H::LENGTH {
								NodeHandlePlan::Hash(range)
							} else {
								NodeHandlePlan::Inline(range)
							});
						}
					}
				}
				NodePlan::NibbledBranch {
					partial: NibbleSlicePlan::new(partial, partial_padding),
					value,
					children,
				}
			}
			NodeHeader::Leaf(nibble_count) => {
				let padding = nibble_count % nibble_ops::NIBBLE_PER_BYTE != 0;
				// check that the padding is valid (if any)
				if padding && nibble_ops::pad_left(data[input.offset]) != 0 {
					return Err(Error::BadFormat);
				}
				let partial = input.take(
					(nibble_count + (nibble_ops::NIBBLE_PER_BYTE - 1)) / nibble_ops::NIBBLE_PER_BYTE,
				)?;
				let partial_padding = nibble_ops::number_padding(nibble_count);
				let count = <Compact<u32>>::decode(&mut input)?.0 as usize;
				let value = input.take(count)?;
				NodePlan::Leaf {
					partial: NibbleSlicePlan::new(partial, partial_padding),
					value,
				}
			}
		};
		Ok((node, result_offset))
	}

	fn branch_node_nibbled_internal(
		partial: impl Iterator<Item = u8>,
		number_nibble: usize,
		children: impl Iterator<
			Item = impl Borrow<Option<ChildReference<<Self as NodeCodecT>::HashOut>>>
		>,
		maybe_value: Option<&[u8]>,
		mut register_children: Option<&mut [Option<Range<usize>>]>,
		hybrid: bool,
		encode_children: bool,
	) -> (Vec<u8>, ChildProofHeader) {
		let mut output = if maybe_value.is_some() {
			partial_from_iterator_encode(
				partial,
				number_nibble,
				NodeKind::BranchWithValue,
			)
		} else {
			partial_from_iterator_encode(
				partial,
				number_nibble,
				NodeKind::BranchNoValue,
			)
		};
		let bitmap_index = output.len();
		let mut bitmap: [u8; BITMAP_LENGTH] = [0; BITMAP_LENGTH];
		(0..BITMAP_LENGTH).for_each(|_| output.push(0));
		if let Some(value) = maybe_value {
			value.encode_to(&mut output);
		};
		let mut ix = 0;
		let ix = &mut ix;
		let mut register_children = register_children.as_mut();
		let register_children = &mut register_children;
		let common = if encode_children && hybrid {
			ChildProofHeader::Range(Range {
				start: 0,
				end: output.len(),
			})
		} else {
			ChildProofHeader::Unused
		};

		let mut child_ix = output.len();
		Bitmap::encode(children.map(|maybe_child| match maybe_child.borrow() {
			Some(ChildReference::Hash(h)) => {
				if let Some(ranges) = register_children {
					// this assume scale codec put len on one byte, which is the
					// case for reasonable hash length.
					let encode_size_offset = 1;
					ranges[*ix] = Some(Range {
						start: child_ix + encode_size_offset,
						end: child_ix + encode_size_offset + h.as_ref().len(),
					});
					child_ix += encode_size_offset + h.as_ref().len();
					*ix += 1;
				}
				if encode_children {
					h.as_ref().encode_to(&mut output);
				}
				true
			}
			&Some(ChildReference::Inline(inline_data, len)) => {
				if let Some(ranges) = register_children {
					let encode_size_offset = 1;
					ranges[*ix] = Some(Range {
						start: child_ix + encode_size_offset,
						end: child_ix + encode_size_offset + len,
					});
					child_ix += encode_size_offset + len;
					*ix += 1;
				}
				if encode_children {
					inline_data.as_ref()[..len].encode_to(&mut output);
				}
				true
			}
			None => {
				if register_children.is_some() {
					*ix += 1;
				}
				false
			},
		}), bitmap.as_mut());
		output[bitmap_index..bitmap_index + BITMAP_LENGTH]
			.copy_from_slice(&bitmap.as_ref()[..BITMAP_LENGTH]);
		(output, common)
	}
}


impl<H: Hasher> NodeCodecT for NodeCodec<H> {
	type Error = Error;
	type HashOut = H::Out;

	fn decode_plan(data: &[u8]) -> sp_std::result::Result<NodePlan, Self::Error> {
		Ok(Self::decode_plan_internal(data, false)?.0)
	}

	fn hashed_null_node() -> <H as Hasher>::Out {
		H::hash(<Self as NodeCodecT>::empty_node())
	}

	fn is_empty_node(data: &[u8]) -> bool {
		data == <Self as NodeCodecT>::empty_node()
	}

	fn empty_node() -> &'static [u8] {
		&[trie_constants::EMPTY_TRIE]
	}

	fn leaf_node(partial: Partial, value: &[u8]) -> Vec<u8> {
		let mut output = partial_encode(partial, NodeKind::Leaf);
		value.encode_to(&mut output);
		output
	}

	fn extension_node(
		_partial: impl Iterator<Item = u8>,
		_nbnibble: usize,
		_child: ChildReference<<H as Hasher>::Out>,
	) -> Vec<u8> {
		unreachable!()
	}

	fn branch_node(
		_children: impl Iterator<Item = impl Borrow<Option<ChildReference<<H as Hasher>::Out>>>>,
		_maybe_value: Option<&[u8]>,
	) -> Vec<u8> {
		unreachable!()
	}

	fn branch_node_nibbled(
		partial: impl Iterator<Item = u8>,
		number_nibble: usize,
		children: impl Iterator<Item = impl Borrow<Option<ChildReference<<H as Hasher>::Out>>>>,
		maybe_value: Option<&[u8]>,
	) -> Vec<u8> {
		Self::branch_node_nibbled_internal(
			partial,
			number_nibble,
			children,
			maybe_value,
			None,
			false,
			true,
		).0
	}
}

impl<H: Hasher> NodeCodecHybrid for NodeCodec<H> {
	type AdditionalHashesPlan = HashesPlan;

	fn decode_plan_compact_proof(data: &[u8]) -> Result<(
		NodePlan,
		Option<(Bitmap, Self::AdditionalHashesPlan)>,
	), Self::Error> {
		let (mut node, mut offset) = Self::decode_plan_internal(data, true)?;

		let hashes_plan = match &mut node {
			NodePlan::Branch { children, .. }
				| NodePlan::NibbledBranch { children, .. } => {
				if data.len() < offset + 3 {
					return Err(codec::Error::from("Branch: missing proof headers").into());
				}
				let keys_position = Bitmap::decode(&data[offset..offset + BITMAP_LENGTH]);
				offset += BITMAP_LENGTH;

				let nb_additional;
				// read inline nodes.
				loop {
					let nb = data[offset] as usize;
					offset += 1;
					if nb >= 128 {
						nb_additional = nb - 128;
						break;
					}
					// 2 for inline index and next elt length.
					if data.len() < offset + nb + 2 {
						return Err(codec::Error::from("Branch: missing proof inline data").into());
					}
					let ix = data[offset] as usize;
					offset += 1;
					let inline = offset..offset + nb;
					if ix >= nibble_ops::NIBBLE_LENGTH {
						return Err(codec::Error::from("Branch: invalid inline index").into());
					}
					children[ix] = Some(NodeHandlePlan::Inline(inline));
					offset += nb;
				}
				let additional_len = nb_additional * H::LENGTH;
				if data.len() < offset + additional_len {
					return Err(codec::Error::from("Branch: missing child proof hashes").into());
				}
				Some((keys_position, HashesPlan::new(nb_additional, offset, H::LENGTH)))
			},
			_ => None,
		};
		Ok((node, hashes_plan))
	}

	fn branch_node_common(
		_children: impl Iterator<Item = impl Borrow<Option<ChildReference<<H as Hasher>::Out>>>>,
		_maybe_value: Option<&[u8]>,
		_register_children: Option<&mut [Option<Range<usize>>]>,
	) -> (Vec<u8>, ChildProofHeader) {
		unreachable!()
	}

	fn branch_node_nibbled_common(
		partial: impl Iterator<Item = u8>,
		number_nibble: usize,
		children: impl Iterator<Item = impl Borrow<Option<ChildReference<Self::HashOut>>>>,
		maybe_value: Option<&[u8]>,
		register_children: Option<&mut [Option<Range<usize>>]>,
	) -> (Vec<u8>, ChildProofHeader) {
		Self::branch_node_nibbled_internal(
			partial,
			number_nibble,
			children,
			maybe_value,
			register_children,
			true,
			true,
		)
	}

	fn branch_node_for_hash(
		_children: impl Iterator<Item = impl Borrow<Option<ChildReference<<H as Hasher>::Out>>>>,
		_maybe_value: Option<&[u8]>,
	) -> Vec<u8> {
		unreachable!()
	}

	fn branch_node_nibbled_for_hash(
		partial: impl Iterator<Item = u8>,
		number_nibble: usize,
		children: impl Iterator<Item = impl Borrow<Option<ChildReference<Self::HashOut>>>>,
		maybe_value: Option<&[u8]>,
	) -> Vec<u8> {
		Self::branch_node_nibbled_internal(
			partial,
			number_nibble,
			children,
			maybe_value,
			None,
			true,
			false,
		).0
	}

	fn encode_compact_proof<BH: BinaryHasher>(
		hash_proof_header: Vec<u8>,
		children: &[Option<ChildReference<BH::Out>>],
		in_proof: &[bool],
		hash_buf: &mut BH::Buffer,
	) -> Vec<u8> {
		let mut result = hash_proof_header;
		let bitmap_start = result.len();
		result.push(0u8);
		result.push(0u8);
		// Write all inline nodes.
		for (ix, child) in children.iter().enumerate() {
			if let Some(ChildReference::Inline(h, nb)) = child.borrow() {
				if *nb > 0 {
					if in_proof[ix] {
						debug_assert!(*nb < 128);
						result.push(*nb as u8);
						result.push(ix as u8);
						result.extend_from_slice(&h.as_ref()[..*nb]);
					}
				} else {
					debug_assert!(in_proof[ix]);
				}
			}
		}
		// We write a bitmap containing all children node that are included in the binary
		// child proof construction.
		// In practice, that is inline values and ommited compacted values).
		Bitmap::encode(in_proof.iter().map(|b| *b), &mut result[bitmap_start..]);

		let additional_hashes = binary_additional_hashes::<BH>(
			&children[..],
			&in_proof[..],
			hash_buf,
		);
		result.push((additional_hashes.len() as u8) | 128); // first bit at one indicates we are on additional hashes
		for hash in additional_hashes {
			result.extend_from_slice(hash.as_ref());
		}
		result
	}

	fn need_hybrid_proof(data: &[u8]) -> Result<Option<(NodePlan, ChildProofHeader)>, ()> {
		if data.len() > 0 {
			if NodeHeader::is_branch(data[0]) {
				let (node, offset) = Self::decode_plan_internal(data, false).map_err(|_| ())?;
				let header = ChildProofHeader::Range( Range {
					start: 0,
					end: offset,
				});
				return Ok(Some((node, header)))
			}
		}
		Ok(None)
	}

	fn codec_error(desc: &'static str) -> Self::Error {
		Error::Decode(desc.into())
	}
}

// utils

/// Encode and allocate node type header (type and size), and partial value.
/// It uses an iterator over encoded partial bytes as input.
fn partial_from_iterator_encode<I: Iterator<Item = u8>>(
	partial: I,
	nibble_count: usize,
	node_kind: NodeKind,
) -> Vec<u8> {
	let nibble_count = sp_std::cmp::min(trie_constants::NIBBLE_SIZE_BOUND, nibble_count);

	let mut output = Vec::with_capacity(3 + (nibble_count / nibble_ops::NIBBLE_PER_BYTE));
	match node_kind {
		NodeKind::Leaf => NodeHeader::Leaf(nibble_count).encode_to(&mut output),
		NodeKind::BranchWithValue => NodeHeader::Branch(true, nibble_count).encode_to(&mut output),
		NodeKind::BranchNoValue => NodeHeader::Branch(false, nibble_count).encode_to(&mut output),
	};
	output.extend(partial);
	output
}

/// Encode and allocate node type header (type and size), and partial value.
/// Same as `partial_from_iterator_encode` but uses non encoded `Partial` as input.
fn partial_encode(partial: Partial, node_kind: NodeKind) -> Vec<u8> {
	let number_nibble_encoded = (partial.0).0 as usize;
	let nibble_count = partial.1.len() * nibble_ops::NIBBLE_PER_BYTE + number_nibble_encoded;

	let nibble_count = sp_std::cmp::min(trie_constants::NIBBLE_SIZE_BOUND, nibble_count);

	let mut output = Vec::with_capacity(3 + partial.1.len());
	match node_kind {
		NodeKind::Leaf => NodeHeader::Leaf(nibble_count).encode_to(&mut output),
		NodeKind::BranchWithValue => NodeHeader::Branch(true, nibble_count).encode_to(&mut output),
		NodeKind::BranchNoValue => NodeHeader::Branch(false, nibble_count).encode_to(&mut output),
	};
	if number_nibble_encoded > 0 {
		output.push(nibble_ops::pad_right((partial.0).1));
	}
	output.extend_from_slice(&partial.1[..]);
	output
}

// This file is part of Substrate.

// Copyright (C) 2018-2020 Parity Technologies (UK) Ltd.
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

//! Substrate Blake2b Hasher implementation

pub mod blake2 {
	use hash_db::Hasher;
	use hash_db::BinaryHasher;
	use hash256_std_hasher::Hash256StdHasher;
	use crate::hash::H256;

	/// Concrete implementation of Hasher using Blake2b 256-bit hashes
	#[derive(Debug)]
	pub struct Blake2Hasher;

	impl Hasher for Blake2Hasher {
		type Out = H256;
		type StdHasher = Hash256StdHasher;
		const LENGTH: usize = 32;

		fn hash(x: &[u8]) -> Self::Out {
			crate::hashing::blake2_256(x).into()
		}
	}

	impl BinaryHasher for Blake2Hasher {
		const NULL_HASH: &'static [u8] = &[14, 87, 81, 192, 38, 229,
			67, 178, 232, 171, 46, 176, 96, 153, 218, 161, 209, 229, 223,
			71, 119, 143, 119, 135, 250, 171, 69, 205, 241, 47, 227, 168];
		type Buffer = blake2_rfc::blake2b::Blake2b;

		fn init_buffer() -> Self::Buffer {
			blake2_rfc::blake2b::Blake2b::new(32)
		}

		fn reset_buffer(buff: &mut Self::Buffer) {
			let _ = core::mem::replace(buff, Self::init_buffer());
		}

		fn buffer_hash(buff: &mut Self::Buffer, x: &[u8]) {
			buff.update(&x[..])
		}

		fn buffer_finalize(buff: &mut Self::Buffer) -> Self::Out {
			let mut res: H256 = Default::default();
			let k = core::mem::replace(buff, Self::init_buffer());
			res.as_mut().copy_from_slice(k.finalize().as_bytes());
			res
		}
	}

	#[cfg(feature = "std")]
	#[test]
	fn test_blake2b_hasher() {
		hash_db::test_binary_hasher::<Blake2Hasher>()
	}
}

pub mod keccak {
	use hash_db::Hasher;
	use hash_db::BinaryHasher;
	use hash256_std_hasher::Hash256StdHasher;
	use crate::hash::H256;
	use tiny_keccak::{Hasher as _, Keccak};

	/// Concrete implementation of Hasher using Keccak 256-bit hashes
	#[derive(Debug)]
	pub struct KeccakHasher;

	impl Hasher for KeccakHasher {
		type Out = H256;
		type StdHasher = Hash256StdHasher;
		const LENGTH: usize = 32;

		fn hash(x: &[u8]) -> Self::Out {
			crate::hashing::keccak_256(x).into()
		}
	}

	impl BinaryHasher for KeccakHasher {
		const NULL_HASH: &'static [u8] = &[197, 210, 70, 1, 134, 247, 35, 60, 146,
			126, 125, 178, 220, 199, 3, 192, 229, 0, 182, 83, 202, 130, 39, 59, 123,
			250, 216, 4, 93, 133, 164, 112];
		type Buffer = Keccak;

		fn init_buffer() -> Self::Buffer {
			Keccak::v256()
		}

		fn reset_buffer(buff: &mut Self::Buffer) {
			let _ = core::mem::replace(buff, Self::init_buffer());
		}

		fn buffer_hash(buff: &mut Self::Buffer, x: &[u8]) {
			buff.update(&x[..])
		}

		fn buffer_finalize(buff: &mut Self::Buffer) -> Self::Out {
			let mut res: H256 = Default::default();
			let k = core::mem::replace(buff, Self::init_buffer());
			k.finalize(res.as_mut());
			res
		}
	}

	#[cfg(feature = "std")]
	#[test]
	fn test_keccack_hasher() {
		hash_db::test_binary_hasher::<KeccakHasher>()
	}
}

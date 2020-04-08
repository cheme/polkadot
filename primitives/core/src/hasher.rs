// Copyright 2018-2020 Parity Technologies (UK) Ltd.
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
		const NULL_HASH: &'static [u8] = &[14, 87, 81, 192, 38, 229, 67,
		178, 232, 171, 46, 176, 96, 153, 218, 161, 209, 229, 223, 71, 119,
		143, 119, 135, 250, 171, 69, 205, 241, 47, 227, 168];
		type Buffer = hash_db::Buffer64;
	}

	#[test]
	fn test_blake_two_hasher() {
		hash_db::test_binary_hasher::<Blake2Hasher>()
	}
}

// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! Contract execution data.

#[cfg(feature = "std")]
use serde::{Serialize, Deserialize};
#[cfg(feature = "std")]
use crate::bytes;
use rstd::vec::Vec;
use parity_codec::{Encode, Decode};

/// Contract storage key.
#[derive(PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug, Hash, PartialOrd, Ord, Clone))]
pub struct StorageKey(#[cfg_attr(feature = "std", serde(with="bytes"))] pub Vec<u8>);

/// Contract storage entry data.
#[derive(PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug, Hash, PartialOrd, Ord, Clone))]
pub struct StorageData(#[cfg_attr(feature = "std", serde(with="bytes"))] pub Vec<u8>);

/// Storage change set
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug, PartialEq, Eq))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
pub struct StorageChangeSet<Hash> {
	/// Block hash
	pub block: Hash,
	/// A list of changes
	pub changes: Vec<(
		StorageKey,
		Option<StorageData>,
	)>,
}

/// Client next state behavior.
#[derive(Encode, Decode)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug, PartialEq, Eq))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
pub enum NextState {
	/// Do not reroot.
	Continue,

	/// A list of ordered reroot calls (first one takes it all).
	TryReroot(Vec<Reroot>),
}

impl Default for NextState {
	fn default() -> Self {
		NextState::Continue
	}
}

/// Reroot configuration.
#[derive(Encode, Decode)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug, PartialEq, Eq))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
pub struct Reroot {
	/// Target state root to use (block number).
	pub block_number: u64,
	/// Calls to make on initialized reroot before
	/// committing to it (switch next state value and
	/// applying revert block on pruning.
	pub payload: Vec<RerootPayLoad>,
}

/// Reroot payload to call on rerooted block.
#[derive(Encode, Decode)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug, PartialEq, Eq))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
pub struct RerootPayLoad {
	/// Method to call.
	pub method: String,
	/// Data payload for this call.
	pub data: Vec<u8>,
}

/// List of all well known keys and prefixes in storage.
pub mod well_known_keys {

	/// Wasm code of the runtime.
	///
	/// Stored as a raw byte vector. Required by substrate.
	pub const CODE: &'static [u8] = b":code";

	/// Number of wasm linear memory pages required for execution of the runtime.
	///
	/// The type of this value is encoded `u64`.
	pub const HEAP_PAGES: &'static [u8] = b":heappages";

	/// Current extrinsic index (u32) is stored under this key.
	pub const EXTRINSIC_INDEX: &'static [u8] = b":extrinsic_index";

	/// Next block state evaluation behavior.
	///
	/// Stored as a SCALED encoded `NextState`. Required by substrate.
	pub const NEXT_STATE: &'static [u8] = b":next_state";

	/// Changes trie configuration is stored under this key.
	pub const CHANGES_TRIE_CONFIG: &'static [u8] = b":changes_trie";

	/// Prefix of child storage keys.
	pub const CHILD_STORAGE_KEY_PREFIX: &'static [u8] = b":child_storage:";

	/// Whether a key is a child storage key.
	///
	/// This is convenience function which basically checks if the given `key` starts
	/// with `CHILD_STORAGE_KEY_PREFIX` and doesn't do anything apart from that.
	pub fn is_child_storage_key(key: &[u8]) -> bool {
		// Other code might depend on this, so be careful changing this.
		key.starts_with(CHILD_STORAGE_KEY_PREFIX)
	}
}

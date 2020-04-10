// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

//! Usage statistics

use codec::{Encode, Decode};
use crate::state_machine_stats::StateMachineStats;

/// Measured count of operations and total bytes.
#[derive(Clone, Debug, Default, Encode, Decode)]
pub struct UsageUnit {
	/// Number of operations.
	pub ops: u64,
	/// Number of bytes.
	pub bytes: u64,
}

// TODO EMCH consider saturating sub instead
impl sp_std::ops::Sub for UsageUnit {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
			UsageUnit {
				ops: self.ops - other.ops,
				bytes: self.bytes - other.bytes,
			}
    }
}

/// Usage statistics for state backend.
#[derive(Clone, Debug, Encode, Decode)]
pub struct UsageInfo {
	/// Read statistics (total).
	pub reads: UsageUnit,
	/// Write statistics (total).
	pub writes: UsageUnit,
	/// Write trie nodes statistics.
	pub nodes_writes: UsageUnit,
	/// Write into cached state machine
	/// change overlay.
	pub overlay_writes: UsageUnit,
	/// Removed trie nodes statistics.
	pub removed_nodes: UsageUnit,
	/// Cache read statistics.
	pub cache_reads: UsageUnit,
	/// Modified value read statistics.
	pub modified_reads: UsageUnit,
	/// Memory used.
	// Encoded as u64 because wasm's usize is u64.
	pub memory: u64,
}

// TODO EMCH consider saturating sub instead
impl sp_std::ops::Sub for UsageInfo {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
			UsageInfo {
				reads: self.reads - other.reads,
				writes: self.writes - other.writes,
				nodes_writes: self.nodes_writes - other.nodes_writes,
				overlay_writes: self.overlay_writes - other.overlay_writes,
				removed_nodes: self.removed_nodes - other.removed_nodes,
				cache_reads: self.cache_reads - other.cache_reads,
				modified_reads: self.modified_reads - other.modified_reads,
				memory: self.memory - other.memory,
			}
    }
}

impl UsageInfo {
	/// Empty statistics.
	///
	/// Means no data was collected.
	pub fn empty() -> Self {
		Self {
			reads: UsageUnit::default(),
			writes: UsageUnit::default(),
			overlay_writes: UsageUnit::default(),
			nodes_writes: UsageUnit::default(),
			removed_nodes: UsageUnit::default(),
			cache_reads: UsageUnit::default(),
			modified_reads: UsageUnit::default(),
			memory: 0,
		}
	}

	/// Add collected state machine to this state.
	pub fn include_state_machine_states(&mut self, count: &StateMachineStats) {
		self.modified_reads.ops += *count.reads_modified.borrow();
		self.modified_reads.bytes += *count.bytes_read_modified.borrow();
		self.overlay_writes.ops += *count.writes_overlay.borrow();
		self.overlay_writes.bytes += *count.bytes_writes_overlay.borrow();
	}
}

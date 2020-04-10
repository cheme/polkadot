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

//! Database usage statistics

use crate::{UsageInfo, UsageUnit};
use std::sync::Arc;
use parking_lot::RwLock;
use prometheus_endpoint::{
	Registry,
	Counter as PCounter,
	U64
};

#[cfg(not(feature = "disable-stats"))]
type IntCounter = PCounter<U64>;

#[cfg(feature = "disable-stats")]
type IntCounter = ();

#[derive(Clone)]
#[repr(transparent)]
struct Counter(IntCounter);

#[cfg(not(feature = "disable-stats"))]
impl Counter {
	#[inline]
	pub fn get(&self) -> u64 {
		self.0.get()
	}

	#[inline]
	pub fn inc(&self) {
		self.0.inc();
	}

	#[inline]
	pub fn inc_by(&self, value: u64) {
		self.0.inc_by(value);
	}

	// TODO EMCH this could help disable, but seems not usefull at this point
	#[inline]
	pub fn tally_value(&self, value: impl FnOnce() -> u64) {
		self.0.inc_by(value());
	}
}

#[cfg(feature = "disable-stats")]
impl Counter {
	#[inline]
	pub fn get(&self) -> u64 { 0 }

	#[inline]
	pub fn inc(&self) {	}

	#[inline]
	pub fn inc_by(&self, _value: u64) { }

	#[inline]
	pub fn tally_value(&self, _value: impl FnOnce() -> u64) { }
}

#[derive(Clone)]
/// Accumulated usage statistics for state queries.
pub struct StateUsageStats {
	counters: Arc<StateUsageStatsInternal>,
	last_take: Arc<RwLock<UsageInfo>>,
}

// TODO using prometheus IntCounterVec is probably way better.
// as it share Arc and better way to register.
struct StateUsageStatsInternal {
	reads: Counter,
	bytes_read: Counter,
	writes: Counter,
	bytes_written: Counter,
	writes_nodes: Counter,
	bytes_written_nodes: Counter,
	removed_nodes: Counter,
	bytes_removed_nodes: Counter,
	reads_cache: Counter,
	bytes_read_cache: Counter,

	/// Number of read query from runtime
	/// that hit a modified value (in state
	/// machine overlay).
	reads_modified: Counter,
	/// Size in byte of read queries that
	/// hit a modified value.
	bytes_read_modified: Counter,
	/// Number of time a write operation
	/// occurs into the state machine overlay.
	writes_overlay: Counter,
	/// Size in bytes of the writes overlay
	/// operation.
	bytes_writes_overlay: Counter,
}

impl StateUsageStatsInternal {
	fn stat_at(&self) -> UsageInfo {
		fn unit(ops: &Counter, bytes: &Counter) -> UsageUnit {
			UsageUnit {
				ops: ops.get(),
				bytes: bytes.get(),
			}
		}

		UsageInfo {
			reads: unit(&self.reads, &self.bytes_read),
			writes: unit(&self.writes, &self.bytes_written),
			nodes_writes: unit(&self.writes_nodes, &self.bytes_written_nodes),
			removed_nodes: unit(&self.removed_nodes, &self.bytes_removed_nodes),
			cache_reads: unit(&self.reads_cache, &self.bytes_read_cache),
			modified_reads: unit(&self.reads_modified, &self.bytes_read_modified),
			overlay_writes: unit(&self.writes_overlay, &self.bytes_writes_overlay),
			// TODO: Proper tracking state of memory footprint here requires
			//       imposing `MallocSizeOf` requirement on half of the codebase,
			//       so it is an open question how to do it better
			memory: 0,
		}
	}
}

/*
impl Collector for StateUsageStats {
}
*/
impl StateUsageStats {
	#[cfg(not(feature = "disable-stats"))]
	/// New empty usage stats.
	pub fn new(registry: Option<&Registry>) -> Self {
		let counters = Arc::new(StateUsageStatsInternal {
			reads: Counter(IntCounter::new("reads", "TODO help msg")
				.expect("TODO why can it fail??")),
			bytes_read: Counter(IntCounter::new("bytes_read", "TODO help msg")
				.expect("TODO why can it fail??")),
			writes: Counter(IntCounter::new("writes", "TODO help msg")
				.expect("TODO why can it fail??")),
			bytes_written: Counter(IntCounter::new("bytes_written", "TODO help msg")
				.expect("TODO why can it fail??")),
			writes_nodes: Counter(IntCounter::new("writes_nodes", "TODO help msg")
				.expect("TODO why can it fail??")),
			bytes_written_nodes: Counter(IntCounter::new("bytes_written_nodes", "TODO help msg")
				.expect("TODO why can it fail??")),
			removed_nodes: Counter(IntCounter::new("removed_nodes", "TODO help msg")
				.expect("TODO why can it fail??")),
			bytes_removed_nodes: Counter(IntCounter::new("bytes_removed_nodes", "TODO help msg")
				.expect("TODO why can it fail??")),
			reads_cache: Counter(IntCounter::new("reads_cache", "TODO help msg")
				.expect("TODO why can it fail??")),
			bytes_read_cache: Counter(IntCounter::new("bytes_read_cache", "TODO help msg")
				.expect("TODO why can it fail??")),
			reads_modified: Counter(IntCounter::new("reads_modified", "TODO help msg")
				.expect("TODO why can it fail??")),
			bytes_read_modified: Counter(IntCounter::new("bytes_read_modified", "TODO help msg")
				.expect("TODO why can it fail??")),
			writes_overlay: Counter(IntCounter::new("writes_overlay", "TODO help msg")
				.expect("TODO why can it fail??")),
			bytes_writes_overlay: Counter(IntCounter::new("bytes_writes_overlay", "TODO help msg")
				.expect("TODO why can it fail??")),
		});
		registry.map(|registry| {
			// TODO these all can return error: warn on error (shutting a process for missing stats
			// seems awkward).
			registry.register(Box::new(counters.reads.0.clone()));
			registry.register(Box::new(counters.bytes_read.0.clone()));
			registry.register(Box::new(counters.writes.0.clone()));
			registry.register(Box::new(counters.bytes_written.0.clone()));
			registry.register(Box::new(counters.writes_nodes.0.clone()));
			registry.register(Box::new(counters.bytes_written_nodes.0.clone()));
			registry.register(Box::new(counters.removed_nodes.0.clone()));
			registry.register(Box::new(counters.bytes_removed_nodes.0.clone()));
			registry.register(Box::new(counters.reads_cache.0.clone()));
			registry.register(Box::new(counters.bytes_read_cache.0.clone()));
			registry.register(Box::new(counters.reads_modified.0.clone()));
			registry.register(Box::new(counters.bytes_read_modified.0.clone()));
			registry.register(Box::new(counters.writes_overlay.0.clone()));
			registry.register(Box::new(counters.bytes_writes_overlay.0.clone()));
		});
		StateUsageStats {
			counters,
			last_take: Arc::new(RwLock::new(UsageInfo::empty())),
		}
	}

	#[cfg(feature = "disable-stats")]
	/// New empty usage stats.
	pub fn new(registry: &mut Registry) -> Self {
		let counters = Arc::new(StateUsageStatsInternal {
			reads: Counter(()),
			bytes_reads: Counter(()),
			writes: Counter(()),
			bytes_written: Counter(()),
			writes_nodes: Counter(()),
			bytes_written_nodes: Counter(()),
			removed_nodes: Counter(()),
			bytes_removed_nodes: Counter(()),
			reads_cache: Counter(()),
			bytes_reads_cache: Counter(()),
			reads_modified: Counter(()),
			bytes_read_modified: Counter(()),
			writes_overlay: Counter(()),
			bytes_writes_overlay: Counter(()),
		});
		StateUsageStats {
			counters,
			last_take: Default::default(),
		}
	}

	/// Tally one read operation, of some length.
	pub fn tally_read(&self, data_bytes: u64, cache: bool) {
		self.counters.reads.inc();
		self.counters.bytes_read.inc_by(data_bytes);
		if cache {
			self.counters.reads_cache.inc();
			self.counters.bytes_read_cache.inc_by(data_bytes);
		}
	}

	/// Tally one key read.
	pub fn tally_key_read(&self, key: &[u8], val: Option<&Vec<u8>>, cache: bool) {
		self.tally_read(key.len() as u64 + val.as_ref().map(|x| x.len() as u64).unwrap_or(0), cache);
	}

	/// Tally one child key read.
	pub fn tally_child_key_read(
		&self,
		key: &(Vec<u8>, Vec<u8>),
		val: Option<Vec<u8>>,
		cache: bool,
	) -> Option<Vec<u8>> {
		let bytes = key.0.len() + key.1.len() + val.as_ref().map(|x| x.len()).unwrap_or(0);
		self.tally_read(bytes as u64, cache);
		val
	}

	/// Tally some write trie nodes operations, including their byte count.
	pub fn tally_writes_nodes(&self, ops: u64, data_bytes: u64) {
		self.counters.writes_nodes.inc_by(ops);
		self.counters.bytes_written_nodes.inc_by(data_bytes);
	}

	/// Tally some removed trie nodes operations, including their byte count.
	pub fn tally_removed_nodes(&self, ops: u64, data_bytes: u64) {
		self.counters.removed_nodes.inc_by(ops);
		self.counters.bytes_removed_nodes.inc_by(data_bytes);
	}

	/// Tally some write key values operations, including their byte count.
	pub fn tally_writes(&self, ops: u64, data_bytes: u64) {
		self.counters.writes.inc_by(ops);
		self.counters.bytes_written.inc_by(data_bytes);
	}

	/// Returns the collected `UsageInfo` and resets the internal state.
	pub fn take(&self) -> crate::UsageInfo {
		let last = self.last_take.read().clone();
		// here all counter nay not be in synch but it is deemed negligeable
		let current =  self.counters.stat_at();
		*self.last_take.write() = current.clone();
		current - last
	}

	pub fn register_overlay_stats(&mut self, stats: &crate::StateMachineStats) {
		self.counters.reads_modified.inc_by(*stats.reads_modified.borrow());
		*stats.reads_modified.borrow_mut() = 0;
		self.counters.bytes_read_modified.inc_by(*stats.bytes_read_modified.borrow());
		*stats.bytes_read_modified.borrow_mut() = 0;
		self.counters.writes_overlay.inc_by(*stats.writes_overlay.borrow());
		*stats.writes_overlay.borrow_mut() = 0;
		self.counters.bytes_writes_overlay.inc_by(*stats.bytes_writes_overlay.borrow());
		*stats.bytes_writes_overlay.borrow_mut() = 0;
	}
}

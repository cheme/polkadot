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

//! State access loggers.
//!
//! When optimistic worker is runnig, we logg our externalities access to be able
//! to resolve if the assumptions are correct on `join`.
//!
//! It is plugged in the overlay by commodity, but could be at a higher level.
//!
//! TODO checks method should be rewrite by zip iterating on all sorted components,
//! and maintaining a streaming state machine,
//! this would also require a 'jump_to' instruction on tree iterator.

use sp_externalities::{WorkerResult, TaskId, StateLog};
use sp_std::collections::btree_set::BTreeSet;
#[cfg(feature = "std")]
use std::collections::HashMap as Map;
#[cfg(not(feature = "std"))]
use sp_std::collections::btree_map::BTreeMap as Map;
use crate::overlayed_changes::radix_trees::AccessTreeWrite;
use sp_core::storage::ChildInfo;
use super::{StorageKey, retain_map};
use sp_std::vec::Vec;

/// Origin for the log.
/// None when the log is for the lifetime of the worker or
/// a children running id when this is related to a children
/// worker.
#[derive(Debug, Clone, Default)]
pub(crate) struct OriginLog {
	// required for received children comparison.
	pub children: BTreeSet<TaskId>,
	// required to send to parent worker.
	pub parent: bool,
}

impl OriginLog {
	fn insert(&mut self, task: Option<TaskId>) {
		if let Some(task) = task {
			self.children.insert(task);
		} else {
			self.parent = true;
		}
	}

	fn remove(&mut self, task: TaskId) -> bool {
		self.children.remove(&task)
	}

	fn contains(&self, task: TaskId) -> bool {
		self.children.contains(&task)
	}

	fn is_empty(&self) -> bool {
		!self.parent && self.children.is_empty()
	}
}


#[derive(Debug, Clone, Default)]
pub(super) struct AccessLogger {
	/// Log that we access all key in read mode (usually by calling storage root).
	/// TODO this should be implied by parent_log_read??
	read_all: OriginLog,
	/// Keep trace of read logging required to compare with children
	/// logged access.
	log_read: OriginLog,
	/// Keep trace of write logging required to compare with children
	/// logged access.
	log_write: OriginLog,
	/// Keep trace of append logging required to compare with children
	/// logged access.
	log_append: OriginLog,
	/// Access logger for top trie.
	top_logger: StateLogger,
	/// Access logger for children trie.
	children_logger: Map<StorageKey, StateLogger>,
	// TODO unused except in test.
	eager_clean: bool,
}

/// Logger for a given trie state.
#[derive(Debug, Clone, Default)]
struct StateLogger {
	read_keys: Map<Vec<u8>, OriginLog>,
	// Intervals are inclusive for start and end.
	read_intervals: Map<(Vec<u8>, Option<Vec<u8>>), OriginLog>,
	write_keys: Map<Vec<u8>, OriginLog>,
	// this is roughly clear prefix.
	write_prefixes: AccessTreeWrite,
	// could be same container as write
	append_keys: Map<Vec<u8>, OriginLog>,
}

impl StateLogger {
	fn remove_all_read_logs(&mut self) {
		self.read_keys.clear();
		self.read_intervals.clear();
	}

	fn remove_all_write_logs(&mut self) {
		self.write_keys.clear();
		self.write_prefixes.clear();
	}

	fn remove_all_append_logs(&mut self) {
		self.append_keys.clear();
	}

	// TODO this seems costy, check usage.
	fn remove_children_read_logs(&mut self, marker: TaskId) {
		retain_map(&mut self.read_keys, |_key, value| {
			value.remove(marker);
			!value.is_empty()
		});
		retain_map(&mut self.read_intervals, |_key, value| {
			value.remove(marker);
			!value.is_empty()
		});
	}

	// TODO this seems costy, check usage.
	fn remove_children_write_logs(&mut self, marker: TaskId) {
		retain_map(&mut self.write_keys, |_key, value| {
			value.remove(marker);
			!value.is_empty()
		});
		let mut to_remove = Vec::new();
		for (key, value) in self.write_prefixes.iter_mut().value_iter() {
			value.remove(marker);
			if value.is_empty() {
				to_remove.push(key.to_vec())
			}
		}
		for key in to_remove.into_iter() {
			self.write_prefixes.remove(&key);
		}
	}

	fn remove_children_append_logs(&mut self, marker: TaskId) {
		retain_map(&mut self.append_keys, |_key, value| {
			value.remove(marker);
			!value.is_empty()
		});
	}

	// TODO is it of any use: involve full iter if empty so
	// doing it is as good?
	fn is_children_read_empty(&self, marker: TaskId) -> bool {
		for (_, ids) in self.read_keys.iter() {
			if ids.contains(marker) {
				return false;
			}
		}
		for (_, ids) in self.read_intervals.iter() {
			if ids.contains(marker) {
				return false;
			}
		}
		true
	}

	fn is_children_write_empty(&self, marker: TaskId) -> bool {
		for (_, ids) in self.write_keys.iter() {
			if ids.contains(marker) {
				return false;
			}
		}
		for (_, ids) in self.write_prefixes.iter().value_iter() {
			if ids.contains(marker) {
				return false;
			}
		}
		true
	}

	fn is_children_append_empty(&self, marker: TaskId) -> bool {
		for (_, ids) in self.append_keys.iter() {
			if ids.contains(marker) {
				return false;
			}
		}
		true
	}

	// compare write/append from parent (`self`) against read from child (`access`).
	fn check_child_read(&self, access: &StateLog, marker: TaskId) -> bool {
		for key in access.read_keys.iter() {
			if !self.check_key_against_write(key, marker) {
				return false;
			}
			if !self.check_key_against_append(key, marker) {
				return false;
			}
		}
		for interval in access.read_intervals.iter() {
			if !self.check_interval_against_write(interval, marker) {
				return false;
			}
			if !self.check_interval_against_append(interval, marker) {
				return false;
			}
		}
		true
	}

	// compare any access from parent (`self`) against write from child (`access`).
	fn check_child_write(&self, access: &StateLog, marker: TaskId) -> bool {
		for key in access.write_keys.iter() {
			if !self.check_key_against_read(key, marker) {
				return false;
			}
			if !self.check_key_against_write(key, marker) {
				return false;
			}
			if !self.check_key_against_append(key, marker) {
				return false;
			}
		}
		// Here ordering prefix could be use to optimize check (skiping child of a given prefix).
		for prefix in access.write_prefix.iter() {
			if !self.check_prefix_against_read(prefix, marker) {
				return false;
			}
			if !self.check_prefix_against_write(prefix, marker) {
				return false;
			}
			if !self.check_prefix_against_append(prefix, marker) {
				return false;
			}
		}
		true
	}

	// compare read or write from parent (`self`) against append from child (`access`).
	fn check_child_append(&self, access: &StateLog, marker: TaskId) -> bool {
		for key in access.append_keys.iter() {
			if !self.check_key_against_read(key, marker) {
				return false;
			}
			if !self.check_key_against_write(key, marker) {
				return false;
			}
		}
		true
	}

	fn check_key_against_append(&self, read_key: &Vec<u8>, marker: TaskId) -> bool {
		if let Some(ids) = self.append_keys.get(read_key) {
			if ids.contains(marker) {
				return false;
			}
		}
		true
	}

	fn check_key_against_write(&self, read_key: &Vec<u8>, marker: TaskId) -> bool {
		if let Some(ids) = self.write_keys.get(read_key) {
			if ids.contains(marker) {
				return false;
			}
		}
		for (_prefix, ids) in self.write_prefixes.seek_iter(read_key.as_slice()).value_iter() {
			if ids.contains(marker) {
				return false;
			}
		}
		true
	}

	fn check_key_against_read(&self, write_key: &Vec<u8>, marker: TaskId) -> bool {
		if let Some(ids) = self.read_keys.get(write_key) {
			if ids.contains(marker) {
				return false;
			}
		}
		// TODO this needs proper children_read_intervals structure.
		for ((start, end), ids) in self.read_intervals.iter() {
			if write_key >= start && end.as_ref().map(|end| write_key <= end).unwrap_or(true) {
				if ids.contains(marker) {
					return false;
				}
			}
		}
		true
	}

	fn check_prefix_against_append(&self, prefix: &Vec<u8>, marker: TaskId) -> bool {
		// TODO here could benefit from a seek then iter.
		let mut first = false;
		for (key, ids) in self.append_keys.iter() {
			if key.starts_with(prefix) {
				if ids.contains(marker) {
					return false;
				} else {
					first = true;
				}
			} else if first {
				break;
			}
		}
		true
	}

	fn check_prefix_against_write(&self, prefix: &Vec<u8>, marker: TaskId) -> bool {
		// TODO here could benefit from a seek then iter.
		let mut first = false;
		for (key, ids) in self.write_keys.iter() {
			if key.starts_with(prefix) {
				if ids.contains(marker) {
					return false;
				} else {
					first = true;
				}
			} else if first {
				break;
			}
		}
		let mut iter = self.write_prefixes.seek_iter(prefix).value_iter();
		while let Some((_prefix, ids)) = iter.next() {
			if ids.contains(marker) {
				return false;
			}
		}
		for (_key, ids) in iter.node_iter().iter_prefix().value_iter() {
			if ids.contains(marker) {
				return false;
			}
		}
		true
	}

	fn check_prefix_against_read(&self, prefix: &Vec<u8>, marker: TaskId) -> bool {
		// TODO here could benefit from a seek then iter.
		let mut first = false;
		for (key, ids) in self.read_keys.iter() {
			if key.starts_with(prefix) {
				if ids.contains(marker) {
					return false;
				} else {
					first = true;
				}
			} else if first {
				break;
			}
		}
		// TODO this needs proper children_read_intervals structure.
		for ((start, end), ids) in self.read_intervals.iter() {
			if prefix.len() == 0
				|| start.starts_with(prefix)
				|| end.as_ref().map(|end| end.starts_with(prefix)).unwrap_or(false)
				|| (prefix >= start && end.as_ref().map(|end| prefix <= end).unwrap_or(true)) {
				if ids.contains(marker) {
					return false;
				}
			}
		}
		true
	}

	fn check_interval_against_append(
		&self,
		interval: &(Vec<u8>, Option<Vec<u8>>),
		marker: TaskId,
	) -> bool {
		// Could use a seek to start here, but this
		// (check read access on write) is a marginal use case
		// so not switching write_key to radix_tree at the time.
		for (key, ids) in self.write_keys.iter() {
			if interval.1.as_ref().map(|end| key > end).unwrap_or(false) {
				break;
			}
			if key >= &interval.0 && ids.contains(marker) {
				return false;
			}
		}
		true
	}
	
	fn check_interval_against_write(
		&self,
		interval: &(Vec<u8>, Option<Vec<u8>>),
		marker: TaskId,
	) -> bool {
		// Could use a seek to start here, but this
		// (check read access on write) is a marginal use case
		// so not switching write_key to radix_tree at the time.
		for (key, ids) in self.write_keys.iter() {
			if interval.1.as_ref().map(|end| key > end).unwrap_or(false) {
				break;
			}
			if key >= &interval.0 && ids.contains(marker) {
				return false;
			}
		}
		let mut iter = self.write_prefixes.seek_iter(interval.0.as_slice()).value_iter();
		while let Some((_prefix, ids)) = iter.next() {
			if ids.contains(marker) {
				return false;
			}
		}
		// TODO here we really should merge redundant/contigus intervals on insert.
		for (key, ids) in iter.node_iter().iter().value_iter() {
			if interval.1.as_ref().map(|end| &key > end).unwrap_or(false) {
				break;
			}
			// This is can do some check twice (all write prefix that are contained
			// by start, as they also where in seek iter)
			if ids.contains(marker) {
				return false;
			}
		}
		true
	}
}

impl AccessLogger {
	fn is_children_read_empty(&self, marker: TaskId) -> bool {
		if !self.top_logger.is_children_read_empty(marker) {
			return false;
		}
		for child_logger in self.children_logger.iter() {
			if !child_logger.1.is_children_read_empty(marker) {
				return false;
			}
		}

		true
	}

	fn is_children_write_empty(&self, marker: TaskId) -> bool {
		if !self.top_logger.is_children_write_empty(marker) {
			return false;
		}
		for child_logger in self.children_logger.iter() {
			if !child_logger.1.is_children_write_empty(marker) {
				return false;
			}
		}

		true
	}

	fn is_children_append_empty(&self, marker: TaskId) -> bool {
		if !self.top_logger.is_children_append_empty(marker) {
			return false;
		}
		for child_logger in self.children_logger.iter() {
			if !child_logger.1.is_children_append_empty(marker) {
				return false;
			}
		}

		true
	}

	pub(super) fn log_writes_against(&mut self, children: Option<TaskId>) {
		self.log_write.insert(children);
	}

	pub(super) fn log_appends_against(&mut self, children: Option<TaskId>) {
		self.log_append.insert(children);
	}

	pub(super) fn log_reads_against(&mut self, children: Option<TaskId>) {
		self.log_read.insert(children);
	}

	pub(super) fn on_worker_result(&mut self, result: &WorkerResult) -> bool {
		match result {
			WorkerResult::CallAt(_result, _delta, marker) => {
				// should not be usefull here
				self.remove_worker(*marker);
				true
			},
			WorkerResult::Optimistic(_result, _delta, marker, accesses) => {
				let result = || -> bool {
					let has_read_child = accesses.has_read();
					let has_write_child = accesses.has_write();
					let has_append_child = accesses.has_append();
//					let has_append_parent = !self.is_children_append_empty(*marker);

					if has_read_child {
						if accesses.read_all {
							if !self.is_children_write_empty(*marker) {
								return false;
							}
							if !self.is_children_append_empty(*marker) {
								return false;
							}
						} else {
							if !self.top_logger.check_child_read(&accesses.top_logger, *marker) {
								return false;
							}
							for (storage_key, child_logger) in accesses.children_logger.iter() {
								if let Some(access_logger) = self.children_logger.get(storage_key) {
									if !access_logger.check_child_read(child_logger, *marker) {
										return false;
									}
								}
							}
						}
					}
					if has_write_child {
						if self.read_all.parent {
							return false;
						}
						if !self.top_logger.check_child_write(&accesses.top_logger, *marker) {
							return false;
						}
						for (storage_key, child_logger) in accesses.children_logger.iter() {
							if let Some(access_logger) = self.children_logger.get(storage_key) {
								if !access_logger.check_child_write(child_logger, *marker) {
									return false;
								}
							}
						}
					}
					if has_append_child {
						if self.read_all.parent {
							return false;
						}
						if !self.top_logger.check_child_append(&accesses.top_logger, *marker) {
							return false;
						}
						for (storage_key, child_logger) in accesses.children_logger.iter() {
							if let Some(access_logger) = self.children_logger.get(storage_key) {
								if !access_logger.check_child_append(child_logger, *marker) {
									return false;
								}
							}
						}
					}

					// merge accesses with parent if needed
					if self.log_write.parent {
						// relative to the current three configs when write is logged for child, it is also for
						// parent.
						for key in accesses.top_logger.write_keys.iter() {
							self.log_write(None, key.as_slice());
						}
						for key in accesses.top_logger.write_prefix.iter() {
							self.log_write_prefix(None, key.as_slice());
						}
						for (storage_key, child_logger) in accesses.children_logger.iter() {
							for key in child_logger.write_keys.iter() {
								self.log_write_storage_key(Some(storage_key.as_slice()), key.as_slice());
							}
							for key in child_logger.write_prefix.iter() {
								self.log_write_prefix_storage_key(Some(storage_key.as_slice()), key.as_slice());
							}
						}
					}
					if self.log_append.parent {
						// relative to the current three configs when write is logged for child, it is also for
						// parent.
						for key in accesses.top_logger.append_keys.iter() {
							self.log_append(None, key.as_slice());
						}
						for (storage_key, child_logger) in accesses.children_logger.iter() {
							for key in child_logger.append_keys.iter() {
								self.log_append_storage_key(Some(storage_key.as_slice()), key.as_slice());
							}
						}
					}

					if self.log_read.parent && accesses.read_all {
						// relative to the current three configs when read is logged for child, it is also for
						// parent.
						self.log_read_all();
					} else if self.log_read.parent {
						for key in accesses.top_logger.read_keys.iter() {
							self.log_read(None, key.as_slice());
						}
						for key in accesses.top_logger.read_intervals.iter() {
							self.log_read_interval(None, key.0.as_slice(), key.1.as_ref().map(|end| end.as_slice()));
						}
						for (storage_key, child_logger) in accesses.children_logger.iter() {
							for key in child_logger.read_keys.iter() {
								self.log_read_storage_key(Some(storage_key.as_slice()), key.as_slice());
							}
							for key in child_logger.read_intervals.iter() {
								self.log_read_interval_storage_key(
									Some(storage_key.as_slice()),
									key.0.as_slice(),
									key.1.as_ref().map(|end| end.as_slice()),
								);
							}
						}
					}

					true
				} ();

				self.remove_worker(*marker);
				result
			},
			// When using filter there is no directly valid case.
			WorkerResult::Valid(_result, _delta) => true,
			// When using filter there is no invalid case.
			WorkerResult::Invalid => true,
			// will panic on resolve so no need to clean filter
			WorkerResult::RuntimePanic
			| WorkerResult::HardPanic => true,
		}
	}

	pub(super) fn remove_worker(&mut self, worker: TaskId) {
		if self.eager_clean {
			return self.remove_worker_eager(worker);
		}
		self.log_write.remove(worker);
		// we could remove all occurence, but we only do when no runing thread
		// to just clear.
		if self.log_write.is_empty() {
			self.top_logger.remove_all_write_logs();
			for child_logger in self.children_logger.iter_mut() {
				child_logger.1.remove_all_write_logs();
			}
		}
		self.log_append.remove(worker);
		if self.log_append.is_empty() {
			self.top_logger.remove_all_append_logs();
			for child_logger in self.children_logger.iter_mut() {
				child_logger.1.remove_all_append_logs();
			}
		}
		self.log_read.remove(worker);
		if self.log_read.is_empty() {
			self.top_logger.remove_all_read_logs();
			for child_logger in self.children_logger.iter_mut() {
				child_logger.1.remove_all_read_logs();
			}
		}
	}

	fn remove_worker_eager(&mut self, worker: TaskId) {
		if self.log_write.remove(worker) {
			if self.log_write.is_empty() {
				self.top_logger.remove_all_write_logs();
				for child_logger in self.children_logger.iter_mut() {
					child_logger.1.remove_all_write_logs();
				}
			} else {
				self.top_logger.remove_children_write_logs(worker);
				for child_logger in self.children_logger.iter_mut() {
					child_logger.1.remove_children_write_logs(worker);
				}
			}
		}
		if self.log_append.remove(worker) {
			if self.log_append.is_empty() {
				self.top_logger.remove_all_append_logs();
				for child_logger in self.children_logger.iter_mut() {
					child_logger.1.remove_all_append_logs();
				}
			} else {
				self.top_logger.remove_children_append_logs(worker);
				for child_logger in self.children_logger.iter_mut() {
					child_logger.1.remove_children_append_logs(worker);
				}
			}
		}

		if self.log_read.remove(worker) {
			if self.log_read.is_empty() {
				self.top_logger.remove_all_read_logs();
				for child_logger in self.children_logger.iter_mut() {
					child_logger.1.remove_all_read_logs();
				}
			} else {
				self.top_logger.remove_children_read_logs(worker);
				for child_logger in self.children_logger.iter_mut() {
					child_logger.1.remove_children_read_logs(worker);
				}
			}
		}
	}

	pub(super) fn log_read_all(&mut self) {
		if self.log_read.parent && !self.read_all.parent {
			self.read_all.parent = true;
			// TODO could clean logs from parent.
			// or also check this for further logging and when doing is_empty.
		}
		self.read_all.children.extend(self.log_read.children.iter().cloned());
		// Here we could remove children read logs, not sure if useful (need iter and filtering).
	}

	fn logger_mut<'a>(
		top_logger: &'a mut StateLogger,
		children_logger: &'a mut Map<StorageKey, StateLogger>,
		storage_key: Option<&[u8]>,
	) -> &'a mut StateLogger {
		if let Some(storage_key) = storage_key {
			children_logger.entry(storage_key.to_vec()).or_insert_with(Default::default)
		} else {
			top_logger
		}
	}

	pub(super) fn log_read(&mut self, child_info: Option<&ChildInfo>, key: &[u8]) {
		self.log_read_storage_key(child_info.map(|child_info| child_info.storage_key()), key)
	}

	fn log_read_storage_key(&mut self, storage_key: Option<&[u8]>, key: &[u8]) {
		if !self.log_read.is_empty() {
			let logger = if let Some(storage_key) = storage_key {
				if !self.children_logger.contains_key(storage_key) {
					self.children_logger.insert(storage_key.to_vec(), Default::default());
				}
				self.children_logger.get_mut(storage_key).expect("lazy init above")
			} else {
				&mut self.top_logger
			};
			let mut children = sp_std::iter::Iterator::peekable(self.log_read.children.difference(&self.read_all.children));
			let parent = self.log_read.parent;
			if children.peek().is_some() || parent {
				let mut entry = logger.read_keys.entry(key.to_vec())
					.or_default();
				entry.children.extend(children.cloned());
				entry.parent = parent;
			}
		}
	}

	pub(super) fn log_read_interval(
		&mut self,
		child_info: Option<&ChildInfo>,
		key: &[u8],
		key_end: Option<&[u8]>,
	) {
		self.log_read_interval_storage_key(child_info.map(|child_info| child_info.storage_key()), key, key_end)
	}

	fn log_read_interval_storage_key(
		&mut self,
		storage_key: Option<&[u8]>,
		key: &[u8],
		key_end: Option<&[u8]>,
	) {
		if !self.log_read.is_empty() {
			let logger = if let Some(storage_key) = storage_key {
				if !self.children_logger.contains_key(storage_key) {
					self.children_logger.insert(storage_key.to_vec(), Default::default());
				}
				self.children_logger.get_mut(storage_key).expect("lazy init above")
			} else {
				&mut self.top_logger
			};
			let mut children = sp_std::iter::Iterator::peekable(self.log_read.children.difference(&self.read_all.children));
			let mut parent = self.log_read.parent;
			if children.peek().is_some() || parent {
				let mut entry = logger.read_intervals.entry((key.to_vec(), key_end.map(|end| end.to_vec())))
					.or_default();
				entry.children.extend(children.cloned());
				entry.parent = parent;
			}
		}
	}

//	fn guard_write(&self, child_info: Option<&ChildInfo>, key: &[u8]) {
	pub(super) fn log_write(&mut self, child_info: Option<&ChildInfo>, key: &[u8]) {
		self.log_write_storage_key(child_info.map(|child_info| child_info.storage_key()), key)
	}

	fn log_write_storage_key(&mut self, storage_key: Option<&[u8]>, key: &[u8]) {
		if !self.log_write.is_empty() {
			let logger = Self::logger_mut(&mut self.top_logger, &mut self.children_logger, storage_key);
			let mut entry = logger.write_keys.entry(key.to_vec())
				.or_default();
			entry.children.extend(self.log_write.children.iter());
			entry.parent = self.log_write.parent;
		}
	}

	pub(super) fn log_append(&mut self, child_info: Option<&ChildInfo>, key: &[u8]) {
		self.log_append_storage_key(child_info.map(|child_info| child_info.storage_key()), key)
	}

	fn log_append_storage_key(&mut self, storage_key: Option<&[u8]>, key: &[u8]) {
		if !self.log_append.is_empty() {
			let logger = Self::logger_mut(&mut self.top_logger, &mut self.children_logger, storage_key);
			let mut entry = logger.append_keys.entry(key.to_vec())
				.or_default();
			entry.children.extend(self.log_append.children.iter());
			entry.parent = self.log_append.parent;
		}
	}

//	fn guard_write_prefix(&self, child_info: Option<&ChildInfo>, key: &[u8]) {
	pub(super) fn log_write_prefix(&mut self, child_info: Option<&ChildInfo>, key: &[u8]) {
		self.log_write_prefix_storage_key(child_info.map(|child_info| child_info.storage_key()), key)
	}

	fn log_write_prefix_storage_key(&mut self, storage_key: Option<&[u8]>, key: &[u8]) {
		if !self.log_write.is_empty() {
			let logger = Self::logger_mut(&mut self.top_logger, &mut self.children_logger, storage_key);
			// TODO a 'entry' api in radix_tree would be nice.
			if let Some(entry) = logger.write_prefixes.get_mut(key) {
				entry.children.extend(self.log_write.children.iter());
				entry.parent = self.log_write.parent;
			} else {
				logger.write_prefixes.insert(key, self.log_write.clone());
			}
		}
	}

	pub(super) fn extract_parent_log(&mut self) -> Option<sp_externalities::AccessLog> {
		if !self.log_read.parent && !self.log_write.parent && !self.log_append.parent {
			return None;
		}

		let mut result = sp_externalities::AccessLog::default();

		result.read_all = self.read_all.parent;

		if !result.read_all && self.log_read.parent {
			result.top_logger.read_keys = sp_std::mem::take(&mut self.top_logger.read_keys).into_iter()
				.map(|(key, access)| {
					debug_assert!(access.parent);
					key
				}).collect();
			result.top_logger.read_intervals = sp_std::mem::take(&mut self.top_logger.read_intervals).into_iter()
				.map(|(key, access)| {
					debug_assert!(access.parent);
					key
				}).collect();
		}
		if self.log_append.parent {
			result.top_logger.append_keys = sp_std::mem::take(&mut self.top_logger.append_keys).into_iter()
				.map(|(key, access)| {
					debug_assert!(access.parent);
					key
				}).collect();
		}
		if self.log_write.parent {
			result.top_logger.write_keys = sp_std::mem::take(&mut self.top_logger.write_keys).into_iter()
				.map(|(key, access)| {
					debug_assert!(access.parent);
					key
				}).collect();

			result.top_logger.write_prefix = self.top_logger.write_prefixes.iter().value_iter()
				.map(|(key, _)| key).collect();
		}
		result.children_logger = sp_std::mem::take(&mut self.children_logger).into_iter()
			.map(|(storage_key, logger)| {
			let mut log = StateLog::default();
			if !result.read_all && self.log_read.parent {
				log.read_keys = logger.read_keys.into_iter()
					.map(|(key, _)| key).collect();
				log.read_intervals = logger.read_intervals.into_iter()
					.map(|(key, _)| key).collect();
			}
			if self.log_append.parent {
				log.append_keys = logger.append_keys.into_iter()
					.map(|(key, _)| key).collect();
			}
			if self.log_write.parent {
				log.write_keys = logger.write_keys.into_iter()
					.map(|(key, _)| key).collect();
				log.write_prefix = logger.write_prefixes.iter().value_iter()
					.map(|(key, _)| key).collect();
			}

			(storage_key.clone(), log)
		}).collect();

		Some(result)
	}
}

#[cfg(test)]
mod test {
	use super::*;

	#[test]
	fn test_check_write_write() {
		let mut parent_access_base = AccessLogger::default();
		let task1 = 1u64;
		let task2 = 2u64;
		parent_access_base.log_writes_against(Some(task1));
		parent_access_base.log_writes_against(Some(task2));
		// log read should not interfere
		parent_access_base.log_reads_against(Some(task1));
		parent_access_base.log_reads_against(Some(task2));
		let mut child_access = StateLog::default();
		child_access.read_write_keys.push(b"key1".to_vec());
		child_access.read_write_prefix.push(b"prefix".to_vec());
		assert!(parent_access_base.top_logger.check_write_write(&child_access, task1));
		assert!(parent_access_base.top_logger.check_write_write(&child_access, task2));

		let mut parent_access = parent_access_base.clone();
		parent_access.log_read(None, &b"key1"[..]);
		parent_access.log_read_interval(None, &b""[..], None);
		assert!(parent_access.top_logger.check_write_write(&child_access, task1));
		assert!(parent_access.top_logger.check_write_write(&child_access, task2));

		parent_access.log_write(None, &b"key1"[..]);
		assert!(!parent_access.top_logger.check_write_write(&child_access, task1));
		assert!(!parent_access.top_logger.check_write_write(&child_access, task2));

		parent_access.remove_worker_eager(task2);
		assert!(!parent_access.top_logger.check_write_write(&child_access, task1));
		assert!(parent_access.top_logger.check_write_write(&child_access, task2));

		let mut parent_access = parent_access_base.clone();
		parent_access.log_write(None, &b"key12"[..]);
		parent_access.log_write(None, &b"key2"[..]);
		parent_access.log_write(None, &b"k"[..]);
		parent_access.log_write(None, &b""[..]);
		parent_access.log_write(None, &b"prefi"[..]);
		parent_access.log_write_prefix(None, &b"a"[..]);
		parent_access.log_write_prefix(None, &b"key10"[..]);
		assert!(parent_access.top_logger.check_write_write(&child_access, task1));

		parent_access.log_write(None, &b"prefixed"[..]);
		assert!(!parent_access.top_logger.check_write_write(&child_access, task1));

		let mut parent_access = parent_access_base.clone();
		parent_access.log_write(None, &b"prefix"[..]);
		assert!(!parent_access.top_logger.check_write_write(&child_access, task1));

		let mut parent_access = parent_access_base.clone();
		parent_access.log_write_prefix(None, &b"key1"[..]);
		assert!(!parent_access.top_logger.check_write_write(&child_access, task1));

		let mut parent_access = parent_access_base.clone();
		parent_access.log_write_prefix(None, &b"ke"[..]);
		assert!(!parent_access.top_logger.check_write_write(&child_access, task1));

		let mut parent_access = parent_access_base.clone();
		parent_access.log_write_prefix(None, &b"pre"[..]);
		assert!(!parent_access.top_logger.check_write_write(&child_access, task1));

		let mut parent_access = parent_access_base.clone();
		parent_access.log_write_prefix(None, &b"prefix"[..]);
		assert!(!parent_access.top_logger.check_write_write(&child_access, task1));

		let mut parent_access = parent_access_base.clone();
		parent_access.log_write_prefix(None, &b"prefixed"[..]);
		assert!(!parent_access.top_logger.check_write_write(&child_access, task1));
	}

	#[test]
	fn test_check_child_read() {
		let mut parent_access_base = AccessLogger::default();
		let task1 = 1u64;
		parent_access_base.log_writes_against(Some(task1));
		// log read in parent should not interfere
		parent_access_base.log_reads_against(Some(task1));
		let mut child_access = StateLog::default();
		child_access.read_write_keys.push(b"keyw".to_vec());
		child_access.read_write_prefix.push(b"prefixw".to_vec());
		child_access.read_write_prefix.push(b"prefixx".to_vec());
		child_access.read_write_prefix.push(b"prefixz".to_vec());
		child_access.read_keys.push(b"keyr".to_vec());
		child_access.read_intervals.push((b"st_int".to_vec(), Some(b"w".to_vec())));
		child_access.read_intervals.push((b"z_int".to_vec(), Some(b"z_inter".to_vec())));
		child_access.read_intervals.push((b"z_z".to_vec(), None));
		assert!(parent_access_base.top_logger.check_child_read(&child_access, task1));

		let mut parent_access = parent_access_base.clone();
		parent_access.log_read(None, &b"keyw"[..]);
		parent_access.log_read(None, &b"keyr"[..]);
		parent_access.log_read_interval(None, &b"z_int"[..], None);
		parent_access.log_write(None, &b"ke"[..]);
		parent_access.log_write(None, &b""[..]);
		parent_access.log_write(None, &b"prefixy"[..]);
		parent_access.log_write(None, &b"st_in"[..]);
		parent_access.log_write(None, &b"w0"[..]);
		assert!(parent_access.top_logger.check_child_read(&child_access, task1));

		let mut parent_access = parent_access_base.clone();
		parent_access.log_write(None, &b"keyr"[..]);
		assert!(!parent_access.top_logger.check_child_read(&child_access, task1));

		let mut parent_access = parent_access_base.clone();
		parent_access.log_write(None, &b"keyw"[..]);
		parent_access.log_write(None, &b"z_inter2"[..]);
		parent_access.log_write(None, &b"z_in"[..]);
		parent_access.log_write(None, &b"z_ins"[..]);
		parent_access.log_write_prefix(None, &b"p"[..]);
		parent_access.log_write_prefix(None, &b"prefixwed"[..]);
		// Note that these logical conflict (log write involve a read) are done by
		// check_write_write when write is enabled.
		// (we rely on the fact that check_child_read is only for read only.
		assert!(parent_access.top_logger.check_child_read(&child_access, task1));

		parent_access.log_write(None, &b"keyr"[..]);
		assert!(!parent_access.top_logger.check_child_read(&child_access, task1));

		let mut parent_access = parent_access_base.clone();
		parent_access.log_write(None, &b"t_in_interval"[..]);
		assert!(!parent_access.top_logger.check_child_read(&child_access, task1));

		let mut parent_access = parent_access_base.clone();
		parent_access.log_write(None, &b"{_in_end_interval"[..]);
		assert!(!parent_access.top_logger.check_child_read(&child_access, task1));

		let mut parent_access = parent_access_base.clone();
		parent_access.log_write_prefix(None, &b""[..]);
		assert!(!parent_access.top_logger.check_child_read(&child_access, task1));

		let mut parent_access = parent_access_base.clone();
		parent_access.log_write_prefix(None, &b"t_in_interval"[..]);
		assert!(!parent_access.top_logger.check_child_read(&child_access, task1));

		let mut parent_access = parent_access_base.clone();
		parent_access.log_write_prefix(None, &b"key"[..]);
		assert!(!parent_access.top_logger.check_child_read(&child_access, task1));

		let mut parent_access = parent_access_base.clone();
		parent_access.log_write_prefix(None, &b"t"[..]);
		assert!(!parent_access.top_logger.check_child_read(&child_access, task1));
	}

	#[test]
	fn test_check_child_write() {
		let mut parent_access_base = AccessLogger::default();
		let task1 = 1u64;
		parent_access_base.log_writes_against(Some(task1));
		// log read in parent should not interfere
		parent_access_base.log_reads_against(Some(task1));
		let mut child_access = StateLog::default();
		child_access.read_write_keys.push(b"keyw".to_vec());
		child_access.read_write_prefix.push(b"prefixw".to_vec());
		child_access.read_write_prefix.push(b"prefixx".to_vec());
		child_access.read_write_prefix.push(b"prefixz".to_vec());
		child_access.read_keys.push(b"keyr".to_vec());
		child_access.read_intervals.push((b"st_int".to_vec(), Some(b"w".to_vec())));
		child_access.read_intervals.push((b"z_int".to_vec(), Some(b"z_inter".to_vec())));
		child_access.read_intervals.push((b"z_z".to_vec(), None));
		assert!(parent_access_base.top_logger.check_child_write(&child_access, task1));

		let mut parent_access = parent_access_base.clone();
		parent_access.log_read(None, &b"st_int"[..]);
		parent_access.log_read(None, &b"keyr"[..]);
		parent_access.log_read(None, &b"prefix"[..]);
		parent_access.log_read(None, &b"prefixy"[..]);
		parent_access.log_read(None, &b"keywa"[..]);
		parent_access.log_read_interval(None, &b"z_i"[..], Some(&b"z_inta"[..]));
		parent_access.log_read_interval(None, &b"z_i"[..], Some(&b"z_j"[..]));
		parent_access.log_read_interval(None, &b"z_int"[..], None);
		parent_access.log_read_interval(None, &b"pre"[..], Some(&b"prefix"[..]));
		parent_access.log_write_prefix(None, &b""[..]);
		parent_access.log_write_prefix(None, &b"z_inti"[..]);
		parent_access.log_write(None, &b"keyw"[..]);
		parent_access.log_write(None, &b"prefixx"[..]);
		assert!(parent_access.top_logger.check_child_write(&child_access, task1));

		parent_access.log_read(None, &b"keyw"[..]);
		assert!(!parent_access.top_logger.check_child_write(&child_access, task1));

		let parent_access = parent_access_base.clone();
		parent_access.log_read(None, &b"prefixx"[..]);
		assert!(!parent_access.top_logger.check_child_write(&child_access, task1));

		let parent_access = parent_access_base.clone();
		parent_access.log_read(None, &b"prefixxa"[..]);
		assert!(!parent_access.top_logger.check_child_write(&child_access, task1));

		let parent_access = parent_access_base.clone();
		parent_access.log_read_interval(None, &b"pre"[..], Some(&b"prefixx"[..]));
		assert!(!parent_access.top_logger.check_child_write(&child_access, task1));

		let parent_access = parent_access_base.clone();
		parent_access.log_read_interval(None, &b"pre"[..], None);
		assert!(!parent_access.top_logger.check_child_write(&child_access, task1));
	}
}

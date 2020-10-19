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

//! Aggregates are aggregated computational state stored to be cached between extrinsics
//! or blocks.
//! They are invalidated when a given value they are build upon get modified.
//! When invalidated or missing, the runtime can always compute them again, this
//! is just an optimization.
//!
//! To avoid storing all access keys and to support range iteration, prefix can also be
//! define as source for an aggregate.


use crate::overlayed_changes::StorageKey;
use sp_std::any::Any;
use codec::{Codec, Encode, Decode};
use sp_std::vec::Vec;
use sp_std::collections::btree_map::BTreeMap;
use sp_std::collections::btree_set::BTreeSet;

use radix_tree::{Derivative, RadixConf, Children, NodeConf, Node,
	Children256, Radix256Conf, Value};

use core::fmt::Debug;

radix_tree::flatten_children!(
	Children256Flatten,
	Node256Flatten,
	Node256NoBackend,
	Children256,
	Radix256Conf,
	(),
);

type RadixTree<V> = radix_tree::Tree<Node256NoBackend<V>>;

/// `Any to use within runtime, `Codec` to transfer to runtime.
pub trait Aggregate: Any {
	/// We use encode to produce transaction,
	/// when decoding it is the runtime that
	/// is responsible to know the actual type to use.
	fn encode(&self) -> Vec<u8>;
}

impl<V: Any + Codec> Aggregate for V {
	fn encode(&self) -> Vec<u8> {
		<Self as Encode>::encode(self)
	}
}

#[derive(PartialEq, Eq)]
#[derive(Encode, Decode, Debug)]
enum AggregateState {
	Building,
	Unresolved,
	Dropped,
	Untouched(Box<dyn Aggregate>),
	// we use a Vec of filter change here because it is only updated once
	Changed(Box<dyn Aggregate>, Vec<(StorageKey, Option<AggregateFilter>)>),
}

#[derive(Encode, Decode)]
struct FiltersTransaction {
	location: StorageKey,
	filter: AggregateFilter,
}

/// Change set is an array of couple aggregate key and
/// encoded aggregate value with new filters.
type Transaction = Vec<(StorageKey, (Vec<u8>, FiltersTransaction))>;

/// If it contains `None`, this means the aggregate was dropped.
/// If it contains `Some(None)` it means the aggregate was not resolved.
type ChangeSetAggregate = sp_std::rc::Rc<sp_std::cell::RefCell<AggregateState>>;

/// Aggregate change with delta management.
/// Initial state should reflect ALL previous state (to invalidate on
/// key modification), only the aggregate content is resolved and
/// decoded lazilly with backend method `encoded_aggregate`.
/// TODO this is currently not using transaction: using the changes
/// from #7290 could make transaction implementation rather straight forward.
pub struct OverlayedAggregates {
	change_set: BTreeMap<StorageKey, ChangeSetAggregate>,
	/// boolean indicates if filter is new.
	filters: RadixTree<Vec<(AggregateFilter, ChangeSetAggregate, bool)>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AggregateFilter {
	/// The filter is about a single value
	SingleValue,
	/// The filter is about a single value
	SingleValueNew,
	/// The filter is about a single value
	SingleValueDropped,
	/// The filter is over the whole prefix
	Prefix,
	/// The filter is over the whole prefix
	PrefixNew,
	/// The filter is over the whole prefix
	PrefixDropped,

}

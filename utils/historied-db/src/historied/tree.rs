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

//! Tree historied data historied db implementations.

// TODO remove "previous code" expect.

#[cfg(feature = "need_implementation_changes")]
use super::ConditionalValueMut;
use super::{HistoriedValue, ValueRef, Value, InMemoryValueRef, InMemoryValue, ForceValueMut,
	InMemoryValueSlice, InMemoryValueRange, UpdateResult, Item, ItemRef,
	ValueDiff, ItemDiff};
use crate::backend::{LinearStorage, LinearStorageRange, LinearStorageSlice, LinearStorageMem};
use crate::historied::linear::{Linear, LinearState, LinearGC, LinearDiff};
use crate::management::tree::{ForkPlan, BranchesContainer, TreeStateGc, DeltaTreeStateGc, MultipleGc, MultipleMigrate};
use sp_std::ops::SubAssign;
use num_traits::One;
use sp_std::vec::Vec;
use sp_std::marker::PhantomData;
use crate::Latest;
use crate::{Context, InitFrom, DecodeWithContext, Trigger};
use codec::{Encode, Input};
use derivative::Derivative;
use core::default::Default;

// TODO for not in memory we need some direct or indexed api, returning value
// and the info if there can be lower value index (not just a direct index).
// -> then similar to those reverse iteration with possible early exit.
// -> Also need to attach some location index (see enumerate use here)

// strategy such as in linear are getting too complex for tree, just using
// macros to remove duplicated code.

// Common code to get from tree.
// Lookup first linear storage in parallel (until incorrect state ordering).
// Call second linear historied value afterward.
macro_rules! tree_get {
	($fn_name: ident, $return_type: ty, $branch_query: ident, $value_query: expr, $post_process: expr) => {
	fn $fn_name<'a>(&'a self, at: &<Self as ValueRef<V>>::S) -> Option<$return_type> {
		// note that we expect branch index to be linearily set
		// along a branch (no state containing unordered branch_index
		// and no history containing unorderd branch_index).
		let mut next_branch_index = self.branches.last();
		for (state_branch_range, state_branch_index) in at.iter() {
			while let Some(branch_ix) = next_branch_index {
				let branch_index = &self.branches.get_state(branch_ix);
				if branch_index < &state_branch_index {
					break;
				} else if branch_index == &state_branch_index {
					// TODO add a lower bound check (maybe debug_assert it only).
					let mut upper_bound = state_branch_range.end.clone();
					upper_bound -= BI::one();
					let branch = self.branches.$branch_query(branch_ix).value;
					if let Some(result) = $value_query(&branch, &upper_bound) {
						return Some($post_process(result, branch))
					}
				}
				next_branch_index = self.branches.previous_index(branch_ix);
			}
		}

		// composite part.
		while let Some(branch_ix) = next_branch_index {
			let branch_index = &self.branches.get_state(branch_ix);
			if branch_index <= &at.composite_treshold.0 {
				let branch = self.branches.$branch_query(branch_ix).value;
				if let Some(result) = $value_query(&branch, &at.composite_treshold.1) {
					return Some($post_process(result, branch))
				}
			}
			next_branch_index = self.branches.previous_index(branch_ix);
		}
	
		None
	}
	}
}

#[derive(Derivative, Debug, Clone, Encode)]
#[derivative(PartialEq(bound="D: PartialEq"))]
pub struct Tree<I, BI, V, D: Context, BD: Context> {
	branches: D,
	#[codec(skip)]
	#[derivative(PartialEq="ignore" )]
	init: D::Context,
	#[codec(skip)]
	#[derivative(PartialEq="ignore" )]
	init_child: BD::Context,
	#[codec(skip)]
	_ph: PhantomData<(I, BI, V, BD)>,
}

impl<I, BI, V, D, BD> DecodeWithContext for Tree<I, BI, V, D, BD>
	where
		D: DecodeWithContext,
		BD: DecodeWithContext,
{
	fn decode_with_context<IN: Input>(input: &mut IN, init: &Self::Context) -> Option<Self> {
		D::decode_with_context(input, &init.0).map(|branches|
			Tree {
				branches,
				init: init.0.clone(),
				init_child: init.1.clone(),
				_ph: PhantomData,
			}
		)
	}
}

impl<I, BI, V, D: Context, BD: Context> Context for Tree<I, BI, V, D, BD> {
	type Context = (D::Context, BD::Context);
}

impl<I, BI, V, D: Context + Trigger, BD: Context> Trigger for Tree<I, BI, V, D, BD> {
	const TRIGGER: bool = <D as Trigger>::TRIGGER;

	fn trigger_flush(&mut self) {
		if Self::TRIGGER {
			self.branches.trigger_flush();
		}
	}
}

impl<I, BI, V, D: InitFrom, BD: InitFrom> InitFrom for Tree<I, BI, V, D, BD> {
	fn init_from(init: Self::Context) -> Self {
		Tree {
			branches: D::init_from(init.0.clone()),
			init: init.0,
			init_child: init.1,
			_ph: PhantomData,
		}
	}
}

type Branch<I, BI, V, BD> = HistoriedValue<Linear<V, BI, BD>, I>;

impl<
	I: Clone,
	BI: LinearState + SubAssign<BI>,
	V: Item + Clone + Eq,
	BD: LinearStorage<V::Storage, BI>,
> Branch<I, BI, V, BD>
{
	pub fn new(value: V, state: &(I, BI), init: BD::Context) -> Self {
		let (branch_index, index) = state.clone();
		let index = Latest::unchecked_latest(index); // TODO cast ptr?
		let history = Linear::new(value, &index, init);
		Branch {
			state: branch_index,
			value: history,
		}
	}
}

impl<
	I: Default + Eq + Ord + Clone,
	BI: LinearState + SubAssign<BI> + One,
	V: Item + Clone,
	D: LinearStorage<Linear<V, BI, BD>, I>, // TODO rewrite to be linear storage of BD only.
	BD: LinearStorage<V::Storage, BI>,
> ValueRef<V> for Tree<I, BI, V, D, BD> {
	type S = ForkPlan<I, BI>;

	tree_get!(get, V, get, |b: &Linear<V, BI, BD>, ix| b.get(ix), |r, _| r);

	fn contains(&self, at: &Self::S) -> bool {
		self.get(at).is_some() // TODO avoid clone??
	}

	fn is_empty(&self) -> bool {
		// This implies empty branch get clean correctly.
		self.branches.len() == 0
	}
}

/// Tree access to Diff structure.
///
/// TODO put in its own module?
pub struct TreeDiff<'a, I, BI, V: ItemDiff, D: Context, BD: Context>(pub &'a Tree<I, BI, V::Diff, D, BD>);

impl<'a, I, BI, V: ItemDiff, D: Context, BD: Context> sp_std::ops::Deref for TreeDiff<'a, I, BI, V, D, BD> {
	type Target = Tree<I, BI, V::Diff, D, BD>;

	fn deref(&self) -> &Tree<I, BI, V::Diff, D, BD> {
		&self.0
	}
}

impl<'a, I, BI, V, D, BD> ValueRef<V::Diff> for TreeDiff<'a, I, BI, V, D, BD>
	where
		I: Default + Eq + Ord + Clone,
		BI: LinearState + SubAssign<BI> + One,
		V: ItemDiff,
		V::Diff: Item + Clone,
		D: LinearStorage<Linear<V::Diff, BI, BD>, I>,
		BD: LinearStorage<<V::Diff as Item>::Storage, BI>,
{
	type S = ForkPlan<I, BI>;

	fn get(&self, at: &Self::S) -> Option<V::Diff> {
		self.0.get(at)
	}

	fn contains(&self, at: &Self::S) -> bool {
		self.0.contains(at)
	}

	fn is_empty(&self) -> bool {
		self.0.is_empty()
	}
}

impl<'a, I, BI, V, D, BD> ValueDiff<V> for TreeDiff<'a, I, BI, V, D, BD>
	where
		I: Default + Eq + Ord + Clone,
		BI: LinearState + SubAssign<BI> + One,
		V: ItemDiff,
		V::Diff: Item + Clone,
		D: LinearStorage<Linear<V::Diff, BI, BD>, I>,
		BD: LinearStorage<<V::Diff as Item>::Storage, BI>,
{
	fn get_diffs(&self, at: &Self::S, changes: &mut Vec<V::Diff>) -> bool {
		// could also exten tree_get macro but it will end up being hard to read,
		// so copying loop here.
		let mut next_branch_index = self.branches.last();
		for (state_branch_range, state_branch_index) in at.iter() {
			while let Some(branch_ix) = next_branch_index {
				let branch_index = &self.branches.get_state(branch_ix);
				if branch_index < &state_branch_index {
					break;
				} else if branch_index == &state_branch_index {
					// TODO add a lower bound check (maybe debug_assert it only).
					let mut upper_bound = state_branch_range.end.clone();
					upper_bound -= BI::one();
					// TODO get_ref variant?
					let branch = self.branches.get(branch_ix).value;
					if LinearDiff::<V, _, _>(&branch).get_diffs(&upper_bound, changes) {
						return true;
					}
				}
				next_branch_index = self.branches.previous_index(branch_ix);
			}
		}

		// composite part.
		while let Some(branch_ix) = next_branch_index {
			let branch_index = &self.branches.get_state(branch_ix);
			if branch_index <= &at.composite_treshold.0 {
				let branch = self.branches.get(branch_ix).value;
				if LinearDiff::<V, _, _>(&branch).get_diffs(&at.composite_treshold.1, changes) {
					return true;
				}
			}
			next_branch_index = self.branches.previous_index(branch_ix);
		}
	
		false
	}
}
	


impl<
	I: Default + Eq + Ord + Clone,
	BI: LinearState + SubAssign<BI> + One,
	V: ItemRef + Clone,
	D: LinearStorageMem<Linear<V, BI, BD>, I>,
	BD: LinearStorageMem<V::Storage, BI>,
> InMemoryValueRef<V> for Tree<I, BI, V, D, BD> {
	tree_get!(get_ref, &V, get_ref, |b: &'a Linear<V, BI, BD>, ix| b.get_ref(ix), |r, _| r );
}

impl<
	I: Default + Eq + Ord + Clone,
	BI: LinearState + SubAssign<BI> + One,
	V: Item + Clone + Eq,
	D: LinearStorage<Linear<V, BI, BD>, I>,
	BD: LinearStorage<V::Storage, BI>,
> Value<V> for Tree<I, BI, V, D, BD> {
	type SE = Latest<(I, BI)>;
	type Index = (I, BI);
	type GC = MultipleGc<I, BI>;
	type Migrate = MultipleMigrate<I, BI>;

	fn new(value: V, at: &Self::SE, init: Self::Context) -> Self {
		let mut v = D::init_from(init.0.clone());
		v.push(Branch::new(value, at.latest(), init.1.clone()));
		Tree {
			branches: v,
			init: init.0,
			init_child: init.1,
			_ph: PhantomData,
		}
	}

	fn set(&mut self, value: V, at: &Self::SE) -> UpdateResult<()> {
		// Warn dup code, can be merge if change set to return previ value: with
		// ref refact will be costless
		let (branch_index, index) = at.latest();
		let mut insert_at = None;
		for branch_ix in self.branches.rev_index_iter() {
			let iter_branch_index = self.branches.get_state(branch_ix);
			if &iter_branch_index == branch_index {
				let index = Latest::unchecked_latest(index.clone());
				let mut branch = self.branches.get(branch_ix);
				return match branch.value.set(value, &index) {
					UpdateResult::Changed(_) => {
						self.branches.emplace(branch_ix, branch);
						UpdateResult::Changed(())
					},
					UpdateResult::Cleared(_) => {
						self.branches.remove(branch_ix);
						if self.branches.len() == 0 {
							UpdateResult::Cleared(())
						} else {
							UpdateResult::Changed(())
						}
					},
					UpdateResult::Unchanged => UpdateResult::Unchanged,
				};
			}
			if &iter_branch_index < branch_index {
				break;
			}
			insert_at = Some(branch_ix);
		}
		let branch = Branch::new(value, at.latest(), self.init_child.clone());
		if let Some(index) = insert_at {
			self.branches.insert(index, branch);
		} else {
			self.branches.push(branch);
		}
		UpdateResult::Changed(())
	}

	fn discard(&mut self, at: &Self::SE) -> UpdateResult<Option<V>> {
		let (branch_index, index) = at.latest();
		for branch_ix in self.branches.rev_index_iter() {
			let iter_branch_index = self.branches.get_state(branch_ix);
			if &iter_branch_index == branch_index {
				let index = Latest::unchecked_latest(index.clone());
				let mut branch = self.branches.get(branch_ix);
				return match branch.value.discard(&index) {
					UpdateResult::Changed(v) => {
						self.branches.emplace(branch_ix, branch);
						UpdateResult::Changed(v)
					},
					UpdateResult::Cleared(v) => {
						self.branches.remove(branch_ix);
						if self.branches.len() == 0 {
							UpdateResult::Cleared(v)
						} else {
							UpdateResult::Changed(v)
						}
					},
					UpdateResult::Unchanged => UpdateResult::Unchanged,
				};
			}
			if &iter_branch_index < branch_index {
				break;
			}
		}

		UpdateResult::Unchanged
	}

	fn gc(&mut self, gc: &Self::GC) -> UpdateResult<()> {
		match gc {
			MultipleGc::Journaled(gc) => self.journaled_gc(gc),
			MultipleGc::State(gc) => self.state_gc(gc),
		}
	}

	fn is_in_migrate((index, linear_index) : &Self::Index, gc: &Self::Migrate) -> bool {
		match gc {
			MultipleMigrate::Noops => (),
			MultipleMigrate::JournalGc(gc) => {
				if let Some(new_start) = gc.pruning_treshold.as_ref() {
					if linear_index <= &new_start {
						return true;
					}
				}
				if let Some(br) = gc.storage.get(&index) {
					return if let Some(bi) = br.0.as_ref() {
						bi <= linear_index
					} else {
						true
					};
				}
			},
			MultipleMigrate::Rewrite(_gc) => {
				unimplemented!()
			},
		}
		false
	}

	fn migrate(&mut self, mig: &Self::Migrate) -> UpdateResult<()> {
		let mut result = UpdateResult::Unchanged;

		match mig {
			MultipleMigrate::JournalGc(gc) => {
				result = self.journaled_gc(gc);
				if let UpdateResult::Cleared(()) = result {
					return UpdateResult::Cleared(());
				}
				let mut new_branch: Option<Branch<I, BI, V, BD>> = None;
				let mut i = 0;
				// merge all less than composite treshold in composite treshold index branch.
				loop {
					if let Some(index) = self.branches.lookup(i) {
						let mut branch = self.branches.get(index);
						if branch.state <= gc.composite_treshold.0 {
							if let Some(new_branch) = new_branch.as_mut() {
								for i in 0.. {
									if let Some(h) = branch.value.storage().lookup(i) {
										let h = branch.value.storage().get(h);
										new_branch.value.storage_mut().push(h);
									} else {
										break;
									}
								}
							} else {
								branch.state = gc.composite_treshold.0.clone();
								new_branch = Some(branch);
							}
						} else {
							break;
						}
					} else {
						break;
					}
					i += 1;
				}
				if let Some(new_branch) = new_branch {
					if i == self.branches.len() {
						self.branches.clear();
						self.branches.push(new_branch);
					} else {
						self.branches.truncate_until(i - 1);
						self.branches.emplace_lookup(0, new_branch);
					}
				}
			},
			MultipleMigrate::Rewrite(_gc) => unimplemented!(),
			MultipleMigrate::Noops => (),
		}

		if let UpdateResult::Changed(()) = result {
			if self.branches.len() == 0 {
				result = UpdateResult::Cleared(());
			}
		}
		result
	}
}

impl<
	I: Default + Eq + Ord + Clone,
	BI: LinearState + SubAssign<BI> + Clone,
	V: Item + Clone + Eq,
	D: LinearStorage<Linear<V, BI, BD>, I>,
	BD: LinearStorage<V::Storage, BI>,
> Tree<I, BI, V, D, BD> {
	fn state_gc(&mut self, gc: &TreeStateGc<I, BI>) -> UpdateResult<()> {
		let mut result = UpdateResult::Unchanged;
		let start_history = &gc.pruning_treshold;
		let mut gc_iter = gc.storage.iter().rev();
		let mut next_branch_index = self.branches.last();
	
		let mut o_gc = gc_iter.next();
		let mut o_branch = next_branch_index.map(|i| (i, self.branches.get_state(i)));
		while let (Some(gc), Some((index, branch_index))) = (o_gc.as_ref(), o_branch.as_ref()) {
			let index = *index;
			next_branch_index = self.branches.previous_index(index);
			if gc.0 == branch_index {
				let (start, end) = gc.1.range();
				let start = start_history.as_ref().and_then(|start_history| if &start < start_history {
					Some(start_history.clone())
				} else {
					None
				}).unwrap_or(start);
				let mut gc = LinearGC {
					new_start: Some(start),
					new_end:  Some(end),
				};

				let mut branch = self.branches.get(index);
				match branch.value.gc(&mut gc) {
					UpdateResult::Unchanged => (),
					UpdateResult::Changed(_) => { 
						self.branches.emplace(index, branch);
						result = UpdateResult::Changed(());
					},
					UpdateResult::Cleared(_) => {
						self.branches.remove(index);
						result = UpdateResult::Changed(());
					}
				}

				o_gc = gc_iter.next();

				o_branch = next_branch_index.map(|i| (i, self.branches.get_state(i)));
			} else if gc.0 < &branch_index {
				self.branches.remove(index);
				result = UpdateResult::Changed(());
				o_branch = next_branch_index.map(|i| (i, self.branches.get_state(i)));
			} else {
				o_gc = gc_iter.next();
			}
		}

		if let UpdateResult::Changed(()) = result {
			if self.branches.len() == 0 {
				result = UpdateResult::Cleared(());
			}
		}

		result
	}

	fn journaled_gc(&mut self, gc: &DeltaTreeStateGc<I, BI>) -> UpdateResult<()> {
		// for all branch check if in deleted.
		// Also apply new start on all.
		let mut result = UpdateResult::Unchanged;
		let start_history = gc.pruning_treshold.as_ref();
		let mut first_new_start = false;
		let mut next_branch_index = self.branches.last();
		while let Some(branch_ix) = next_branch_index {
			let mut branch = self.branches.get(branch_ix);
			let new_start = if branch.state <= gc.composite_treshold.0 {
				match start_history.as_ref() {
					None => None,
					Some(n_start) => {
						if first_new_start {
							self.branches.remove(branch_ix);
							result = UpdateResult::Changed(());
							next_branch_index = self.branches.previous_index(branch_ix);
							continue;
						} else {
							if let Some(b) = branch.value.storage().lookup(0) {
								let b = branch.value.storage().get(b);
								if &b.state < n_start {
									first_new_start = true;
								}
							}
							start_history.cloned()
						}
					},
				}
			} else {
				None
			};

			if let Some(mut gc) = if let Some(change) = gc.storage.get(&branch.state) {
				if change.0.is_none() {
					self.branches.remove(branch_ix);
					result = UpdateResult::Changed(());
					None
				} else {
					Some(LinearGC {
						new_start,
						new_end: change.0.clone(),
					})
				}
			} else {
				if first_new_start {
					Some(LinearGC {
						new_start,
						new_end: None,
					})
				} else {
					None
				}
			} {
				match branch.value.gc(&mut gc) {
					UpdateResult::Unchanged => (),
						UpdateResult::Changed(_) => { 
						self.branches.emplace(branch_ix, branch);
						result = UpdateResult::Changed(());
					},
					UpdateResult::Cleared(_) => {
						self.branches.remove(branch_ix);
						result = UpdateResult::Changed(());
					}
				}
			}
			next_branch_index = self.branches.previous_index(branch_ix);
		}

		if let UpdateResult::Changed(()) = result {
			if self.branches.len() == 0 {
				result = UpdateResult::Cleared(());
			}
		}

		result
	}

	#[cfg(test)]
	fn nb_internal_history(&self) -> usize {
		let mut nb = 0;
		for index in self.branches.rev_index_iter() {
			let branch = self.branches.get(index);
			nb += branch.value.storage().len();
		}
		nb
	}
	#[cfg(test)]
	fn nb_internal_branch(&self) -> usize {
		self.branches.len()
	}
}


impl<
	I: Default + Eq + Ord + Clone,
	BI: LinearState + SubAssign<BI> + One,
	V: ItemRef + Clone + Eq,
	D: LinearStorageMem<Linear<V, BI, BD>, I>,
	BD: LinearStorageMem<V::Storage, BI, Context = D::Context>,
> InMemoryValue<V> for Tree<I, BI, V, D, BD> {
	fn get_mut(&mut self, at: &Self::SE) -> Option<&mut V> {
		let (branch_index, index) = at.latest();
		for branch_ix in self.branches.rev_index_iter() {
			let iter_branch_index = self.branches.get_state(branch_ix);
			if &iter_branch_index == branch_index {
				let branch = self.branches.get_ref_mut(branch_ix);
				let index = Latest::unchecked_latest(index.clone());
				return branch.value.get_mut(&index);
			}
			if &iter_branch_index < branch_index {
				break;
			}
		}
		None
	}

	fn set_mut(&mut self, value: V, at: &Self::SE) -> UpdateResult<Option<V>> {
		// Warn dup code, can be merge if change set to return previ value: with
		// ref refact will be costless
		let (branch_index, index) = at.latest();
		let mut insert_at = None;
		let mut next_branch_index = self.branches.last();
		while let Some(branch_ix) = next_branch_index {
			let branch = self.branches.get_ref_mut(branch_ix);
			let iter_branch_index = &branch.state;
			if iter_branch_index == branch_index {
				let index = Latest::unchecked_latest(index.clone());
				return branch.value.set_mut(value, &index);
			}
			if iter_branch_index < branch_index {
				break;
			}
			insert_at = Some(branch_ix);
			next_branch_index = self.branches.previous_index(branch_ix);
		}
		let branch = Branch::new(value, at.latest(), self.init_child.clone());
		if let Some(index) = insert_at {
			self.branches.insert(index, branch);
		} else {
			self.branches.push(branch);
		}
		UpdateResult::Changed(None)
	}
}

#[cfg(feature = "need_implementation_changes")]
impl<
	I: Default + Eq + Ord + Clone,
	BI: LinearState + SubAssign<BI> + One,
	V: Item + Clone + Eq,
	D: LinearStorage<Linear<V, BI, BD>, I>,
	BD: LinearStorage<V::Storage, BI>,
> Tree<I, BI, V, D, BD> {
	fn set_if_inner(
		&mut self,
		value: V,
		at: &<Self as Value<V>>::Index,
		no_overwrite: bool,
	) -> Option<UpdateResult<()>> {
		let (branch_index, index) = at;
		let mut insert_at = None;
		for branch_ix in self.branches.rev_index_iter() {
			let iter_branch_index = self.branches.get_state(branch_ix);
			if &iter_branch_index == branch_index {
				let mut branch = self.branches.get(branch_ix);
				return match if no_overwrite {
					branch.value.set_if_possible_no_overwrite(value, &index)
				} else {
					branch.value.set_if_possible(value, &index)
				} {
					Some(UpdateResult::Changed(_)) => {
						self.branches.emplace(branch_ix, branch);
						Some(UpdateResult::Changed(()))
					},
					Some(UpdateResult::Cleared(_)) => {
						self.branches.remove(branch_ix);
						if self.branches.len() == 0 {
							Some(UpdateResult::Cleared(()))
						} else {
							Some(UpdateResult::Changed(()))
						}
					},
					r => r,
				};
			}
			if &iter_branch_index < branch_index {
				break;
			}
			insert_at = Some(branch_ix);
		}
		let branch = Branch::new(value, at, self.init_child.clone());
		if let Some(index) = insert_at {
			self.branches.insert(index, branch);
		} else {
			self.branches.push(branch);
		}
		Some(UpdateResult::Changed(()))
	}
	fn can_if_inner(
		&self,
		value: Option<&V>,
		at: &<Self as Value<V>>::Index,
	) -> bool {
		let (branch_index, index) = at;
		for branch_ix in self.branches.rev_index_iter() {
			let iter_branch_index = self.branches.get_state(branch_ix);
			if &iter_branch_index == branch_index {
				let branch = self.branches.get(branch_ix);
				return branch.value.can_set(value, &index);
			}
			if &iter_branch_index < branch_index {
				break;
			}
		}
		true
	}
}

impl<
	I: Default + Eq + Ord + Clone,
	BI: LinearState + SubAssign<BI> + One,
	V: Item + Clone + Eq,
	D: LinearStorage<Linear<V, BI, BD>, I>,
	BD: LinearStorage<V::Storage, BI>,
> ForceValueMut<V> for Tree<I, BI, V, D, BD> {
	type IndexForce = Self::Index;

	fn force_set(&mut self, value: V, at: &Self::Index) -> UpdateResult<()> {
		// Warn dup code, just different linear function call from fn set,
		// and using directly index, TODO factor result handle at least.
		let (branch_index, index) = at;
		let mut insert_at = None;
		for branch_ix in self.branches.rev_index_iter() {
			let iter_branch_index = self.branches.get_state(branch_ix);
			if &iter_branch_index == branch_index {
				let index = index.clone();
				let mut branch = self.branches.get(branch_ix);
				return match branch.value.force_set(value, &index) {
					UpdateResult::Changed(_) => {
						self.branches.emplace(branch_ix, branch);
						UpdateResult::Changed(())
					},
					UpdateResult::Cleared(_) => {
						self.branches.remove(branch_ix);
						if self.branches.len() == 0 {
							UpdateResult::Cleared(())
						} else {
							UpdateResult::Changed(())
						}
					},
					UpdateResult::Unchanged => UpdateResult::Unchanged,
				};
			}
			if &iter_branch_index < branch_index {
				break;
			}
			insert_at = Some(branch_ix);
		}
		let branch = Branch::new(value, at, self.init_child.clone());
		if let Some(index) = insert_at {
			self.branches.insert(index, branch);
		} else {
			self.branches.push(branch);
		}
		UpdateResult::Changed(())
	}
}


#[cfg(feature = "need_implementation_changes")]
// TODO current implementation is incorrect, we need an index that fails at first
// branch that is parent to the dest (a tree path flattened into a ForkPlan like
// struct). Element prior (I, BI) are not needed (only children).
// Then we still apply only at designated (I, BI) but any value in the plan are
// skipped.
impl<
	I: Default + Eq + Ord + Clone,
	BI: LinearState + SubAssign<BI> + One,
	V: Item + Clone + Eq,
	D: LinearStorage<Linear<V, BI, BD>, I>,
	BD: LinearStorage<V::Storage, BI>,
> ConditionalValueMut<V> for Tree<I, BI, V, D, BD> {
	// TODO this would require to get all branch index that are children
	// of this index, and also their current upper bound.
	// That can be fairly costy.
	type IndexConditional = Self::Index;

	fn can_set(&self, no_overwrite: Option<&V>, at: &Self::IndexConditional) -> bool {
		self.can_if_inner(no_overwrite, at)
	}
	
	fn set_if_possible(&mut self, value: V, at: &Self::IndexConditional) -> Option<UpdateResult<()>> {
		self.set_if_inner(value, at, false)
	}

	fn set_if_possible_no_overwrite(&mut self, value: V, at: &Self::IndexConditional) -> Option<UpdateResult<()>> {
		self.set_if_inner(value, at, true)
	}
}

type LinearBackendTempSize = crate::backend::in_memory::MemoryOnly<Option<Vec<u8>>, u32>;
type TreeBackendTempSize = crate::backend::in_memory::MemoryOnly<Linear<Option<Vec<u8>>, u32, LinearBackendTempSize>, u32>;

impl Tree<u32, u32, Option<Vec<u8>>, TreeBackendTempSize, LinearBackendTempSize> {
	/// Temporary function to get occupied stage.
	/// TODO replace by heapsizeof
	pub fn temp_size(&self) -> usize {
		let mut size = 0;
		for i in self.branches.rev_index_iter() {
			let b = self.branches.get_ref(i);
			size += 4; // branch index (using u32 as usize)
			size += b.value.temp_size();
		}
		size
	}
}

impl<
	I: Default + Eq + Ord + Clone,
	BI: LinearState + SubAssign<BI> + One,
	V: Item + Clone + AsRef<[u8]> + AsMut<[u8]>,
	D: LinearStorageSlice<Linear<V, BI, BD>, I>,
	BD: AsRef<[u8]> + AsMut<[u8]> + LinearStorageRange<V::Storage, BI>,
> InMemoryValueSlice<V> for Tree<I, BI, V, D, BD> {
	tree_get!(
		get_slice,
		&[u8],
		get_slice,
		|b: &'a [u8], ix| <Linear<V, BI, BD>>::get_range(b, ix),
		|result, b: &'a [u8]| &b[result]
	);
}


#[cfg(test)]
mod test {
	use super::*;
	use crate::management::tree::test::{test_states, test_states_st};
	use crate::InitFrom;

	#[test]
	fn compile_double_encoded_single() {
		use crate::backend::encoded_array::{EncodedArray, NoVersion};
		use crate::historied::ValueRef;

		type BD<'a> = EncodedArray<'a, Vec<u8>, NoVersion>;
//		type D<'a> = crate::historied::linear::MemoryOnly<
		type D<'a> = EncodedArray<'a,
			crate::historied::linear::Linear<Vec<u8>, u32, BD<'a>>,
			NoVersion,
//			u32
		>;
		let item: Tree<u32, u32, Vec<u8>, D, BD> = InitFrom::init_from(((), ()));
		let at: ForkPlan<u32, u32> = Default::default();
		item.get(&at);
		item.get_slice(&at);
		let latest = Latest::unchecked_latest((0, 0));
		let _item: Tree<u32, u32, Vec<u8>, D, BD> = Tree::new(b"dtd".to_vec(), &latest, ((), ()));
//		let slice = &b"dtdt"[..];
//		use crate::backend::encoded_array::{EncodedArrayValue};
//		let bd = crate::historied::linear::Linear::<Vec<u8>, u32, BD>::from_slice(slice);
//		let bd = BD::from_slice(slice);
		let bd = D::default();
		use crate::backend::LinearStorage;
		bd.get_lookup(1usize);
	}

	#[test]
	fn compile_double_encoded_node() {
		use crate::backend::encoded_array::{EncodedArray, DefaultVersion};
		use crate::backend::nodes::{Head, Node, ContextHead};
		use crate::backend::nodes::test::{MetaNb, MetaSize};
		use crate::historied::ValueRef;
		use sp_std::collections::btree_map::BTreeMap;

		type EncArray<'a> = EncodedArray<'a, Vec<u8>, DefaultVersion>;
		type Backend<'a> = BTreeMap<Vec<u8>, Node<Vec<u8>, u32, EncArray<'a>, MetaSize>>;
		type BD<'a> = Head<Vec<u8>, u32, EncArray<'a>, MetaSize, Backend<'a>, ()>;

		type V2<'a> = crate::historied::linear::Linear<Vec<u8>, u32, BD<'a>>;
		type EncArray2<'a> = EncodedArray<'a, V2<'a>, DefaultVersion>;
		type Backend2<'a> = BTreeMap<Vec<u8>, Node<V2<'a>, u32, EncArray2<'a>, MetaSize>>;
//		type D<'a> = crate::historied::linear::MemoryOnly<
		type D<'a> = Head<V2<'a>, u32, EncArray2<'a>, MetaSize, Backend2<'a>, ContextHead<Backend<'a>, ()>>;
		let init_head_child = ContextHead {
			backend: Backend::new(),
			key: b"any".to_vec(),
			node_init_from: (),
		};
		let init_head = ContextHead {
			backend: Backend2::new(),
			key: b"any".to_vec(),
			node_init_from: init_head_child.clone(),
		};
		let item: Tree<u32, u32, Vec<u8>, D, BD> = InitFrom::init_from((init_head.clone(), init_head_child.clone()));
		let at: ForkPlan<u32, u32> = Default::default();
		item.get(&at);

//	D: LinearStorage<Linear<V, BI, BD>, I>, // TODO rewrite to be linear storage of BD only.
//	BD: LinearStorage<V, BI>,

/*
//		item.get_slice(&at);
		let latest = Latest::unchecked_latest((0, 0));
		let _item: Tree<u32, u32, Vec<u8>, D, BD> = Tree::new(b"dtd".to_vec(), &latest, init_head.clone());
*/
//		let slice = &b"dtdt"[..];
//		use crate::backend::encoded_array::{EncodedArrayValue};
//		let bd = crate::historied::linear::Linear::<Vec<u8>, u32, BD>::from_slice(slice);
//		let bd = BD::from_slice(slice);
		let bd = D::init_from(init_head);
		use crate::backend::LinearStorage;
		let _a: Option<HistoriedValue<V2, u32>> = bd.get_lookup(1usize);
	}


	#[test]
	fn compile_double_encoded_node_2() {
		use crate::backend::in_memory::MemoryOnly;
		use crate::backend::nodes::{Head, Node, ContextHead};
		use crate::backend::nodes::test::{MetaNb, MetaSize};
		use crate::historied::ValueRef;
		use sp_std::collections::btree_map::BTreeMap;

		type MemOnly = MemoryOnly<Vec<u8>, u32>;
		type Backend = BTreeMap<Vec<u8>, Node<Vec<u8>, u32, MemOnly, MetaSize>>;
		type BD = Head<Vec<u8>, u32, MemOnly, MetaSize, Backend, ()>;

		type V2 = crate::historied::linear::Linear<Vec<u8>, u32, BD>;
		type MemOnly2 = MemoryOnly<V2, u32>;
		type Backend2 = BTreeMap<Vec<u8>, Node<V2, u32, MemOnly2, MetaSize>>;
		type D = Head<V2, u32, MemOnly2, MetaSize, Backend2, ContextHead<Backend, ()>>;
		let init_head_child = ContextHead {
			backend: Backend::new(),
			key: b"any".to_vec(),
			node_init_from: (),
		};
		let init_head = ContextHead {
			backend: Backend2::new(),
			key: b"any".to_vec(),
			node_init_from: init_head_child.clone(),
		};
		let item: Tree<u32, u32, Vec<u8>, D, BD> = InitFrom::init_from((init_head.clone(), init_head_child.clone()));
		let at: ForkPlan<u32, u32> = Default::default();
		item.get(&at);

		let bd = D::init_from(init_head);
		use crate::backend::LinearStorage;
		let _a: Option<HistoriedValue<V2, u32>> = bd.get_lookup(1usize);
	}

	#[test]
	fn test_set_get() {
		// TODO EMCH parameterize test
		type BD = crate::backend::in_memory::MemoryOnly<u32, u32>;
		type D = crate::backend::in_memory::MemoryOnly<
			crate::historied::linear::Linear<u32, u32, BD>,
			u32,
		>;
		// 0> 1: _ _ X
		// |			 |> 3: 1
		// |			 |> 4: 1
		// |		 |> 5: 1
		// |> 2: _
		let mut states = test_states();
		let mut item: Tree<u32, u32, u32, D, BD> = InitFrom::init_from(((), ()));

		for i in 0..6 {
			assert_eq!(item.get(&states.query_plan(i)), None);
		}

		// setting value respecting branch build order
		for i in 1..6 {
			item.set(i, &states.unchecked_latest_at(i).unwrap());
		}

		for i in 1..6 {
			assert_eq!(item.get_ref(&states.query_plan(i)), Some(&i));
		}

		let ref_1 = states.query_plan(1);
		assert_eq!(Some(false), states.branch_state_mut(&1, |ls| ls.drop_state()));

		let ref_1_bis = states.query_plan(1);
		assert_eq!(item.get(&ref_1), Some(1));
		assert_eq!(item.get(&ref_1_bis), None);
		item.set(11, &states.unchecked_latest_at(1).unwrap());
		// lazy linear clean of drop state on insert
		assert_eq!(item.get(&ref_1), Some(11));
		assert_eq!(item.get(&ref_1_bis), Some(11));

		item = InitFrom::init_from(((), ()));

		// need fresh state as previous modification leaves unattached branches
		let mut states = test_states();
		// could rand shuffle if rand get imported later.
		let disordered = [
			[1,2,3,5,4],
			[2,5,1,3,4],
			[5,3,2,4,1],
		];
		for r in disordered.iter() {
			for i in r {
				item.set(*i, &states.unchecked_latest_at(*i).unwrap());
			}
			for i in r {
				assert_eq!(item.get_ref(&states.query_plan(*i)), Some(i));
			}
		}
	}

	#[cfg(feature = "need_implementation_changes")]
	#[test]
	fn test_conditional_set_get() {
		use crate::{Management, ManagementRef, ForkableManagement};
		use crate::test::simple_impl::StateInput;
		type BD = crate::backend::in_memory::MemoryOnly<u32, u32>;
		type D = crate::backend::in_memory::MemoryOnly<
			crate::historied::linear::Linear<u32, u32, BD>,
			u32,
		>;
		// 0> 1: _ _ X
		// |			 |> 3: 1
		// |			 |> 4: 1
		// |		 |> 5: 1
		// |> 2: _
		let mut states = test_states();
		let mut item: Tree<u32, u32, u32, D, BD> = InitFrom::init_from(((), ()));
		let mut item2: Tree<u32, u32, u32, D, BD> = InitFrom::init_from(((), ()));

		for i in 0..6 {
			assert_eq!(item.get(&states.query_plan(i)), None);
		}

		// setting value not respecting branch build order
		// set in past (latest is 1, 2) is fine
		assert_eq!(Some(UpdateResult::Changed(())), item.set_if_possible(1, &(1, 1)));
		assert_eq!(Some(UpdateResult::Changed(())), item2.set_if_possible(1, &(1, 2)));
		// but not with another value
		assert_eq!(None, item.set_if_possible(8, &(1, 0)));
		assert_eq!(None, item2.set_if_possible(8, &(1, 1)));
		// can overwrite
		assert_eq!(Some(UpdateResult::Changed(())), item.set_if_possible(2, &(1, 1)));
		assert_eq!(Some(UpdateResult::Changed(())), item2.set_if_possible(2, &(1, 2)));
		// not if not allowed
		assert_eq!(None, item.set_if_possible_no_overwrite(3, &(1, 1)));
		assert_eq!(None, item2.set_if_possible_no_overwrite(3, &(1, 2)));
		// unchanged is allowed
		assert_eq!(Some(UpdateResult::Unchanged), item.set_if_possible(2, &(1, 1)));
		assert_eq!(Some(UpdateResult::Unchanged), item2.set_if_possible(2, &(1, 2)));
		assert_eq!(item.get_ref(&states.query_plan(1)), Some(&2));
		states.drop_state(&1u32);
		states.drop_state(&1u32);
		assert_eq!(item.get_ref(&states.query_plan(1)), None);
		assert_eq!(item2.get_ref(&states.query_plan(1)), None);
		// no longer allowd to change the branch TODO we should be able to, but
		// with blockchain tree use case with removal only on canonicalisation
		// and pruning it should be fine.
		assert_eq!(None, item2.set_if_possible(3, &(1, 1)));
	}

	#[test]
	fn test_force_set_get() {
		use crate::{Management, ManagementRef, ForkableManagement};
		use crate::test::simple_impl::StateInput;
		type BD = crate::backend::in_memory::MemoryOnly<u32, u32>;
		type D = crate::backend::in_memory::MemoryOnly<
			crate::historied::linear::Linear<u32, u32, BD>,
			u32,
		>;
		// 0> 1: _ _ X
		// |			 |> 3: 1
		// |			 |> 4: 1
		// |		 |> 5: 1
		// |> 2: _
		let mut states = test_states();
		let mut item: Tree<u32, u32, u32, D, BD> = InitFrom::init_from(((), ()));

		for i in 0..6 {
			assert_eq!(item.get(&states.query_plan(i)), None);
		}

		// setting value not respecting branch build order
		assert_eq!(UpdateResult::Changed(()), item.force_set(0, &(1, 2)));
		assert_eq!(UpdateResult::Changed(()), item.force_set(1, &(1, 1)));
		// out of range
		assert_eq!(UpdateResult::Changed(()), item.force_set(8, &(1, 0)));
		// can set in invalid range too
		assert_eq!(UpdateResult::Changed(()), item.force_set(3, &(2, 5)));
		assert_eq!(UpdateResult::Changed(()), item.force_set(2, &(2, 1)));

		assert_eq!(item.get_ref(&states.query_plan(1)), Some(&0));
		assert_eq!(item.get_ref(&states.query_plan(2)), Some(&2));
		states.drop_state(&1u32);
		assert_eq!(item.get_ref(&states.query_plan(1)), Some(&1));
		states.drop_state(&1u32);
		assert_eq!(item.get_ref(&states.query_plan(1)), None);
	}

	use ref_cast::RefCast;
	#[derive(RefCast)]
	#[repr(transparent)]
	#[derive(Clone, Copy, PartialEq, Eq, Debug)]
	/// U16 with 0 as neutral item.
	struct U16Neutral(u16); 

	impl std::ops::Deref for U16Neutral {
		type Target = u16;
		fn deref(&self) -> &u16 {
			&self.0
		}
	}

	impl std::ops::DerefMut for U16Neutral {
		fn deref_mut(&mut self) -> &mut u16 {
			&mut self.0
		}
	}

	impl From<u16> for U16Neutral {
		#[inline(always)]
		fn from(v: u16) -> Self {
			U16Neutral(v)
		}
	}

	impl Item for U16Neutral {
		const NEUTRAL: bool = true;

		type Storage = u16;

		#[inline(always)]
		fn is_neutral(&self) -> bool {
			self.0 == 0
		}

		#[inline(always)]
		fn is_storage_neutral(storage: &Self::Storage) -> bool {
			storage == &0u16
		}

		#[inline(always)]
		fn from_storage(storage: Self::Storage) -> Self {
			U16Neutral(storage)
		}

		#[inline(always)]
		fn into_storage(self) -> Self::Storage {
			self.0
		}
	}

	impl ItemRef for U16Neutral {
		fn from_storage_ref(storage: &Self::Storage) -> &Self {
			U16Neutral::ref_cast(storage)
		}

		fn into_storage_ref(&self) -> &Self::Storage {
			&self.0
		}

		fn from_storage_ref_mut(storage: &mut Self::Storage) -> &mut Self {
			U16Neutral::ref_cast_mut(storage)
		}

		fn into_storage_ref_mut(&mut self) -> &mut Self::Storage {
			&mut self.0
		}
	}

	#[test]
	fn test_migrate() {
		use crate::{Management, ManagementRef, ForkableManagement};
		use crate::test::simple_impl::StateInput;
		type BD = crate::backend::in_memory::MemoryOnly<u16, u32>;
		type D = crate::backend::in_memory::MemoryOnly<
			crate::historied::linear::Linear<U16Neutral, u32, BD>,
			u32,
		>;

		let check_state = |states: &mut crate::test::fuzz::InMemoryMgmtSer, target: Vec<(u32, u32)>| {
			let mut gc = states.get_migrate();
			let (pruning, mut iter) = gc.migrate().touched_state();
			assert_eq!(pruning, None);
			let mut set = std::collections::BTreeSet::new();
			for s in iter {
				set.insert(s.clone());
			}

			let reference: std::collections::BTreeSet<_> = target.into_iter().collect();
			assert_eq!(set, reference);
		};

		let mut states = crate::test::fuzz::InMemoryMgmtSer::default();
		let s0 = states.latest_state_fork();

		let mut item1: Tree<u32, u32, U16Neutral, D, BD> = InitFrom::init_from(((), ()));
		let mut item2: Tree<u32, u32, U16Neutral, D, BD> = InitFrom::init_from(((), ()));
		let s1 = states.append_external_state(StateInput(1), &s0).unwrap();
		item1.set(1.into(), &states.get_db_state_mut(&StateInput(1)).unwrap());
		item2.set(1.into(), &states.get_db_state_mut(&StateInput(1)).unwrap());
		// fusing cano
		let _ = states.append_external_state(StateInput(101), s1.latest()).unwrap();
		item1.set(2.into(), &states.get_db_state_mut(&StateInput(101)).unwrap());
		item2.set(2.into(), &states.get_db_state_mut(&StateInput(101)).unwrap());
		let s1 = states.append_external_state(StateInput(102), s1.latest()).unwrap();
		item1.set(3.into(), &states.get_db_state_mut(&StateInput(102)).unwrap());
		let s1 = states.append_external_state(StateInput(103), s1.latest()).unwrap();
		item1.set(4.into(), &states.get_db_state_mut(&StateInput(103)).unwrap());
		let _ = states.append_external_state(StateInput(104), s1.latest()).unwrap();
		item1.set(5.into(), &states.get_db_state_mut(&StateInput(104)).unwrap());
		let s1 = states.append_external_state(StateInput(105), s1.latest()).unwrap();
		item1.set(6.into(), &states.get_db_state_mut(&StateInput(105)).unwrap());
		item2.set(6.into(), &states.get_db_state_mut(&StateInput(105)).unwrap());
		// end fusing (shift following branch index by 2)
		let s2 = states.append_external_state(StateInput(2), &s0).unwrap();
		let s1b = states.append_external_state(StateInput(12), s1.latest()).unwrap();
		let s1 = states.append_external_state(StateInput(13), s1b.latest()).unwrap();
		let sx = states.append_external_state(StateInput(14), s1.latest()).unwrap();
		let qp14 = states.get_db_state(&StateInput(14)).unwrap();
		assert_eq!(states.drop_state(sx.latest(), true).unwrap().len(), 1);
		let s3 = states.append_external_state(StateInput(3), s1.latest()).unwrap();
		let s4 = states.append_external_state(StateInput(4), s1.latest()).unwrap();
		let s5 = states.append_external_state(StateInput(5), s1b.latest()).unwrap();
		// 0> 1: _ _ X
		// |			 |> 3: 1
		// |			 |> 4: 1
		// |		 |> 5: 1
		// |> 2: _ _
		let mut item3: Tree<u32, u32, U16Neutral, D, BD> = InitFrom::init_from(((), ()));
		let mut item4: Tree<u32, u32, U16Neutral, D, BD> = InitFrom::init_from(((), ()));
		item1.set(15.into(), &states.get_db_state_mut(&StateInput(5)).unwrap());
		item2.set(15.into(), &states.get_db_state_mut(&StateInput(5)).unwrap());
		item1.set(12.into(), &states.get_db_state_mut(&StateInput(2)).unwrap());

		let s3head = states.append_external_state(StateInput(32), s3.latest()).unwrap();
		item1.set(13.into(), &states.get_db_state_mut(&StateInput(32)).unwrap());
		item2.set(13.into(), &states.get_db_state_mut(&StateInput(32)).unwrap());
		item3.set(13.into(), &states.get_db_state_mut(&StateInput(32)).unwrap());
		item4.set(13.into(), &states.get_db_state_mut(&StateInput(32)).unwrap());
		let s3tmp = states.append_external_state(StateInput(33), s3head.latest()).unwrap();
		item1.set(14.into(), &states.get_db_state_mut(&StateInput(33)).unwrap());
		item3.set(0.into(), &states.get_db_state_mut(&StateInput(33)).unwrap());
		let s3head = states.append_external_state(StateInput(34), s3tmp.latest()).unwrap();
		let s6 = states.append_external_state(StateInput(6), s3tmp.latest()).unwrap();
		let s3head = states.append_external_state(StateInput(35), s3head.latest()).unwrap();
		item1.set(15.into(), &states.get_db_state_mut(&StateInput(35)).unwrap());
		item2.set(15.into(), &states.get_db_state_mut(&StateInput(35)).unwrap());
		item4.set(0.into(), &states.get_db_state_mut(&StateInput(35)).unwrap());
		item1.set(0.into(), &states.get_db_state_mut(&StateInput(6)).unwrap());

		let old_state = states.clone();
		// Apply change of composite to 33
		let filter_out = [101, 104, 2, 4, 5];
		let mut filter_qp = vec![qp14.latest_index()];
		// dropped 14
		check_state(&mut states, filter_qp.clone());
		for i in filter_out.iter() {
			let qp = states.get_db_state(&StateInput(*i)).unwrap();
			filter_qp.push(qp.latest_index());
		}

		let fp = states.get_db_state(&StateInput(35)).unwrap();
		states.canonicalize(fp, *s3tmp.latest(), None);
		// other drops from filter_out
		check_state(&mut states, filter_qp.clone());
		let filter_in = [1, 102, 103, 105, 12, 13, 32, 33, 34, 35, 6];
		let no_qp = [14];
		//panic!("{:?} \n {:?}", old_state, states);
		let mut gc_item1 = item1.clone();
		let mut gc_item2 = item2.clone();
		let mut gc_item3 = item3.clone();
		let mut gc_item4 = item4.clone();
		{
			let gc = states.get_gc().unwrap();
			gc_item1.gc(gc.as_ref());
			gc_item2.gc(gc.as_ref());
			gc_item3.gc(gc.as_ref());
			gc_item4.gc(gc.as_ref());
			//panic!("{:?}", (gc.as_ref(), item4, gc_item4));
		}
		assert_eq!(gc_item1.nb_internal_history(), 8);
		assert_eq!(gc_item2.nb_internal_history(), 4);
		assert_eq!(gc_item3.nb_internal_history(), 2); // actually untouched
		assert_eq!(gc_item4.nb_internal_history(), 2); // actually untouched
		assert_eq!(gc_item1.nb_internal_branch(), 5);
		assert_eq!(gc_item2.nb_internal_branch(), 3);
		assert_eq!(gc_item3.nb_internal_branch(), 1);
		assert_eq!(gc_item4.nb_internal_branch(), 1);

		for i in filter_in.iter() {
			let fp = states.get_db_state(&StateInput(*i)).unwrap();
			assert_eq!(gc_item1.get_ref(&fp), item1.get_ref(&fp));
			assert_eq!(gc_item2.get_ref(&fp), item2.get_ref(&fp));
			assert_eq!(gc_item3.get_ref(&fp), item3.get_ref(&fp));
			assert_eq!(gc_item4.get_ref(&fp), item4.get_ref(&fp));
		}
//		panic!("{:?}", (gc, item1, gc_item1));

		// migrate 
		let filter_in = [33, 34, 35, 6];
		let mut gc_item1 = item1.clone();
		let mut gc_item2 = item2.clone();
		let mut gc_item3 = item3.clone();
		let mut gc_item4 = item4.clone();
		let mut states = states;
		{
			let mut gc = states.get_migrate();
			gc_item1.migrate(gc.migrate());
			gc_item2.migrate(gc.migrate());
			gc_item3.migrate(gc.migrate());
			gc_item4.migrate(gc.migrate());
			gc.applied_migrate();
		}
		// empty (applied_migrate ran)
		check_state(&mut states, vec![]);

		for i in filter_in.iter() {
			let fp = states.get_db_state(&StateInput(*i)).unwrap();
			assert_eq!(gc_item1.get_ref(&fp), item1.get_ref(&fp));
			assert_eq!(gc_item2.get_ref(&fp), item2.get_ref(&fp));
			assert_eq!(gc_item3.get_ref(&fp), item3.get_ref(&fp));
			assert_eq!(gc_item4.get_ref(&fp), item4.get_ref(&fp));
		}
		assert_eq!(gc_item1.nb_internal_history(), 8);
		assert_eq!(gc_item2.nb_internal_history(), 4);
		assert_eq!(gc_item3.nb_internal_history(), 2);
		assert_eq!(gc_item4.nb_internal_history(), 2);
		assert_eq!(gc_item1.nb_internal_branch(), 2);
		assert_eq!(gc_item2.nb_internal_branch(), 1);
		assert_eq!(gc_item3.nb_internal_branch(), 1);
		assert_eq!(gc_item4.nb_internal_branch(), 1);

		// on previous state set migrate with pruning_treshold 
		let filter_in = [33, 34, 35, 6];
		let mut gc_item1 = item1.clone();
		let mut gc_item2 = item2.clone();
		let mut gc_item3 = item3.clone();
		let mut gc_item4 = item4.clone();
		let mut states = old_state;
		let fp = states.get_db_state(&StateInput(35)).unwrap();
		states.canonicalize(fp, *s3tmp.latest(), Some(s3tmp.latest().1));
		{
			let mut gc = states.get_migrate();
			gc_item1.migrate(gc.migrate());
			gc_item2.migrate(gc.migrate());
			gc_item3.migrate(gc.migrate());
			gc_item4.migrate(gc.migrate());
			gc.applied_migrate();
			//panic!("{:?}", (gc, item3, gc_item3));
		}
		for i in filter_in.iter() {
			let fp = states.get_db_state(&StateInput(*i)).unwrap();
			assert_eq!(gc_item1.get_ref(&fp), item1.get_ref(&fp));
			assert_eq!(gc_item2.get_ref(&fp), item2.get_ref(&fp));
			assert_eq!(gc_item3.get_ref(&fp), None); // neutral element
			assert_eq!(gc_item4.get_ref(&fp), item4.get_ref(&fp));
		}
		assert_eq!(gc_item1.nb_internal_history(), 3);
		assert_eq!(gc_item2.nb_internal_history(), 2);
		assert_eq!(gc_item3.nb_internal_history(), 0);
		assert_eq!(gc_item4.nb_internal_history(), 2);
		assert_eq!(gc_item1.nb_internal_branch(), 2);
		assert_eq!(gc_item2.nb_internal_branch(), 1);
		assert_eq!(gc_item3.nb_internal_branch(), 0);
		assert_eq!(gc_item4.nb_internal_branch(), 1);
	}

	#[test]
	fn test_diff1() {
		use crate::historied::{DiffBuilder};
		use crate::historied::xdelta::{BytesDelta, BytesDiff, BytesDiffBuilder}; 
		use crate::{Management, ManagementRef, ForkableManagement};
		use crate::test::simple_impl::StateInput;
		type BD = crate::backend::in_memory::MemoryOnly<Vec<u8>, u32>;
		type D = crate::backend::in_memory::MemoryOnly<
			crate::historied::linear::Linear<BytesDiff, u32, BD>,
			u32,
		>;

		// 0> 1: _ _ X
		// |			 |> 3: 1
		// |			 |> 4: 1
		// |		 |> 5: 1
		// |> 2: _
		let mut states = test_states();
		let mut item: Tree<u32, u32, BytesDiff, D, BD> = InitFrom::init_from(((), ()));

		let successive_values: Vec<BytesDelta> = vec![
			[0u8, 1, 2, 3][..].into(), // (1, 1)
			[1, 1, 2, 3][..].into(), // (1,2)
			[1, 3][..].into(), // (3, 3)
			[][..].into(), // 4, 3 (follow) (1, 2)
		];

		let mut successive_deltas: Vec<BytesDiff> = Vec::with_capacity(successive_values.len());

		let mut builder = BytesDiffBuilder::new_diff_builder();
		successive_deltas.push(builder.calculate_diff(&Default::default(), &successive_values[0]));
		successive_deltas.push(builder.calculate_diff(&successive_values[0], &successive_values[1]));
		successive_deltas.push(builder.calculate_diff(&successive_values[1], &successive_values[2]));
		successive_deltas.push(builder.calculate_diff(&successive_values[1], &successive_values[3]));

		let successive_deltas = successive_deltas;

		item.set(successive_deltas[0].clone(), &Latest::unchecked_latest((1, 1)));
		item.set(successive_deltas[1].clone(), &Latest::unchecked_latest((1, 2)));
		item.set(successive_deltas[2].clone(), &Latest::unchecked_latest((3, 3)));
		item.set(successive_deltas[3].clone(), &Latest::unchecked_latest((4, 3)));

		assert_eq!(item.get(&states.query_plan(1)).as_ref(), Some(&successive_deltas[1]));
		assert_eq!(item.get(&states.query_plan(3)).as_ref(), Some(&successive_deltas[2]));
		assert_eq!(item.get(&states.query_plan(4)).as_ref(), Some(&successive_deltas[3]));

		let item = TreeDiff::<_, _, BytesDelta, _, _>(&item);
		assert_eq!(item.get_diff(&states.query_plan(1)).as_ref(), Some(&successive_values[1]));
		assert_eq!(item.get_diff(&states.query_plan(3)).as_ref(), Some(&successive_values[2]));
		assert_eq!(item.get_diff(&states.query_plan(4)).as_ref(), Some(&successive_values[3]));
	}

	#[test]
	fn test_diff2() {
		use crate::historied::map_delta::{MapDelta, MapDiff}; 
		use crate::{Management, ManagementRef, ForkableManagement};
		use crate::test::simple_impl::StateInput;
		type BD = crate::backend::in_memory::MemoryOnly<Vec<u8>, u32>;
		type D = crate::backend::in_memory::MemoryOnly<
			crate::historied::linear::Linear<MapDiff<u8, u8>, u32, BD>,
			u32,
		>;

		// 0> 1: _ _ X
		// |			 |> 3: 1
		// |			 |> 4: 1
		// |		 |> 5: 1
		// |> 2: _
		let mut states = test_states();
		let mut item: Tree<u32, u32, MapDiff<u8, u8>, D, BD> = InitFrom::init_from(((), ()));

		let successive_values: Vec<MapDelta<u8, u8>> = vec![
			MapDelta::default(), // (1, 1)
			MapDelta([(0, 1)][..].iter().cloned().collect()), // (1,2)
			MapDelta([(0, 1), (1, 3)][..].iter().cloned().collect()), // (3, 3)
			MapDelta::default(), // (1, 1)
		];

		let successive_deltas: Vec<MapDiff<u8, u8>> = vec![
			MapDiff::Reset,
			MapDiff::Insert(0, 1),
			MapDiff::Insert(1, 3),
			MapDiff::Remove(0),
		];

		item.set(successive_deltas[0].clone(), &Latest::unchecked_latest((1, 1)));
		item.set(successive_deltas[1].clone(), &Latest::unchecked_latest((1, 2)));
		item.set(successive_deltas[2].clone(), &Latest::unchecked_latest((3, 3)));
		item.set(successive_deltas[3].clone(), &Latest::unchecked_latest((4, 3)));

		assert_eq!(item.get(&states.query_plan(1)).as_ref(), Some(&successive_deltas[1]));
		assert_eq!(item.get(&states.query_plan(3)).as_ref(), Some(&successive_deltas[2]));
		assert_eq!(item.get(&states.query_plan(4)).as_ref(), Some(&successive_deltas[3]));

		let item = TreeDiff::<_, _, MapDelta<u8, u8>, _, _>(&item);
		assert_eq!(item.get_diff(&states.query_plan(1)).as_ref(), Some(&successive_values[1]));
		assert_eq!(item.get_diff(&states.query_plan(3)).as_ref(), Some(&successive_values[2]));
		assert_eq!(item.get_diff(&states.query_plan(4)).as_ref(), Some(&successive_values[3]));
	}
}

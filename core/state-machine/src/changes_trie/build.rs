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

//! Structures and functions required to build changes trie for given block.

use primitives::child_trie::ChildTrie;
use std::collections::{BTreeMap, BTreeSet};
use std::collections::btree_map::Entry;
use codec::Decode;
use hash_db::Hasher;
use num_traits::One;
use crate::backend::Backend;
use crate::overlayed_changes::{OverlayedChanges, OverlayedValueResult};
use crate::trie_backend_essence::TrieBackendEssence;
use crate::changes_trie::build_iterator::digest_build_iterator;
use crate::changes_trie::input::{InputKey, InputPair, DigestIndex, ExtrinsicIndex};
use crate::changes_trie::{AnchorBlockId, ConfigurationRange, Storage, BlockNumber};
use crate::changes_trie::input::ChildIndex;

/// Prepare input pairs for building a changes trie of given block.
///
/// Returns Err if storage error has occurred OR if storage haven't returned
/// required data.
pub(crate) fn prepare_input<'a, B, H, Number>(
	backend: &'a B,
	storage: &'a dyn Storage<H, Number>,
	config: ConfigurationRange<'a, Number>,
	changes: &'a OverlayedChanges,
	parent: &'a AnchorBlockId<H::Out, Number>,
) -> Result<(
		impl Iterator<Item=InputPair<Number>> + 'a,
		Vec<(ChildIndex<Number>, impl Iterator<Item=InputPair<Number>> + 'a)>,
		Vec<Number>,
	), String>
	where
		B: Backend<H>,
		H: Hasher + 'a,
		Number: BlockNumber,
{
	let number = parent.number.clone() + One::one();
	let (extrinsics_input, children_extrinsics_input) = prepare_extrinsics_input(
		backend,
		&number,
		changes,
	)?;
	let (digest_input, mut children_digest_input, digest_input_blocks) = prepare_digest_input::<H, Number>(
		parent,
		config,
		number,
		storage,
	)?;

	let mut children_digest = Vec::with_capacity(children_extrinsics_input.len());
	for (child_index, ext_iter) in children_extrinsics_input.into_iter() {
		let dig_iter = children_digest_input.remove(&child_index);
		children_digest.push((
			child_index,
			Some(ext_iter).into_iter().flatten()
				.chain(dig_iter.into_iter().flatten()),
		));
	}
	for (child_index, dig_iter) in children_digest_input.into_iter() {
		children_digest.push((
			child_index,
			None.into_iter().flatten()
				.chain(Some(dig_iter).into_iter().flatten()),
		));
	}

	Ok((
		extrinsics_input.chain(digest_input),
		children_digest,
		digest_input_blocks,
	))
}
/// Prepare ExtrinsicIndex input pairs.
fn prepare_extrinsics_input<'a, B, H, Number>(
	backend: &'a B,
	block: &Number,
	changes: &'a OverlayedChanges,
) -> Result<(
		impl Iterator<Item=InputPair<Number>> + 'a,
		BTreeMap<ChildIndex<Number>, impl Iterator<Item=InputPair<Number>> + 'a>,
	), String>
	where
		B: Backend<H>,
		H: Hasher + 'a,
		Number: BlockNumber,
{

	let mut children_tries = BTreeSet::<ChildTrie>::new();
	let mut children_result = BTreeMap::new();
	for (_ks, v) in changes.prospective.children.iter()
		.chain(changes.committed.children.iter()) {
		children_tries.insert(v.child_trie.clone());
	}
	for child_trie in children_tries {
		let child_index = ChildIndex::<Number> {
			block: block.clone(),
			storage_key: child_trie.parent_slice().to_vec(),
		};
	
		let iter = prepare_extrinsics_input_inner(backend, block, changes, Some(child_trie))?;
		children_result.insert(child_index, iter);
	}

	let top = prepare_extrinsics_input_inner(backend, block, changes, None)?;

	Ok((top, children_result))
}
	
fn prepare_extrinsics_input_inner<'a, B, H, Number>(
	backend: &'a B,
	block: &Number,
	changes: &'a OverlayedChanges,
	child_trie: Option<ChildTrie>,
) -> Result<impl Iterator<Item=InputPair<Number>> + 'a, String>
	where
		B: Backend<H>,
		H: Hasher,
		Number: BlockNumber,
{
	let (committed, prospective) = if let Some(ct) = child_trie.as_ref() {
		(
			changes.committed.children.get(ct.keyspace())
				.map(|cs| &cs.values),
			changes.prospective.children.get(ct.keyspace())
				.map(|cs| &cs.values),
		)
	} else {
		(Some(&changes.committed.top), Some(&changes.prospective.top))
	};
	committed.iter().flat_map(|c| c.iter())
		.chain(prospective.iter().flat_map(|c| c.iter()))
		.filter(|( _, v)| v.extrinsics.is_some())
		.try_fold(BTreeMap::new(), |mut map: BTreeMap<&[u8], (ExtrinsicIndex<Number>, Vec<u32>)>, (k, v)| {
			match map.entry(k) {
				Entry::Vacant(entry) => {
					// ignore temporary values (values that have null value at the end of operation
					// AND are not in storage at the beginning of operation
	
					if let Some(ct) = child_trie.as_ref() {
						match changes.child_storage(ct.node_ref(), k) {
							OverlayedValueResult::NotFound
							| OverlayedValueResult::Deleted => {
								if !backend.exists_storage(k).map_err(|e| format!("{}", e))? {
									return Ok(map)
								}
							},
							OverlayedValueResult::Modified(_val) => (),
						}
					} else {
						match changes.storage(k) {
							OverlayedValueResult::NotFound
							| OverlayedValueResult::Deleted => {
								if !backend.exists_storage(k).map_err(|e| format!("{}", e))? {
									return Ok(map)
								}
							},
							OverlayedValueResult::Modified(_val) => (),
						}
					};

					let extrinsics = v.extrinsics.as_ref()
						.expect("filtered by filter() call above; qed")
						.iter().cloned().collect();
					entry.insert((ExtrinsicIndex {
						block: block.clone(),
						key: k.to_vec(),
					}, extrinsics));
				},
				Entry::Occupied(mut entry) => {
					// we do not need to check for temporary values here, because entry is Occupied
					// AND we are checking it before insertion
					let extrinsics = &mut entry.get_mut().1;
					extrinsics.extend(
						v.extrinsics.as_ref()
							.expect("filtered by filter() call above; qed")
							.iter()
							.cloned()
					);
					extrinsics.sort_unstable();
				},
			}

			Ok(map)
		})
		.map(|pairs| pairs.into_iter().map(|(_, (k, v))| InputPair::ExtrinsicIndex(k, v)))
}


/// Prepare DigestIndex input pairs.
fn prepare_digest_input<'a, H, Number>(
	parent: &'a AnchorBlockId<H::Out, Number>,
	config: ConfigurationRange<Number>,
	block: Number,
	storage: &'a dyn Storage<H, Number>,
) -> Result<(
		impl Iterator<Item=InputPair<Number>> + 'a,
		BTreeMap<ChildIndex<Number>, impl Iterator<Item=InputPair<Number>> + 'a>,
		Vec<Number>,
	), String>
	where
		H: Hasher,
		H::Out: 'a,
		Number: BlockNumber,
{
	let build_skewed_digest = config.end.as_ref() == Some(&block);
	let block_for_digest = if build_skewed_digest {
		config.config.next_max_level_digest_range(config.zero.clone(), block.clone())
			.map(|(_, end)| end)
			.unwrap_or_else(|| block.clone())
	} else {
		block.clone()
	};

	let digest_input_blocks = digest_build_iterator(config, block_for_digest).collect::<Vec<_>>();
	digest_input_blocks.clone().into_iter()
		.try_fold(
			(BTreeMap::new(), BTreeMap::new()), move |(mut map, mut child_map), digest_build_block| {
			let extrinsic_prefix = ExtrinsicIndex::key_neutral_prefix(digest_build_block.clone());
			let digest_prefix = DigestIndex::key_neutral_prefix(digest_build_block.clone());
			let child_prefix = ChildIndex::key_neutral_prefix(digest_build_block.clone());
			let trie_root = storage.root(parent, digest_build_block.clone())?;
			let trie_root = trie_root.ok_or_else(|| format!("No changes trie root for block {}", digest_build_block.clone()))?;

			let insert_to_map = |map: &mut BTreeMap<_,_>, key: Vec<u8>| {
				match map.entry(key.clone()) {
					Entry::Vacant(entry) => {
						entry.insert((DigestIndex {
							block: block.clone(),
							key,
						}, vec![digest_build_block.clone()]));
					},
					Entry::Occupied(mut entry) => {
						// DigestIndexValue must be sorted. Here we are relying on the fact that digest_build_iterator()
						// returns blocks in ascending order => we only need to check for duplicates
						//
						// is_dup_block could be true when key has been changed in both digest block
						// AND other blocks that it covers
						let is_dup_block = entry.get().1.last() == Some(&digest_build_block);
						if !is_dup_block {
							entry.get_mut().1.push(digest_build_block.clone());
						}
					},
				}
			};

			// try to get all updated keys from cache
			let populated_from_cache = storage.with_cached_changed_keys(
				&trie_root,
				&mut |changed_keys| {
					for (storage_key, changed_keys) in changed_keys {
						let map = match storage_key {
							Some(storage_key) => child_map
								.entry(ChildIndex::<Number> {
									block: block.clone(),
									storage_key: storage_key.clone(),
								})
								.or_default(),
							None => &mut map,
						};
						for changed_key in changed_keys.iter().cloned() {
							insert_to_map(map, changed_key);
						}
					}
				}
			);
			if populated_from_cache {
				return Ok((map, child_map));
			}

			let mut children_roots = BTreeMap::<Vec<u8>, _>::new();
			{
				let trie_storage = TrieBackendEssence::<_, H>::new(
					crate::changes_trie::TrieBackendStorageAdapter(storage),
					trie_root,
				);

				trie_storage.for_key_values_with_prefix(&child_prefix, |key, value|
					if let Ok(InputKey::ChildIndex::<Number>(trie_key)) = Decode::decode(&mut &key[..]) {
						if let Ok(value) = <Vec<u8>>::decode(&mut &value[..]) {
							let mut trie_root = <H as Hasher>::Out::default();
							trie_root.as_mut().copy_from_slice(&value[..]);
							children_roots.insert(trie_key.storage_key, trie_root);
						}
					});

				trie_storage.for_keys_with_prefix(&extrinsic_prefix, |key|
					if let Ok(InputKey::ExtrinsicIndex::<Number>(trie_key)) = Decode::decode(&mut &key[..]) {
						insert_to_map(&mut map, trie_key.key);
					});

				trie_storage.for_keys_with_prefix(&digest_prefix, |key|
					if let Ok(InputKey::DigestIndex::<Number>(trie_key)) = Decode::decode(&mut &key[..]) {
						insert_to_map(&mut map, trie_key.key);
					});
			}

			for (storage_key, trie_root) in children_roots.into_iter() {
				let child_index = ChildIndex::<Number> {
					block: block.clone(),
					storage_key,
				};

				let mut map = child_map.entry(child_index).or_default();
				let trie_storage = TrieBackendEssence::<_, H>::new(
					crate::changes_trie::TrieBackendStorageAdapter(storage),
					trie_root,
				);
				trie_storage.for_keys_with_prefix(&extrinsic_prefix, |key|
					if let Ok(InputKey::ExtrinsicIndex::<Number>(trie_key)) = Decode::decode(&mut &key[..]) {
						insert_to_map(&mut map, trie_key.key);
					});

				trie_storage.for_keys_with_prefix(&digest_prefix, |key|
					if let Ok(InputKey::DigestIndex::<Number>(trie_key)) = Decode::decode(&mut &key[..]) {
						insert_to_map(&mut map, trie_key.key);
					});
			}
			Ok((map, child_map))
		})
		.map(|(pairs, child_pairs)| (
			pairs.into_iter().map(|(_, (k, v))| InputPair::DigestIndex(k, v)),
			child_pairs.into_iter().map(|(sk, pairs)|
				(sk, pairs.into_iter().map(|(_, (k, v))| InputPair::DigestIndex(k, v)))).collect(),
			digest_input_blocks,
		))
}

#[cfg(test)]
mod test {
	use codec::Encode;
	use primitives::{Blake2Hasher, map};
	use primitives::storage::well_known_keys::{EXTRINSIC_INDEX};
	use crate::backend::InMemory;
	use crate::changes_trie::{RootsStorage, Configuration, storage::InMemoryStorage};
	use crate::changes_trie::build_cache::{IncompleteCacheAction, IncompleteCachedBuildData};
	use crate::overlayed_changes::{OverlayedValue, OverlayedChangeSet, ChildOverlayChangeSet};
	use super::*;

	fn prepare_for_build(zero: u64) -> (
		InMemory<Blake2Hasher>,
		InMemoryStorage<Blake2Hasher, u64>,
		OverlayedChanges,
		Configuration,
	) {
		let config = Configuration { digest_interval: 4, digest_levels: 2 };
		let backend: InMemory<_> = vec![
			(vec![100], vec![255]),
			(vec![101], vec![255]),
			(vec![102], vec![255]),
			(vec![103], vec![255]),
			(vec![104], vec![255]),
			(vec![105], vec![255]),
		].into_iter().collect::<::std::collections::HashMap<_, _>>().into();
		let child_trie_key1 = b":child_storage:default:1".to_vec();
		let child_trie_key2 = b":child_storage:default:2".to_vec();
		let child_trie1 = ChildTrie::fetch_or_new(|_| None, |_| (), &b"1"[..], || 3u128);
		let child_trie2 = ChildTrie::fetch_or_new(|_| None, |_| (), &b"2"[..], || 4u128);
		let keyspace1 = child_trie1.keyspace().to_vec();
		let keyspace2 = child_trie2.keyspace().to_vec();
		let storage = InMemoryStorage::with_inputs(vec![
			(zero + 1, vec![
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: zero + 1, key: vec![100] }, vec![1, 3]),
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: zero + 1, key: vec![101] }, vec![0, 2]),
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: zero + 1, key: vec![105] }, vec![0, 2, 4]),
			]),
			(zero + 2, vec![
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: zero + 2, key: vec![102] }, vec![0]),
			]),
			(zero + 3, vec![
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: zero + 3, key: vec![100] }, vec![0]),
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: zero + 3, key: vec![105] }, vec![1]),
			]),
			(zero + 4, vec![
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: zero + 4, key: vec![100] }, vec![0, 2, 3]),
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: zero + 4, key: vec![101] }, vec![1]),
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: zero + 4, key: vec![103] }, vec![0, 1]),

				InputPair::DigestIndex(DigestIndex { block: zero + 4, key: vec![100] }, vec![zero + 1, zero + 3]),
				InputPair::DigestIndex(DigestIndex { block: zero + 4, key: vec![101] }, vec![zero + 1]),
				InputPair::DigestIndex(DigestIndex { block: zero + 4, key: vec![102] }, vec![zero + 2]),
				InputPair::DigestIndex(DigestIndex { block: zero + 4, key: vec![105] }, vec![zero + 1, zero + 3]),
			]),
			(zero + 5, Vec::new()),
			(zero + 6, vec![
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: zero + 6, key: vec![105] }, vec![2]),
			]),
			(zero + 7, Vec::new()),
			(zero + 8, vec![
				InputPair::DigestIndex(DigestIndex { block: zero + 8, key: vec![105] }, vec![zero + 6]),
			]),
			(zero + 9, Vec::new()), (zero + 10, Vec::new()), (zero + 11, Vec::new()), (zero + 12, Vec::new()),
			(zero + 13, Vec::new()), (zero + 14, Vec::new()), (zero + 15, Vec::new()),
		], vec![(child_trie1.clone(), vec![
				(zero + 1, vec![
					InputPair::ExtrinsicIndex(ExtrinsicIndex { block: zero + 1, key: vec![100] }, vec![1, 3]),
					InputPair::ExtrinsicIndex(ExtrinsicIndex { block: zero + 1, key: vec![101] }, vec![0, 2]),
					InputPair::ExtrinsicIndex(ExtrinsicIndex { block: zero + 1, key: vec![105] }, vec![0, 2, 4]),
				]),
				(zero + 2, vec![
					InputPair::ExtrinsicIndex(ExtrinsicIndex { block: zero + 2, key: vec![102] }, vec![0]),
				]),
				(zero + 4, vec![
					InputPair::ExtrinsicIndex(ExtrinsicIndex { block: zero + 2, key: vec![102] }, vec![0, 3]),

					InputPair::DigestIndex(DigestIndex { block: zero + 4, key: vec![102] }, vec![zero + 2]),
				]),
			]),
		]);
		let changes = OverlayedChanges {
			prospective: OverlayedChangeSet { top: vec![
					(vec![100], OverlayedValue {
						value: Some(vec![200]),
						extrinsics: Some(vec![0, 2].into_iter().collect())
					}),
					(vec![103], OverlayedValue {
						value: None,
						extrinsics: Some(vec![0, 1].into_iter().collect())
					}),
				].into_iter().collect(),
				children: vec![
					(keyspace1.clone(), ChildOverlayChangeSet {
						child_trie: child_trie1.clone(),
						values: vec![
							(vec![100], OverlayedValue {
								value: Some(vec![200]),
								extrinsics: Some(vec![0, 2].into_iter().collect())
							})
						].into_iter().collect()
					}),
					(keyspace2.clone(), ChildOverlayChangeSet {
						child_trie: child_trie2,
						values: vec![
							(vec![100], OverlayedValue {
								value: Some(vec![200]),
								extrinsics: Some(vec![0, 2].into_iter().collect())
							})
						].into_iter().collect()
					}),
				].into_iter().collect(),
				pending_child: map![
					child_trie_key1.clone() => Some(keyspace1.clone()),
					child_trie_key2 => Some(keyspace2) 
				],
			},
			committed: OverlayedChangeSet { top: vec![
					(EXTRINSIC_INDEX.to_vec(), OverlayedValue {
						value: Some(3u32.encode()),
						extrinsics: None,
					}),
					(vec![100], OverlayedValue {
						value: Some(vec![202]),
						extrinsics: Some(vec![3].into_iter().collect())
					}),
					(vec![101], OverlayedValue {
						value: Some(vec![203]),
						extrinsics: Some(vec![1].into_iter().collect())
					}),
				].into_iter().collect(),
				children: vec![
					(keyspace1.clone(), ChildOverlayChangeSet {
						child_trie: child_trie1,
						values: vec![
							(vec![100], OverlayedValue {
								value: Some(vec![202]),
								extrinsics: Some(vec![3].into_iter().collect())
							})
						].into_iter().collect()
					}),
				].into_iter().collect(),
				pending_child: map![
					child_trie_key1 => Some(keyspace1)
				],
			},
			changes_trie_config: Some(config.clone()),
		};

		(backend, storage, changes, config)
	}

	fn configuration_range<'a>(config: &'a Configuration, zero: u64) -> ConfigurationRange<'a, u64> {
		ConfigurationRange {
			config,
			zero,
			end: None,
		}
	}

	#[test]
	fn build_changes_trie_nodes_on_non_digest_block() {
		fn test_with_zero(zero: u64) {
			let (backend, storage, changes, config) = prepare_for_build(zero);
			let parent = AnchorBlockId { hash: Default::default(), number: zero + 4 };
			let changes_trie_nodes = prepare_input(
				&backend,
				&storage,
				configuration_range(&config, zero),
				&changes,
				&parent,
			).unwrap();
			assert_eq!(changes_trie_nodes.0.collect::<Vec<InputPair<u64>>>(), vec![
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: zero + 5, key: vec![100] }, vec![0, 2, 3]),
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: zero + 5, key: vec![101] }, vec![1]),
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: zero + 5, key: vec![103] }, vec![0, 1]),
			]);
			assert_eq!(changes_trie_nodes.1.into_iter()
				.map(|(k,v)| (k, v.collect::<Vec<_>>())).collect::<Vec<_>>(), vec![
				(ChildIndex { block: zero + 5u64, storage_key: b"1".to_vec() },
					vec![
						InputPair::ExtrinsicIndex(ExtrinsicIndex { block: zero + 5u64, key: vec![100] }, vec![0, 2, 3]),
					]),
				(ChildIndex { block: zero + 5, storage_key: b"2".to_vec() },
					vec![
						InputPair::ExtrinsicIndex(ExtrinsicIndex { block: zero + 5, key: vec![100] }, vec![0, 2]),
					]),
			]);

		}

		test_with_zero(0);
		test_with_zero(16);
		test_with_zero(17);
	}

	#[test]
	fn build_changes_trie_nodes_on_digest_block_l1() {
		fn test_with_zero(zero: u64) {
			let (backend, storage, changes, config) = prepare_for_build(zero);
			let parent = AnchorBlockId { hash: Default::default(), number: zero + 3 };
			let changes_trie_nodes = prepare_input(
				&backend,
				&storage,
				configuration_range(&config, zero),
				&changes,
				&parent,
			).unwrap();
			assert_eq!(changes_trie_nodes.0.collect::<Vec<InputPair<u64>>>(), vec![
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: zero + 4, key: vec![100] }, vec![0, 2, 3]),
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: zero + 4, key: vec![101] }, vec![1]),
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: zero + 4, key: vec![103] }, vec![0, 1]),

				InputPair::DigestIndex(DigestIndex { block: zero + 4, key: vec![100] }, vec![zero + 1, zero + 3]),
				InputPair::DigestIndex(DigestIndex { block: zero + 4, key: vec![101] }, vec![zero + 1]),
				InputPair::DigestIndex(DigestIndex { block: zero + 4, key: vec![102] }, vec![zero + 2]),
				InputPair::DigestIndex(DigestIndex { block: zero + 4, key: vec![105] }, vec![zero + 1, zero + 3]),
			]);
			assert_eq!(changes_trie_nodes.1.into_iter()
				.map(|(k,v)| (k, v.collect::<Vec<_>>())).collect::<Vec<_>>(), vec![
				(ChildIndex { block: zero + 4u64, storage_key: b"1".to_vec() },
					vec![
						InputPair::ExtrinsicIndex(ExtrinsicIndex { block: zero + 4u64, key: vec![100] }, vec![0, 2, 3]),

						InputPair::DigestIndex(DigestIndex { block: zero + 4, key: vec![100] }, vec![zero + 1]),
						InputPair::DigestIndex(DigestIndex { block: zero + 4, key: vec![101] }, vec![zero + 1]),
						InputPair::DigestIndex(DigestIndex { block: zero + 4, key: vec![102] }, vec![zero + 2]),
						InputPair::DigestIndex(DigestIndex { block: zero + 4, key: vec![105] }, vec![zero + 1]),
					]),
				(ChildIndex { block: zero + 4, storage_key: b"2".to_vec() },
					vec![
						InputPair::ExtrinsicIndex(ExtrinsicIndex { block: zero + 4, key: vec![100] }, vec![0, 2]),
					]),
			]);

		}

		test_with_zero(0);
		test_with_zero(16);
		test_with_zero(17);
	}

	#[test]
	fn build_changes_trie_nodes_on_digest_block_l2() {
		fn test_with_zero(zero: u64) {
			let (backend, storage, changes, config) = prepare_for_build(zero);
			let parent = AnchorBlockId { hash: Default::default(), number: zero + 15 };
			let changes_trie_nodes = prepare_input(
				&backend,
				&storage,
				configuration_range(&config, zero),
				&changes,
				&parent,
			).unwrap();
			assert_eq!(changes_trie_nodes.0.collect::<Vec<InputPair<u64>>>(), vec![
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: zero + 16, key: vec![100] }, vec![0, 2, 3]),
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: zero + 16, key: vec![101] }, vec![1]),
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: zero + 16, key: vec![103] }, vec![0, 1]),

				InputPair::DigestIndex(DigestIndex { block: zero + 16, key: vec![100] }, vec![zero + 4]),
				InputPair::DigestIndex(DigestIndex { block: zero + 16, key: vec![101] }, vec![zero + 4]),
				InputPair::DigestIndex(DigestIndex { block: zero + 16, key: vec![102] }, vec![zero + 4]),
				InputPair::DigestIndex(DigestIndex { block: zero + 16, key: vec![103] }, vec![zero + 4]),
				InputPair::DigestIndex(DigestIndex { block: zero + 16, key: vec![105] }, vec![zero + 4, zero + 8]),
			]);
			assert_eq!(changes_trie_nodes.1.into_iter()
				.map(|(k,v)| (k, v.collect::<Vec<_>>())).collect::<Vec<_>>(), vec![
				(ChildIndex { block: zero + 16u64, storage_key: b"1".to_vec() },
					vec![
						InputPair::ExtrinsicIndex(ExtrinsicIndex { block: zero + 16u64, key: vec![100] }, vec![0, 2, 3]),

						InputPair::DigestIndex(DigestIndex { block: zero + 16, key: vec![102] }, vec![zero + 4]),
					]),
				(ChildIndex { block: zero + 16, storage_key: b"2".to_vec() },
					vec![
						InputPair::ExtrinsicIndex(ExtrinsicIndex { block: zero + 16, key: vec![100] }, vec![0, 2]),
					]),
			]);

		}

		test_with_zero(0);
		test_with_zero(16);
		test_with_zero(17);
	}

	#[test]
	fn build_changes_trie_nodes_on_skewed_digest_block() {
		fn test_with_zero(zero: u64) {
			let (backend, storage, changes, config) = prepare_for_build(zero);
			let parent = AnchorBlockId { hash: Default::default(), number: zero + 10 };

			let mut configuration_range = configuration_range(&config, zero);
			let changes_trie_nodes = prepare_input(
				&backend,
				&storage,
				configuration_range.clone(),
				&changes,
				&parent,
			).unwrap();
			assert_eq!(changes_trie_nodes.0.collect::<Vec<InputPair<u64>>>(), vec![
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: zero + 11, key: vec![100] }, vec![0, 2, 3]),
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: zero + 11, key: vec![101] }, vec![1]),
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: zero + 11, key: vec![103] }, vec![0, 1]),
			]);

			configuration_range.end = Some(zero + 11);
			let changes_trie_nodes = prepare_input(
				&backend,
				&storage,
				configuration_range,
				&changes,
				&parent,
			).unwrap();
			assert_eq!(changes_trie_nodes.0.collect::<Vec<InputPair<u64>>>(), vec![
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: zero + 11, key: vec![100] }, vec![0, 2, 3]),
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: zero + 11, key: vec![101] }, vec![1]),
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: zero + 11, key: vec![103] }, vec![0, 1]),

				InputPair::DigestIndex(DigestIndex { block: zero + 11, key: vec![100] }, vec![zero + 4]),
				InputPair::DigestIndex(DigestIndex { block: zero + 11, key: vec![101] }, vec![zero + 4]),
				InputPair::DigestIndex(DigestIndex { block: zero + 11, key: vec![102] }, vec![zero + 4]),
				InputPair::DigestIndex(DigestIndex { block: zero + 11, key: vec![103] }, vec![zero + 4]),
				InputPair::DigestIndex(DigestIndex { block: zero + 11, key: vec![105] }, vec![zero + 4, zero + 8]),
			]);
		}

		test_with_zero(0);
		test_with_zero(16);
		test_with_zero(17);
	}

	#[test]
	fn build_changes_trie_nodes_ignores_temporary_storage_values() {
		fn test_with_zero(zero: u64) {
			let (backend, storage, mut changes, config) = prepare_for_build(zero);

			// 110: missing from backend, set to None in overlay
			changes.prospective.top.insert(vec![110], OverlayedValue {
				value: None,
				extrinsics: Some(vec![1].into_iter().collect())
			});

			let parent = AnchorBlockId { hash: Default::default(), number: zero + 3 };
			let changes_trie_nodes = prepare_input(
				&backend,
				&storage,
				configuration_range(&config, zero),
				&changes,
				&parent,
			).unwrap();
			assert_eq!(changes_trie_nodes.0.collect::<Vec<InputPair<u64>>>(), vec![
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: zero + 4, key: vec![100] }, vec![0, 2, 3]),
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: zero + 4, key: vec![101] }, vec![1]),
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: zero + 4, key: vec![103] }, vec![0, 1]),

				InputPair::DigestIndex(DigestIndex { block: zero + 4, key: vec![100] }, vec![zero + 1, zero + 3]),
				InputPair::DigestIndex(DigestIndex { block: zero + 4, key: vec![101] }, vec![zero + 1]),
				InputPair::DigestIndex(DigestIndex { block: zero + 4, key: vec![102] }, vec![zero + 2]),
				InputPair::DigestIndex(DigestIndex { block: zero + 4, key: vec![105] }, vec![zero + 1, zero + 3]),
			]);
			assert_eq!(changes_trie_nodes.1.into_iter()
				.map(|(k,v)| (k, v.collect::<Vec<_>>())).collect::<Vec<_>>(), vec![
				(ChildIndex { block: zero + 4u64, storage_key: b"1".to_vec() },
					vec![
						InputPair::ExtrinsicIndex(ExtrinsicIndex { block: zero + 4u64, key: vec![100] }, vec![0, 2, 3]),

						InputPair::DigestIndex(DigestIndex { block: zero + 4, key: vec![100] }, vec![zero + 1]),
						InputPair::DigestIndex(DigestIndex { block: zero + 4, key: vec![101] }, vec![zero + 1]),
						InputPair::DigestIndex(DigestIndex { block: zero + 4, key: vec![102] }, vec![zero + 2]),
						InputPair::DigestIndex(DigestIndex { block: zero + 4, key: vec![105] }, vec![zero + 1]),
					]),
				(ChildIndex { block: zero + 4, storage_key: b"2".to_vec() },
					vec![
						InputPair::ExtrinsicIndex(ExtrinsicIndex { block: zero + 4, key: vec![100] }, vec![0, 2]),
					]),
			]);

		}

		test_with_zero(0);
		test_with_zero(16);
		test_with_zero(17);
	}

	#[test]
	fn cache_is_used_when_changes_trie_is_built() {
		let (backend, mut storage, changes, _) = prepare_for_build(0);
		let config = changes.changes_trie_config.as_ref().unwrap();
		let parent = AnchorBlockId { hash: Default::default(), number: 15 };

		// override some actual values from storage with values from the cache
		//
		// top-level storage:
		// (keys 100, 101, 103, 105 are now missing from block#4 => they do not appear
		// in l2 digest at block 16)
		//
		// "1" child storage:
		// key 102 is now missing from block#4 => it doesn't appear in l2 digest at block 16
		// (keys 103, 104) are now added to block#4 => they appear in l2 digest at block 16
		//
		// "2" child storage:
		// (keys 105, 106) are now added to block#4 => they appear in l2 digest at block 16
		let trie_root4 = storage.root(&parent, 4).unwrap().unwrap();
		let cached_data4 = IncompleteCacheAction::CacheBuildData(IncompleteCachedBuildData::new())
			.set_digest_input_blocks(vec![1, 2, 3])
			.insert(None, vec![vec![100], vec![102]].into_iter().collect())
			.insert(Some(b"1".to_vec()), vec![vec![103], vec![104]].into_iter().collect())
			.insert(Some(b"2".to_vec()), vec![vec![105], vec![106]].into_iter().collect())
			.complete(4, &trie_root4);
		storage.cache_mut().perform(cached_data4);

		let (root_changes_trie_nodes, child_changes_tries_nodes, _) = prepare_input(
			&backend,
			&storage,
			configuration_range(&config, 0),
			&changes,
			&parent,
		).unwrap();
		assert_eq!(root_changes_trie_nodes.collect::<Vec<InputPair<u64>>>(), vec![
			InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 16, key: vec![100] }, vec![0, 2, 3]),
			InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 16, key: vec![101] }, vec![1]),
			InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 16, key: vec![103] }, vec![0, 1]),

			InputPair::DigestIndex(DigestIndex { block: 16, key: vec![100] }, vec![4]),
			InputPair::DigestIndex(DigestIndex { block: 16, key: vec![102] }, vec![4]),
			InputPair::DigestIndex(DigestIndex { block: 16, key: vec![105] }, vec![8]),
		]);

		let child_changes_tries_nodes = child_changes_tries_nodes
			.into_iter()
			.map(|(k, i)| (k, i.collect::<Vec<_>>()))
			.collect::<BTreeMap<_, _>>();
		assert_eq!(
			child_changes_tries_nodes.get(&ChildIndex { block: 16u64, storage_key: b"1".to_vec() }).unwrap(),
			&vec![
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 16u64, key: vec![100] }, vec![0, 2, 3]),

				InputPair::DigestIndex(DigestIndex { block: 16u64, key: vec![103] }, vec![4]),
				InputPair::DigestIndex(DigestIndex { block: 16u64, key: vec![104] }, vec![4]),
			],
		);
		assert_eq!(
			child_changes_tries_nodes.get(&ChildIndex { block: 16u64, storage_key: b"2".to_vec() }).unwrap(),
			&vec![
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 16u64, key: vec![100] }, vec![0, 2]),

				InputPair::DigestIndex(DigestIndex { block: 16u64, key: vec![105] }, vec![4]),
				InputPair::DigestIndex(DigestIndex { block: 16u64, key: vec![106] }, vec![4]),
			],
		);

	}
}

import CLRSLean.Chapter_21.Section_21_1_Disjoint_Set_Operations
import CLRSLean.Chapter_21.Section_21_2_Linked_List_Representation
import CLRSLean.Chapter_21.Section_21_3_Forest_Representation

/-!
# Chapter 21 - Data Structures for Disjoint Sets

Chapter 21 introduces the union-find (disjoint-set) data structure, one of the
most elegant and practical data structures in algorithm design.  The chapter
builds from an abstract specification through concrete representations to a
near-optimal implementation using union by rank and path compression.

The Lean formalization covers:

## Sections

* 21.1 Disjoint-set operations: {lit}`proved` for the abstract partition model.
  Main results:
  {lit}`CLRS.Chapter21.DisjointSets.unique_set_containing`,
  {lit}`CLRS.Chapter21.DisjointSets.makeSet_isRoot` (via structure construction),
  {lit}`CLRS.Chapter21.DisjointSets.union_merges`,
  {lit}`CLRS.Chapter21.DisjointSets.partition_invariant`,
  {lit}`CLRS.Chapter21.DisjointSets.makeSet_preserves_partition`,
  {lit}`CLRS.Chapter21.DisjointSets.union_preserves_partition`, and
  {lit}`CLRS.Chapter21.DisjointSets.same_set_iff_findSet_eq`.

* 21.2 Linked-list representation: {lit}`partial`.
  Main results:
  {lit}`CLRS.Chapter21.LinkedListDS.weighted_union`,
  and {lit}`CLRS.Chapter21.LinkedListDS.weighted_union_size_sum`.

* 21.3+21.4 Forest representation with union by rank and path compression:
  {lit}`partial`.
  Main results:
  {lit}`CLRS.Chapter21.DisjointSetForest.makeSet_isRoot`,
  {lit}`CLRS.Chapter21.DisjointSetForest.makeSet_size_ge_rank_pow`,
  {lit}`CLRS.Chapter21.DisjointSetForest.union_preserves_rank_size`,
  {lit}`CLRS.Chapter21.DisjointSetForest.rank_log_bound_of_size_ge_pow`,
  {lit}`CLRS.Chapter21.DisjointSetForest.findSetCompressFuel_root`, and
  {lit}`CLRS.Chapter21.DisjointSetForest.findSetCompressFuel_snd_eq_findSetFuel`.

## Current Coverage

Section 21.1 establishes the abstract specification: a collection of
pairwise-disjoint Finsets covering `Fin n`.  The partition invariant is
structural — the data type *is* a partition — so the proofs are clean and
complete.  `makeSet` and `union` are proven to preserve the partition invariant.

Section 21.2 provides the linked-list representation with the weighted-union
heuristic, proving that a weighted union produces a combined set at least as
large as the sum of its parts.

Section 21.3+21.4 is the core contribution: the rooted-tree forest with union
by rank.  The key lemma `union_preserves_rank_size` shows that `size[r] ≥
2^(rank[r])` is maintained for all distinct roots under union by rank.  Combined
with the bound `size[r] ≤ n`, this yields `rank[r] ≤ log₂ n` via
`rank_log_bound_of_size_ge_pow`, giving the O(log n) height guarantee.

Path compression is implemented in `findSetCompressFuel` with proofs that
a root remains unchanged (`findSetCompressFuel_root`) and that the returned
root equals the one from simple `findSetFuel`
(`findSetCompressFuel_snd_eq_findSetFuel`).

## Current Gaps

* Section 21.2: A full accounting of the `O(m + n log n)` bound for `m`
  operations requires tracking cumulative pointer updates across a sequence.
* Section 21.3+21.4: The inverse-Ackermann amortized analysis for the combined
  union-by-rank + path-compression bound is deferred.  The current proofs give
  the O(log n) per-operation bound (without path compression).
* The connection between the abstract `DisjointSets` model (Section 21.1) and
  the `DisjointSetForest` implementation (Section 21.3) via a simulation
  relation is a strengthening target.
-/

namespace CLRS
namespace Chapter21
end Chapter21
end CLRS

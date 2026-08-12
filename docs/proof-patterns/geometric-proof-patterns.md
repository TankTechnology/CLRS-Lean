# Geometric Proof Patterns in CLRS-Lean

This atlas records the "geometric structures" that recur throughout the current CLRS-Lean proofs.
Here "geometry" does not mean Euclidean geometry, but the shape of the objects under proof: how boundaries move, how local pieces are replaced, how intervals nest, how tables depend on one another.

The goal has two layers:

- Let readers search existing proofs by proof shape, not just by chapter.
- Distill the shapes that have already recurred into small Lean utilities, rather than prematurely designing a huge algorithmic-proof framework.

The Lean modules extracted so far live in `CLRSLean/ProofPatterns/`:

- `Boundary.lean`: one-dimensional boundary advancement.
- `Exchange.lean`: greedy exchange certificates.
- `Fiber.lean`: bucket/fiber decomposition.
- `Interval.lean`: strict interval precedence and nesting.

The potential telescope for amortized analysis already forms a general framework in
`CLRSLean/Chapter_17/Section_17_1_Amortized_Framework.lean`, so it is not migrated again for now.

## 1. Boundary Shift

**Geometric intuition**

An object is cut by a boundary into two parts: processed/unprocessed, prefix/suffix, left region/right region, scanned/unscanned.
The main action of the proof is "the boundary moves one step, and the invariant still holds".

**Lean skeleton**

`CLRS.ProofPatterns.BoundaryTrace` writes the state as a trace indexed by natural numbers:

```lean
BoundaryTrace.state : Nat -> State
```

Core theorems:

```lean
CLRS.ProofPatterns.boundary_holds
CLRS.ProofPatterns.boundary_holds_upto
CLRS.ProofPatterns.terminal_of_boundary
```

**Project instances**

- Heapsort: `SortedSuffix` and `PrefixLeSuffix` cut the array into a heap prefix and a sorted suffix.
  Key theorems include `arrayHeapSortStep_suffix_head_bounds_prefix`,
  `arrayHeapSortInPlaceLoop_exact_state_correct`.
- Quicksort: `partitionLoop_invariant` maintains the partition to the left and right of the pivot.
- Counting sort: scans buckets by key from low to high.
- Kruskal: scans the processed prefix by edge weight, gradually expanding the forest.

**How to reuse**

In a new proof, whenever "the state at step `i`" and "the state at step `i+1`" appear, prefer writing:

```lean
Invariant i (state i) ->
Invariant (i + 1) (state (i + 1))
```

Finally, use `boundary_holds` or `boundary_holds_upto` to push to the end.

## 2. Exchange Certificate

**Geometric intuition**

Take an arbitrary feasible solution, replace one small piece of it with the greedy choice, and obtain a new feasible solution that is structurally closer to the greedy solution and no worse.
This is a "local replacement quadrilateral":

```text
old feasible solution
        |
        | exchange
        v
new feasible solution containing greedy choice
```

**Lean skeleton**

`CLRS.ProofPatterns.ExchangeCertificate` fixes only the minimal common shape:

```lean
exchange : Solution -> Solution
feasible_exchange : feasible s -> feasible (exchange s)
target_exchange : feasible s -> target (exchange s)
noWorse_exchange : feasible s -> noWorse (exchange s) s
```

`target` is the structural property obtained after the exchange; `noWorse` is determined by the specific problem.
Maximization problems can use `NoLessScore`, and minimization problems can use `NoGreaterCost`.

**Project instances**

- Activity selection: exchange any optimal choice for one beginning with the activity that finishes earliest.
- Huffman: put the two lowest-frequency symbols into sibling leaves via split-leaf/exchange.
- MST/Kruskal: add a light crossing edge to the spanning tree, then delete one edge on the path.

**How to reuse**

For a new greedy proof, do not start by writing the big theorem "the algorithm is always optimal".
First write an exchange certificate, proving that any competitor can be exchanged for one containing the greedy local choice.
Then connect the recursive subproblem or the cut property.

## 3. Fiber Decomposition

**Geometric intuition**

Use a key to split a list into several fibers/buckets; first prove each fiber correct internally, then reassemble the global result in key order.

**Lean skeleton**

`CLRS.ProofPatterns.fiber` is a key-generic bucket:

```lean
fiber key xs k
```

Core lemmas:

```lean
fiber_sublist
fiber_append
mem_fiber_iff
fiber_all_keys_eq
fiber_eq_nil_of_forall_ne
fiber_fiber_eq
```

**Project instances**

- Counting sort: the current `bucket` is a specialized version for natural-number keys.
- Radix sort: the digit class is a multi-layer stacking of fibers.
- Bucket sort: the bucket index determines where an element lands, and the expected analysis also counts bucket sizes.
- Hash tables: each chain in chained addressing can be viewed as a fiber of the hash key.

**How to reuse**

If Chapter 8 is later refactored, the local `bucket` definition can first be replaced or bridged to `fiber`:

```lean
bucket key xs k = fiber key xs k
```

Do not rush to change existing proved theorems; a more stable approach is to use the `fiber_*` lemmas in new theorems, and recycle old local lemmas only after they recur two or three times.

## 4. Interval Nesting

**Geometric intuition**

Between timestamps, recursive intervals, and adjacent power intervals there are usually only two clean relations:

- One interval is strictly before another.
- One interval is strictly nested inside another.

DFS's parenthesis theorem is the most obvious version of this structure.

**Lean skeleton**

`CLRS.ProofPatterns.NatInterval` provides the minimal interval model:

```lean
NatInterval.Valid
NatInterval.StrictlyBefore
NatInterval.NestedInside
```

Core lemmas:

```lean
NatInterval.nestedInside_trans
NatInterval.nestedInside_irrefl
NatInterval.nestedInside_asymm
NatInterval.strictlyBefore_trans
NatInterval.strictlyBefore_asymm
```

**Project instances**

- DFS: `intervalNestedInside` compares discovery/finish intervals.
- Maximum subarray: left/right/crossing is an interval decomposition around the boundary.
- Master theorem all-input bridge: any input is sandwiched between adjacent exact powers.

**How to reuse**

When encountering a new timestamp or index-interval proof, one can first define a projection to `NatInterval`:

```lean
def dfsInterval (s : DFSState V) (u : V) : NatInterval := ...
```

Then reuse the generic asymmetry/transitivity lemmas, leaving DFS-specific facts to the discovery/finish times themselves.

## 5. Local Surgery

**Geometric intuition**

Only modify a small piece of a tree or heap, and prove that the external frame is unchanged and the global invariant is preserved.

**Current status**

For now this category is only written into the atlas; no Lean module has been extracted. The reason is that it is easily contaminated by concrete data structures:

- Red-black tree rotation cares about color, black height, and BST order.
- Order-statistic tree rotation cares about stored size and rank/select.
- B-tree split child cares about child bounds, key order, and membership.
- Heapify cares about the array index and the heap prefix.

**Project instances**

- `rankSelect?_rotateLeft` / `rankSelect?_rotateRight`
- `splitChild_preserves_childBounded`
- `PrefixLeBound.of_maxHeapifyFuel`

**How to reuse**

For now this category keeps local lemmas per chapter.
When two different chapters both need a "frame-preserving edit" interface, extract one:

```lean
before --local edit--> after
outside patch unchanged
Invariant before -> Invariant after
```

## 6. Table/Grid Dynamic Programming

**Geometric intuition**

DP proofs usually move over a two-dimensional table: a cell's value is determined by the left, upper, or upper-left neighbors, or by some split point.
Reconstruction then traces a path or a split tree through the table.

**Current status**

No Lean module is extracted for now, because the shapes of value, certificate, and reconstruction differ considerably across DP problems.
But the documentation can already be searched by this pattern.

**Project instances**

- Matrix-chain multiplication: `MatrixChainLowerBound`, `MatrixChainSplitOptimal`, `matrixChain_correct`.
- LCS: `LCSCertificate`, the table recurrence, and `lcs_correct`.
- Rod cutting / optimal BST: one- or two-dimensional table optimality certificates.

**How to reuse**

Prefer to split a new DP proof into three layers:

1. local recurrence lower/upper bound;
2. the table satisfies the recurrence;
3. the reconstruction certificate consumes the table recurrence.

## 7. Potential Telescope

**Geometric intuition**

Amortized analysis adds the actual cost and the potential change:

```text
actual_i + Phi_{i+1} - Phi_i
```

After summing along the trace, the intermediate potential terms all cancel.

**Existing Lean framework**

Chapter 17 already has a general version:

```lean
CLRS.Chapter17.AccountingTrace
CLRS.Chapter17.PotentialTrace
CLRS.Chapter17.potential_totalCost_eq_totalAmortized_sub_delta
CLRS.Chapter17.potential_totalCost_le_totalAmortized
```

**Project instances**

- Stack/multipop aggregate analysis.
- Binary counter flips.
- Dynamic table insert/delete.
- Fibonacci heap potential.

**How to reuse**

New amortized proofs directly import the Chapter 17 framework, unless it is later decided to move it up to `ProofPatterns`.
It is not migrated now, in order to avoid disturbing the already-stable Chapter 17 API.

## 8. Scale Sandwich

**Geometric intuition**

Complexity proofs often use the sandwiching of "exact points" and "arbitrary input points":

```text
exact power <= n < next exact power
```

First prove on the clean spine, then sandwich all inputs between adjacent spine points.

**Project instances**

- Recursion-tree exact powers.
- Master theorem floor/ceiling all-input transfer.
- Randomized quicksort's harmonic bound can be seen as another kind of envelope.

**How to reuse**

This category currently stays in Chapter 4, because it depends heavily on asymptotic notation and exact-power recurrences.
If the complexity proofs in Chapters 24-26 again need an "exact spine -> all input" bridge, consider extracting it to ProofPatterns.

## Extraction Rule

The extraction rule stays conservative:

- A pattern first enters this atlas.
- Only after at least two chapters independently reuse it is a small Lean module extracted.
- Small modules extract only the geometric skeleton and generic algebra, not concrete algorithm semantics.
- Stable chapters do not undergo large refactors for "nice abstractions"; new proofs prefer these modules, and old lemmas are recycled only after natural repetition.

Current priorities:

1. New proofs prefer `Boundary`, `Fiber`, `Interval`, and `Exchange`.
2. A later refactor of Chapter 8 can bridge `bucket` and `fiber`.
3. Later proofs for Chapter 22's DFS parenthesis/white-path can use `NatInterval` as the outer interval language.
4. Greedy/cut proofs for the graph algorithms in Chapters 23/24 continue to try `ExchangeCertificate`.
5. `LocalSurgery` and the DP grid temporarily remain in documentation mode, with code extracted once the reuse pressure becomes clearer.

# Chapter 25 attached adjacency-list flow-cost design

## Implementation note (2026-08-28)

The implemented route keeps the run state as a concrete matching and attaches
the semantic flow definitionally as `matchingToFlow`.  It proves that every
such flow is integral and that the returned one is maximal.  The exact BFS
state still erases to the legacy semantic BFS, but the complete matching-state
sequence is not claimed equal to `bfsFlowIter`, since separate valid path
choices can produce different maximum matchings.  Residual-to-graph path
projection is an explicit charged pass.  The resulting conventional product
bound is `20 * V_f * (E_f + 1)`.
The support index is built once and reused by every recursive attempt.  The
counter formalizes the declared textbook unit-cost RAM operations rather than
the reduction cost of Lean's persistent data structures.

**Status:** route A approved on 2026-08-28.

## Goal

Close the remaining textbook-level gap in CLRS Fourth Edition Section 25.1:
the augmenting-flow method for bipartite matching returns a maximum matching
within `O(V_f E_f)` work on the constructed flow network.

The returned matching, its semantic flow, the BFS path used for augmentation,
and the work counter must belong to the same executable run.  The theorem must
not attach a stipulated budget to an implementation that performs different
operations.

Here `V_f` and `E_f` denote the vertex and support-arc counts of the constructed
flow network.  For a bipartite graph `G`,

```text
V_f = |V| + 2
E_f = |G.L| + |G.E| + |G.R|.
```

## Existing proof surface

The implementation reuses the semantic results that are already proved:

- Chapter 24's residual-edge relation, executable residual BFS, shortest
  augmenting path, and flow augmentation theory;
- Chapter 25's `matchingToFlow` construction and exact residual-edge
  characterization for matching flows;
- the translation between residual paths and alternating paths;
- the alternating-path augmentation and Berge maximum-matching theorems.

Those results remain the semantic reference model.  The new code supplies the
missing concrete representation, work-accounting execution, and refinement
links.

## Rejected shortcuts

The following do not meet the target theorem and must not appear in the final
public interface:

1. Running the current `residualBFS`, whose neighborhood operation filters all
   vertices, while merely recording an adjacency-list budget.
2. Defining `work` as an arithmetic expression independent of the returned
   execution.
3. Charging a path-length update while returning Chapter 24's extensional
   `Flow.augment` without a concrete path-update loop or refinement theorem.
4. Extracting an arbitrary augmenting path after BFS and updating along that
   unrelated path.
5. Proving only a specification-level budget theorem and describing it as the
   running time of the executable algorithm.

## Representation

### Residual support

For a matching `M`, every residual edge of `matchingToFlow M` lies in one of
the two orientations of a fixed support arc:

- source-to-left arcs;
- graph arcs from the left partition to the right partition;
- right-to-sink arcs.

`ResidualSupport.lean` will define this finite directed support and prove:

```text
residualEdge (matchingToFlow M) u v
  ↔ (u, v) is an enabled orientation of a support arc,
```

together with the exact forward-support cardinality `E_f` and a bound of
`2 * E_f` on the oriented residual candidates.

### Adjacency buckets

The support is indexed once by source vertex.  Querying the neighbors of `u`
then filters only `u`'s bucket by the current residual predicate.  The reusable
Chapter 24 layer proves:

- membership equivalence with the supplied edge relation;
- no duplicate candidates in a bucket;
- the sum of all bucket lengths equals the candidate-support length;
- filtering preserves the required membership and cardinality bounds.

The one-time index construction is accounted for explicitly, or exposed as a
preprocessing term in the final run cost.  It is never silently omitted.

### Primitive work model

The counter is a textbook RAM-model counter, not a claim about Lean kernel
reduction steps.  One unit is charged for each support insertion, bucket read,
residual-candidate test, queue/set bookkeeping action, parent write, and
matching-edge edit performed by the costed program.  Vertex and edge keys are
finite indices, so indexed reads and writes are the adjacency-list primitives
being modeled.  The theorem does not claim that arbitrary `Finset` or
`DecidableEq` implementations have unit cost.

## Costed residual BFS

`CostedSupportBFS.lean` implements a BFS over the indexed buckets.  Its state
contains the ordinary queue/seen/parent data plus counters for:

- vertex dequeue and bookkeeping work;
- residual-candidate scans;
- newly discovered vertices and parent writes.

The key invariants are:

1. every vertex enters the queue at most once;
2. only the bucket of a dequeued vertex is scanned;
3. the sum of scanned bucket lengths is bounded by the candidate-support
   length;
4. erasing counters and the support representation yields the same discovery
   result and reconstructed shortest path as the existing semantic BFS.

Bucket correctness first proves that the bucket-filtered `Finset` of new
neighbors is exactly the existing `bfsNewNeighbors`.  Therefore the erasure
claim is an equality of BFS states, not merely an equality of reachability
predicates or distances.

The result theorem therefore has both semantic and cost components:

```text
erase (costedResidualBFS support φ) = residualBFS φ
costedResidualBFS.work ≤ cV * V_f + cE * orientedSupportSize
```

for explicit natural-number constants `cV` and `cE`.  The public Chapter 25
specialization then derives a concrete linear bound in `V_f + E_f`.

## Attached matching update

The run state is a concrete matching `M`; its semantic flow is always
`matchingToFlow M`.  When costed BFS returns a source-to-sink path, the
translation layer converts that exact returned path into an alternating path.

`MatchingAugment.lean` implements the alternating-path flip as a structural
recursion over that path.  The same recursion returns:

- the updated matching `M'`;
- the number of inspected path edges and matching edits;
- proofs that `M'` is the alternating-path augmentation of `M`;
- `M'.size = M.size + 1`;
- a refinement theorem relating `matchingToFlow M'` to semantic flow
  augmentation along the BFS path.

Consequently the update cost is attached to operations executed by the code,
and is bounded by the simple path length, hence by `V_f`.

## Costed run

`CostedRun.lean` performs the following attempt:

```text
matching M
  -> costed adjacency-list residual BFS for matchingToFlow M
  -> no path: halt/stutter with the BFS work
  -> path: translate that exact path, flip it, and add the actual update work.
```

The run records:

- the current matching;
- its semantic flow `matchingToFlow M`;
- augmentation count;
- accumulated preprocessing, BFS, and update work;
- whether a no-path result has already made later attempts stutter.

It runs for at most `|G.L|` successful augmentation opportunities.  Each
successful step increases matching size by one, while every matching has size
at most `|G.L|`.  A no-path result is maximum by the existing residual-path
translation and Berge theorem.

The final theorem combines correctness and work for one run:

```text
let run := costedMatchingRun G
run.matching.IsMaximum
  ∧ run.flow = matchingToFlow run.matching
  ∧ run.augmentations ≤ |G.L|
  ∧ run.work ≤ preprocess G + |G.L| * attemptBound G
```

with separate proved bounds

```text
preprocess G ≤ c0 * (V_f + E_f)
attemptBound G ≤ c1 * (V_f + E_f).
```

This yields the textbook `O(V_f E_f)` statement for the constructed network;
the exact natural-number inequality remains the primary machine-checkable
claim.

## Module boundaries

The difficult proofs are split so Lean never has to re-elaborate one oversized
file during development.

### Reusable Chapter 24 layer

- `Chapter_24/.../S4_ExecutableBFS/SupportAdjacency.lean`: finite support,
  buckets, membership, and cardinality lemmas.
- `Chapter_24/.../S4_ExecutableBFS/CostedSupportBFS.lean`: costed BFS,
  invariants, shortest-path result, and erasure to the existing BFS.

These files import the existing executable BFS; the existing file does not
import them, avoiding an import cycle.

### Chapter 25 specialization

- `FlowExecution/ResidualSupport.lean`: the bipartite-flow support and exact
  residual coverage.
- `FlowExecution/CostedBFS.lean`: specialization of the reusable BFS and the
  exact BFS-path-to-alternating-path bridge.
- `FlowExecution/MatchingAugment.lean`: concrete alternating-path update,
  cost, size growth, and flow refinement.
- `FlowExecution/CostedRun.lean`: one-attempt and whole-run accounting,
  maximality, and the combined headline theorem.
- `FlowExecution.lean`: public imports only; large proofs stay in the small
  implementation files.

The existing `Model.lean`, `Step.lean`, `Run.lean`, and `Refinement.lean`
remain semantic infrastructure.  Any earlier budget-only theorem is either
renamed as a specification bound or removed from the public textbook claim so
that no ambiguity remains.

## Verification and commit checkpoints

Implementation proceeds through four independently reviewable commits:

1. residual support and adjacency-bucket coverage/cardinality;
2. costed BFS, erasure, and the actual scan bound;
3. exact BFS-path matching update and attached update cost;
4. costed run, maximum-matching result, total `O(V_f E_f)` bound, tests, trust
   audit, and documentation sync.

During development, each new file and its focused interface test is compiled
directly.  The Chapter 25 aggregate target, trust audit, repository audit
scripts, and broader root gate are run only at integration checkpoints.

Acceptance requires:

- no `sorry`, `admit`, `axiom`, `native_decide`, or hidden classical-choice
  shortcut for the executable update;
- a focused test that exposes the erasure, per-attempt cost, refinement, and
  final combined theorem;
- `Tests/Trust/Chapter_25.lean` passing;
- Chapter 25 and repository audit gates passing;
- issue #339 updated with exact theorem names and commit evidence.

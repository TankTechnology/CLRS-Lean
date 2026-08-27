# Whole-Book Proof-Gap Audit

- Audit date: 2026-08-28 (Asia/Shanghai)
- Source baseline: `7315db6a`
- Canonical scope: CLRS fourth edition, Chapters 1--35
- Selected inventory at the baseline: 1,668 / 1,668 theorem entries
- Kernel-hole scan: no live `sorry`, `admit`, project-local `axiom`, or
  theorem-bearing `partial def`

This is an immutable evidence snapshot, not a second live progress ledger.  The
current numeric status remains in `docs/clrs-proof-progress.csv` and
`docs/clrs-fourth-edition-map.csv`; unresolved proof work is tracked in GitHub
issues.

## Closure checkpoints after the audit baseline

- Chapter 2 target #335 is closed on branch `codex/whole-book-proof-closure`:
  the recursive execution calls the verified local merge, erases to the public
  merge sort, and carries an all-input Θ(n log n) cost theorem (`08c188c8`).
- Chapter 11 target #337 is closed on the same branch: uniform permutations are
  counted through their injective prefixes, their event probability is proved
  equal to `probeTail`, and the concrete probe-count expectations inherit CLRS
  Theorems 11.6--11.8.
- Chapter 35 target #341 is closed on the same branch: costed map-add, merge,
  trim, target-filter, and maximum scans erase to the original semantics; the
  execution-derived work theorem and `approxSubsetSumWithCost_fptas` bundle
  feasibility, approximation, and polynomial work for the same run.
- Chapter 28 target #340 is closed on the same branch: explicit pivot scanning,
  row permutation, pointwise elimination, and Schur-block recursion return
  certified LUP factors or singular failure; the decomposition counter is
  cubic and the costed LUP-SOLVE counter is quadratic.
- Chapter 15 target #338 is closed on the same branch: stable stamped entries,
  a list-backed array binary min-heap, verified insert/extract-min operations,
  and the complete heap loop refine `huffmanOfFreqs` exactly.  Construction and
  merge counters follow the actual Chapter 6 heap-controller paths and satisfy
  the explicit `4n(log₂(n+1)+1)` bound.

The matrix below remains the dated baseline that motivated those batches; the
live ledger and GitHub issues record their current state.

## Audit question

The existing inventory answers “are all declarations selected by the project
proved?”  This audit asks the stronger question: “does the selected boundary
cover the main textbook proof obligations without disconnecting the algorithm,
its invariant, its correctness theorem, and its cost or probability model?”

Each chapter is checked in six lanes:

1. algorithm semantics;
2. correctness and invariant/structure preservation;
3. optimality, exchange, adversary, or lower-bound argument where applicable;
4. cost attached to the proved execution;
5. provenance of probability, graph, numeric, or machine assumptions;
6. canonical public evidence through a chapter import and native axiom audit.

Classifications are `proved`, `document-drift`, `interface-gap`,
`semantic-bridge-gap`, `core-proof-gap`, `deferred-implementation`, and
`future-work`.  Pointer mutation, RAM/cache/hardware behavior, floating-point
error, exercises, and chapter problems are not counted as mathematical chapter
failures unless a chapter's central claim is itself an implementation or cost
theorem.

## Chapter matrix

| Ch. | Algorithm semantics | Correctness / invariant | Optimality / lower bound | Cost attachment | Model provenance | Public evidence | Verdict and exact next target |
|---:|---|---|---|---|---|---|---|
| 1 | Expository guide; no algorithm target. | Not applicable. | Not applicable. | Not applicable. | Scope is stated explicitly. | `CLRSLean.FourthEdition.Chapter_01`; `Tests/Trust/Chapter_01.lean`. | `proved` for the expository contract. |
| 2 | Insertion sort is executable. Local `mergeWithCost` is executable, but public `mergeSort` delegates to `List.mergeSort`. | `insertionSort_sorted`; `merge_correct`; `mergeSort_perm`. | Not applicable. | Line costs and local MERGE costs are proved; the all-input recurrence is proved, but neither is attached to one top-level local-MERGE execution. | Immutable-list and symbolic unit-cost boundaries are explicit. | `Tests/Trust/Chapter_02.lean`. | **`semantic-bridge-gap` (high):** define a terminating top-level merge sort that calls local `mergeWithCost`; prove erasure, sortedness, permutation, and an execution-derived cost bound. |
| 3 | Mathematical asymptotic and standard-function interfaces match the chapter. | CLRS formulations are bridged by `isBigTheta_iff_clrs`, strict `o`/`ω`, growth hierarchy, and Robbins bounds. | Growth comparisons and Stirling bounds are proved. | Not an executable-algorithm chapter. | Positivity and domain assumptions are explicit. | `Tests/Trust/Chapter_03.lean`. | `proved`; exercises and machine costs are `future-work`. |
| 4 | Naive multiplication and Strassen are executable. Explicit branching trees model both textbook examples at fixed depth/exact real scales. | Matrix correctness, branching-tree decomposition, Master, and Akra--Bazzi bounds are proved. | Three Master regimes and Akra--Bazzi upper/lower packages are proved. | Recurrence costs are explicit; matrix RAM costs remain abstract. | All-input floor/ceiling transfer exists for Master recurrences, but is not connected to the explicit §4.4 branching-tree examples. | `Tests/Trust/Chapter_04.lean`. | **`semantic-bridge-gap` (medium):** connect an integer floor/ceiling branching recurrence to `BranchingRecursionTree`, including unequal termination depths and total-cost equality. |
| 5 | Executable Fisher--Yates and HIRE-ASSISTANT models are present. | Permutation, loop invariant, record-count identity, and hiring transport are proved. | Longest-streak two-sided bounds and online-hiring asymptotics are proved. | Expected cost is attached through the explicit finite executions. | Uniform permutations and independent swap choices are explicit finite sample spaces. | `Tests/Trust/Chapter_05.lean`. | `proved`; additional textbook examples are `future-work`. |
| 6 | Indexed heap, fuelled MAX-HEAPIFY, BUILD-MAX-HEAP, in-place-style heapsort, and array-prefix priority operations are present. | Heap, permutation, active-prefix, and state contracts are bundled. | Not applicable. | Costed erasure and logarithmic/linear/n-log-n bounds are attached to the functional-array executions. | Persistent-list allocation and RAM instructions are excluded explicitly. | `Tests/Trust/Chapter_06.lean`. | `proved`; imperative RAM realization is `deferred-implementation`. |
| 7 | Functional quicksort, scan-state PARTITION, array refinement, and an explicit random-permutation execution are present. | Sortedness/permutation and the pointwise pair-trace-to-execution bridge are proved. | Comparison probabilities and expected Θ(n log n) are proved. | `operationalRandomizedQuicksortExpectedComparisons` averages the actual recursive counter. | No independence of pair indicators is assumed; permutation symmetry is proved. | `Tests/Trust/Chapter_07.lean`. | `proved`; RAM accounting and sharp tail bounds are `future-work`. |
| 8 | Decision trees, counting/radix/bucket executions, and a mutable output-array refinement are present. | Sorting, stability, permutation, and decision-tree injectivity are proved. | The comparison lower bound and expected bucket-sort result are proved. | Counting, radix, and bucket costs are attached to their selected executions. | Finite-uniform bucket placement is explicit. | `Tests/Trust/Chapter_08.lean`. | `proved`; per-instruction RAM accounting is `deferred-implementation`. |
| 9 | Pairwise min/max, RANDOMIZED-SELECT, and recursive median-of-medians SELECT are executable. | Rank, pivot, totality, and recursive correctness certificates are proved. | Linear expected and worst-case selection bounds are proved. | The final `recursiveMedianOfMediansComparisonCost_linear_bound` is attached to the executable recursion, not only the abstract recurrence wrapper. | Fresh choices are modeled by nested finite conditional uniformity. | `Tests/Trust/Chapter_09.lean`. | `proved`; RNG and RAM costs are `deferred-implementation`. |
| 10 | Array-backed stack/circular queue and functional list/tree models are executable. | Overflow/underflow/wrap, list membership, and LCRS round trips are proved. | Not applicable. | No asymptotic claim requiring a cost model is advertised. | Pointer identity, free lists, and allocation are excluded project-wide. | `Tests/Trust/Chapter_10.lean`. | `proved` at the abstract data-structure boundary; pointer memory is `deferred-implementation`. |
| 11 | Deterministic tables, concrete hash families, open addressing, and perfect hashing are modeled. | Insert/search/delete and perfect-hash correctness are proved. | Universal-family collision and expected-search bounds are proved. | Expected open-addressing probes are derived from the declared `probeTail` product, not from the executable permutation sample. | Chaining and universal hashing use explicit finite spaces; open-addressing uniform hashing stops at an assumed without-replacement product. | `Tests/Trust/Chapter_11.lean`. | **`semantic-bridge-gap` (high):** prove that a uniform `Equiv.Perm (Fin m)` hits a fixed occupied `Finset` in its first `i` positions with probability exactly `probeTail m n i`, then transport the expectation theorems. |
| 12 | Functional BST, zipper parent layer, and imperative pointer-heap TRANSPLANT/leaf insertion refinements are present. | Search, neighbors, insert/delete, ordering, transplant equivalence, and expected height are proved. | Random-BST ancestor probabilities and logarithmic expected height are proved. | Height-based operation bounds are attached to the selected executions. | Pointer heap abstraction is explicit; RAM instruction costs are excluded. | `Tests/Trust/Chapter_12.lean`. | `proved`; low-level RAM cost is `deferred-implementation`. |
| 13 | Executable functional red-black insert/delete plus pointer/sentinel rotations and recoloring are present. | `insert_correct` and `delete_correct` preserve the bundled red-black shape, BST order, and exact membership. | Lemma 13.1 logarithmic height is proved. | Insert/delete logarithmic control costs are proved; full imperative fixup rewiring is not claimed. | Functional balancing is connected to pointer-local primitives without claiming a mutable heap implementation. | `Tests/Trust/Chapter_13.lean`. | `proved` at the mathematical tree boundary; full in-place pointer fixup is `deferred-implementation`. |
| 14 | Rod cutting, matrix-chain, LCS, and optimal-BST tabulations/memoization are executable. | Optimal values, reconstructions, and table invariants are proved. | Optimality recurrences are proved. | Quadratic/cubic/table-size bounds are attached to the tabulated or memoized models. | Exact arithmetic and abstract table access are explicit. | `Tests/Trust/Chapter_14.lean`. | `proved`; RAM table semantics is `deferred-implementation`. |
| 15 | Activity selection, Huffman merging, greedy meta-theory, and offline caching are executable at mathematical level. | Feasibility/exchange, Huffman optimality, and cache trace optimality are proved. | Greedy and exchange theorems are complete. | Activity and caching costs are attached. Huffman's verified executable is list-based with a quadratic comparison bound; `textbookHeapHuffmanWork` is a detached formula, not a heap execution. | The distinction is documented but the O(n log n) textbook implementation is not refined to the verified output. | `Tests/Trust/Chapter_15.lean`. | **`semantic-bridge-gap` (medium):** implement/cost a binary-min-heap Huffman execution and prove erasure or output optimality plus O(n log n) operations. |
| 16 | Stack/counter traces and dynamic-table operations are executable at the size/state level; an array-copy refinement exists. | Potential nonnegativity and trace invariants are proved. | Aggregate, accounting, and potential-method results are proved. | Per-operation amortized charges telescope to the actual selected trace cost. | Allocation and RAM copying constants are explicitly excluded. | `Tests/Trust/Chapter_16.lean`. | `proved`; allocator/RAM behavior is `deferred-implementation`. |
| 17 | Order-statistic and interval-tree updates refine augmented red-black trees. | Size/max-high augmentation, rotation, insert/delete, rank, and interval search are proved. | Generic augmentation theorem is proved. | O(log n) query/update bounds use the underlying red-black height. | Constant-time `combine` is an explicit premise. | `Tests/Trust/Chapter_17.lean`. | `proved`. |
| 18 | Node-level split, insertion, rotation/merge deletion, root normalization, and executable search are present. | `insertRoot_correct`, `composedDeleteRoot_correct`, uniqueness, membership, height, and well-formedness are proved. | Logarithmic height/disk-access relation is proved. | Disk-access bounds are attached to executable search/insert/delete constructions. | Tree-shape equality with the flat specification is not claimed; membership/search refinement is sufficient for the public spec. | `Tests/Trust/Chapter_18.lean`. | `proved`; page layout/pointer mutation is `deferred-implementation`, exact spec-tree shape equality is `future-work`. |
| 19 | Linked-list and forest representations, path compression, union by rank, and costed operation traces are executable. | Partition refinement, representative correctness, and run erasure are proved. | Rank-mass and inverse-Ackermann potential arguments are proved. | The final O((m+n)α(n)) bound is attached to actual parent traversals. | Ackermann level/index assumptions are explicit. | `Tests/Trust/Chapter_19.lean`. | `proved`; canonical notes contain a stale reference to a stateful Kruskal scan that Chapter 21 has since closed (`document-drift`). |
| 20 | Fuelled BFS, labelled BFS, DFS, Kahn/DFS topological sort, and Kosaraju are executable. | Reachability, shortest distance, parenthesis, edge classification, DAG order, and SCC partition are proved. | Not applicable. | BFS upper and exact DFS vertex-plus-edge costs are attached to the traversals. | Finite adjacency model is explicit. | `Tests/Trust/Chapter_20.lean`. | `proved`; operation-level RAM is `deferred-implementation`. |
| 21 | Mathematical Kruskal/Prim plus stateful union-find Kruskal and indexed-queue Prim executions are present. | Cut safety, spanning/forest preservation, union-find connectivity refinement, and queue/run refinement are proved. | Both MST optimality chains are proved. | O(E log E) Kruskal and O(E log V) Prim operation bounds are attached to the selected executions. | Concrete binary-heap array storage is excluded. | `Tests/Trust/Chapter_21.lean`. | `proved`; the §21.2 overview still says union-find correctness is deferred although child modules close it (`document-drift`). |
| 22 | Bellman--Ford, DAG shortest paths, and Dijkstra state/loop are executable. | Relaxation invariants and the §22.5 property stack are proved. | Difference-constraint equivalence is proved. | O(VE), O(V+E), and O(E log V) abstract work bounds are tied to selected algorithms. | Weight-sign assumptions are explicit. | `Tests/Trust/Chapter_22.lean`. | `proved`; mutable/RAM relaxation scheduling is `deferred-implementation`. |
| 23 | Repeated squaring, Floyd--Warshall, and Johnson constructions are present. | Shortest-distance, reconstruction, negative-cycle, and reweighting correctness are proved. | Not applicable. | O(V³ log V), O(V³), and Johnson work are attached to the real constructions. | Finite exact-weight graph model is explicit. | `Tests/Trust/Chapter_23.lean`. | `proved`; the progress note uses legacy “Sections 25.1--25.3” without labeling it as source numbering (`document-drift`). |
| 24 | Edmonds--Karp, residual BFS, push--relabel, and relabel-to-front models are present. | Max-flow/min-cut, augmentation, height/preflow, matching reduction, and termination invariants are proved. | Critical-edge counting and MFMC are proved. | O(VE²), O(V²E), and O(V³) counts are attached to their selected runs. | Integral/unit-capacity assumptions are explicit. | `Tests/Trust/Chapter_24.lean`. | `proved`; progress prose should label 26.x identifiers as legacy source numbering (`document-drift`). |
| 25 | Berge augmentation, Gale--Shapley, and the terminating Hungarian loop are executable at finite mathematical level. | Matching, stability/perfectness, alternating-tree, potential, and augmentation invariants are proved. | Maximum matching, proposer optimality, and assignment optimality are proved. | Gale--Shapley and Hungarian termination are bounded; the §25.1 flow-method O(VE) execution bound is not stated. | Finite preference/assignment models are explicit. | `Tests/Trust/Chapter_25.lean`. | **`semantic-bridge-gap` (low):** attach the unit-capacity augmenting-flow execution count to `flowMethod_finds_maximum_matching` and derive O(VE). |
| 26 | Greedy DAG scheduler, P-ADD/P-MATMUL, P-MERGE, P-MERGE-SORT, and parallel Strassen models are executable. | Value correctness, race-free indexing, sortedness/permutation, and schedule completion are proved. | Work/span scheduling bound is proved. | Work/span counters are stored in the same execution records and have all-input asymptotics. | Fork-join DAG model is explicit. | `Tests/Trust/Chapter_26.lean`. | `proved`; canonical notes should label `Chapter_27` as the legacy source namespace (`document-drift`). |
| 27 | Ski rental/elevator, MOVE-TO-FRONT, and LRU paging executions are present. | Online-state and phase/inversion invariants are proved. | Competitive upper and matching deterministic lower bounds are proved. | Costs are the same costs used in the competitive ratios. | Adversarial request sequences and offline comparators are explicit. | `Tests/Trust/Chapter_27.lean`. | `proved`. |
| 28 | Forward/back substitution are executable once factors are supplied. LUP decomposition itself is only an existence theorem, not an executable `LUP-DECOMPOSITION`. | `exists_lup_decomposition`, `forwardSubst_spec`, `backSubst_spec`, and `lupSolve_correct` prove the mathematical factorization/solve contract. | Existence/uniqueness and determinant corollaries are proved. | `substitutionCost`, `lupDecompositionCost`, `matrixInversionCost`, and `choleskyCost` are closed-form definitions detached from the recursive executions; LUP has no execution to count. | Exact fields/reals are explicit, but the constructive pivot/elimination algorithm is absent. | `Tests/Trust/Chapter_28.lean`. | **`core-proof-gap` (high):** define total executable LUP decomposition with failure only for singular input, prove factorization and triangular invariants, then derive counts from that execution; similarly attach substitution costs. |
| 29 | General-form normalization and a certified solver wrapper call the finite Bland/initialized SIMPLEX development. | Feasibility/objective equivalence and solver completeness are proved. | Weak/strong duality and complementary slackness are proved. | No polynomial runtime claim is advertised for simplex. | Solver is `noncomputable` over exact reals but follows finite pivot semantics; the detailed simplex sources are correctly cataloged as online material. | `Tests/Trust/Chapter_29.lean`. | `proved` at the exact-real mathematical algorithm boundary. |
| 30 | Coefficient, DFT, recursive/iterative FFT, multiplication, and circuit evaluations are executable over exact algebraic structures. | DFT/inverse/convolution, FFT erasure, multiplication correctness, and circuit evaluation are proved. | Not applicable. | Work, butterfly/gate count, and depth recurse over the same execution/circuit syntax. | Exact roots and characteristic assumptions are explicit; floating-point analysis is excluded. | `Tests/Trust/Chapter_30.lean`. | `proved`; numerical error/hardware/cache are `deferred-implementation`. |
| 31 | Euclid, modular solver, repeated squaring, RSA key/encrypt/decrypt, and Miller--Rabin loop interfaces are executable. | Number-theoretic, CRT, RSA correctness, and primality/liar bounds are proved. | Miller--Rabin error analysis is proved. | Operation-count layers are provided for the selected algorithms. | RSA security is explicitly not inferred from functional correctness. | `Tests/Trust/Chapter_31.lean`. | `proved`; cryptographic hardness/security is outside scope. |
| 32 | Naive, rolling Rabin--Karp, DFA, KMP, and suffix-array constructions/queries are executable. | Soundness/completeness and refinement to naive matching are proved. | Not applicable. | Rolling, DFA, KMP, and suffix-array comparison costs are attached to executions. | Hash collisions are filtered by exact confirmation; modulus assumptions are explicit. | `Tests/Trust/Chapter_32.lean`. | `proved`; stale Rabin--Karp prose was corrected by the audit consistency batch. |
| 33 | Lloyd iteration, multiplicative weights, and gradient-descent iterates are explicit mathematical updates. | Monotone k-means cost, MW potential accounting, and GD telescoping are proved. | Mean optimality and regret/convergence guarantees are proved. | Iteration-count bounds are the mathematical theorem statements; no floating-point runtime is claimed. | Exact-real loss/gradient assumptions are explicit. | `Tests/Trust/Chapter_33.lean`. | `proved`; numerical implementation is `deferred-implementation`. |
| 34 | Fixed TM2 machines, serialized languages, Cook--Levin circuit generation, and all §34.4--§34.5 reductions/verifiers are concrete. | Exact raw-language semantics, malformed-input behavior, certificate bounds, and NP membership/hardness chains are proved. | Cook--Levin and NP-completeness theorems are proved. | Output size and original-input polynomial machine runtime are proved for the required maps/verifiers. | Typed-to-serialized bridges and fixed-machine witnesses are explicit. | `Tests/Trust/Chapter_34.lean`. | `proved`; direct lowering of smaller SAT assignment checkers is `future-work`. |
| 35 | Approximation algorithms for vertex cover, metric TSP, set cover, MAX-3-CNF/LP rounding, and subset sum are defined. | Feasibility and approximation-factor theorems are proved. | Exchange/charging/random/rounding arguments are proved. | For APPROX-SUBSET-SUM, `approxSubsetSum_fptas` only bounds the final trimmed-list length; no costed MERGE-LISTS/TRIM/outer execution proves the claimed polynomial runtime. | Exact-real ε and list-size assumptions are explicit. | `Tests/Trust/Chapter_35.lean`. | **`core-proof-gap` (high):** define a costed APPROX-SUBSET-SUM execution, prove erasure and per-step merge/trim cost, then prove total O(n² log t / ε) and an actual FPTAS wrapper. |

## Confirmed main-path gaps

The audit confirms seven proof targets.  The first three affect the strongest
current textbook-completion claims most directly.

| Priority | Chapter | Classification | Why it matters | Closure target |
|---:|---:|---|---|---|
| P0 | 35 | `core-proof-gap` | The theorem named “FPTAS running time” is presently a list-length bound, not a runtime theorem. | Costed `merge`, `trim`, and outer APPROX-SUBSET-SUM execution; erasure; total polynomial bound. |
| P0 | 28 | `core-proof-gap` | LUP existence and solve-from-factors do not formalize executable LUP-DECOMPOSITION; its Θ(n³) cost is stipulated. | Executable pivot/elimination decomposition, factorization/invariants, execution-derived operation count. |
| P0 | 2 | `semantic-bridge-gap` | The proved local MERGE is not used by the public merge-sort execution. | Local-MERGE top-level merge sort, correctness, erasure/specification, and attached cost. |
| P1 | 11 | `semantic-bridge-gap` | Uniform-hashing tail probabilities are the probability model rather than a result derived from random probe permutations. | Exact finite counting theorem equating the probe event probability with `probeTail`. |
| P1 | 15 | `semantic-bridge-gap` | Huffman optimality is executable, but the textbook O(n log n) heap cost is detached from that execution. | Verified binary-min-heap Huffman refinement and cost theorem. |
| P2 | 4 | `semantic-bridge-gap` | Exact-depth branching trees and all-input recurrence tools are not connected for the §4.4 examples. | Integer floor/ceiling branching-tree construction with unequal-depth cost equality. |
| P2 | 25 | `semantic-bridge-gap` | Maximum-matching correctness is proved, but the textbook O(VE) unit-capacity flow execution cost is absent. | Costed augmenting-flow-to-matching theorem. |

Tracking issues:

- [#335](https://github.com/TankTechnology/CLRS-Lean/issues/335) — Chapter 2 executable merge-sort/MERGE bridge.
- [#336](https://github.com/TankTechnology/CLRS-Lean/issues/336) — Chapter 4 integer branching-tree bridge.
- [#337](https://github.com/TankTechnology/CLRS-Lean/issues/337) — Chapter 11 uniform probe-permutation probability.
- [#338](https://github.com/TankTechnology/CLRS-Lean/issues/338) — Chapter 15 heap-based Huffman execution and cost.
- [#339](https://github.com/TankTechnology/CLRS-Lean/issues/339) — Chapter 25 flow-method O(VE) matching cost.
- [#340](https://github.com/TankTechnology/CLRS-Lean/issues/340) — Chapter 28 executable LUP decomposition and cost.
- [#341](https://github.com/TankTechnology/CLRS-Lean/issues/341) — Chapter 35 costed APPROX-SUBSET-SUM FPTAS.

## Documentation findings

These do not require new mathematical proofs:

- Chapter 31's 17/18 count and §31.9 canonical-range errors were corrected and
  are now rejected by `scripts/check_progress_csv.py`.
- Chapter 32's source-level Rabin--Karp gap note was stale; `hash_slide` and the
  rolling correctness/cost layer already close it.
- Chapter 19's progress note still treats a stateful Kruskal scan as future,
  while canonical Chapter 21 now contains the stateful scan and cost proof.
- Chapter 21 §21.2's opening paragraph says union-find correctness is deferred,
  while its child modules prove the union-find bridge and stateful scan.
- Chapters 23, 24, and 26 use legacy third-edition section or namespace numbers
  in canonical progress prose without consistently labeling them as legacy
  source identifiers.

## Scope exclusions retained

The following recurring boundaries remain honest optional refinements rather
than main mathematical proof gaps:

- mutable arrays, pointers, allocation, free lists, and word-RAM instructions;
- cache/hardware/distributed execution semantics;
- floating-point roundoff and numerical stability for exact-algebra models;
- concrete random-number generators when a finite uniform sample is already
  proved;
- exercises, chapter problems, and optional high-probability strengthenings;
- direct machine lowerings not needed by an already concrete reduction or
  verifier chain.

## Recommended execution order

Start with Chapter 2, then Chapter 35, Chapter 11, and Chapter 28.  Chapter 2
is the smallest central execution bridge and establishes a reusable pattern for
attaching cost records to recursive algorithms.  Chapter 35 can reuse that
pattern for MERGE-LISTS/TRIM.  Chapter 11 is independent probability work.
Chapter 28 is the deepest constructive algorithm gap and should begin only
after its pivot/failure interface is designed.  Chapters 15, 4, and 25 follow
as lower-risk or lower-centrality closures.

Before any chapter's public status is changed, its focused interface, trust
audit, placeholder scan, repository check, and full chapter build must pass.

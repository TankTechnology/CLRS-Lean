# Chapters 1–13: semantic/content audit

[Chapter overview](index.md) · [Independent cross-review and final classifications](cross-review-01-13.md) · [Reproducible counterexamples](counterexamples.md)

This file preserves the first-pass evidence table. The cross-review record and overview govern the final section verdicts and corrections.


Baseline: `c8b074e961fb204ab50b9ea123b864260dafde38`. Read-only source audit; no Lean/repository files changed. Corpus configuration absent. **NOT-INDEPENDENTLY-VERIFIED applies globally to every textbook-equivalence, coverage, numbering, MATCH, or difference conclusion below.** Findings about what the current source computes or what a theorem actually states are independently checkable from source. This draft does not claim an exhaustive line-by-line verification of every imported proof.

Method: read all canonical chapter guides, mapped section guides (including shared sections), all thirteen `tests/Trust/Chapter_NN.lean`, pertinent focused interfaces, and actual definitions/theorem statements and selected proof bodies. Followed headline helper chains for merge sort, Fisher–Yates/hiring expectation, heap control costs, randomized quicksort/BST comparison identity, counting-sort output construction, fresh-rank SELECT, open-addressing probability, BST expected height, and red-black invariant bundling. Long arithmetic/combinatorial developments were **sampled**, explicitly indicated per chapter. Earlier audits were treated as historical claims, not current evidence. The structural gate and full build/trust results were supplied by root; I additionally compiled `/tmp/clrs-audit-counterexamples-01-13.lean` successfully (exit 0), demonstrating the Chapter 13 defects. Root independently reproduced these.

Path convention in tables: `Cnn/…` means repository-relative `src/CLRSLean/FourthEdition/Chapter_nn/…`; `Gnn` means `src/CLRSLean/FourthEdition/Chapter_nn.lean`. All locations refer to current source, not the older audit's shifted line numbers. Verdicts evaluate **the stated represented model**; MATCH means no source defect found within the reviewed claim and boundary; it does not mean complete correspondence to unavailable textbook text. A boundary explicitly excluded by the guide is not automatically a defect.

## Chapter 1 — The role of algorithms

Depth: full guide and trust file. No theorem-bearing section is claimed.

| Mapped section / claim | Location / declarations | Verdict | Evidence / boundary |
|---|---|---|---|
| 1.1 Algorithms | `G01:11`, prose-only boundary at `G01:66`; `tests/Trust/Chapter_01.lean:10` | MATCH | Correctly states this is expository; the trust example `True` is not presented as an algorithm theorem. |
| 1.2 Algorithms as technology | `G01:32`, `G01:57` | MINOR | No theorem expected. Conventions overstate that partial operations return junk rather than `Option`, contradicted by queue/selection APIs, and reading recommendations still use legacy chapter numbers 16/23 for greedy/MST. Update fourth-edition navigation/conventions; no proof impact. |

Completion interpretation: appropriate as an expository guide, not a formally proved chapter of algorithm claims.

## Chapter 2 — Getting started

Depth: full insertion algorithm/proofs, full line-cost definitions and formula/specialization interfaces; merge definitions and execution/correctness/cost spine read; long recurrence support sampled. `Chapter_02_Merge_Interface`, `Chapter_02_LineCost_Interface`, main interface and trust reviewed.

| Section / claim | Location / declarations | Verdict | Evidence / boundary |
|---|---|---|---|
| 2.1 Insertion correctness | `C02/Section_02_1_Insertion_Sort.lean:42` `insertSorted`, `:51` `insertionSort`, `:98` ordered insertion, `:117` permutation, `:129` sorted result, `:137` permutation | MATCH | Recursively sorts tail then inserts head; induction preserves all occurrences and sortedness. Empty/singleton are genuine base cases. Immutable `List Nat`, not an array prefix execution; documented representation boundary. |
| 2.2 Symbolic line table | `C02/Section_02_2_Analyzing_Algorithms/LineCost/Definitions.lean:50` `insertionSortLineCounts`, `:74` `insertionSortRunningTime`; `LineCost/BestWorst.lean` named best/worst substitutions | MATCH, bounded | Seven fields and exact arithmetic formula exist, closing the old missing-table issue. `t : Nat → Nat` is supplied, not extracted from an input trace. There is no trace-validity predicate: e.g. all `tᵢ=0` yields zero while tests but nonzero assignments. These are symbolic formulas, not evidence such traces execute. |
| 2.2 Worst/best comparisons | `C02/Section_02_2_Analyzing_Algorithms.lean:59` `insertionSortWorstComparisons`, `:141` theta; `:149` `insertSortedComparisons`, `:154` actual recursive counter, `:171` best-case equality | UNCERTAIN for execution worst-case closure | Best-case count is genuinely attached to the recursive algorithm. Worst-case function is defined directly as `triangular (n-1)` and its Θ theorem only proves arithmetic about that function. Whole-source search found no universal bound/attainment theorem connecting it to `insertionSortComparisons`. Add those two connections if claiming executable worst-case Θ; retain symbolic-table result. This is a missing bridge, not a false Θ theorem. |
| 2.3 MERGE and merge sort | `C02/Section_02_3_Designing_Algorithms/Merge/Definitions.lean:28` `mergeWithCost`; `MergeSort/Definitions.lean:34` `mergeSortWithCost`, `:59` `mergeSortWork`; `MergeSort/Cost.lean:192,242` recurrence/asymptotic theorems | MATCH | Both nonempty MERGE branches consume one head and charge a comparison/write; empty side charges remaining writes. The top-level execution now recursively invokes this MERGE, proves permutation/sortedness and counter erasure, and derives work by input length. This closes the historical “only List.mergeSort wrapper” issue. Costs charge abstract writes/comparisons, not allocation. |

No reason to reopen closed MERGE or line-table issues. The residual worst-case execution bridge should be stated precisely instead of inferring completion from the name `WorstComparisons`.

## Chapter 3 — Characterizing running times

Depth: full bridge statements and selected proof bodies, growth/identity inventories, Robbins finite bound and polynomial bridge; long special-function proofs sampled. Three focused bridge/identity/growth interfaces and trust read.

| Section / claim | Location / declarations | Verdict | Evidence / boundary |
|---|---|---|---|
| 3.1 O/Ω/Θ | `C03/Section_03_1_Asymptotic_Notation/Core.lean` five wrappers and shared threshold; `CLRSBridge.lean:83` `isBigTheta_iff_clrs` | MATCH | Norm-based signed-function semantics are connected to nonnegative inequalities with explicit eventual nonnegativity. Common thresholds use maxima; quantifier order retains constants before threshold/input. |
| 3.2 Strict o/ω | `C03/Section_03_1_Asymptotic_Notation/CLRSBridge.lean:114` `isLittleO_iff_clrs_strict`, `:147` little-omega bridge | MATCH | Strict bridge adds necessary eventual positivity. Proof chooses `c/2`; common zeros would otherwise invalidate `<`. Real-domain and transitivity wrappers exist; this is a justified hypothesis, not an undisclosed hole. |
| 3.3 Functions, growth, Stirling | `C03/Section_03_2_Standard_Functions/GrowthBridges.lean:58` `polynomial_isBigTheta_degree`; `GrowthHierarchy.lean:108` `complete_growth_hierarchy`; `Robbins.lean:240` exact factorial identity, `:263` `robbinsAlpha_bounds` | MATCH | Nonzero-polynomial condition excludes the zero leading term; exact finite Robbins error and real exponent hierarchy are present. Identity wrappers do delegate to Mathlib, openly. Legacy `3.2` headings inside supporting modules are a numbering MINOR, not a mathematical gap. |

Old absolute-value/strictness and Stirling omissions have current source closure; no new substantive source defect identified in sampled claims.

## Chapter 4 — Divide-and-conquer

Depth: matrix algorithms and correctness fully read at key execution spine; substitution templates, recurrence signatures, integer tree expansion/equality read; Master/continuous/Akra–Bazzi analytic proof bodies sampled. FourthEdition interface, integer tree test and trust checked. No general textbook equivalence asserted.

| Section / claim | Location / declarations | Verdict | Evidence / boundary |
|---|---|---|---|
| 4.1 Square multiplication | `C04/Section_04_1_Multiplying_Square_Matrices.lean:73` `mulRec`, `:102` correctness, `:132` `mulWork`, `:263` runtime Θ | MATCH for algebra; UNCERTAIN execution cost | Eight recursive block products over `SqMat R k` compute ring multiplication. Work is a separately defined recurrence, not a counter projected from `mulRec`; no counted-execution bridge found. The all-natural-size recurrence does not itself implement arbitrary-size matrix padding. |
| 4.2 Strassen | `C04/Section_04_2_Strassen_Algorithm.lean:176` `strassenRec`, `:194` recursive correctness, `:220` `padOne`, `:265` `strassenWork`, `:394` runtime Θ | MATCH for algebra; UNCERTAIN cost attachment | Exactly seven recursive products and standard reconstruction, valid over arbitrary rings. Padding theorem embeds one already power-of-two square into the next. Separately solves `7T(floor(n/2))+n²`; runtime wording should distinguish recurrence analysis from execution instrumentation. |
| 4.3 Substitution | `C04/Section_04_3_Substitution_Method.lean:39,52,65` upper/lower/sandwich, `:81` linear template | MATCH | Honest one-step induction templates: base plus preserved induction implication, and concrete additive/geometric instantiations. No standalone general recurrence solver is claimed. |
| 4.4 Recursion trees | `C04/Section_04_4_Recursion_Tree_Method/Branching/IntegerTree/Execution.lean:37` `build`, `:107` `build_totalCost_eq`; `…/Balanced.lean:46`; `…/Unbalanced.lean:73,108` | MATCH | Well-founded size descent, cutoff leaves, independent recurrence equations and exact total-cost equality; unbalanced floor/ceiling trees genuinely allow unequal depths. This closes the earlier common-depth-only concern. Current §4.4 guide explicitly says transport of these rounded executions into asymptotic interfaces remains separate; map wording “connect to” should not imply that transport is done. |
| 4.5 Master method | `C04/Section_04_5_Master_Theorem.lean:43` recurrence, `:182` case1, `:243` case2, `:379` polylog case2, `:445` case3 | MATCH for advertised criteria; UNCERTAIN full textbook theorem | Case1 geometric forcing and case2 bounds are real analytic conclusions. Case3 assumes eventual normalized value ≤ constant·last forcing, already an upper domination conclusion; the all-input legacy callers retain that assumption. This is honestly called a tail-dominated criterion, but is not a derivation of domination from a conventional forcing regularity condition. |
| 4.6 Continuous master | `C04/Section_04_6_Continuous_Master_Theorem.lean:61` `geomSum`, `:161` `continuousWork`, `:210,270,308` three cases | MATCH for represented calculation | “Continuous” layer sums real-valued work at natural depth, natural a/b/p, exact sizes `b^k`. It is not a general real-input recurrence proof. Geometric three-case estimates and scale bridges are explicit. |
| 4.7 Akra–Bazzi | `C04/Section_04_7_Akra_Bazzi.lean:402` `PolynomialGrowth`, `:416` recurrence, `:1037` upper bound, `:1779,1793,2213` Θ wrappers | MATCH for explicit regimes; UNCERTAIN full coverage | Forcing is nonnegative, monotone and Θ(n^q); coefficients are positive natural multiplicities, base costs fixed, floor perturbations. Proven regimes require p>0 and q<p, q=p, or q≥p+1. Missing interval p<q<p+1 and p=0 remain outside these wrappers. Section explicitly states regimes, so do not call restricted theorem false. `G04` says §§4.1–4.7 “close”; it should carry the same restricted boundary. |

Example boundary: branches `(2,2)`, root p=1, forcing n^(3/2) satisfies the stated monomial regularity but none of the three Θ wrappers' exponent relations. `g(n)=n log n` is not Θ(n^q) for any q. These demonstrate scope, not counterexamples to proved statements. Recommended metadata fix: state the exact regimes and recurrence-model nature of matrix work. Full theorem/general execution work remains a separate undertaking.

## Chapter 5 — Probabilistic analysis

Depth: hiring execution, Fisher–Yates execution/uniformity, expectation bridge fully read; prefix-event probability and birthday/streak/on-line hiring combinatorial proof spines sampled. Focused tests include small shuffle/hiring executions, empty on-line strategy and boundary threshold cases.

| Section / claim | Location / declarations | Verdict | Evidence / boundary |
|---|---|---|---|
| 5.1 Hiring | `C05/Section_05_1_Hiring_Problem.lean:194,204,139` `recordsFrom`, `hireAssistant`, `expectedHires_eq_harmonic` | MATCH | First candidate hired, later strict records counted; mathematical expectation is a finite rank-symmetry model. Hiring expenditure multiplies number hired by hireCost; it does not include interview scan cost. |
| 5.2 Indicators | `C05/Section_05_2_Indicator_Expectation.lean:24` `indicator_expectation_eq_probability`; `Section_05_2_Indicator_Random_Variables.lean:166` fixed-point expectation | MATCH | Both sides use the same finite uniform space, with linearity independent of indicator independence. Fixed-point result includes positive n condition. |
| 5.3 Randomization | `C05/Section_05_3_Randomized_Algorithms/FisherYates/Execution.lean:32` `fisherYatesEquiv`, `:75` invariant; `…/Uniformity.lean:45` `fisherYates_uniform`; `Section_05_3_Randomized_Hiring/ExpectationBridge.lean:60` bridge | MATCH | Constructive dependent choice-vector/permutation bijection, one-swap suffix equations, exact uniform distribution. `hiringExpectationBridge` is actually proved and fed to the unconditional expectation/cost wrappers; do not report it as an open certificate. |
| 5.4 Applications | `C05/Section_05_4_Probabilistic_Analysis.lean:237,283,777,1318` `expectedCollisions_eq`, `expectedBallsInBin_eq`, longest-streak upper/lower; `…/OnlineHiring.lean:847` closed probability, `:1166` asymptotic | MATCH within sampled model | Independent coordinates are `Fin k → Fin n`; coincidence expectation is genuine. Fair-flip streak bounds concern maximum run, and on-line hiring has executable threshold strategy, uniform permutation event and harmonic/asymptotic probability. Deep tail/asymptotic proofs sampled. |

No new confirmed defect. Prose section 5.4 undersummarizes its later streak results, but chapter guide/trust exposes them.

## Chapter 6 — Heapsort

Depth: indexed predicates, heapify repair, bottom-up builder and cost erasure read; heap-sort invariant and checked-insert proof spines sampled. Trust bundles genuine array operations; focused insertion examples exercise inactive suffix and oversized heapSize rejection.

| Section / claim | Location / declarations | Verdict | Evidence / boundary |
|---|---|---|---|
| 6.1 Heaps | `C06/Section_06_1_Heaps.lean:280` `ArrayMaxHeap`, `:418` root maximum | MATCH | Heap size bounded by backing list, zero-based parent/children, both child inequalities. Descending-list scaffold is explicitly auxiliary. |
| 6.2 Heapify | `C06/Section_06_2_Maintaining_Heap_Property.lean:750` `maxHeapifyFuel`, `:1061` repair, `:1074` root theorem | MATCH with stronger local interface | Repair uses fuel≥heapSize−i, supplied by callers. “From i” predicate constrains all parent indices≥i, not only descendants of i, so module's literal subtree-language is stronger than ordinary subtree precondition. This does not obstruct bottom-up build or root heapify. |
| 6.3 Build heap | `C06/Section_06_3_Building_A_Heap.lean:45` loop, `:126` builder, `:179` correctness; `C06/Section_06_4_Heapsort/CostedExecution.lean:613` linear bound | MATCH | Starts at floor(n/2), descending repairs, leaf initialization supplies invariant. Permutation and length accompany heapness. Cost uses sum of logarithmic height envelopes and ≤3n, not crude n² control bound. |
| 6.4 Heapsort | `C06/Section_06_4_Heapsort.lean:91` invariant, `:521` loop, `:829` correctness; `…/CostedExecution.lean:37` costed heapify, `:49` erasure, `:743` final log-cost bundle | MATCH | Sorted suffix + heap prefix + cross-order; root-to-end swap, shrink, repair. Concrete frame counter erased to same algorithm. Explicit O(n log n) upper envelope, not a worst-case Ω lower bound. Immutable backing storage is declared, not a new MAJOR. |
| 6.5 Priority queues | `C06/Section_06_5_Priority_Queues.lean:536` increase-key state, `:836` delete state; `…/Insert/Checked.lean:90` checked insert; `…/Insert/Cost.lean:123` state+log counter | MATCH | Bounds/keys checked, upward bubble replaces scaffold rebuilding. Checked insert preserves inactive tail and grows active length. Delete is a value/set-of-occurrences interface, not identity-bearing node deletion; duplicate-maximum object identity is outside it. |

Historical `ch06` still lists rebuild/List representation as MAJOR and treats logarithmic height envelope as exact tree height. Do not reuse that as fresh defect evidence: current public operations are local heap algorithms with explicit control-cost boundary. Correct the historical report separately if updating audit metadata.

## Chapter 7 — Quicksort

Depth: partition/recursive algorithm and interface claims read; pair-trace/operational bridge and BST normalization spines sampled. Trust and FourthEdition interface explicitly check the formerly missing execution bridge.

| Section / claim | Location / declarations | Verdict | Evidence / boundary |
|---|---|---|---|
| 7.1 Quicksort | `C07/Section_07_1_Description_Of_Quicksort.lean:129` partition, `:474` scan-loop correctness, `:618` array wrapper+trace, `:744` quicksort correctness | MATCH | Stable functional partition into ≤pivot and >pivot, all occurrences preserved; full-fuel recursion guarantees sorting. Adjacent-swap reachability is a finite trace, not a proof that the actual mutable Lomuto loop ran; guide says mutable refinement deferred. |
| 7.2 Performance | `C07/Section_07_2_Performance_Of_Quicksort.lean:46,133` `quickSortComparisonsFuel`, `quickSortComparisons_quadratic` | MATCH | Counter follows partition sizes and both recursive calls, and ≤n² is proved. Guide explicitly limits this section to an upper bound; absence of worst-case attaining sequence is not hidden. |
| 7.3 Randomized version | `C07/Section_07_3_Randomized_Quicksort/ExplicitRandomness/OperationalBridge.lean:22,31,51,59` | MATCH | Pointwise equality between natural pair trace and actual recursive quicksort comparisons on uniform priority-permutation input, composed through total BST depths. This is stronger than merely assigning a closed-form expected count. Distinct ranks are explicit; no claim for duplicate-rich randomized inputs. |
| 7.4 Analysis | `C07/Section_07_4_Analysis_Of_Quicksort.lean:62,95` `expectedRunningTime_eq_sum_compared_prob`, `expectedRunningTime_isBigTheta_nlogn` | MATCH within comparison metric | Pair probability and finite linearity yield Θ(n log n), supported by operational bridge above. “Running time” is identified with comparisons; RAM/array execution remains deferred and should stay visible. |

No reopened probability-provenance gap: current pointwise bridge is real.

## Chapter 8 — Sorting in linear time

Depth: lower-bound model/proof spine read; counting-sort mutable output module fully read with its actual reverse-bucket helper; radix execution/cost and bucket execution/distribution/cost definitions read, correctness/probability proofs sampled. Current trust emphasizes cost names but does not test charged passes against execution.

| Section / claim | Location / declarations | Verdict | Evidence / boundary |
|---|---|---|---|
| 8.1 Lower bound | `C08/Section_08_1_Lower_Bound_For_Sorting.lean:77` `SortTree`, `:91` height, `:136` run, `:150` `CorrectSort`, `:337` flagship lower bound | MINOR / UNCERTAIN runtime bridge | Correct-sort injectivity establishes ≥n! leaves, and structural height lower bound is valid. Structural height need not equal maximum *reachable* execution depth because infeasible branches are allowed. The theorem states height, not existence of an input with enough comparisons. See finding F8c. |
| 8.2 Counting sort | `C08/Section_08_2_Counting_Sort/MutableOutputArray.lean:84` scatter, `:113` wrapper, `:188` correctness, `:243` cost; `CountTables.lean:159` reverseBucket | MAJOR | Correctness/stability/permutation bridge is real. Advertised linear per-pass cost is not this algorithm's key-comparison count: actual execution rescans all n inputs once for every key. See F8a. |
| 8.3 Radix | `C08/Section_08_3_Radix_Sort.lean:715` `radixSortByWithCost`, `:740` exact assigned cost | MAJOR inherited cost claim; MATCH correctness | Stable low-to-high passes, bounded digit window, numeric-order bridge are substantive. Its costed loop calls per-key-filter `countingSortBy` and charges fictional linear-pass expression from 8.2. Correctness erasure cannot establish that charge upper-bounds execution. |
| 8.4 Bucket sort | `C08/Section_08_4_Bucket_Sort.lean:79` bucketSortBy, `:225` bucketSortByRank, `:611` distributeBuckets, `:660,664` paired cost, `:762` expectation | MAJOR | Genuine finite-uniform occupancy second moment and expected n+Σn_j². However the actual public sorter filters the full input separately for every bucket; added single-pass distributor has no execution caller. See F8b. |

### F8a — Counting-sort linear cost is assigned to a repeated-scan algorithm

`scatter` folds over `List.range (maxKey+1)` and calls `reverseBucket key xs k` each time. `reverseBucket` folds all of xs and evaluates `key x == k` once per element. Therefore exactly n(k+1) such tests precede output appends. At n=k=10 this is 110 tests, while `countingSortArrayCost` assigns 42 total steps; for k=n this is Θ(n²), not O(n+k), even with unit-cost array operations. No CPU/RAM refinement objection is needed: these are source-level key tests. The comments at `MutableOutputArray.lean:23–30,235–244` advertise four linear passes and an executable work bound absent from the program.

Fix: implement one count pass, one prefix-sum pass, and one reverse input scatter into indexed output with mutable cumulative counts; instrument those passes and prove erasure/cost. Alternatively accurately label existing algorithm as a stable bucket specification with O(nk) key tests and retain the independent CLRS linear formula as a specification. Radix must consume the real linear implementation or narrow its runtime claim. Impact: Chapter 8 linear executable sorting completion is not presently supported.

### F8b — Bucket-sort expected linear charge ignores its actual distribution scan

`bucketSortByRank` calls `bucketSortBy`, whose body applies `bucket bucketOf xs j` for every j; `bucket` is full-input filter. For n buckets and n inputs it makes n² bucket-key tests on every assignment, so expected distribution work is n² under the *same* uniform sample space. `distributeBuckets` at :611 is a real single-pass candidate but whole-source references are only its own size theorem and prose. `bucketSortByRankWithCost` simply pairs the old sorter with n+Σn_j², while the module says the metric is bound to “real executable construction.” This remains false independently of the correct occupancy expectation.

Fix: make the public executable consume `distributeBuckets` output, prove its bucket-content refinement (up to reversal), instrument a per-bucket sorter and compose a cost bound, and include bucket-array initialization/concatenation costs. Keep current deterministic sorted/permutation and finite expectation lemmas.

### F8c — Decision-tree structural height versus reachable run length

The model allows `node i i l r`; every permutation takes l, while r can be arbitrarily deep. Wrap a correct sorter l in this node with an unreachable deep r: maximum reachable run length grows by one, structural height can grow arbitrarily. Thus the comment “This is the worst-case number of comparisons” at :88 is false. The proved lower bound on height does not automatically establish a lower bound on max run cost. The intended runtime lower bound is true for comparison sorting but needs a reachable/pruned-tree argument or a prefix-code counting argument with bounded run lengths. Add `runCost` and prove an existential worst-input lower bound. This is an interface gap, not a counterexample to `comparisonSort_worstCase_lowerBound` as stated.

## Chapter 9 — Medians and order statistics

Depth: min/max full algorithm/certificate, selection definitions and final correctness/linear bounds, randomized schedule and expectation semantics read; long grouped-pivot combinatorics and linear bound induction sampled. Both Closure and focused interfaces/trust reviewed.

| Section / claim | Location / declarations | Verdict | Evidence / boundary |
|---|---|---|---|
| 9.1 Min/max | `C09/Section_09_1_Minimum_And_Maximum.lean:72` minMax?, `:184` certificate, `:241` comparisons | MATCH | Empty returns none, singleton zero comparisons, pair one, each added pair three. Extrema occur in input and bound all members. Advertised ≤3 floor(n/2) is a valid envelope, not asserted exact count for even n. |
| 9.2 Randomized SELECT | `C09/Section_09_2_Selection_In_Expected_Linear_Time.lean:559` rank correctness; `Section_09_3_Selection_In_Worst_Case_Linear_Time/Randomized_Select.lean:374,408,640,905` | MATCH within declared partition metric | Counts handle duplicates; fresh current-rank choice each call, schedule errors reject, state-dependent nested expectation, ≤4cn majorizer derived using actual continuation size. The pivot is computed by sorting/indexing `selectByRank?`; its execution cost is explicitly excluded in `G09`. Do not advertise full runtime of this implementation, but don't flag an undisclosed gap. |
| 9.3 Worst-case SELECT | `C09/Section_09_3_Selection_In_Worst_Case_Linear_Time.lean:1456` recursive selector correctness, `:2196` full comparison charge ≤100n | MATCH within declared model | Separate older pivot/path-only interfaces remain, but final theorem includes nested median selection and grouping/partition charges; final induction consumes actual pivot size bound. No unfurnished pivot certificate in final closure. Full RAM/primitive cost is excluded. |

The prominent guide accurately limits randomized cost to partition work. Source/test names containing “comparisons” should be read with that boundary.

## Chapter 10 — Elementary data structures

Depth: stack/queue and linked-list modules fully read; LCRS encode/decode and round-trip theorem spine read. Trust tests cover push, wrap and LCRS. No theorem-count inference.

| Section / claim | Location / declarations | Verdict | Evidence / boundary |
|---|---|---|---|
| 10.1 Stacks/queues | `C10/Section_10_1_Simple_Array_Based_Data_Structures.lean:136` ArrayStack, `:180` ArrayQueue, `:188` enqueue, `:197` dequeue | MATCH on valid states; MINOR missing validity API | Functional LIFO/FIFO and concrete pointer transitions/overflow exist. Raw structures have no top≤capacity or 0≤head,tail<capacity invariant. Zero-capacity queue with head=tail=0 accepts enqueue because Nat mod 0 returns its input. Add a valid-state predicate and preservation/constructor contract, or reject zero capacity/out-of-range pointers. Valid n>1 empty-queue theorem is correctly guarded. |
| 10.2 Linked lists | `C10/Section_10_2_Linked_Lists.lean:31` search, `:40` deleteAll, `:47` soundness, `:76` membership iff | MINOR | List model explicitly deletes **all equal keys**, not one identity-bearing node; duplicates `[x,x]` both disappear. Proves search soundness but no returned-first/minimal-index or none-completeness theorem. This is openly a limited functional model; pointer/sentinel deletion and O(1) identity deletion remain beyond it. |
| 10.3 Rooted trees | `C10/Section_10_3_Representing_Rooted_Trees.lean:83,102,150` `toLCRSForest`, `ofLCRSForest`, both round trips and `lcrsEquiv` | MATCH | Genuine information-preserving ordered-forest/LCRS bijection, node count and preorder preserved. Single rooted tree round trip is separate. Module heading still says old §10.4; metadata/navigation MINOR only. |

Chapter completion should mean its declared functional/array-pointer model, not a full mutable linked-list implementation.

## Chapter 11 — Hash tables

Depth: direct table fully read; chain/universal family definitions and probabilistic signatures sampled; open-addressing finite permutation definitions and tail-count bridge read; perfect-table definition/search and construction/trial endings fully read, collision counting sampled. Interface/trust explicitly cover recent uniform-probe bridge.

| Section / claim | Location / declarations | Verdict | Evidence / boundary |
|---|---|---|---|
| 11.1 Direct address | `C11/Section_11_1_Direct_Address_Tables.lean:52,58,64` `search_insert_same`, `search_insert_other`, `search_delete_same` | MATCH | Total Nat-indexed Option-valued table, overwrite/delete/frame semantics. Bounds and actual array costs expressly deferred. |
| 11.2 Chaining | `C11/Section_11_2_Chained_Hash_Tables.lean:557,647` expectedRandomSuccessfulSearchCost, universal_expected_search_cost; deterministic update definitions in same file | MATCH | Deterministic membership updates separate from independent-uniform assignment expectation and random hash-function universality model. Deletion filters all copies, an explicit key-set model. Successful cost averages query/insertion position under stated uniform assumptions. |
| 11.3 Hash functions | `C11/Section_11_3_Hash_Functions.lean:134,442` affineHash_isUniversal and affineHashMod_isUniversal | MATCH | Actual finite field families discharge IsUniversal. Exact-field family permits zero slope; general outer-mod-m family is separately proved with prime/range conditions. Do not report universality as an open assumption. |
| 11.4 Open addressing | `C11/Section_11_4_Open_Addressing.lean:185` openSearch_openInsert; `…/UniformProbe/Probability.lean:57,72,125` exact tail probability/expectation/log bound | MATCH under not-full load | Permutation extension counting realizes the without-replacement tail model; searches count first empty slot, and log bound assumes 0<n<m. Successful expectation is explicitly average over insertion-time occupancies, not a full dynamic table process. Source main-page “sample space deferred” gap note is stale; this gap has closed. At full table count definition has an extra terminal tail, but advertised bound excludes it. |
| 11.5 Practical considerations (mapped perfect hashing) | `C11/Section_11_5_Perfect_Hashing.lean:68` PerfectHashTable, `:82` sec_inj, `:103` search iff, `:864` trials, `:931` constructionCost, `:970` expected cost | MAJOR interface, MINOR/UNCERTAIN construction claim | Exact membership theorem is valid but stronger-than-documented invariant restricts entire key universe, and construction cost is an analytic upper-budget expression without a builder bridge. See F11. Fourth-edition “Practical considerations” versus promoted legacy perfect hashing is explicitly mapped; unavailable corpus prevents certifying all section content covered. |

### F11 — Perfect-hash invariant and construction scope

`sec_inj` is documented to be injective **on stored keys**, but has no `x∈keys`/`y∈keys` premises. Take key universe `{a,b}`, stored set `{a}`, one primary bucket, secondary map sending both a and b to slot zero, and slot zero storing a. This is a correct static search table: a succeeds, b fails equality check. It cannot inhabit the current structure because sec_inj implies a=b. All the table storage/only-keys fields are otherwise satisfiable; `perfectSearch_iff_mem` does not use sec_inj. Fix: add both stored-key hypotheses and connect finite secondary slot bounds/table construction. Severity MAJOR: representation contract excludes valid perfect tables, though search theorem remains true.

The probability theorem uses all assignments `Fin n → Fin(n²)` (SUHA), not an arbitrary already-proved universal family parameter H; module wording should accurately say this. `constructionCost = n+2*totalSecondarySpace` analytically replaces trial count by its proposed expectation upper bound. Final `<5n` proof unfolds this expression and invokes expected space; it never constructs PerfectHashTable or ties successful sampled trials to returned tables. Preserve as analytic budget theorem, or add a builder and conditional expectation proof before claiming end-to-end randomized construction.

`trialsUntilCollisionFree` returns `t+1` if first t trials fail. Comment calls that an **overestimate** of unbounded trials; on a continuation with next two trials failing, true waiting time >t+1, so it is a lower truncation. Uniform upper bounds on truncation expectations can support an unbounded result with an explicit limit/termination argument, but no such bridge is present. Fix this comment and state the finite-truncation boundary (already partly exposed in theorem docs).

## Chapter 12 — Binary search trees

Depth: definitions, full query-contract signatures and deletion/zipper proof spines; pointer representation and uniqueness read; expected-height transfer and treap endpoint read; deep ancestor and exponential-tail derivations sampled. Trust and query/closure/expected-height interfaces reviewed.

| Section / claim | Location / declarations | Verdict | Evidence / boundary |
|---|---|---|---|
| 12.1 BST model | `C12/Section_12_1_Binary_Search_Trees.lean:146` BSTree, `:170` Ordered | MINOR | Strict left<root<right and duplicate-suppressing insertion form a key set. Tree membership/order theorem matches that model. It should not be read as a multiset/node-identity BST. |
| 12.2 Queries | same file `:281` search iff, `:595,614,627,646` some/none successor/predecessor specs, `:1387` iterative search bridge | MATCH | Genuine extremal elements and complete some/none interfaces under Ordered. No vacuous returned-value-only contract: query existence is also characterized. O(h) descent counters are present; pointer/RAM cost explicitly deferred. |
| 12.3 Insert/delete | same `:906` membership deletion, `:967` ordering, `:1219` insertion ordering, `:1580` transplant deletion equality, `:1923` RepresentsW | MATCH | Deletion uses actual right minimum/deleteMin and preserves all nondeleted keys. Zipper transplant equivalence is real. Pointer representation carries finite disjoint node sets, preventing the sharing/cycle problem seen in Chapter13. Pointer parent fields are not fully tracked by this relation; claims should retain child-structure refinement scope. |
| Additional expected height (not another mapped fourth-edition section) | `C12/Section_12_1_Binary_Search_Trees/RandomConstruction.lean:186` height bridge; `…/ExpectedHeight.lean:21,26,50,58` expected height and bounds; `src/CLRSLean/Extensions/TreapHeight.lean:1239` | MATCH in sampled chain | Pointwise height equality, probability-preserving reversed-priority reindexing, then genuine **maximum height** tail theorem ≤30Hn. It is not confused with expected depth of one node. Chapter guide labels this “12.4” although map has only 12.1–12.3; mark numbering/supplement status clearly. |

No confirmed new core correctness defect. Scope is functional set BST plus selected pointer primitives, not full pointer TREE-DELETE execution.

## Chapter 13 — Red-black trees

Depth: invariant/algorithm definitions and functional correctness endpoints, all rotation/store module, insertion/deletion cost definitions and proofs, and WellFormed bundle read; large balancing case proofs sampled. Interface/trust checks functional invariant but not pointer rotation semantics. Both root and this auditor compiled counterexamples successfully.

| Section / claim | Location / declarations | Verdict | Evidence / boundary |
|---|---|---|---|
| 13.1 RB properties | `C13/Section_13_1_Red_Black_Trees.lean:149,1281` RedBlackShape, height_log_bound, insertFixup/del invariants; `C13/WellFormed.lean:25,55,61` | MATCH for functional set trees | Height bound and balanced-color shape, plus BST and exact membership contracts, are substantive. Okasaki/Kahrs functional algorithms are disclosed. Entire shape case proof not reread line-by-line. |
| 13.2 Rotations | `C13/Section_13_2_Rotations.lean:103` StoreRepr, `:236,258` pointer rotations; `:125,151` functional inorder/BST | MAJOR pointer implementation and representation | Functional rotations preserve inorder/BST. Pointer rotations omit root/parent reconnection and StoreRepr permits sentinel aliases/cycles. See F13a/F13b. |
| 13.3 Insertion | `C13/Section_13_3_Insertion.lean:173` insertCost, `:199` log bound, `:271` bst_insert | MAJOR cost claim; MATCH functional correctness | Cost only follows search descent; no rotations/recolors counted or bridged. Inorder preservation does not establish operational identity to RB-INSERT-FIXUP. |
| 13.4 Deletion | `C13/Section_13_4_Deletion.lean:50` deleteCost, `:79` log bound, `:208` bst_delete; `C13/WellFormed.lean` delete_correct | MAJOR cost claim; MATCH functional correctness | Height-based join budget is inserted directly into unrelated recursive cost formula. No composed pointer delete execution or domination proof. Functional membership+shape+BST theorem is valid and remains usable. |

### F13a — Pointer rotation disconnects the promoted subtree

In rotateLeftP, x.right becomes beta, y.left becomes x, and parents of x/y/beta are locally changed. There is **no change to s.root or nx.parent's child link**. Example: root1, node1=(key1,black,left0,right2,parent0), node2=(key2,red,left0,right0,parent1). Input represents keys [1,2]. After rotateLeftP at1, root remains1 and node1 has no children; output rooted tree represents [1], while promoted node2 is unreachable from root. Symmetric right rotation has same omission. Root witness compiled at `/tmp/CLRSChapter13Audit.lean`; independent auditor witness at `/tmp/clrs-audit-counterexamples-01-13.lean`.

Fix: when parent is sentinel, update root to promoted node; otherwise update the correct parent's left/right link, preserving allocation and all affected parent links. Prove StoreRepr/refinement under a strengthened valid store predicate and semantic regression examples. Assigned rotateCost=6 must match an explicit operation metric or be called a bounded charge. Severity MAJOR for advertised pointer layer; not a failure of functional red-black theorem.

### F13b — StoreRepr does not guarantee acyclicity/unique tree interpretation

`StoreRepr.nil` accepts pointer0 unconditionally. `StoreRepr.node` neither requires i≠0 nor requires `s.get 0=none`, disjoint subtrees, or correct parent links. Let root=0 and node0 have both child pointers0. This same cyclic store represents empty by nil constructor, and a nonempty singleton by node constructor with two nil proofs. Thus the explicit comment at :96–101 claiming finite induction “enforces acyclicity” is false. With nonzero pointers it also permits shared subtrees and unconstrained parent fields.

Fix: reserve sentinel at the representation boundary; carry footprints/disjointness and parent consistency (Chapter12.RepresentsW is a useful pattern); prove tree uniqueness/frame preservation before pointer rotation correctness. Severity MAJOR: central representation predicate admits malformed stores and cannot justify the advertised pointer correspondence.

### F13c — Search-depth formulas advertised as complete pointer costs

`insertCost` at §13.3:173 returns one on empty/equal and adds two per chosen descent; no `balanceLeft`, `balanceRight`, rotations, recoloring, result value or pointer store appears. `deleteCost` at §13.4:50 similarly adds two along descent and, on target hit, directly charges height(left)+height(right). Its proof only uses max-height inequalities. Theorems :199/:79 bound **these formulas**, not execution of insert/delete/fixup. Docs and map call them O(log n) pointer-operation execution theorems. Whole-source search found no cost erasure or simulation/upper-domination bridge. Existing `keys_balanceLeft/Right` prove inorder equality, not that the execution follows the textbook cases.

Fix: instrument actual functional insertion/deletion including all rebalance cases, prove erasure plus per-level bound, and call the metric abstract case work unless a pointer refinement is proved. For the pointer claim, compose corrected local primitives with a real insertion/deletion state machine and charge writes. Alternatively narrow docs/map to descent/height budgets. Severity MAJOR because claimed operation-cost closure goes beyond theorem statement. Functional `insert_correct` and `delete_correct` should retain MATCH.

## Consolidation priorities

1. Confirmed source defects needing review: Chapter8 repeated scans versus linear executable cost, Chapter13 pointer rotation/representation failures, Chapter11 sec_inj quantifier omission.
2. Confirmed claim/interface gaps: Chapter13 unbound cost formulas; Chapter8 unreachable-height interpretation; Chapter11 construction budget/truncation wording. Distinguish analytic true theorems from claimed algorithm semantics.
3. Scope/metadata corrections without invalid-proof allegations: Akra–Bazzi restricted regimes, matrix cost recurrence attachment, insertion worst-case bridge, Chapter10 valid-state domain, fourth-edition numbering and stale gap notes.
4. Preserve checked achievements: Chapters2 MERGE execution, 3 strict/asymptotic/Robbins bridges, 5 hiring and shuffle probability, 6 actual heap operations, 7 operational comparison expectation, 9 recursive pivot-cost closure, 11 explicit probe probability, 12 expected **height**, 13 functional WellFormed.

Final adjudications are recorded in the accompanying adversarial review. Do not convert this sampled, corpus-unverified content review into an unconditional “all textbook claims proved” conclusion.

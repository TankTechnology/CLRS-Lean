# CLRS-Lean Proof Map

This ledger records what is proved, what is partial, and what is currently
deferred.  It is intended to become the website's main navigation table.

For a coarser planning view, see
[`proof-status-board.md`](proof-status-board.md).  That board groups chapters
and sections into `main proof completed`, `structured but not complete`, and
`missing core theorem`, so work does not keep cycling back to already completed
main-proof areas without a specific refinement goal.

## Chapter 1 - The Role of Algorithms

- Lean source: `CLRSLean/Chapter_01.lean`
- Status: `expository`
- Main theorem: none
- Current gap: none; theorem-bearing work starts in later chapters

This page explains the project contract: translate each selected textbook claim
into a Lean-friendly model, expose a public theorem interface, prove it, and
record the status honestly.

## Chapter 2 - Getting Started

### Section 2.1 - Insertion sort

- Lean source: `CLRSLean/Chapter_02/Section_02_1_Insertion_Sort.lean`
- Status: `proved`
- Main theorems:
  - `CLRS.Chapter02.insertionSort_sorted`
  - `CLRS.Chapter02.insertionSort_perm`
- Proof pattern: induction, sortedness preservation, permutation preservation
- Current gap: none for the current functional-list theorem statement

The section proves functional correctness for insertion sort over lists of
natural numbers.  The proof mirrors the textbook loop invariant by separating
orderedness from element preservation.

### Section 2.2 - Analyzing algorithms

- Lean source: `CLRSLean/Chapter_02/Section_02_2_Analyzing_Algorithms.lean`
- Status: `proved`
- Main theorems:
  - `CLRS.Chapter02.insertionSortWorstComparisons_quadratic`
  - `CLRS.Chapter02.insertionSortWorstComparisons_eventually_quadratic`
- Proof pattern: triangular sum, natural-number inequalities, asymptotic wrapper
- Current gap: full RAM semantics and exact line-by-line pseudocode cost are
  future strengthening targets

The section proves that the standard insertion-sort worst-case comparison count
is bounded by a quadratic function.

### Section 2.3 - Designing algorithms

- Lean source: `CLRSLean/Chapter_02/Section_02_3_Designing_Algorithms.lean`
- Status: `proved`
- Main theorems:
  - `CLRS.Chapter02.mergeSort_sortedLE`
  - `CLRS.Chapter02.mergeSort_perm`
  - `CLRS.Chapter02.mergeSortRecurrenceOnPowersOfTwo_closedForm`
- Proof pattern: divide and conquer, sortedness, permutation preservation,
  recurrence solving
- Current gap: arbitrary-size floor/ceiling recurrence and full RAM execution
  cost are future strengthening targets

The section proves functional correctness for merge sort using Lean's verified
`List.mergeSort` implementation.  It also proves the exact closed form of the
standard recurrence on input sizes `2^k`.

## Chapter 3 - Growth of Functions

### Section 3.1 - Asymptotic notation

- Lean source: `CLRSLean/Chapter_03/Section_03_1_Asymptotic_Notation.lean`
- Status: `proved`
- Main theorems:
  - `CLRS.Chapter03.isBigO_iff`
  - `CLRS.Chapter03.isLittleO_iff`
  - `CLRS.Chapter03.isBigOmega_iff`
  - `CLRS.Chapter03.isLittleOmega_iff`
  - `CLRS.Chapter03.isBigTheta_trans`
- Proof pattern: bridge CLRS discrete witnesses to Mathlib filters
- Current gap: none for the wrapper interface

The section gives CLRS-facing names for O, Ω, Θ, o, and ω over functions
`ℕ → ℝ`, proves the textbook-style witness forms, and collects basic algebraic
rules.

### Section 3.2 - Standard functions

- Lean source: `CLRSLean/Chapter_03/Section_03_2_Standard_Functions.lean`
- Status: `partial`
- Main proved theorems:
  - `CLRS.Chapter03.isLittleO_pow_pow`
  - `CLRS.Chapter03.isBigO_pow_pow`
  - `CLRS.Chapter03.isLittleO_pow_const_exp`
  - `CLRS.Chapter03.isLittleO_log_rpow`
  - `CLRS.Chapter03.isLittleO_log_pow_rpow`
  - `CLRS.Chapter03.isBigO_log_pow_rpow`
  - `CLRS.Chapter03.isLittleO_exp_exp_of_lt`
  - `CLRS.Chapter03.isEquivalent_harmonic_log`
  - `CLRS.Chapter03.isBigTheta_harmonic_log`
  - `CLRS.Chapter03.isBigTheta_nat_floor_coerce`
  - `CLRS.Chapter03.isBigTheta_nat_ceil_coerce`
  - `CLRS.Chapter03.isBigTheta_nat_floor_half_coerce`
  - `CLRS.Chapter03.isBigTheta_nat_ceil_half_coerce`
  - `CLRS.Chapter03.factorial_upper_bound`
  - `CLRS.Chapter03.factorial_lower_bound_offset`
  - `CLRS.Chapter03.factorial_lower_bound_half_pow`
  - `CLRS.Chapter03.isLittleO_exp_vs_factorial`
  - `CLRS.Chapter03.isLittleO_factorial_pow_self`
- Proof pattern: reuse Mathlib asymptotic and factorial facts through the CLRS
  wrappers
- Current gap: the rest of the CLRS standard-function table remains a
  strengthening target.

This section is the safe part of the `chapter-1-exploration` branch merged into
the main site.  It compiles, but it is not yet the whole Chapter 3 growth
library.

## Chapter 4 - Divide and Conquer

Chapter 4 is not limited to the Master-method file.  The current development
now includes a maximum-subarray specification theorem, Strassen's 2 by 2 block
algebra correctness theorem, recurrence layers for the substitution and
recursion-tree proof methods, the exact-power Master theorem core, and a first
all-input asymptotic transfer bridge.  Section 4.6 now also proves the
adjacent-power bridge that generates power-sandwich witnesses from one-step
comparison-scale bounds, plus the first concrete discrete critical-power scale
wrapper.  The full floor/ceiling Master Theorem still needs analytic comparison
scales and recurrence instantiations packaged as final case statements.

### Section 4.1 - The maximum-subarray problem

- Lean source: `CLRSLean/Chapter_04/Section_04_1_Maximum_Subarray.lean`
- Status: `proved` for the current functional correctness model
- Main proved theorems:
  - `CLRS.Chapter04.mem_nonemptySubarrays_iff`
  - `CLRS.Chapter04.mem_crossingSubarrays_iff`
  - `CLRS.Chapter04.bestCandidate_correct`
  - `CLRS.Chapter04.maxCrossingSubarray_correct`
  - `CLRS.Chapter04.maxCrossingSubarray_isNonemptySubarray_append`
  - `CLRS.Chapter04.subarray_append_left_or_right_or_crossing`
  - `CLRS.Chapter04.subarray_append_optimal_of_cases`
  - `CLRS.Chapter04.maxSubarrayDivideStep_correct`
  - `CLRS.Chapter04.maxSubarrayDivideTree_correct`
  - `CLRS.Chapter04.maxSubarrayDivideFuel_correct`
  - `CLRS.Chapter04.maxSubarray_exists_of_ne_nil`
  - `CLRS.Chapter04.maxSubarray_correct`
- Proof pattern: enumerate all nonempty contiguous subarrays, prove the
  enumerator exact, prove the crossing-helper enumerator exact, prove the
  left/right/crossing split classification, then prove finite argmax optimality
  for the exhaustive selector, the executable combine step, and recursive
  split-tree/fuelled divide-and-conquer selectors
- Current gap: add runtime analysis and a lower-level RAM/pseudocode cost model

### Section 4.2 - Strassen's algorithm for matrix multiplication

- Lean source: `CLRSLean/Chapter_04/Section_04_2_Strassen_Algorithm.lean`
- Status: `proved` for 2 by 2 block algebra
- Main proved theorems:
  - `CLRS.Chapter04.Matrix2.strassen_eq_mul`
  - `CLRS.Chapter04.strassen2x2_correct`
- Proof pattern: represent a 2 by 2 block matrix as four ring elements, define
  ordinary block multiplication and Strassen's seven-product reconstruction,
  then discharge the four component equalities by noncommutative ring
  normalization
- Current gap: recursive splitting, dimension bookkeeping, and runtime analysis
  remain future refinement targets

### Section 4.3 - The substitution method

- Lean source: `CLRSLean/Chapter_04/Section_04_3_Substitution_Method.lean`
- Status: `proved` for one-step recurrence bounds
- Main proved theorems:
  - `CLRS.Chapter04.substitution_upper_bound`
  - `CLRS.Chapter04.substitution_lower_bound`
  - `CLRS.Chapter04.substitution_sandwich`
  - `CLRS.Chapter04.linear_substitution_upper_bound`
  - `CLRS.Chapter04.geometric_substitution_upper_bound`
- Proof pattern: ordinary induction over the recurrence index; the guessed
  bound is treated as an invariant preserved by one recurrence step
- Current gap: floor/ceiling and multi-branch recurrences should instantiate
  these lemmas after deriving the appropriate one-step inequality

### Section 4.4 - The recursion-tree method

- Lean source: `CLRSLean/Chapter_04/Section_04_4_Recursion_Tree_Method.lean`
- Status: `proved` for additive level-cost expansions
- Main proved theorems:
  - `CLRS.Chapter04.recursion_tree_additive_unroll`
  - `CLRS.Chapter04.recursion_tree_additive_upper_envelope`
  - `CLRS.Chapter04.recursion_tree_additive_lower_envelope`
  - `CLRS.Chapter04.recursion_tree_constant_level_cost`
- Proof pattern: finite sum induction, then envelope bounds on the level costs
- Current gap: branching recurrences such as `T(n) = aT(n/b) + f(n)` should
  first group each recursion depth into one level-cost function before using
  this additive core

### Section 4.5 - The master method

- Lean source: `CLRSLean/Chapter_04/Section_04_5_Master_Theorem.lean`
- Status: `proved` for exact-power recurrences
- Main proved theorems:
  - `CLRS.Chapter04.h_formula`
  - `CLRS.Chapter04.master_case1_geometric`
  - `CLRS.Chapter04.master_case2_constant_forcing`
  - `CLRS.Chapter04.master_case3_tail_dominated`
- Proof pattern: unroll the exact-power recurrence after dividing by `a^i`,
  then prove bounded, constant, and tail-dominated normalized-forcing criteria
- Current gap: extending exact powers `n = b^i` to all input sizes needs a
  monotone recurrence model and floor/ceiling sandwiching

### Section 4.6 - Proof of the master theorem

- Lean source: `CLRSLean/Chapter_04/Section_04_6_Master_Theorem_All_Input.lean`
- Status: `partial` with floor/ceiling exact-power extraction, all-input
  transfer, adjacent-power sandwich generation, a discrete critical-power
  scale wrapper, and packaged floor/ceiling Master case 1 wrappers proved
- Main proved theorems:
  - `CLRS.Chapter04.FloorDivideRecurrence`
  - `CLRS.Chapter04.CeilDivideRecurrence`
  - `CLRS.Chapter04.exactPowerRecurrence_of_floorDivideRecurrence`
  - `CLRS.Chapter04.exactPowerRecurrence_of_ceilDivideRecurrence`
  - `CLRS.Chapter04.powerInterval_of_pos`
  - `CLRS.Chapter04.eventuallyPowerUpperSandwich_of_powerStep`
  - `CLRS.Chapter04.eventuallyPowerLowerSandwich_of_powerStep`
  - `CLRS.Chapter04.allInput_bigO_of_power_upper_sandwich`
  - `CLRS.Chapter04.allInput_bigOmega_of_power_lower_sandwich`
  - `CLRS.Chapter04.allInput_bigTheta_of_power_sandwich`
  - `CLRS.Chapter04.allInput_bigTheta_of_powerStep`
  - `CLRS.Chapter04.criticalPowerScale`
  - `CLRS.Chapter04.criticalPowerScale_monotoneAbs`
  - `CLRS.Chapter04.criticalPowerScale_powerStepBound`
  - `CLRS.Chapter04.allInput_bigTheta_of_criticalPowerScale`
  - `CLRS.Chapter04.exactPower_allInput_masterCase1_criticalPowerScale`
  - `CLRS.Chapter04.floorDivide_allInput_masterCase1_criticalPowerScale`
  - `CLRS.Chapter04.ceilDivide_allInput_masterCase1_criticalPowerScale`
- Proof pattern: first show that floor and ceiling all-input recurrences reduce
  to `ExactPowerRecurrence` on powers of the base, using the arithmetic facts
  `(b^(i+1))/b = b^i` and `(b^(i+1)+b-1)/b = b^i`.  Then assume
  absolute-value monotonicity for the cost function and explicit upper/lower
  power-sandwich hypotheses for the comparison function; use the exact-power
  O/Ω/Θ bound at a sufficiently large power and transfer it back to an
  arbitrary large input by monotonicity.  The newer `powerStep` layer proves
  the CLRS adjacent-power argument: for any positive `n`, `Nat.log` gives
  `b^i ≤ n < b^(i+1)`; monotonicity and one-step control of `g(bn)` by `g(n)`
  then generate both power-sandwich hypotheses automatically.  The
  `criticalPowerScale` wrapper instantiates this bridge for the discrete scale
  `a^(⌊log_b n⌋)`, matching `a^i` on exact powers.  The newest packaged case 1
  wrappers combine floor/ceiling recurrence extraction, exact-power
  `master_case1_geometric`, and this all-input critical-scale bridge.
- Current gap: prove analytic comparison-scale wrappers for the usual CLRS
  scales, then package the remaining CLRS all-input
  floor/ceiling case statements.

## Chapter 5 - Probabilistic Analysis and Randomized Algorithms

### Section 5.1 - The hiring problem

- Lean source: `CLRSLean/Chapter_05/Section_05_1_Hiring_Problem.lean`
- Status: `proved` for the finite rank-symmetry model
- Main proved theorems:
  - `CLRS.Chapter05.uniformAverage_indicator_singleton`
  - `CLRS.Chapter05.hireProbability_eq`
  - `CLRS.Chapter05.expectedHiresByIndicators_eq_harmonic`
  - `CLRS.Chapter05.expectedHires_eq_harmonic`
  - `CLRS.Chapter05.harmonic_isBigTheta_log`
  - `CLRS.Chapter05.expectedHires_isBigTheta_log`
- Proof pattern: compute singleton probability in a finite uniform rank space,
  sum indicator expectations, prove the equivalent recurrence by induction, and
  transfer the Chapter 3.2 harmonic-number Θ theorem to expected hires
- Current gap: none for the current finite rank-symmetry model; a lower-level
  random-permutation and pseudocode execution model remains a future refinement

## Chapter 6 - Heapsort

### Section 6.1 - Heaps

- Lean source: `CLRSLean/Chapter_06/Section_06_1_Heaps.lean`
- Status: `proved` for the indexed heap predicate and root maximum
- Main proved theorems:
  - `CLRS.Chapter06.parent_lt_self`
  - `CLRS.Chapter06.eq_left_or_right_parent`
  - `CLRS.Chapter06.ArrayMaxHeap.getElem_le_root`
  - `CLRS.Chapter06.ArrayMaxHeapFrom.to_global`
  - `CLRS.Chapter06.ArrayMaxHeapExceptFrom.to_global`
  - `CLRS.Chapter06.orderedDesc_arrayMaxHeap`
- Proof pattern: define zero-based parent/left/right arithmetic, state the
  indexed and localized max-heap predicates, prove every node reaches the root
  through smaller parents, and transfer the compact descending-list heap model
  to the indexed predicate.
- Current gap: none for the current heap predicate and root-maximum theorem;
  Sections 6.2--6.4 consume this layer for heapify, build-heap, and heapsort.

### Section 6.2 - Maintaining the heap property

- Lean source: `CLRSLean/Chapter_06/Section_06_2_Maintaining_Heap_Property.lean`
- Status: `proved` for fuelled `MAX-HEAPIFY` repair
- Main proved theorems:
  - `CLRS.Chapter06.swapAt_perm`
  - `CLRS.Chapter06.valAt_swapAt_left`
  - `CLRS.Chapter06.valAt_swapAt_right`
  - `CLRS.Chapter06.maxHeapifyFuel_length`
  - `CLRS.Chapter06.maxHeapifyFuel_perm`
  - `CLRS.Chapter06.maxHeapifyFuel_valAt_of_heapSize_le`
  - `CLRS.Chapter06.valAt_i_le_maxChildIndex`
  - `CLRS.Chapter06.valAt_left_le_maxChildIndex`
  - `CLRS.Chapter06.valAt_right_le_maxChildIndex`
  - `CLRS.Chapter06.arrayMaxHeap_of_except_of_maxChildIndex_self`
  - `CLRS.Chapter06.arrayMaxHeapFrom_of_exceptFrom_of_maxChildIndex_self`
  - `CLRS.Chapter06.maxChildIndex_eq_left_or_right_of_ne`
  - `CLRS.Chapter06.heapSize_sub_maxChildIndex_lt_of_ne`
  - `CLRS.Chapter06.arrayMaxHeapExceptFrom_after_swap_at_root`
  - `CLRS.Chapter06.arrayMaxHeapFrom_of_maxHeapifyFuel_succ`
  - `CLRS.Chapter06.arrayMaxHeapExceptFrom_after_swap_path`
  - `CLRS.Chapter06.badChildrenLeParent_after_swap`
  - `CLRS.Chapter06.arrayMaxHeapFrom_of_maxHeapifyFuel`
  - `CLRS.Chapter06.maxHeapifyFuel_child_repair_after_swap`
  - `CLRS.Chapter06.maxHeapifyFuel_swap_branch_repair`
  - `CLRS.Chapter06.maxHeapifyFuel_repair_subtree`
  - `CLRS.Chapter06.maxHeapifyFuel_root_isMaxHeap`
- Proof pattern: model array reads with a total fallback, prove swaps preserve
  length and permutation, prove the CLRS `largest` choice dominates the root
  and in-heap children, prove the no-swap branch, prove a localized
  single-swap certificate, add the path-bound invariant that protects incoming
  edges, expose the child-recursive swap branch as a named theorem, and compose
  these facts into a fuelled recursive repair theorem.
- Current gap: none for the recursive repair theorem; Section 6.4 consumes it in
  the in-place heapsort proof.

### Section 6.3 - Building a heap

- Lean source: `CLRSLean/Chapter_06/Section_06_3_Building_A_Heap.lean`
- Status: `proved`
- Main proved theorems:
  - `CLRS.Chapter06.ArrayMaxHeapFrom.of_half`
  - `CLRS.Chapter06.ArrayMaxHeapFrom.except_pred`
  - `CLRS.Chapter06.buildMaxHeapLoop_length`
  - `CLRS.Chapter06.buildMaxHeapLoop_perm`
  - `CLRS.Chapter06.buildMaxHeapLoop_isMaxHeap`
  - `CLRS.Chapter06.arrayBuildMaxHeap_isMaxHeap`
  - `CLRS.Chapter06.arrayBuildMaxHeap_perm`
  - `CLRS.Chapter06.arrayBuildMaxHeap_correct`
- Proof pattern: observe that every parent index from `heapSize / 2` onward is
  a leaf, then scan indices downward.  Each step weakens the already-built
  suffix to an except-heap at the current index and invokes the recursive
  `MAX-HEAPIFY` repair theorem from Section 6.2.
- Current gap: none for the bottom-up builder theorem; Section 6.4 consumes it in
  the in-place heapsort proof.

### Section 6.4 - The heapsort algorithm

- Lean source: `CLRSLean/Chapter_06/Section_06_4_Heapsort.lean`
- Status: `proved` for the in-place CLRS loop refinement
- Main proved theorems:
  - `CLRS.Chapter06.ArrayMaxHeapExcept.of_swap_root_last`
  - `CLRS.Chapter06.SortedSuffix.of_swap_root_last`
  - `CLRS.Chapter06.PrefixLeBound.of_swap_root_last`
  - `CLRS.Chapter06.PrefixLeBound.of_maxHeapifyFuel`
  - `CLRS.Chapter06.SortedSuffix.maxHeapifyFuel`
  - `CLRS.Chapter06.orderedAsc_of_sortedSuffix_zero`
  - `CLRS.Chapter06.HeapSortLoopInvariant.initial`
  - `CLRS.Chapter06.arrayHeapSortStep_suffix_head_eq_root`
  - `CLRS.Chapter06.arrayHeapSortStep_suffix_head_bounds_prefix`
  - `CLRS.Chapter06.HeapSortLoopInvariant.step`
  - `CLRS.Chapter06.arrayHeapSortStep_state_correct`
  - `CLRS.Chapter06.HeapSortLoopInvariant.orderedAsc_of_heapSize_le_one`
  - `CLRS.Chapter06.HeapSortLoopInvariant.orderedAsc_of_zero`
  - `CLRS.Chapter06.arrayHeapSortStep_length`
  - `CLRS.Chapter06.arrayHeapSortStep_perm`
  - `CLRS.Chapter06.arrayHeapSortInPlaceLoop_length`
  - `CLRS.Chapter06.arrayHeapSortInPlaceLoop_perm`
  - `CLRS.Chapter06.arrayHeapSortInPlaceLoop_exact_shrink_invariant`
  - `CLRS.Chapter06.arrayHeapSortInPlaceLoop_exact_terminal_invariant`
  - `CLRS.Chapter06.arrayHeapSortInPlaceLoop_terminal_invariant`
  - `CLRS.Chapter06.arrayHeapSortInPlaceLoop_orderedAsc`
  - `CLRS.Chapter06.arrayHeapSortInPlaceLoop_state_correct`
  - `CLRS.Chapter06.arrayHeapSortInPlaceLoop_exact_state_correct`
  - `CLRS.Chapter06.arrayHeapSortInPlace_terminal_invariant`
  - `CLRS.Chapter06.arrayHeapSortInPlace_length`
  - `CLRS.Chapter06.arrayHeapSortInPlace_perm`
  - `CLRS.Chapter06.arrayHeapSortInPlace_orderedAsc`
  - `CLRS.Chapter06.arrayHeapSortInPlace_state_correct`
  - `CLRS.Chapter06.arrayHeapSortInPlace_exact_state_correct`
  - `CLRS.Chapter06.arrayHeapSortInPlace_correct`
  - `CLRS.Chapter06.arrayHeapSort_eq_arrayHeapSortInPlace`
  - `CLRS.Chapter06.arrayHeapSort_terminal_invariant`
  - `CLRS.Chapter06.arrayHeapSort_state_correct`
  - `CLRS.Chapter06.arrayHeapSort_exact_state_correct`
  - `CLRS.Chapter06.arrayHeapSort_orderedAsc`
  - `CLRS.Chapter06.arrayHeapSort_perm`
  - `CLRS.Chapter06.arrayHeapSort_correct`
- Proof pattern: the in-place loop repeatedly swaps the root with the last
  heap-prefix cell, shrinks the prefix, and heapifies the root.  The
  sorted-suffix invariant is represented by `SortedSuffix`, `PrefixLeSuffix`,
  and `HeapSortLoopInvariant`.  The proof isolates the root/last swap
  certificate, exposes `arrayHeapSortStep_suffix_head_eq_root` for the CLRS
  fact that the old heap root becomes the new suffix head, proves that heapify
  preserves the new sorted suffix and prefix bound, composes them into
  `HeapSortLoopInvariant.step`, and then iterates that
  theorem through the fuelled loop.  The exact-shrink theorem exposes the
  CLRS-style partial-run fact that `fuel` genuine iterations leave heap size
  `heapSize - fuel`, and the top-level in-place implementation now uses exactly
  `heap.length - 1` fuel rather than an extra terminal no-op.
  The exact partial-run state package
  `arrayHeapSortInPlaceLoop_exact_state_correct` combines that invariant with
  permutation and length preservation.  The terminal loop invariant is exposed directly by
  `arrayHeapSortInPlaceLoop_terminal_invariant`,
  `arrayHeapSortInPlace_terminal_invariant`, and
  `arrayHeapSort_terminal_invariant`; the bundled state-correctness theorems
  additionally expose the terminal invariant, sortedness, permutation, and
  length preservation in one package, with exact non-existential top-level
  packages provided by `arrayHeapSortInPlace_exact_state_correct` and
  `arrayHeapSort_exact_state_correct`.  The public `arrayHeapSort` name is
  definitionally tied to this in-place loop.
- Current gap: none for the current functional-array correctness theorem; RAM
  costs and lower-level imperative array semantics remain separate refinements.

### Section 6.5 - Priority queues

- Lean source: `CLRSLean/Chapter_06/Section_06_5_Priority_Queues.lean`
- Status: `proved` for the functional heap interface plus array-level
  `HEAP-MAXIMUM`, full fuelled `HEAP-INCREASE-KEY`, `HEAP-EXTRACT-MAX`, and
  `HEAP-DELETE`
- Main proved theorems:
  - `CLRS.Chapter06.heapInsert_orderedDesc`
  - `CLRS.Chapter06.heapInsert_perm`
  - `CLRS.Chapter06.heapInsert_max`
  - `CLRS.Chapter06.heapIncreaseKey_orderedDesc`
  - `CLRS.Chapter06.heapIncreaseKey_perm`
  - `CLRS.Chapter06.heapDelete_orderedDesc`
  - `CLRS.Chapter06.heapDelete_perm`
  - `CLRS.Chapter06.arrayHeapMaximum?_max`
  - `CLRS.Chapter06.ArrayMaxHeap.set_increased_except_up`
  - `CLRS.Chapter06.ArrayMaxHeapExceptUp.bubble_step`
  - `CLRS.Chapter06.ArrayMaxHeapExceptUp.bubbleUpFuel_global`
  - `CLRS.Chapter06.arrayHeapIncreaseKey?_state_correct`
  - `CLRS.Chapter06.arrayHeapIncreaseKeyNoBubble?_state_correct`
  - `CLRS.Chapter06.arrayHeapExtractMax?_state_correct`
  - `CLRS.Chapter06.arrayHeapDelete?_state_correct`
- Proof pattern: maintain or rebuild the descending-list heap invariant and
  state each operation's multiset behavior with `List.Perm`; for array
  `HEAP-MAXIMUM`, use the indexed heap predicate plus the parent-chain proof
  that every heap element is at most the root.  For `HEAP-INCREASE-KEY`, use an
  upward-exception predicate: after writing the larger key, only the incoming
  edge to that key may be bad, and one parent swap moves that exception to the
  parent while preserving the child subtrees.  A fuelled loop repeats this step
  along the strict parent chain until the key reaches the root or is bounded by
  its parent; the no-bubble state theorem is recovered as the immediate-stop
  case.  For array
  `HEAP-EXTRACT-MAX`,
  reuse the Section 6.4 root/last swap certificate and Section 6.2 heapify
  repair theorem: the theorem returns the old maximum, shrinks the heap prefix
  by one, proves the repaired prefix is again a max-heap, preserves length and
  permutation, and records that the extracted key is stored just outside the
  new heap prefix.  For array `HEAP-DELETE`, raise the target cell to the old
  root maximum and reuse the extract-max theorem; the state theorem records the
  deleted key, shrinks the heap prefix, preserves backing-list length, and
  exposes the post-replacement permutation.
- Current gap: implementation-level complexity remains future refinement work.

## Chapter 7 - Quicksort

### Section 7.1 - Description of quicksort

- Lean source: `CLRSLean/Chapter_07/Section_07_1_Description_Of_Quicksort.lean`
- Status: `proved` for the current functional-list model and scan-state
  partition loop
- Main proved theorems:
  - `CLRS.Chapter07.partitionAround_left_eq_filter`
  - `CLRS.Chapter07.partitionAround_right_eq_filter`
  - `CLRS.Chapter07.mem_partitionAround_left_iff`
  - `CLRS.Chapter07.mem_partitionAround_right_iff`
  - `CLRS.Chapter07.partitionAround_correct`
  - `CLRS.Chapter07.partitionAround_perm`
  - `CLRS.Chapter07.partitionAround_left_allLeUpper`
  - `CLRS.Chapter07.partitionAround_right_allGt`
  - `CLRS.Chapter07.partitionLoop_invariant`
  - `CLRS.Chapter07.partitionLoop_eq_partitionAround`
  - `CLRS.Chapter07.partitionLoop_correct`
  - `CLRS.Chapter07.clrsPartition_correct`
  - `CLRS.Chapter07.quickSort_perm`
  - `CLRS.Chapter07.quickSort_ordered`
  - `CLRS.Chapter07.quickSort_correct`
- Proof pattern: define a stable pivot partition, prove each side equals the
  corresponding stable filter, derive membership classification and
  permutation preservation, prove a scan-state CLRS partition-loop invariant,
  connect the loop to the stable partition specification, then prove a fuelled
  functional quicksort by induction on fuel.  The fuel parameter makes the
  decreasing subproblem obligation explicit: each partition side has length at
  most the original tail.
- Current gap: mutable-array `PARTITION` with swaps and returned pivot index,
  deterministic performance analysis, randomized quicksort, and expected
  running time remain future strengthening targets

The section proves the mathematical correctness spine for quicksort before
introducing array mutation or probability.  The theorem
`CLRS.Chapter07.partitionAround_correct` packages the stable partition
classification, `CLRS.Chapter07.partitionLoop_correct` packages the scan-state
partition-loop invariant consequences, and `CLRS.Chapter07.quickSort_correct`
packages sortedness and permutation preservation.  This gives Chapter 7 a
stable base for later CLRS refinements: the next proof layer should refine the
scan-state loop to the mutable array `PARTITION` procedure.

### Sections 7.2-7.4 - Performance and randomized quicksort

- Lean source: not yet created
- Status: `future-work`
- Planned theorem targets:
  - mutable-array `PARTITION` refinement with swaps and returned pivot index;
  - deterministic quicksort recurrence bounds for selected input models;
  - randomized quicksort specification;
  - expected running time under a formal probability model.
- Difficulty note: randomized expected-time analysis is a hard proof track
  because it requires a probability model for random pivots or random
  permutations plus a recurrence or indicator-variable cost argument.

## Chapter 8 - Sorting in Linear Time

### Section 8.2 - Counting sort

- Lean source: `CLRSLean/Chapter_08/Section_08_2_Counting_Sort.lean`
- Status: `proved` for the stable bucket specification
- Main proved theorems:
  - `CLRS.Chapter08.countingSortBy_ordered`
  - `CLRS.Chapter08.countingSortBy_bucket_eq`
  - `CLRS.Chapter08.countingSortBy_mem_iff`
  - `CLRS.Chapter08.countingSortBy_perm`
  - `CLRS.Chapter08.countingSortBy_correct`
- Proof pattern: model counting sort as a stable scan over key buckets
  `0, 1, ..., maxKey`; prove each bucket contains exactly the input elements
  with that key, prove output keys are ordered by concatenating ordered buckets,
  package stability as equality of every equal-key subsequence, and derive
  permutation preservation by comparing counts through each element's own
  key-bucket.
- Current gap: array-level count table, prefix sums, and linear-time cost are
  implementation refinements over this stable bucket theorem.

This section proves the mathematical CLRS correctness spine for counting sort.
The theorem `CLRS.Chapter08.countingSortBy_bucket_eq` is deliberately stronger
than membership preservation: for every key, filtering the output by that key
returns exactly the same list as filtering the input by that key.  Thus equal
keys keep their original relative order, which is the stability property used by
radix sort.  The theorem `CLRS.Chapter08.countingSortBy_perm` upgrades this
from membership preservation to true multiset preservation.

### Section 8.3 - Radix sort

- Lean source: `CLRSLean/Chapter_08/Section_08_3_Radix_Sort.lean`
- Status: `proved` for the abstract stable digit-pass model with complete
  digit-signature stability, concrete base-`b` digit extraction, and key-order
  packaging
- Main proved theorems:
  - `CLRS.Chapter08.radixPass_orderedRel`
  - `CLRS.Chapter08.radixSortBy_ordered`
  - `CLRS.Chapter08.radixSortBy_stable`
  - `CLRS.Chapter08.radixSortBy_mem_iff`
  - `CLRS.Chapter08.radixSortBy_perm`
  - `CLRS.Chapter08.radixSortBy_correct`
  - `CLRS.Chapter08.radixSortBy_correct_stable`
  - `CLRS.Chapter08.baseDigit`
  - `CLRS.Chapter08.baseDigitsLow_allDigitsLe`
  - `CLRS.Chapter08.radixSortNatBy_correct_stable`
  - `CLRS.Chapter08.RadixDigitOrderRespectsKey`
  - `CLRS.Chapter08.radixSortNatBy_correct_keyOrdered_of_digitOrder`
  - `CLRS.Chapter08.radixDigitOrderRespectsKey_singleDigit`
  - `CLRS.Chapter08.radixSortNatBy_correct_keyOrdered_singleDigit`
- Proof pattern: represent a radix key as a low-to-high list of digit
  functions; prove that one stable counting-sort pass upgrades a lower-priority
  relation to a higher-priority lexicographic relation; separately prove that
  each complete digit-signature subsequence is preserved by composing
  counting-sort bucket stability with the induction hypothesis; then iterate
  both lemmas over the digit list.
- Current gap: the full multi-digit numeric-key ordering refinement is a future
  strengthening target.  The concrete base-`b` extractor now feeds the abstract
  theorem, ordinary key ordering is packaged behind
  `RadixDigitOrderRespectsKey`, and the one-digit case is proved.  The
  remaining arithmetic bridge is the bounded multi-digit theorem.

The theorem `CLRS.Chapter08.radixSortBy_correct_stable` packages the core
facts: the result is ordered by the induced most-significant-first
lexicographic relation, each complete digit-signature subsequence is preserved,
membership is preserved when all digit functions are bounded by the declared
maximum digit, and the output is a permutation of the input.  The wrapper
`CLRS.Chapter08.radixSortNatBy_correct_stable` instantiates that theorem with
the concrete digits `(key / b^i) % b`.  The theorem
`CLRS.Chapter08.radixSortNatBy_correct_keyOrdered_of_digitOrder` converts the
digit-lexicographic result to `OrderedBy key` once the digit-order bridge is
provided, and `CLRS.Chapter08.radixSortNatBy_correct_keyOrdered_singleDigit`
proves that bridge automatically when all keys fit in one digit.

### Section 8.4 - Bucket sort

- Lean source: `CLRSLean/Chapter_08/Section_08_4_Bucket_Sort.lean`
- Status: `proved` for deterministic bucket-index correctness
- Main proved theorems:
  - `CLRS.Chapter08.bucketSortBy_perm`
  - `CLRS.Chapter08.bucketSortBy_ordered`
  - `CLRS.Chapter08.bucketSortBy_correct`
  - `CLRS.Chapter08.sortBucketByRank_ordered`
  - `CLRS.Chapter08.sortBucketByRank_perm`
  - `CLRS.Chapter08.bucketSortByRank_correct`
- Proof pattern: scan bucket indices in increasing order, prove each per-bucket
  sorter preserves the bucket as a permutation, prove all emitted elements have
  the scanned bucket index, and use a cross-bucket monotonicity assumption to
  concatenate ordered buckets into an ordered output.
- Current gap: expected-time bucket-sort analysis is still blocked on a
  probability model for input distribution.

The executable wrapper `CLRS.Chapter08.bucketSortByRank` sorts each bucket with
Lean's verified `mergeSort`.  Its correctness theorem proves ordered output,
membership preservation, and permutation preservation under the deterministic
bucket interval hypothesis.

## Chapter 9 - Medians and Order Statistics

### Section 9.2 - Selection by rank

- Lean source: `CLRSLean/Chapter_09/Section_09_2_Select_By_Rank.lean`
- Status: `proved` for the specification selector and pivot-style quickselect
- Main proved theorems:
  - `CLRS.Chapter09.sortedCopy_perm`
  - `CLRS.Chapter09.sortedCopy_pairwise`
  - `CLRS.Chapter09.selectByRank?_mem`
  - `CLRS.Chapter09.selectByRank?_rankCorrect`
  - `CLRS.Chapter09.selectByRank?_correct`
  - `CLRS.Chapter09.quickSelect?_mem`
  - `CLRS.Chapter09.quickSelect?_rankCorrect`
  - `CLRS.Chapter09.quickSelect?_correct`
- Proof pattern: prove the specification selector by sorting followed by
  zero-based indexing; prove pivot-style quickselect by recursively preserving
  a count-based rank certificate through the `< pivot`, pivot-block, and
  `> pivot` branches.
- Current gap: randomized SELECT and CLRS median-of-medians split-size/runtime
  analysis remain strengthening targets.

The rank certificate handles duplicates directly.  If `selectByRank? k xs` or
`quickSelect? k xs` returns `x`, then `x ∈ xs`, the number of elements below
`x` is at most `k`, and the number of elements at most `x` is greater than
`k`.

### Section 9.3 - Deterministic selection

- Lean source: `CLRSLean/Chapter_09/Section_09_3_Deterministic_Select.lean`
- Status: `proved` for pivot-parametric deterministic SELECT correctness
- Main proved theorems:
  - `CLRS.Chapter09.selectWithPivot?_mem`
  - `CLRS.Chapter09.selectWithPivot?_rankCorrect`
  - `CLRS.Chapter09.selectWithPivot?_correct`
  - `CLRS.Chapter09.deterministicPivot?_mem`
  - `CLRS.Chapter09.deterministicSelect?_mem`
  - `CLRS.Chapter09.deterministicSelect?_rankCorrect`
  - `CLRS.Chapter09.deterministicSelect?_correct`
- Proof pattern: abstract over a pivot function with
  `CLRS.Chapter09.PivotMembership`, then reuse the Chapter 9.2
  `RankCertificate` lifting lemmas for the low side, pivot block, and high
  side.  The deterministic instance chooses the specification median as its
  pivot, so the rank proof is separated from the linear-time implementation
  argument.
- Current gap: the CLRS median-of-medians split-size theorem and worst-case
  linear recurrence remain future strengthening targets.

### Sections 9.3-9.4 - Randomized and linear-time selection refinements

- Lean source: not yet created for randomized SELECT or the CLRS
  median-of-medians runtime layer
- Status: `future-work` for median-of-medians split-size/runtime refinement;
  `blocked-design` for randomized expected time
- Planned theorem targets:
  - randomized SELECT returns a value satisfying
    `CLRS.Chapter09.RankCertificate`;
  - CLRS median-of-medians SELECT supplies the same certificate with the
    standard split-size inequalities;
  - expected or worst-case linear-time bounds under explicit cost models.
- Difficulty note: randomized expected-time analysis requires a probability
  model, and deterministic linear time requires the median-of-medians split-size
  inequalities.

## Chapter 10 - Elementary Data Structures

### Section 10.1 - Stacks and queues

- Lean source: `CLRSLean/Chapter_10/Section_10_1_Stacks_And_Queues.lean`
- Status: `proved` for the functional-list model
- Main theorems:
  - `CLRS.Chapter10.pop_push`
  - `CLRS.Chapter10.dequeue_enqueue_empty`
  - `CLRS.Chapter10.dequeue_enqueue_nonempty`
  - `CLRS.Chapter10.length_enqueue`
- Proof pattern: definitional equations over list-backed stacks and queues
- Current gap: array overflow/underflow, circular buffers, and RAM costs are
  deferred to a future execution model

The section proves the algebraic behavior of stacks and queues using lists:
stack top is list head, and queue front is list head with enqueue at the back.

### Section 10.2 - Linked lists

- Lean source: `CLRSLean/Chapter_10/Section_10_2_Linked_Lists.lean`
- Status: `proved` for the functional-list model
- Main theorems:
  - `CLRS.Chapter10.listSearch_sound`
  - `CLRS.Chapter10.mem_listInsert_self`
  - `CLRS.Chapter10.mem_listInsert_of_mem`
  - `CLRS.Chapter10.mem_listDeleteAll_iff`
- Proof pattern: list recursion, membership preservation, filter membership
- Current gap: predecessor/successor pointer updates and free-list allocation
  require an imperative memory model

## Chapter 11 - Hash Tables

### Section 11.1 - Direct-address tables

- Lean source: `CLRSLean/Chapter_11/Section_11_1_Direct_Address_Tables.lean`
- Status: `proved` for the functional table model
- Main theorems:
  - `CLRS.Chapter11.search_insert_same`
  - `CLRS.Chapter11.search_insert_other`
  - `CLRS.Chapter11.search_delete_same`
  - `CLRS.Chapter11.search_delete_other`
- Proof pattern: total functions, point update by `if`
- Current gap: bounded arrays and RAM costs are deferred

### Section 11.2 - Chained hash tables

- Lean source: `CLRSLean/Chapter_11/Section_11_2_Chained_Hash_Tables.lean`
- Status: `partial`
- Main proved theorems:
  - `CLRS.Chapter11.bucket_hashInsert_same`
  - `CLRS.Chapter11.bucket_hashInsert_other`
  - `CLRS.Chapter11.bucket_hashDelete_same`
  - `CLRS.Chapter11.bucket_hashDelete_other`
  - `CLRS.Chapter11.hashSearch_hashInsert_self`
  - `CLRS.Chapter11.hashSearch_hashInsert_iff`
  - `CLRS.Chapter11.hashSearch_hashDelete_self`
  - `CLRS.Chapter11.hashSearch_hashDelete_iff`
- Proof pattern: deterministic bucket update/delete for a fixed hash function
- Current gap: expected search time under simple uniform hashing requires a
  probability model over keys or hash functions

## Chapter 12 - Binary Search Trees

### Section 12.1 - Binary search trees

- Lean source: `CLRSLean/Chapter_12/Section_12_1_Binary_Search_Trees.lean`
- Status: `partial`
- Main proved theorems:
  - `CLRS.Chapter12.BSTree.search_eq_true_iff`
  - `CLRS.Chapter12.BSTree.minimum?_inTree`
  - `CLRS.Chapter12.BSTree.minimum?_le_of_ordered`
  - `CLRS.Chapter12.BSTree.maximum?_inTree`
  - `CLRS.Chapter12.BSTree.le_maximum?_of_ordered`
  - `CLRS.Chapter12.BSTree.successor?_least_greater`
  - `CLRS.Chapter12.BSTree.predecessor?_greatest_less`
  - `CLRS.Chapter12.BSTree.inTree_insert_iff`
  - `CLRS.Chapter12.BSTree.inTree_insert_self`
  - `CLRS.Chapter12.BSTree.insert_ordered`
  - `CLRS.Chapter12.BSTree.inTree_delete_iff`
  - `CLRS.Chapter12.BSTree.delete_ordered`
- Proof pattern: inductive tree membership, bound predicates, ordered invariant,
  extremal-path recursion, and successor-replacement deletion
- Current gap: parent-pointer successor/predecessor procedures, transplant,
  and pointer-level mutation remain future section targets

This section proves the core ordered-tree interface: search is equivalent to
membership, minimum/maximum return actual extremal keys, functional
successor/predecessor return least-greater/greatest-less keys, insertion adds
exactly one key, and functional deletion removes exactly the requested key while
preserving the BST ordering invariant.

## Chapter 13 - Red-Black Trees

### Section 13.1 - Red-black trees

- Lean source: `CLRSLean/Chapter_13/Section_13_1_Red_Black_Trees.lean`
- Status: `partial`
- Main proved theorems:
  - `CLRS.Chapter13.RBTree.inTree_rotateLeft_iff`
  - `CLRS.Chapter13.RBTree.inTree_rotateRight_iff`
  - `CLRS.Chapter13.RBTree.inTree_repaintRoot_iff`
  - `CLRS.Chapter13.RBTree.red_node_children_black`
  - `CLRS.Chapter13.RBTree.noRedRed_repaint_black`
  - `CLRS.Chapter13.RBTree.balancedBlackHeight_repaintRoot`
  - `CLRS.Chapter13.RBTree.balancedBlackHeight_rotateLeft_red_red`
  - `CLRS.Chapter13.RBTree.balancedBlackHeight_rotateRight_red_red`
  - `CLRS.Chapter13.RBTree.redBlackShape_repaint_rotateLeft_red_red`
  - `CLRS.Chapter13.RBTree.redBlackShape_repaint_rotateRight_red_red`
  - `CLRS.Chapter13.RBTree.redBlackShape_repaint_black`
- Proof pattern: local colored-tree invariants, rotations, root recoloring,
  and red-red rotation repair certificates
- Current gap: full `RB-INSERT`, `RB-INSERT-FIXUP`, `RB-DELETE`, and
  `RB-DELETE-FIXUP` are not mechanized

The section builds the local invariant library needed before mechanizing the
full balancing algorithms.

## Chapter 16 - Greedy Algorithms

### Section 16.1 - Activity selection

- Lean source: `CLRSLean/Chapter_16/Section_16_1_Activity_Selection.lean`
- Status: `proved` for the finite sorted-list model
- Main proved theorems:
  - `CLRS.ActivitySelection.earliest_finish_minFinish`
  - `CLRS.ActivitySelection.finishSorted_head_minFinish`
  - `CLRS.ActivitySelection.finishSorted_activitiesAfter`
  - `CLRS.ActivitySelection.finishSorted_greedyChoiceCertificate`
  - `CLRS.ActivitySelection.activitySelection`
  - `CLRS.ActivitySelection.activitySelection_cons_eq`
  - `CLRS.ActivitySelection.greedySelect_cons_eq`
  - `CLRS.ActivitySelection.greedySelect_sublist`
  - `CLRS.ActivitySelection.greedySelect_feasible`
  - `CLRS.ActivitySelection.greedy_choice_optimal_from_certificate`
  - `CLRS.ActivitySelection.greedySelect_after_maxCardinality`
  - `CLRS.ActivitySelection.greedySelect_cons_maxCardinality`
  - `CLRS.ActivitySelection.greedySelect_maxCardinality`
  - `CLRS.ActivitySelection.activitySelection_cons_maxCardinality`
  - `CLRS.ActivitySelection.activitySelection_maxCardinality`
  - `CLRS.ActivitySelection.greedySelect_optimal_length`
  - `CLRS.ActivitySelection.greedySelect_cons_recursive_correct`
  - `CLRS.ActivitySelection.activitySelection_cons_recursive_correct`
  - `CLRS.ActivitySelection.activitySelection_cons_correct`
  - `CLRS.ActivitySelection.activitySelection_correct`
- Proof pattern: finish-time order, earliest-finish greedy choice, recursive
  sublist/feasibility invariants, automatic exchange-certificate construction,
  and recursive maximum-cardinality optimality
- Current gap: none for the current finite-list theorem statement; a lower-level
  refinement to CLRS array/pseudocode execution is future work.

The section proves the core finite-list model for CLRS activity selection: on a
finish-time-sorted input, the recursive executable selector returns a feasible
sublist with maximum cardinality among all feasible sublists.  The auxiliary
certificate theorem remains available as a reusable proof interface, but the
main theorem now derives that certificate internally from sorted order.  The
theorem `CLRS.ActivitySelection.greedySelect_cons_maxCardinality` exposes the
nonempty recursive step, while
`CLRS.ActivitySelection.activitySelection_maxCardinality` and
`CLRS.ActivitySelection.activitySelection_cons_maxCardinality` expose the same
optimality certificates under the CLRS-facing algorithm name.
`CLRS.ActivitySelection.greedySelect_optimal_length` exposes the same result as
the direct textbook inequality against any feasible competing sublist.  The
bundled recursion theorem
`CLRS.ActivitySelection.activitySelection_cons_recursive_correct` combines the
exact cons-case equation, optimal recursive tail, optimal full solution,
feasibility, sublist membership, and optimal-length inequality in one
reader-facing statement.  The
reader-facing theorem `CLRS.ActivitySelection.activitySelection_correct`
bundles sublist membership, feasibility, and optimal length; the companion
`CLRS.ActivitySelection.activitySelection_cons_correct` exposes the same bundle
for the nonempty recursive step.

### Section 16.3 - Huffman codes

- Lean source: `CLRSLean/Chapter_16/Section_16_3_Huffman_Codes.lean`
- Status: `proved`
- Main proved theorems:
  - `CLRS.HuffmanV2.optimum_huffman_freqs`
  - `CLRS.HuffmanV2.huffmanOfFreqs_correct`
  - `CLRS.HuffmanV2.huffmanOfFreqs_cost_le`
- Proof pattern: greedy exchange argument, split-leaf transformation
- Current gap: none for the current theorem statement

The section proves that Huffman coding produces an optimal prefix tree for a
nonempty frequency table with distinct symbols and positive frequencies.  The
`huffmanOfFreqs_correct` wrapper packages frequency preservation and optimality,
while `huffmanOfFreqs_cost_le` gives the direct minimum-cost comparison against
any consistent tree with the same frequency table.

## Chapter 23 - Minimum Spanning Trees

### Section 23.1 - Growing a minimum spanning tree

- Lean source:
  `CLRSLean/Chapter_23/Section_23_1_Growing_Minimum_Spanning_Trees.lean`
- Status: `partial`
- Main proved theorem: `CLRS.MST.safe_edge_of_lightest_crossing`
- Supporting theorems:
  - `CLRS.MST.Graph.connected_crosses_cut`
  - `CLRS.MST.FiniteGraph.minimumSpanningTree_of_mstExtending_empty`
  - `CLRS.MST.FiniteGraph.mstExtending_empty_of_minimumSpanningTree`
  - `CLRS.MST.FiniteGraph.minimumSpanningTree_iff_mstExtending_empty`
  - `CLRS.MST.FiniteGraph.exists_crossing_tree_edge_of_cut`
  - `CLRS.MST.FiniteGraph.exists_crossing_tree_edge_preserving_prefix`
  - `CLRS.MST.mst_exchange_step`
- Proof pattern: cut property, safe edge, exchange argument
- Current gap: the path/cut crossing-edge lemma now exists; Section 23.2 turns
  an explicit path-decomposition certificate into a replacement spanning-tree
  theorem.  The remaining gap is deriving that certificate automatically from a
  canonical finite simple path or cycle representation.

This section contains the mathematical core of the CLRS MST proof.  It proves
that a light edge crossing a cut is safe once the graph-specific exchange
certificate is supplied, proves that the abstract empty-prefix optimum
specification is equivalent to the concrete finite-graph MST specification, and
it now derives the cut-crossing tree edge needed to preserve an accepted prefix
across a respecting cut.

### Section 23.2 - Kruskal and Prim

- Lean source: `CLRSLean/Chapter_23/Section_23_2_Kruskal_And_Prim.lean`
- Status: `partial`
- Main proved theorems:
  - `CLRS.MST.kruskal_optimal`
  - `CLRS.MST.FiniteGraph.kruskal_minimum_spanning_tree_of_cycle_test`
- Supporting theorems:
  - `CLRS.MST.Graph.ExchangePath`
  - `CLRS.MST.Graph.InsertedEdgeConnection`
  - `CLRS.MST.Graph.exchangePath_connected_insert`
  - `CLRS.MST.Graph.insertedEdgeConnection_of_exchangePath`
  - `CLRS.MST.Graph.exchangePath_of_insert_connected`
  - `CLRS.MST.Graph.exchangePath_iff_insertedEdgeConnection`
  - `CLRS.MST.FiniteGraph.exchangePath_of_insert_connects_erased_edge`
  - `CLRS.MST.FiniteGraph.exchangePath_iff_insertedEdgeConnection_of_spanningTree`
  - `CLRS.MST.FiniteGraph.exchangePath_of_insertedEdgeConnection`
  - `CLRS.MST.FiniteGraph.spanningTree_exchange_of_path_certificate`
  - `CLRS.MST.FiniteGraph.cut_exchange_certificate`
  - `CLRS.MST.FiniteGraph.exists_replacement_spanning_tree_of_cut`
  - `CLRS.MST.FiniteGraph.cutCertificate_of_lightest_crossing`
  - `CLRS.MST.lightest_crossing_of_sorted_prefix`
  - `CLRS.MST.cut_certificate_of_component_oracle_sorted_prefix`
  - `CLRS.MST.processed_edge_mem_or_connected_of_exact_component_kruskal`
  - `CLRS.MST.processed_prefix_excludes_of_exact_component_kruskal`
  - `CLRS.MST.lightest_crossing_of_exact_component_kruskal_prefix`
  - `CLRS.MST.cut_certificate_of_exact_component_kruskal_prefix`
  - `CLRS.MST.FiniteGraph.kruskal_subset_edges`
  - `CLRS.MST.FiniteGraph.kruskal_forest_of_exact_component`
  - `CLRS.MST.FiniteGraph.kruskal_spans_of_complete_exact_component`
  - `CLRS.MST.FiniteGraph.kruskal_spanning_tree_of_complete_exact_component`
  - `CLRS.MST.FiniteGraph.kruskal_optimal_of_complete_exact_component`
  - `CLRS.MST.FiniteGraph.kruskal_optimal_of_complete_exact_component_empty`
  - `CLRS.MST.FiniteGraph.kruskal_minimum_spanning_tree_of_complete_exact_component_empty`
  - `CLRS.MST.FiniteGraph.kruskal_optimal`
- Proof pattern: exact-component prefix accounting, sorted-order lightness,
  component-cycle-test forest preservation, complete-scan spanning, and
  safe-edge induction over an edge list
- Deferred implementation: union-find correctness
- Current gaps:
  - refine exact components to an executable union-find implementation if
    implementation correctness becomes part of scope;
  - derive the inserted-edge connection automatically from a canonical finite
    simple path/cycle representation;
  - discharge the prefix-local sorted-lightness proof in the full recursive
    optimality wrapper, rather than requiring a global lightness hypothesis;
  - add Prim's algorithm theorem interface.

The section proves the sorted-order lightness step in two layers: first with an
explicit processed-prefix exclusion invariant, then from exact components for a
real Kruskal prefix.  It also proves the certificate-based replacement exchange
step: `ExchangePath` is enough to prove that adding one edge and deleting one
tree edge preserves spanning-tree structure and the accepted prefix.  The new
bridge lemmas show that `ExchangePath` is equivalent to the named cycle-style
`InsertedEdgeConnection` once the erased tree edge disconnects its endpoints.
It also proves forest preservation for the exact-component cycle test and proves that a
complete scan of a connected finite graph returns a spanning tree.  The
finite-graph optimality wrapper can now discharge the final spanning-tree side
condition from exact components, complete edge coverage, graph connectedness,
and an initial forest.  The finite cycle-test wrapper separately exposes the
same `IsMinimumSpanningTree` conclusion whenever a cycle-test implementation's
accepted edge set is already known to be a spanning tree.

## Deferred And Blocked Items

| Item | Status | Reason |
| --- | --- | --- |
| Union-find implementation correctness | `deferred-implementation` | Not needed for the mathematical MST correctness theorem. |
| Chapter 6 priority-queue RAM costs | `deferred-implementation` | Array heap predicates, localized heap predicates, `largest` lemmas, no-swap heapify repair, recursive fuelled `MAX-HEAPIFY` repair, bottom-up build-heap, in-place heapsort loop correctness, bundled heapsort state-correctness, swap preservation, array `HEAP-MAXIMUM`, full fuelled `HEAP-INCREASE-KEY`, array `HEAP-EXTRACT-MAX`, and index-based `HEAP-DELETE` state correctness are proved; RAM costs remain refinement targets. |
| Chapter 7 mutable-array partition | `future-work` | Stable-filter partition classification, scan-state partition-loop correctness, and functional quicksort correctness are proved; the next refinement is the CLRS array `PARTITION` swap model and returned pivot index. |
| Chapter 7 randomized expected time | `blocked-design` | Needs a probability model for random pivots or random permutations and a cost recurrence/indicator argument. |
| Chapter 8 count-array implementation | `future-work` | Stable bucket correctness is proved; the next refinement is an array count table and prefix-sum implementation of `COUNTING-SORT` connected to `countingSortBy`. |
| Chapter 8 radix numeric-key refinement | `future-work` | Abstract radix-sort correctness, complete digit-signature stability, the concrete base-`b` natural-key wrapper, key-order packaging, and the one-digit arithmetic case are proved; the remaining refinement is the bounded multi-digit arithmetic bridge from digit lexicographic order to ordinary key order. |
| Chapter 8 bucket-sort expected time | `blocked-design` | Deterministic bucket-sort correctness is proved by `bucketSortByRank_correct`; expected-time analysis needs a probability model for input distribution. |
| Chapter 9 randomized SELECT expected time | `blocked-design` | Selection-by-rank correctness is proved for the specification selector, pivot-style quickselect, and pivot-parametric deterministic SELECT; randomized expected time needs a probability model and cost recurrence. |
| Chapter 9 deterministic linear-time SELECT | `future-work` | Pivot-parametric deterministic SELECT correctness is proved by `deterministicSelect?_correct`; the CLRS median-of-medians split-size and recurrence proof remains. |
| Maximum-subarray runtime analysis | `future-work` | Exhaustive-search, crossing-helper optimality, the executable combine step, and recursive split-tree/fuelled selector correctness are proved; runtime recurrence and RAM-cost refinement remain. |
| Chapter 4 concrete all-input Master-theorem instantiation | `future-work` | Floor/ceiling exact-power extraction, generic all-input transfer, adjacent-power sandwich generation, the discrete critical-power wrapper, and packaged floor/ceiling case 1 wrappers are proved; analytic comparison-scale wrappers and remaining final case statements remain. |
| Hash-table expected-time analysis | `blocked-design` | Needs a probability model for simple uniform hashing. |
| Pointer-level linked lists and free lists | `future-work` | Requires an imperative memory model. |
| BST transplant and parent-pointer navigation | `future-work` | Functional successor/predecessor queries and functional deletion are proved; pointer-transplant semantics remain. |
| Full red-black insertion/deletion | `blocked-design` | Needs a balancing representation and invariant-preservation proof across fixup cases. |
| Automatic MST exchange-path extraction | `blocked-design` | The certificate-based replacement spanning-tree theorem is proved from `ExchangePath`, and inserted-edge connectivity now bridges to that certificate; the remaining design work is extracting that inserted connection from a canonical finite simple path/cycle API. |
| Prim's algorithm | `statement` | Section file exists only through the Chapter 23.2 target; theorem interface has not been added yet. |
| CLRS exercises | `future-work` | Keep the first pass focused on main textbook claims; add exercises after section interfaces stabilize. |
| Chapter-end problems | `future-work` | Treat as a second track with explicit priority and difficulty labels. |
| Full RAM semantics | `future-work` | Requires an imperative machine/cost semantics rather than only mathematical functions and recurrences. |
| General merge-sort recurrence | `future-work` | Needs floor/ceiling arithmetic and an asymptotic theorem for all input sizes. |

## Publication Value

The proof map is intentionally honest.  Completed sections show theorem names
that compile.  Partial sections expose the exact missing mathematical or
representation layer.  This lets future contributors pick a section without
reverse-engineering the project state.

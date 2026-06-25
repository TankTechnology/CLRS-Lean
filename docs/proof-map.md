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
comparison-scale bounds, discrete case-1/2/3 Master-scale wrappers, packaged
floor/ceiling Master cases, and natural-exponent polynomial comparison wrappers
for cases 1 and 2.  A real-log bridge now connects the discrete scales to the textbook
`n^(log_b a)` for all `a ≥ 1` and `b > 1`, so case-1 and case-2 wrappers
compose with it to CLRS-facing asymptotic bounds.  The remaining gap is a
similarly textbook-facing case-3 comparison scale.

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
  scale wrapper, a discrete log-critical scale wrapper, a tail-dominated scale
  wrapper, polynomial comparison wrappers for `a = b^p`, and packaged
  floor/ceiling Master cases 1, 2, and 3 proved
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
  - `CLRS.Chapter04.criticalPowerLogScale`
  - `CLRS.Chapter04.criticalPowerLogScale_monotoneAbs`
  - `CLRS.Chapter04.criticalPowerLogScale_powerStepBound`
  - `CLRS.Chapter04.allInput_bigTheta_of_criticalPowerLogScale`
  - `CLRS.Chapter04.tailDominatedScale`
  - `CLRS.Chapter04.tailDominatedScale_exactPower`
  - `CLRS.Chapter04.allInput_bigTheta_of_tailDominatedScale`
  - `CLRS.Chapter04.polynomialScale`
  - `CLRS.Chapter04.polynomialLogScale`
  - `CLRS.Chapter04.criticalPowerScale_isBigTheta_polynomialScale`
  - `CLRS.Chapter04.criticalPowerLogScale_isBigTheta_polynomialLogScale`
  - `CLRS.Chapter04.realLogExponent`
  - `CLRS.Chapter04.realLogScale`
  - `CLRS.Chapter04.criticalPowerScale_isBigTheta_realLogScale`
  - `CLRS.Chapter04.exactPower_allInput_masterCase1_criticalPowerScale`
  - `CLRS.Chapter04.floorDivide_allInput_masterCase1_criticalPowerScale`
  - `CLRS.Chapter04.ceilDivide_allInput_masterCase1_criticalPowerScale`
  - `CLRS.Chapter04.exactPower_allInput_masterCase1_polynomialScale`
  - `CLRS.Chapter04.floorDivide_allInput_masterCase1_polynomialScale`
  - `CLRS.Chapter04.ceilDivide_allInput_masterCase1_polynomialScale`
  - `CLRS.Chapter04.exactPower_allInput_masterCase2_criticalPowerLogScale`
  - `CLRS.Chapter04.floorDivide_allInput_masterCase2_criticalPowerLogScale`
  - `CLRS.Chapter04.ceilDivide_allInput_masterCase2_criticalPowerLogScale`
  - `CLRS.Chapter04.exactPower_allInput_masterCase2_polynomialLogScale`
  - `CLRS.Chapter04.floorDivide_allInput_masterCase2_polynomialLogScale`
  - `CLRS.Chapter04.ceilDivide_allInput_masterCase2_polynomialLogScale`
  - `CLRS.Chapter04.exactPower_allInput_masterCase3_tailDominatedScale`
  - `CLRS.Chapter04.floorDivide_allInput_masterCase3_tailDominatedScale`
  - `CLRS.Chapter04.ceilDivide_allInput_masterCase3_tailDominatedScale`
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
  `criticalPowerScale`, `criticalPowerLogScale`, and `tailDominatedScale`
  wrappers instantiate this bridge for the discrete scales
  `a^(⌊log_b n⌋)`, `(⌊log_b n⌋+1)a^(⌊log_b n⌋)`, and the case-3 last-forcing
  scale, matching the three exact-power Master scales.  The polynomial
  comparison layer proves that when `a = b^p`, the first scale is
  `Θ(n^p)` and the second scale is `Θ((⌊log_b n⌋+1)n^p)`, then exports
  exact/floor/ceiling case-1 and case-2 wrappers with those textbook-facing
  conclusions.  The packaged wrappers combine floor/ceiling recurrence
  extraction, the exact-power Master case theorem, and the corresponding
  all-input bridge.
- New real-log bridge: `CLRS.Chapter04.realLogExponent`, `CLRS.Chapter04.realLogScale`, and
  `CLRS.Chapter04.criticalPowerScale_isBigTheta_realLogScale` now connect the
  discrete scale `a^(⌊log_b n⌋)` to the textbook scale `n^(log_b a)` for all
  `a ≥ 1` and `b > 1`.  Case-1 and case-2 all-input Master wrappers compose
  with this bridge via `isBigTheta_trans` to yield CLRS-facing
  `Θ(n^(log_b a))` and `Θ((⌊log_b n⌋+1)n^(log_b a))` bounds without the
  natural-exponent restriction.
- Current gap: add a similarly textbook-facing case-3 comparison scale
  (connecting the tail-dominated discrete scale to `f(n)` with the CLRS
  regularity condition).

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
- Status: `proved` for the current functional-list model, scan-state partition
  loop, returned pivot-index wrapper, and adjacent-swap trace
- Main proved theorems:
  - `CLRS.Chapter07.partitionAround_left_eq_filter`
  - `CLRS.Chapter07.partitionAround_right_eq_filter`
  - `CLRS.Chapter07.mem_partitionAround_left_iff`
  - `CLRS.Chapter07.mem_partitionAround_right_iff`
  - `CLRS.Chapter07.partitionAround_correct`
  - `CLRS.Chapter07.partitionAround_perm`
  - `CLRS.Chapter07.partitionAround_left_allLeUpper`
  - `CLRS.Chapter07.partitionAround_right_allGt`
  - `CLRS.Chapter07.AdjacentSwapTrace.to_perm`
  - `CLRS.Chapter07.AdjacentSwapTrace.of_perm`
  - `CLRS.Chapter07.partitionLoop_invariant`
  - `CLRS.Chapter07.partitionLoop_eq_partitionAround`
  - `CLRS.Chapter07.partitionLoop_correct`
  - `CLRS.Chapter07.clrsPartition_correct`
  - `CLRS.Chapter07.clrsPartitionArray_pivot`
  - `CLRS.Chapter07.clrsPartitionArray_left_bound`
  - `CLRS.Chapter07.clrsPartitionArray_right_bound`
  - `CLRS.Chapter07.clrsPartitionArray_perm`
  - `CLRS.Chapter07.clrsPartitionArray_swapTrace`
  - `CLRS.Chapter07.clrsPartitionArray_correct`
  - `CLRS.Chapter07.clrsPartitionArray_correct_with_trace`
  - `CLRS.Chapter07.quickSort_perm`
  - `CLRS.Chapter07.quickSort_ordered`
  - `CLRS.Chapter07.quickSort_correct`
- Proof pattern: define a stable pivot partition, prove each side equals the
  corresponding stable filter, derive membership classification and
  permutation preservation, prove a scan-state CLRS partition-loop invariant,
  connect the loop to the stable partition specification, package a returned
  pivot-index postcondition, derive an explicit adjacent-swap trace from the
  permutation theorem, then prove a fuelled functional quicksort by induction
  on fuel.  The fuel parameter makes the decreasing subproblem obligation
  explicit: each partition side has length at most the original tail.
- Current gap: an index-level mutable-array `PARTITION` loop, deterministic
  performance analysis, randomized quicksort, and expected running time remain
  future strengthening targets

The section proves the mathematical correctness spine for quicksort before
introducing array mutation or probability.  The theorem
`CLRS.Chapter07.partitionAround_correct` packages the stable partition
classification, `CLRS.Chapter07.partitionLoop_correct` packages the scan-state
partition-loop invariant consequences,
`CLRS.Chapter07.clrsPartitionArray_correct` packages the returned pivot-index
postcondition, `CLRS.Chapter07.clrsPartitionArray_correct_with_trace` adds an
adjacent-swap trace, and `CLRS.Chapter07.quickSort_correct` packages sortedness
and permutation preservation.  This gives Chapter 7 a stable base for later
CLRS refinements: the next proof layer should refine the scan-state loop to an
index-level mutable array `PARTITION` procedure.

### Sections 7.2-7.4 - Performance and randomized quicksort

- Lean source: not yet created
- Status: `future-work`
- Planned theorem targets:
  - mutable-array `PARTITION` refinement with an index-level loop invariant;
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
  digit-signature stability, concrete base-`b` digit extraction, bounded
  fixed-width key-order packaging, and ordinary natural-key correctness
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
  - `CLRS.Chapter08.baseDigitsLow_value_eq_mod_pow`
  - `CLRS.Chapter08.baseDigitsLow_value_eq_self_of_lt`
  - `CLRS.Chapter08.radixRel_accValue_le`
  - `CLRS.Chapter08.radixLex_value_le`
  - `CLRS.Chapter08.radixSortNatBy_correct_stable`
  - `CLRS.Chapter08.RadixDigitOrderRespectsKey`
  - `CLRS.Chapter08.radixSortNatBy_correct_keyOrdered_of_digitOrder`
  - `CLRS.Chapter08.radixDigitOrderRespectsKey_of_bounded`
  - `CLRS.Chapter08.radixDigitOrderRespectsKey_singleDigit`
  - `CLRS.Chapter08.radixSortNatBy_correct_keyOrdered_singleDigit`
  - `CLRS.Chapter08.radixSortNatBy_correct_keyOrdered_of_bounded`
- Proof pattern: represent a radix key as a low-to-high list of digit
  functions; prove that one stable counting-sort pass upgrades a lower-priority
  relation to a higher-priority lexicographic relation; separately prove that
  each complete digit-signature subsequence is preserved by composing
  counting-sort bucket stability with the induction hypothesis; then iterate
  both lemmas over the digit list.
- Current gap: none for the current bounded fixed-width radix theorem.  The
  concrete base-`b` extractor feeds the abstract theorem, ordinary key ordering
  is packaged behind `RadixDigitOrderRespectsKey`, and bounded keys are proved
  to respect the induced digit lexicographic order.

The theorem `CLRS.Chapter08.radixSortBy_correct_stable` packages the core
facts: the result is ordered by the induced most-significant-first
lexicographic relation, each complete digit-signature subsequence is preserved,
membership is preserved when all digit functions are bounded by the declared
maximum digit, and the output is a permutation of the input.  The wrapper
`CLRS.Chapter08.radixSortNatBy_correct_stable` instantiates that theorem with
the concrete digits `(key / b^i) % b`.  The theorem
`CLRS.Chapter08.radixSortNatBy_correct_keyOrdered_of_digitOrder` converts the
digit-lexicographic result to `OrderedBy key` once the digit-order bridge is
provided.  The theorem
`CLRS.Chapter08.radixSortNatBy_correct_keyOrdered_of_bounded` proves that
bridge from the fixed-width bound `key x < base ^ digitCount`; the one-digit
theorem remains as a compact special case.

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
  - `CLRS.Chapter09.geCount_eq_length_sub_ltCount`
  - `CLRS.Chapter09.quickSelect?_mem`
  - `CLRS.Chapter09.quickSelect?_rankCorrect`
  - `CLRS.Chapter09.quickSelect?_correct`
- Proof pattern: prove the specification selector by sorting followed by
  zero-based indexing; prove pivot-style quickselect by recursively preserving
  a count-based rank certificate through the `< pivot`, pivot-block, and
  `> pivot` branches.
- Current gap: randomized SELECT and runtime analysis remain strengthening
  targets; the deterministic median-of-medians split-size wrapper is now
  proved in Section 9.3.

The rank certificate handles duplicates directly.  If `selectByRank? k xs` or
`quickSelect? k xs` returns `x`, then `x ∈ xs`, the number of elements below
`x` is at most `k`, and the number of elements at most `x` is greater than
`k`.

### Section 9.3 - Deterministic selection

- Lean source: `CLRSLean/Chapter_09/Section_09_3_Deterministic_Select.lean`
- Status: `proved` for pivot-parametric deterministic SELECT correctness and
  executable median-of-medians SELECT correctness and partition-size bounds
- Main proved theorems:
  - `CLRS.Chapter09.selectWithPivot?_mem`
  - `CLRS.Chapter09.selectWithPivot?_rankCorrect`
  - `CLRS.Chapter09.selectWithPivot?_correct`
  - `CLRS.Chapter09.medianOfFive?_certificate`
  - `CLRS.Chapter09.medianOfFive?_isSome_of_length_eq_five`
  - `CLRS.Chapter09.gtCount_eq_length_sub_leCount`
  - `CLRS.Chapter09.fullGroupsOfFive_lengths`
  - `CLRS.Chapter09.fullGroupsOfFive_length_mul_five_le`
  - `CLRS.Chapter09.fullGroupsOfFive_length_near`
  - `CLRS.Chapter09.fullGroupsOfFive_flatten_sublist`
  - `CLRS.Chapter09.leCount_le_of_sublist`
  - `CLRS.Chapter09.geCount_le_of_sublist`
  - `CLRS.Chapter09.medianOfFiveGroups?_certificates`
  - `CLRS.Chapter09.medianOfFiveGroups?_mem_flatten`
  - `CLRS.Chapter09.medianOfFiveGroups?_isSome_of_all_lengths`
  - `CLRS.Chapter09.fullGroupsOfFive_medianGroupCertificates`
  - `CLRS.Chapter09.fullGroupsOfFive_medianOfFiveGroups?_isSome`
  - `CLRS.Chapter09.medianGroupCertificates_leCount_lower_bound`
  - `CLRS.Chapter09.medianGroupCertificates_geCount_lower_bound`
  - `CLRS.Chapter09.medianGroupCertificates_selectPivot_split_counts`
  - `CLRS.Chapter09.fullGroupsOfFive_selectPivot_split_counts`
  - `CLRS.Chapter09.fullGroupsOfFive_medianPivot_split_counts`
  - `CLRS.Chapter09.fullGroupsOfFive_medianPivot_fullInput_split_counts`
  - `CLRS.Chapter09.fullGroupsOfFive_medianPivot_partition_lengths`
  - `CLRS.Chapter09.fullGroupsOfFive_medianPivot_partition_size_bound`
  - `CLRS.Chapter09.deterministicPivot?_mem`
  - `CLRS.Chapter09.deterministicSelect?_mem`
  - `CLRS.Chapter09.deterministicSelect?_rankCorrect`
  - `CLRS.Chapter09.deterministicSelect?_correct`
  - `CLRS.Chapter09.medianOfMediansPivot?_mem`
  - `CLRS.Chapter09.medianOfMediansPivot?_partition_size_bound`
  - `CLRS.Chapter09.medianOfMediansSelect?_mem`
  - `CLRS.Chapter09.medianOfMediansSelect?_rankCorrect`
  - `CLRS.Chapter09.medianOfMediansSelect?_correct`
- Proof pattern: abstract over a pivot function with
  `CLRS.Chapter09.PivotMembership`, then reuse the Chapter 9.2
  `RankCertificate` lifting lemmas for the low side, pivot block, and high
  side.  The deterministic median instance chooses the specification median as
  its pivot, while the median-of-medians instance chooses the median of the
  executable group medians and proves that this pivot is an input member.  The
  five-element median certificate packages the local 3/3 count fact, the
  executable full-grouping wrapper drops at most four trailing elements, and
  the grouped split-count theorems lift those facts through a sublist bridge to
  full-input count lower bounds around a median-of-medians pivot.  The
  partition-size wrapper packages these count bounds as
  `10 * branchSize ≤ 7 * n + 12` for both strict recursive branches.
- Current gap: the worst-case linear recurrence remains a future strengthening
  target.

### Sections 9.3-9.4 - Randomized and linear-time selection refinements

- Lean source: not yet created for randomized SELECT or the CLRS
  median-of-medians runtime layer
- Status: `future-work` for median-of-medians runtime refinement;
  `blocked-design` for randomized expected time
- Planned theorem targets:
  - randomized SELECT returns a value satisfying
    `CLRS.Chapter09.RankCertificate`;
  - connect the proved median-of-medians certificate and standard split-size
    inequalities to an explicit worst-case recurrence;
  - expected or worst-case linear-time bounds under explicit cost models.
- Difficulty note: randomized expected-time analysis requires a probability
  model, and deterministic linear time now requires the recurrence layer over
  the proved median-of-medians branch-size theorem.

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

## Chapter 17 - Amortized Analysis

- Lean source:
  `CLRSLean/Chapter_17.lean`,
  `CLRSLean/Chapter_17/Section_17_1_Amortized_Framework.lean`,
  `CLRSLean/Chapter_17/Section_17_2_Stack_And_Counter.lean`, and
  `CLRSLean/Chapter_17/Section_17_4_Dynamic_Tables.lean`
- Status: `partial`
- Main proved theorems:
  - `CLRS.Chapter17.aggregate_bound_of_prefix_bound`
  - `CLRS.Chapter17.accounting_totalCost_eq_totalCharge_sub_delta`
  - `CLRS.Chapter17.accounting_totalCost_le_totalCharge`
  - `CLRS.Chapter17.potential_totalCost_eq_totalAmortized_sub_delta`
  - `CLRS.Chapter17.potential_totalCost_le_totalAmortized`
  - `CLRS.Chapter17.multiPop_totalCost_le`
  - `CLRS.Chapter17.binaryCounter_increment_potential_le_two`
  - `CLRS.Chapter17.binaryCounter_trace_potential_le`
  - `CLRS.Chapter17.binaryCounter_trace_totalFlips_le`
  - `CLRS.Chapter17.binaryCounter_totalFlips_le`
  - `CLRS.Chapter17.dynamicPotential_nonneg`
  - `CLRS.Chapter17.dynamicTableInsertCost_pos`
  - `CLRS.Chapter17.dynamicTableInsertCost_le_num_succ`
  - `CLRS.Chapter17.dynamicTableInsertCost_of_fits`
  - `CLRS.Chapter17.dynamicTableInsertCost_of_expand`
  - `CLRS.Chapter17.dynamicTableInsertSize_of_fits`
  - `CLRS.Chapter17.dynamicTableInsertSize_of_expand`
  - `CLRS.Chapter17.dynamicTableInsertSize_fits`
  - `CLRS.Chapter17.dynamicTableInsertSize_ge_size`
  - `CLRS.Chapter17.dynamicTableInsert_valid`
  - `CLRS.Chapter17.dynamicTableInsert_num`
  - `CLRS.Chapter17.dynamicTableInsert_size`
  - `CLRS.Chapter17.dynamicTableInsert_size_of_fits`
  - `CLRS.Chapter17.dynamicTableInsert_size_of_expand`
  - `CLRS.Chapter17.dynamicTableInsert_num_gt`
  - `CLRS.Chapter17.dynamicTableInsert_num_ge`
  - `CLRS.Chapter17.dynamicTableInsert_capacity_fits`
  - `CLRS.Chapter17.dynamicTableInsert_capacity_ge_size`
  - `CLRS.Chapter17.dynamicTableInsert_amortizedBound`
  - `CLRS.Chapter17.dynamicTableDeleteCost_pos_of_nonempty`
  - `CLRS.Chapter17.dynamicTableDeleteCost_pos_iff_nonempty`
  - `CLRS.Chapter17.dynamicTableDeleteCost_zero_iff_empty`
  - `CLRS.Chapter17.dynamicTableDeleteCost_le_num`
  - `CLRS.Chapter17.dynamicTableDeleteCost_empty`
  - `CLRS.Chapter17.dynamicTableDeleteCost_of_contract`
  - `CLRS.Chapter17.dynamicTableDeleteCost_of_no_contract`
  - `CLRS.Chapter17.dynamicTableDeleteSize_of_contract`
  - `CLRS.Chapter17.dynamicTableDeleteSize_of_no_contract`
  - `CLRS.Chapter17.dynamicTableDeleteSize_fits`
  - `CLRS.Chapter17.dynamicTableDeleteSize_le_size`
  - `CLRS.Chapter17.dynamicTableDelete_valid`
  - `CLRS.Chapter17.dynamicTableDelete_num`
  - `CLRS.Chapter17.dynamicTableDelete_size`
  - `CLRS.Chapter17.dynamicTableDelete_size_of_contract`
  - `CLRS.Chapter17.dynamicTableDelete_size_of_no_contract`
  - `CLRS.Chapter17.dynamicTableDelete_num_le`
  - `CLRS.Chapter17.dynamicTableDelete_num_empty`
  - `CLRS.Chapter17.dynamicTableDelete_num_lt_of_nonempty`
  - `CLRS.Chapter17.dynamicTableDelete_capacity_fits`
  - `CLRS.Chapter17.dynamicTableDelete_capacity_le_size`
  - `CLRS.Chapter17.dynamicTableDelete_amortizedBound`
  - `CLRS.Chapter17.dynamicTable_amortizedBound`
- Proof pattern: finite-prefix sums, accounting credit balance, potential
  telescoping, executable counter trace induction, size-level table potential
  nonnegativity, capacity feasibility/direction, post-state field equations,
  post-state allocation-size case specs, stored-count direction,
  post-state capacity corollaries, actual-cost and capacity-choice case specs,
  zero/positive deletion-cost wrappers,
  lower/upper bounds, and transitions
- Current gap: mutable-array copying, RAM/allocation constants, and sharper
  CLRS load-factor potential refinements remain strengthening targets.

Chapter 17 now provides the reusable amortized-analysis layer for later data
structure chapters.  The generic aggregate/accounting/potential facts are
sorry-free, and the stack, executable binary-counter trace, and dynamic-table
examples compile against stable public theorem names.  The executable counter
trace now has a multi-step potential bound and an empty-counter {lit}`2n` flip
bound.  Dynamic-table insertion and deletion/contraction now expose size-level
potential nonnegativity, capacity feasibility/direction, direct post-state
stored-count and capacity corollaries, post-state field equations, actual-cost
and capacity-choice case specs, exact zero/positive deletion-cost wrappers,
positive-cost and upper-bound transition facts, while
mutable-array copying and
allocator semantics remain future refinements.

## Chapter 18 - B-Trees

- Lean source:
  `CLRSLean/Chapter_18.lean`,
  `CLRSLean/Chapter_18/Section_18_1_B_Tree_Model.lean`, and
  `CLRSLean/Chapter_18/Section_18_2_B_Tree_Insertion.lean`, and
  `CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion.lean`
- Status: `partial`
- Main proved theorems:
  - `CLRS.Chapter18.BTree.search_correct`
  - `CLRS.Chapter18.BTree.minKeys_zero`
  - `CLRS.Chapter18.BTree.minKeys_pos`
  - `CLRS.Chapter18.BTree.one_le_minKeys`
  - `CLRS.Chapter18.BTree.minKeys_lower_bound`
  - `CLRS.Chapter18.BTree.minKeys_succ`
  - `CLRS.Chapter18.BTree.minKeys_le_succ`
  - `CLRS.Chapter18.BTree.minKeys_monotone_height`
  - `CLRS.Chapter18.BTree.splitChild_preserves_model`
  - `CLRS.Chapter18.BTree.splitChild_valid`
  - `CLRS.Chapter18.BTree.splitChild_mem_iff`
  - `CLRS.Chapter18.BTree.splitChild_mem_old`
  - `CLRS.Chapter18.BTree.splitChild_not_mem_iff`
  - `CLRS.Chapter18.BTree.splitChild_search_iff`
  - `CLRS.Chapter18.BTree.splitChild_search_old`
  - `CLRS.Chapter18.BTree.splitChild_search_false_iff`
  - `CLRS.Chapter18.BTree.splitChild_search_false_old`
  - `CLRS.Chapter18.BTree.insert_preserves_model`
  - `CLRS.Chapter18.BTree.insert_mem_iff`
  - `CLRS.Chapter18.BTree.insert_search_iff`
  - `CLRS.Chapter18.BTree.insert_mem_self`
  - `CLRS.Chapter18.BTree.insert_search_self`
  - `CLRS.Chapter18.BTree.insert_mem_old`
  - `CLRS.Chapter18.BTree.insert_search_old`
  - `CLRS.Chapter18.BTree.insert_not_mem_iff`
  - `CLRS.Chapter18.BTree.insert_search_false_iff`
  - `CLRS.Chapter18.BTree.insert_search_false_of_ne`
  - `CLRS.Chapter18.BTree.delete_preserves_model`
  - `CLRS.Chapter18.BTree.delete_mem_iff`
  - `CLRS.Chapter18.BTree.delete_search_iff`
  - `CLRS.Chapter18.BTree.delete_not_mem`
  - `CLRS.Chapter18.BTree.delete_search_deleted_false`
  - `CLRS.Chapter18.BTree.delete_mem_of_ne`
  - `CLRS.Chapter18.BTree.delete_search_of_ne`
  - `CLRS.Chapter18.BTree.delete_not_mem_iff`
  - `CLRS.Chapter18.BTree.delete_search_false_iff`
  - `CLRS.Chapter18.BTree.delete_search_false_old`
- Proof pattern: mathematical key-set model, structural validity predicate,
  minimum-key expression base/positivity arithmetic and height monotonicity,
  specification-level split/insert/delete wrappers, search correctness reuse,
  direct split validity/preservation corollaries, and direct inserted/deleted-key
  plus old-key successful and unsuccessful query preservation corollaries,
  old failed-search preservation wrappers, and exact failed membership
  specifications
- Current gap: full node occupancy/separator/same-depth invariant stack,
  node-level deletion repair, disk-page I/O, and pointer mutation remain
  strengthening targets.

Chapter 18 now has a first-pass B-tree theorem surface.  Search, split-child,
insertion, and deletion are proved against an abstract membership model, and
the update wrappers expose direct search-after-update specifications plus
direct split validity/preservation and inserted/deleted-key plus old-key query
preservation corollaries, including exact unsuccessful-search specifications
and direct old failed-search preservation wrappers.
The same specification layer now exposes exact failed membership facts for
split-child, insertion, and deletion.
The height
expression is packaged with a height-zero base case, positivity wrappers, a
minimum-key lower bound and height-step recurrence, plus adjacent and
arbitrary-height monotonicity facts.  The current split,
insert, and delete operations are specification
wrappers, so the chapter is still `partial` rather than a complete page-level
mutation proof.

## Chapter 19 - Fibonacci Heaps

- Lean source:
  `CLRSLean/Chapter_19.lean` and
  `CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model.lean`
- Status: `partial`
- Main proved theorems:
  - `CLRS.Chapter19.FibHeap.makeHeap_correct`
  - `CLRS.Chapter19.FibHeap.makeHeap_valid`
  - `CLRS.Chapter19.FibHeap.potential_makeHeap`
  - `CLRS.Chapter19.FibHeap.potential_nonneg`
  - `CLRS.Chapter19.FibHeap.minimum_correct`
  - `CLRS.Chapter19.FibHeap.minimum_none_iff`
  - `CLRS.Chapter19.FibHeap.insert_correct`
  - `CLRS.Chapter19.FibHeap.insert_valid`
  - `CLRS.Chapter19.FibHeap.insert_mem_iff`
  - `CLRS.Chapter19.FibHeap.insert_mem_self`
  - `CLRS.Chapter19.FibHeap.insert_mem_old`
  - `CLRS.Chapter19.FibHeap.insert_not_mem_iff`
  - `CLRS.Chapter19.FibHeap.insert_minimum_correct`
  - `CLRS.Chapter19.FibHeap.insert_minimum_none_iff`
  - `CLRS.Chapter19.FibHeap.union_correct`
  - `CLRS.Chapter19.FibHeap.union_valid`
  - `CLRS.Chapter19.FibHeap.union_mem_iff`
  - `CLRS.Chapter19.FibHeap.union_mem_left`
  - `CLRS.Chapter19.FibHeap.union_mem_right`
  - `CLRS.Chapter19.FibHeap.union_not_mem_iff`
  - `CLRS.Chapter19.FibHeap.union_minimum_correct`
  - `CLRS.Chapter19.FibHeap.union_minimum_none_iff`
  - `CLRS.Chapter19.FibHeap.extractMin_correct`
  - `CLRS.Chapter19.FibHeap.extractMin_valid`
  - `CLRS.Chapter19.FibHeap.extractMin_mem_iff`
  - `CLRS.Chapter19.FibHeap.extractMin_not_mem`
  - `CLRS.Chapter19.FibHeap.extractMin_mem_of_ne`
  - `CLRS.Chapter19.FibHeap.extractMin_not_mem_iff`
  - `CLRS.Chapter19.FibHeap.extractMin_none_iff`
  - `CLRS.Chapter19.FibHeap.extractMin_remaining_minimum_correct`
  - `CLRS.Chapter19.FibHeap.extractMin_remaining_minimum_none_iff`
  - `CLRS.Chapter19.FibHeap.decreaseKey_correct`
  - `CLRS.Chapter19.FibHeap.decreaseKey_valid`
  - `CLRS.Chapter19.FibHeap.decreaseKey_mem_iff`
  - `CLRS.Chapter19.FibHeap.decreaseKey_mem_new`
  - `CLRS.Chapter19.FibHeap.decreaseKey_mem_old`
  - `CLRS.Chapter19.FibHeap.decreaseKey_not_mem_iff`
  - `CLRS.Chapter19.FibHeap.decreaseKey_minimum_correct`
  - `CLRS.Chapter19.FibHeap.decreaseKey_minimum_none_iff`
  - `CLRS.Chapter19.FibHeap.delete_correct`
  - `CLRS.Chapter19.FibHeap.delete_valid`
  - `CLRS.Chapter19.FibHeap.delete_mem_iff`
  - `CLRS.Chapter19.FibHeap.delete_not_mem`
  - `CLRS.Chapter19.FibHeap.delete_mem_of_ne`
  - `CLRS.Chapter19.FibHeap.delete_not_mem_iff`
  - `CLRS.Chapter19.FibHeap.delete_minimum_correct`
  - `CLRS.Chapter19.FibHeap.delete_minimum_none_iff`
  - `CLRS.Chapter19.FibHeap.heapPotential_telescope`
  - `CLRS.Chapter19.FibHeap.fibLowerBound_step`
  - `CLRS.Chapter19.FibHeap.fibLowerBound_pos`
  - `CLRS.Chapter19.FibHeap.fibLowerBound_le_succ`
  - `CLRS.Chapter19.FibHeap.fibLowerBound_monotone`
  - `CLRS.Chapter19.FibHeap.fibLowerBound_add_two_ge_double`
  - `CLRS.Chapter19.FibHeap.fibLowerBound_even_lower_bound`
  - `CLRS.Chapter19.FibHeap.fibLowerBound_half_lower_bound`
  - `CLRS.Chapter19.FibHeap.degreeIndex_half_le_log_card`
  - `CLRS.Chapter19.FibHeap.degreeIndex_le_twice_log_card_add_one`
  - `CLRS.Chapter19.FibHeap.degree_bound_log`
- Proof pattern: finite-set key semantics, normalized root/mark counters,
  direct operation-result validity wrappers, empty-result query
  characterization, heap-potential nonnegativity and
  Chapter 17 potential-method instantiation, direct operation-key and old-key
  preservation membership corollaries, exact failed membership specifications,
  returned minimum-after-update positive and empty-result specifications,
  Fibonacci lower-bound recurrence
  plus a two-step doubling induction over even indices, a half-index bridge,
  and a conditional binary-log degree budget
- Current gap: pointer handles, heap-ordered forest/cascading-cut transition
  system, consolidation arrays, duplicate keys, and the subtree-size induction
  leading to the true Fibonacci log-degree proof remain strengthening targets.

Chapter 19 now records the operation-level Fibonacci-heap contracts against an
abstract finite key set, including empty-heap construction and empty-result
minimum/extract-min specifications plus direct
insert/union/extract-min/decrease-key/delete membership facts plus
operation-key and old-key preservation membership corollaries plus exact failed
membership specifications, direct operation-result validity wrappers, and
returned minimum-after-update positive and empty-result specifications.  The standard
potential function now has zero-initial and nonnegativity facts and is connected
to the Chapter 17 telescoping theorem, and the Fibonacci lower-bound
sequence now exposes its local recurrence, positivity, and adjacent
monotonicity, plus the derived arbitrary-index monotonicity theorem and an
even-index and half-index power-of-two lower bound.  A conditional
degree-to-binary-log bridge now packages the arithmetic step that will be used
once a pointer-forest subtree-size invariant is available.  The current
maximum-degree theorem is still deliberately conservative for this first pass;
it bounds the proxy by a key-count budget rather than proving the full
Fibonacci logarithmic theorem.

## Chapter 20 - van Emde Boas Trees

- Lean source:
  `CLRSLean/Chapter_20.lean`,
  `CLRSLean/Chapter_20/Section_20_1_VEB_Universe.lean`, and
  `CLRSLean/Chapter_20/Section_20_2_VEB_Tree.lean`
- Status: `partial`
- Main proved theorems:
  - `CLRS.Chapter20.VEB.index_high_low`
  - `CLRS.Chapter20.VEB.high_index`
  - `CLRS.Chapter20.VEB.low_index`
  - `CLRS.Chapter20.VEB.index_lt`
  - `CLRS.Chapter20.VEB.high_lt`
  - `CLRS.Chapter20.VEB.low_lt`
  - `CLRS.Chapter20.VEB.member_correct`
  - `CLRS.Chapter20.VEB.member_lt_univ`
  - `CLRS.Chapter20.VEB.minimum_correct`
  - `CLRS.Chapter20.VEB.minimum_lt_univ`
  - `CLRS.Chapter20.VEB.minimum_none_iff`
  - `CLRS.Chapter20.VEB.maximum_correct`
  - `CLRS.Chapter20.VEB.maximum_lt_univ`
  - `CLRS.Chapter20.VEB.maximum_none_iff`
  - `CLRS.Chapter20.VEB.successor_correct`
  - `CLRS.Chapter20.VEB.successor_lt_univ`
  - `CLRS.Chapter20.VEB.successor_none_iff`
  - `CLRS.Chapter20.VEB.predecessor_correct`
  - `CLRS.Chapter20.VEB.predecessor_lt_univ`
  - `CLRS.Chapter20.VEB.predecessor_none_iff`
  - `CLRS.Chapter20.VEB.insert_correct`
  - `CLRS.Chapter20.VEB.insert_member_iff`
  - `CLRS.Chapter20.VEB.insert_member_lt_univ`
  - `CLRS.Chapter20.VEB.insert_member_self`
  - `CLRS.Chapter20.VEB.insert_member_old`
  - `CLRS.Chapter20.VEB.insert_member_false_iff`
  - `CLRS.Chapter20.VEB.insert_minimum_correct`
  - `CLRS.Chapter20.VEB.insert_minimum_lt_univ`
  - `CLRS.Chapter20.VEB.insert_minimum_none_iff`
  - `CLRS.Chapter20.VEB.insert_maximum_correct`
  - `CLRS.Chapter20.VEB.insert_maximum_lt_univ`
  - `CLRS.Chapter20.VEB.insert_maximum_none_iff`
  - `CLRS.Chapter20.VEB.insert_successor_correct`
  - `CLRS.Chapter20.VEB.insert_successor_lt_univ`
  - `CLRS.Chapter20.VEB.insert_successor_none_iff`
  - `CLRS.Chapter20.VEB.insert_predecessor_correct`
  - `CLRS.Chapter20.VEB.insert_predecessor_lt_univ`
  - `CLRS.Chapter20.VEB.insert_predecessor_none_iff`
  - `CLRS.Chapter20.VEB.delete_correct`
  - `CLRS.Chapter20.VEB.delete_member_iff`
  - `CLRS.Chapter20.VEB.delete_member_lt_univ`
  - `CLRS.Chapter20.VEB.delete_member_deleted_false`
  - `CLRS.Chapter20.VEB.delete_member_of_ne`
  - `CLRS.Chapter20.VEB.delete_member_false_iff`
  - `CLRS.Chapter20.VEB.delete_minimum_correct`
  - `CLRS.Chapter20.VEB.delete_minimum_lt_univ`
  - `CLRS.Chapter20.VEB.delete_minimum_none_iff`
  - `CLRS.Chapter20.VEB.delete_maximum_correct`
  - `CLRS.Chapter20.VEB.delete_maximum_lt_univ`
  - `CLRS.Chapter20.VEB.delete_maximum_none_iff`
  - `CLRS.Chapter20.VEB.delete_successor_correct`
  - `CLRS.Chapter20.VEB.delete_successor_lt_univ`
  - `CLRS.Chapter20.VEB.delete_successor_none_iff`
  - `CLRS.Chapter20.VEB.delete_predecessor_correct`
  - `CLRS.Chapter20.VEB.delete_predecessor_lt_univ`
  - `CLRS.Chapter20.VEB.delete_predecessor_none_iff`
  - `CLRS.Chapter20.VEB.operationDepth_zero`
  - `CLRS.Chapter20.VEB.operationDepth_succ`
  - `CLRS.Chapter20.VEB.operationDepth_linear`
  - `CLRS.Chapter20.VEB.operationDepth_monotone`
  - `CLRS.Chapter20.VEB.operationDepth_strict_mono`
- Proof pattern: natural-number quotient/remainder arithmetic, bounded
  high/low recomposition, finite-set representation semantics,
  extrema/successor via `Finset.min'`/`max'`, successful-query universe-bound
  bridges, direct updated-key, old-key preservation, and failed member queries
  after updates, update-query universe-bound corollaries, and definition unfolding for
  first-pass operation-depth recurrence and monotonicity facts
- Current gap: recursive min/max-summary-cluster state, word-RAM base cases,
  and an explicit Chapter 3 asymptotic bridge for `O(log log u)` remain
  strengthening targets.

Chapter 20 now proves the high/low/index arithmetic, including both directions
of bounded high/low recomposition, and a set-specification layer for the main
vEB queries and updates.  This includes both positive and empty-result
extrema/successor/predecessor cases plus successful-query universe-bound
corollaries, membership-after-update, direct updated-key and old-key
member-preservation corollaries, exact failed member-query corollaries,
positive and empty-result extrema-after-update, and both positive and
no-neighbor specifications for neighbor queries after updates, plus direct
universe-bound corollaries for successful queries after updates.  The
current operation-depth facts expose the base case, successor step, and a
linear/monotone wrapper over the universe exponent, not yet a full asymptotic
translation for the original universe size.

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
| Chapter 7 mutable-array partition | `future-work` | Stable-filter partition classification, scan-state partition-loop correctness, a returned pivot-index wrapper, an adjacent-swap trace, and functional quicksort correctness are proved; the next refinement is the CLRS array `PARTITION` index-level loop invariant. |
| Chapter 7 randomized expected time | `blocked-design` | Needs a probability model for random pivots or random permutations and a cost recurrence/indicator argument. |
| Chapter 8 count-array implementation | `future-work` | Stable bucket correctness is proved; the next refinement is an array count table and prefix-sum implementation of `COUNTING-SORT` connected to `countingSortBy`. |
| Chapter 8 bucket-sort expected time | `blocked-design` | Deterministic bucket-sort correctness is proved by `bucketSortByRank_correct`; expected-time analysis needs a probability model for input distribution. |
| Chapter 9 randomized SELECT expected time | `blocked-design` | Selection-by-rank correctness is proved for the specification selector, pivot-style quickselect, and pivot-parametric deterministic SELECT; randomized expected time needs a probability model and cost recurrence. |
| Chapter 9 deterministic linear-time SELECT | `future-work` | Pivot-parametric deterministic SELECT correctness is proved by `deterministicSelect?_correct`; executable median-of-medians SELECT correctness is proved by `medianOfMediansSelect?_correct`; the local five-element median certificate is proved by `medianOfFive?_certificate`; executable full-input split-count bounds are proved by `fullGroupsOfFive_medianPivot_fullInput_split_counts`; the `7n/10 + O(1)` branch-size bound is proved by `medianOfMediansPivot?_partition_size_bound`. The recurrence proof remains. |
| Maximum-subarray runtime analysis | `future-work` | Exhaustive-search, crossing-helper optimality, the executable combine step, and recursive split-tree/fuelled selector correctness are proved; runtime recurrence and RAM-cost refinement remain. |
| Chapter 4 concrete all-input Master-theorem instantiation | `future-work` | Floor/ceiling exact-power extraction, generic all-input transfer, adjacent-power sandwich generation, the discrete critical-power, log-critical, and tail-dominated wrappers, packaged floor/ceiling cases 1/2/3, and natural-exponent polynomial wrappers for cases 1/2 are proved; the general `n^(log_b a)`, real-log, and case-3 comparison layers remain. |
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

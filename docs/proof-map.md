# CLRS-Lean Proof Map

This ledger records what is proved, what is partial, and what is currently
deferred.  It is intended to become the website's main navigation table.

For a coarser planning view, see
[`proof-status-board.md`](proof-status-board.md).  That board groups chapters
and sections into `main proof completed`, `structured but not complete`, and
`missing core theorem`, so work does not keep cycling back to already completed
main-proof areas without a specific refinement goal.

## Probability Toolkit

- Lean source: `CLRSLean/Probability/FiniteExpectation.lean`
- Status: `proved` — generic API (`expect`/`prob` over `Finset.range n`) and the
  `[Fintype Ω]` layer (`fintypeExpect` with add/nonneg/const/indicator/sum/equiv)
  proved; product-independence primitive `expect_mul_of_indep` proved.
- Provides: `expect`, `prob`, `indicator`, `fintypeExpect`
- Main theorems: `expect_add`, `expect_const`, `expect_nonneg`, `prob_singleton`,
  `prob_add_of_disjoint`, `fintypeExpect_add`, `fintypeExpect_nonneg`,
  `fintypeExpect_const`, `fintypeExpect_indicator_singleton`, `fintypeExpect_sum`,
  `fintypeExpect_equiv`, `expect_mul_of_indep`, `fintypeExpect_fst`
- Used by: Chapter 5 (Hiring Problem), Chapter 8.4 (Bucket Sort), Chapter 11.2 (Chained Hashing)
- Remaining: none for the finite-uniform layer; `MeasureTheory` integration is out of scope

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
  - `CLRS.Chapter03.isLittleO_pow_two_pow`
  - `CLRS.Chapter03.isLittleO_log_rpow`
  - `CLRS.Chapter03.isLittleO_log_pow_rpow`
  - `CLRS.Chapter03.isBigO_log_pow_rpow`
  - `CLRS.Chapter03.isLittleO_log_id`
  - `CLRS.Chapter03.isLittleO_loglog_log`
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
  - `CLRS.Chapter03.isLittleO_two_pow_factorial`
  - `CLRS.Chapter03.isBigOmega_factorial_exp`
  - `CLRS.Chapter03.isLittleO_pow_factorial`
  - `CLRS.Chapter03.isLittleO_factorial_pow_self`
  - `CLRS.Chapter03.isBigTheta_log_factorial`
  - `CLRS.Chapter03.isBigTheta_log_logb`
  - `CLRS.Chapter03.isBigTheta_logb_log`
  - `CLRS.Chapter03.isLittleO_logb_rpow`
  - `CLRS.Chapter03.isLittleO_log_pow_const_exp`
  - `CLRS.Chapter03.isLittleO_one_log`
- Proof pattern: reuse Mathlib asymptotic and factorial facts through the CLRS
  wrappers; `isBigTheta_log_factorial` uses Mathlib's Stirling approximation
  (`le_log_factorial_stirling`) for the lower bound and `n! ≤ n^n` for the
  upper bound; the base-2 and base-`b` comparisons and the polynomial/factorial
  chains are obtained by instantiation and transitivity through the existing
  wrappers (`isLittleO_pow_const_exp`, `isLittleO_exp_vs_factorial`,
  `isBigTheta_log_logb`, `Real.isLittleO_log_id_atTop`).
- Current gap: the CLRS standard-function comparison table is complete for the
  polynomial, logarithmic, exponential, harmonic, floor/ceiling, and factorial
  rows — including the adjacent hierarchy links
  `1 ≺ log (log n) ≺ log n ≺ n ≺ n^a ≺ 2^n ≺ n!` and the `log_b` base-change
  facts.  The iterated logarithm `lg* n` and Fibonacci-number growth remain
  future strengthening targets, not comparison-table entries.

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
  for cases 1 and 2.  A real-log bridge now connects the case-1 discrete scale
  to the textbook `n^(log_b a)` for all `a ≥ 1` and `b > 1`, and a real-log-log
  bridge connects the case-2 discrete scale to `n^(log_b a) log n`; exact/floor/
  ceiling case-1 and case-2 wrappers are exposed directly in those textbook
  scales.  The case-3 regularity bridge now connects the discrete
  tail-dominated scale to the textbook forcing function; remaining Chapter 4
  work is algorithm and cost refinement.

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
- Status: `proved` for the 2 by 2 block algebra, the recursive algorithm with
  correctness and padding, and the `Θ(n^(log₂ 7))` runtime
- Main proved theorems:
  - `CLRS.Chapter04.Matrix2.strassen_eq_mul`
  - `CLRS.Chapter04.strassen2x2_correct`
  - `CLRS.Chapter04.strassen2_eq_mul`
  - `CLRS.Chapter04.strassenRec_correct`
  - `CLRS.Chapter04.strassenRec_padOne`
  - `CLRS.Chapter04.strassen_runtime_bigTheta`
- Proof pattern: represent a 2 by 2 block matrix as four ring elements (and,
  for the recursion, as a depth-indexed `SqMat R k` quad-tree of `2 × 2`
  blocks), define ordinary block multiplication and Strassen's seven-product
  reconstruction, then discharge the four component equalities by
  noncommutative ring normalization.  The recursive `strassenRec` bottoms out at
  the scalar base case and its correctness is an induction on depth reducing to
  the 2 by 2 identity; zero-padding into the next power-of-two block preserves
  the top-left product.  The runtime is the CLRS floor recurrence
  `T(n) = 7 T(⌊n/2⌋) + n²` fed through the Chapter 4 Master-theorem case-1
  wrapper `floorDivide_allInput_masterCase1_realLogScale`, whose comparison
  scale `realLogScale 7 2 n` is the textbook `n^(log₂ 7)`
- Current gap: a lower-level RAM/pseudocode cost model and an arbitrary-`n`
  padding bijection to `Matrix (Fin n)` remain future refinement targets

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
  - `CLRS.Chapter04.realLogLogScale`
  - `CLRS.Chapter04.criticalPowerLogScale_isBigTheta_realLogLogScale`
  - `CLRS.Chapter04.exactPower_allInput_masterCase1_criticalPowerScale`
  - `CLRS.Chapter04.floorDivide_allInput_masterCase1_criticalPowerScale`
  - `CLRS.Chapter04.ceilDivide_allInput_masterCase1_criticalPowerScale`
  - `CLRS.Chapter04.exactPower_allInput_masterCase1_realLogScale`
  - `CLRS.Chapter04.floorDivide_allInput_masterCase1_realLogScale`
  - `CLRS.Chapter04.ceilDivide_allInput_masterCase1_realLogScale`
  - `CLRS.Chapter04.exactPower_allInput_masterCase1_polynomialScale`
  - `CLRS.Chapter04.floorDivide_allInput_masterCase1_polynomialScale`
  - `CLRS.Chapter04.ceilDivide_allInput_masterCase1_polynomialScale`
  - `CLRS.Chapter04.exactPower_allInput_masterCase2_criticalPowerLogScale`
  - `CLRS.Chapter04.floorDivide_allInput_masterCase2_criticalPowerLogScale`
  - `CLRS.Chapter04.ceilDivide_allInput_masterCase2_criticalPowerLogScale`
  - `CLRS.Chapter04.exactPower_allInput_masterCase2_realLogLogScale`
  - `CLRS.Chapter04.floorDivide_allInput_masterCase2_realLogLogScale`
  - `CLRS.Chapter04.ceilDivide_allInput_masterCase2_realLogLogScale`
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
- New real-log bridge: `CLRS.Chapter04.realLogExponent`,
  `CLRS.Chapter04.realLogScale`, and
  `CLRS.Chapter04.criticalPowerScale_isBigTheta_realLogScale` now connect the
  discrete scale `a^(⌊log_b n⌋)` to the textbook scale `n^(log_b a)` for all
  `a ≥ 1` and `b > 1`.  The named case-1 wrappers
  `exactPower_allInput_masterCase1_realLogScale`,
  `floorDivide_allInput_masterCase1_realLogScale`, and
  `ceilDivide_allInput_masterCase1_realLogScale` compose that bridge with the
  existing case-1 all-input theorems via `isBigTheta_trans`.
- New real-log-log bridge: `CLRS.Chapter04.realLogLogScale` and
  `CLRS.Chapter04.criticalPowerLogScale_isBigTheta_realLogLogScale` connect the
  discrete case-2 scale `(⌊log_b n⌋+1)a^(⌊log_b n⌋)` to the textbook scale
  `n^(log_b a) log n`; the named exact/floor/ceiling case-2 wrappers compose
  this bridge with the existing case-2 all-input theorems.
- New case-3 regularity bridge: `CLRS.Chapter04.Case3Regularity`,
  `CLRS.Chapter04.tailDominatedScale_eq_f_on_exact_powers`, and
  `CLRS.Chapter04.tailDominatedScale_isBigTheta_f_of_regularity` now connect
  the discrete case-3 scale `tailDominatedScale a b f` to the textbook scale
  `f(n)` under the CLRS regularity condition `a·f(⌊n/b⌋) ≤ c·f(n)` for
  `c < 1`, together with nonnegativity, monotonicity, and a one-step growth
  bound on `f`.  This completes the textbook-facing case-3 comparison scale.

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
- Current gap: an index-level mutable-array `PARTITION` loop remains the main
  implementation refinement; the probability-space interpretation of random
  pivots and sharper tail/lower-bound results are separate analysis targets

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
index-level mutable array `PARTITION` procedure while preserving the already
proved comparison-count and recurrence facts.

### Section 7.2 - Performance of quicksort

- Lean source: `CLRSLean/Chapter_07/Section_07_2_Performance_Of_Quicksort.lean`
- Status: `proved` for the current deterministic comparison-count model
- Main proved theorems:
  - `CLRS.Chapter07.partitionAround_length_add`
  - `CLRS.Chapter07.quickSortComparisonsFuel_quadratic`
  - `CLRS.Chapter07.quickSortComparisons_quadratic`
- Proof pattern: count one pivot comparison against every element in the
  current tail, prove partition length accounting, and use fuel induction to
  bound the total comparison count by `n^2`
- Current gap: connect this mathematical comparison counter to a lower-level
  mutable-array execution and cost semantics

### Section 7.3 - Randomized quicksort

- Lean source: `CLRSLean/Chapter_07/Section_07_3_Randomized_Quicksort.lean`
- Status: `proved` for the expected-comparison recurrence model
- **Probability model**: `CLRSLean/Chapter_07/Section_07_3_Randomized_Quicksort/Comparison_Probability.lean` — proves
  `P(compared i j) = 2/(j-i+1)` using the uniform random permutation
  symmetry lemma (`isFirst_prob`).
- Main proved theorems:
  - `CLRS.Chapter07.harmonic_succ`
  - `CLRS.Chapter07.sum_expectedComparisons_eq`
  - `CLRS.Chapter07.expectedComparisons_closed_form`
  - `CLRS.Chapter07.expectedComparisons_recurrence`
  - `CLRS.Chapter07.expectedComparisons_telescope`
  - `CLRS.Chapter07.expectedComparisons_clrs_harmonic_bound`
  - `CLRS.Chapter07.expectedComparisons_harmonic_bound`
  - `CLRS.Chapter07.expectedComparisons_quadratic`
  - `CLRS.Chapter07.expectedComparisons_monotone`
- Probability model theorems:
  - `CLRS.Chapter07.isFirst_prob` — symmetry lemma: P(s first in S) = 1/|S|
  - `CLRS.Chapter07.comparedInQuicksort` / `CLRS.Chapter07.compared_prob` — CLRS Thm 7.3
- Proof pattern: define the CLRS expected-comparison sequence over rationals,
  expose the named closed form, prove the recurrence identity and telescoping
  relation, then bound the closed form by harmonic-number envelopes.
  The probability model adds uniform random permutation semantics via
  transposition-symmetry bijection on `Equiv.Perm (Fin n)`.
- Current gap: asymptotic Θ(n log n) bridge from `compared_prob` to the
  existing harmonic-number bound

## Chapter 8 - Sorting in Linear Time

### Section 8.2 - Counting sort

- Lean sources:
  - `CLRSLean/Chapter_08/Section_08_2_Counting_Sort.lean`
  - `CLRSLean/Chapter_08/Section_08_2_Counting_Sort/CountTables.lean`
  - `CLRSLean/Chapter_08/Section_08_2_Counting_Sort/MutableOutputArray.lean`
- Status: `proved` for the stable bucket specification, the count-table
  refinement, and the mutable output-array refinement
- Main proved theorems:
  - `CLRS.Chapter08.countingSortBy_ordered`
  - `CLRS.Chapter08.countingSortBy_bucket_eq`
  - `CLRS.Chapter08.countingSortBy_mem_iff`
  - `CLRS.Chapter08.countingSortBy_perm`
  - `CLRS.Chapter08.countingSortBy_correct`
  - `CLRS.Chapter08.countTable_toList`
  - `CLRS.Chapter08.countTable_size`
  - `CLRS.Chapter08.cumulativeCountTable_length`
  - `CLRS.Chapter08.countingSortByTable_correct`
  - `CLRS.Chapter08.ReverseScan.countingSortByReverse_correct`
  - `CLRS.Chapter08.MutableOutput.countingSortArray_toList`
  - `CLRS.Chapter08.MutableOutput.countingSortArray_correct`
  - `CLRS.Chapter08.MutableOutput.scatter_range_size`
  - `CLRS.Chapter08.MutableOutput.countingSortArray_size`
  - `CLRS.Chapter08.MutableOutput.countingSortArray_size_of_allKeysLe`
  - `CLRS.Chapter08.MutableOutput.countingSortArrayCost_bigO`
- Proof pattern: model counting sort as a stable scan over key buckets
  `0, 1, ..., maxKey`; prove each bucket contains exactly the input elements
  with that key, prove output keys are ordered by concatenating ordered buckets,
  package stability as equality of every equal-key subsequence, and derive
  permutation preservation by comparing counts through each element's own
  key-bucket.  The count-table refinement then proves that table lengths,
  cumulative boundaries, and per-key reverse scans are extensionally equal to
  the stable bucket specification.  The mutable output-array refinement fills a
  single physical `Array` by appending each key's reverse-scan segment, proves
  the array reads back extensionally equal to `countingSortBy` (so it inherits
  ordered/stable/membership/permutation correctness), identifies the fill
  offsets with the cumulative counts, and records the linear `O(n + k)` per-pass
  work bound.
- Current gap: a full RAM/step-count operational cost semantics charging
  individual array reads and writes through an execution model remains out of
  scope; the linear work bound is a per-pass step count matching the CLRS
  accounting.

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
  - `CLRS.Chapter08.uniformAverageFin_indicator_singleton`
  - `CLRS.Chapter08.uniformAverageFin2_collision`
  - `CLRS.Chapter08.expectedBucketQuadraticCost_self_eq`
  - `CLRS.Chapter08.expectedBucketQuadraticCost_self_linear_bound`
  - `CLRS.Chapter08.expectedBucketSortCost_self_eq`
  - `CLRS.Chapter08.expectedBucketSortCost_linear_bound`
  - `CLRS.Chapter08.expectedBucketSortCost_isBigO`
  - `CLRS.Chapter08.expectedBucketQuadraticCost_eq_secondMoment`
- Proof pattern: scan bucket indices in increasing order, prove each per-bucket
  sorter preserves the bucket as a permutation, prove all emitted elements have
  the scanned bucket index, and use a cross-bucket monotonicity assumption to
  concatenate ordered buckets into an ordered output.  The finite-uniform cost
  layer proves the singleton-bucket and two-bucket collision probabilities and
  packages the CLRS second-moment expression
  `E[Σ_i n_i^2] = n + n(n-1)/m`.  The abstract expected-cost wrapper adds the
  linear scan/distribution term and proves the concrete `≤ 3n` bound and
  `isBigO` for `n` elements in `n` buckets.  The second moment is additionally
  proved as a **true expectation** over the explicit independent uniform input
  distribution `Fin n → Fin m` (`expectedBucketQuadraticCost_eq_secondMoment`),
  where the pairwise independence step reuses
  `CLRS.Probability.expect_mul_of_indep`.
- Current gap: RAM/step-count cost semantics (this layer measures expected
  comparison/occupancy cost, not machine steps).

The executable wrapper `CLRS.Chapter08.bucketSortByRank` sorts each bucket with
Lean's verified `mergeSort`.  Its correctness theorem proves ordered output,
membership preservation, and permutation preservation under the deterministic
bucket interval hypothesis.  The theorem
`CLRS.Chapter08.expectedBucketSortCost_linear_bound` captures the linear
expected-cost wrapper used by the textbook proof when the number of buckets
equals the number of input elements.

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
  - `CLRS.Chapter09.selectRecurrence_linear_step`
  - `CLRS.Chapter09.medianOfMediansPivot?_recursive_branch_size_bound`
  - `CLRS.Chapter09.medianOfMediansPivot?_low_branch_linear_work_step`
  - `CLRS.Chapter09.medianOfMediansPivot?_high_branch_linear_work_step`
  - `CLRS.Chapter09.selectRecurrence_linear_induction`
  - `CLRS.Chapter09.medianOfMedians_linear_bound`
  - `CLRS.Chapter09.clrsSelectRecurrence_linear_bound`
  - `CLRS.Chapter09.deterministicPivot?_mem`
  - `CLRS.Chapter09.deterministicSelect?_mem`
  - `CLRS.Chapter09.deterministicSelect?_rankCorrect`
  - `CLRS.Chapter09.deterministicSelect?_correct`
  - `CLRS.Chapter09.medianOfMediansPivot?_mem`
  - `CLRS.Chapter09.medianOfMediansPivot?_partition_size_bound`
  - `CLRS.Chapter09.medianOfMediansSelect?_mem`
  - `CLRS.Chapter09.medianOfMediansSelect?_rankCorrect`
  - `CLRS.Chapter09.medianOfMediansSelect?_correct`
  - `CLRS.Chapter09.selectCost_linear_step`
  - `CLRS.Chapter09.selectCostFuel_linear_bound`
  - `CLRS.Chapter09.selectCost_linear_bound`
  - `CLRS.Chapter09.medianOfMediansSelectCost_linear_bound`
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
- Current gap: the abstract recurrence, the linear bound, and a concrete
  executable cost counter (`CLRS.Chapter09.medianOfMediansSelectCost`, defined
  by the same recursion as `medianOfMediansSelect?`) with the explicit bound
  `medianOfMediansSelectCost k xs ≤ 17 * xs.length` are all proved.  The counter
  charges the linear partition scan along the recursion path and folds the
  median-of-medians pivot selection into a linear-cost oracle; the next
  strengthening target is a fully operational RAM step-count that also unfolds
  the recursive cost of computing the pivot.

### Section 9.2 - Randomized SELECT expected running time

- Lean source: `CLRSLean/Chapter_09/Section_09_3_Deterministic_Select/Randomized_Select.lean`
- Status: `proved` for the randomized-select expected-comparison model, its
  recurrence, and the CLRS Theorem 9.2 linear expected-time bound
- Main proved theorems:
  - `CLRS.Chapter09.randSelectExpectedCost_succ`
  - `CLRS.Chapter09.randSelectExpectedCost_recurrence`
  - `CLRS.Chapter09.expect_eq_fintypeExpect`
  - `CLRS.Chapter09.randSelectExpectedCost_recurrence_fintype`
  - `CLRS.Chapter09.randSelectExpectedCost_nonneg`
  - `CLRS.Chapter09.maxSideSum_add_two`
  - `CLRS.Chapter09.four_mul_maxSideSum_le`
  - `CLRS.Chapter09.sum_maxSide_real_bound`
  - `CLRS.Chapter09.randSelectExpectedCost_le`
  - `CLRS.Chapter09.randSelectExpectedCost_bigO_linear`
  - `CLRS.Chapter09.randomizedSelect_expected_bigO_linear`
  - `CLRS.Chapter09.pivotAtIndex?_mem`
  - `CLRS.Chapter09.randomizedSelectAtIndex?_rankCorrect`
  - `CLRS.Chapter09.randomizedSelectAtIndex?_mem`
- Proof pattern: the expected cost `randSelectExpectedCost c` is defined as the
  CLRS majorizing recurrence, where each step averages over a uniform,
  independent pivot rank via the shared toolkit `CLRS.Probability.expect`
  (`expect_eq_fintypeExpect` restates that average as `CLRS.Probability.fintypeExpect`
  over the per-step sample space `Fin n`); `randSelectExpectedCost_recurrence`
  *derives* the CLRS recurrence `E[T(n+1)] = c(n+1) + expect (n+1) (fun i => E[T(max i (n-i))])`
  from that definition.  The linear bound `randSelectExpectedCost_le`
  (`E[T(n)] ≤ 4·c·n`) is the substitution method: the combinatorial core
  `four_mul_maxSideSum_le` proves `4·Σ_{i<n} max i (n-1-i) ≤ 3·n²` (via the
  two-step recurrence `maxSideSum_add_two`), which is the constant `< 1` the
  substitution needs.  `randomizedSelect_expected_bigO_linear` packages this as
  `CLRS.Chapter03.isBigO (fun n => E[T n]) (fun n => (n : ℝ))` (CLRS Theorem 9.2).
  Rank correctness is inherited by instantiating the Section 9.3
  pivot-parametric `selectWithPivot?` skeleton with an index pivot oracle
  (`randomizedSelectAtIndex?_rankCorrect`).
- Current gap: the model charges the larger partition side (the standard
  majorizing recurrence upper-bounding the true expected cost); a fully joint
  distribution over all recursion levels and a concrete step-count cost model
  remain future refinements.

### Section 9.3 and median-of-medians runtime refinements

- Lean source: median-of-medians runtime refinement should build on
  `CLRSLean/Chapter_09/Section_09_3_Deterministic_Select.lean`
- Status: `future-work` for executable median-of-medians cost refinement
- Planned theorem targets:
  - connect executable `medianOfMediansSelect?` cost semantics to the proved
    abstract recurrence and `CLRS.Chapter09.clrsSelectRecurrence_linear_bound`.
- Difficulty note: deterministic linear time now mainly requires a
  cost-refinement layer over the proved median-of-medians branch-size and
  recurrence theorems.  Randomized SELECT expected time is now proved (see the
  Section 9.2 randomized SELECT page above).

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
  - `CLRS.Chapter11.uniformAverageFin_add`
  - `CLRS.Chapter11.uniformAverageFin_nonneg`
  - `CLRS.Chapter11.uniformAverageFin_indicator_singleton`
  - `CLRS.Chapter11.finiteHashLoadFactor_nonneg`
  - `CLRS.Chapter11.expectedSearchChainLength_eq_loadFactor`
  - `CLRS.Chapter11.expectedSearchChainLength_nonneg`
  - `CLRS.Chapter11.expectedUnsuccessfulSearchCost_eq_one_plus_loadFactor`
  - `CLRS.Chapter11.expectedUnsuccessfulSearchCost_ge_one`
  - `CLRS.Chapter11.totalBucketLength_finiteHashInsert`
  - `CLRS.Chapter11.expectedSearchChainLength_finiteHashInsert`
  - `CLRS.Chapter11.finiteHashLoadFactor_finiteHashInsert`
  - `CLRS.Chapter11.expectedUnsuccessfulSearchCost_finiteHashInsert`
  - `CLRS.Chapter11.expectedRandomChainLength_eq_loadFactor`
  - `CLRS.Chapter11.expectedRandomUnsuccessfulSearchCost`
- Proof pattern: deterministic bucket update/delete for a fixed hash function,
  plus a finite-uniform bucket expectation layer over `Fin m`.  The toolkit now
  includes average additivity, nonnegativity, load-factor equality, and
  single-insert changes to total chain length, load factor, expected chain
  length, and unsuccessful-search cost.  The SUHA layer additionally proves the
  expected chain length `α = n/m` and expected unsuccessful-search cost `1 + α`
  as **true expectations** over the explicit independent uniform hashing
  distribution `Fin n → Fin m` (single-coordinate marginalisation of
  `CLRS.Probability.fintypeExpect`).
- Current gap: successful-search analysis and a random hash *function* model
  (rather than random key placement); RAM/probe-count semantics.

## Chapter 12 - Binary Search Trees

### Section 12.1 - Binary search trees

- Lean source: `CLRSLean/Chapter_12/Section_12_1_Binary_Search_Trees.lean`
- Interface test: `Tests/Chapter_12_Interface.lean`
- Status: `partial`
- Main proved theorems:
  - `CLRS.Chapter12.BSTree.search_eq_true_iff`
  - `CLRS.Chapter12.BSTree.minimum?_inTree`
  - `CLRS.Chapter12.BSTree.minimum?_le_of_ordered`
  - `CLRS.Chapter12.BSTree.maximum?_inTree`
  - `CLRS.Chapter12.BSTree.le_maximum?_of_ordered`
  - `CLRS.Chapter12.BSTree.successor?_least_greater`
  - `CLRS.Chapter12.BSTree.successor?_eq_some_iff`
  - `CLRS.Chapter12.BSTree.successor?_eq_none_iff`
  - `CLRS.Chapter12.BSTree.successor?_isSome_iff_exists_greater`
  - `CLRS.Chapter12.BSTree.predecessor?_greatest_less`
  - `CLRS.Chapter12.BSTree.predecessor?_eq_some_iff`
  - `CLRS.Chapter12.BSTree.predecessor?_eq_none_iff`
  - `CLRS.Chapter12.BSTree.predecessor?_isSome_iff_exists_less`
  - `CLRS.Chapter12.BSTree.inTree_insert_iff`
  - `CLRS.Chapter12.BSTree.inTree_insert_self`
  - `CLRS.Chapter12.BSTree.search_insert_eq_true_iff`
  - `CLRS.Chapter12.BSTree.insert_ordered`
  - `CLRS.Chapter12.BSTree.inTree_delete_iff`
  - `CLRS.Chapter12.BSTree.delete_ordered`
  - `CLRS.Chapter12.BSTree.not_inTree_delete_self`
  - `CLRS.Chapter12.BSTree.delete_eq_self_of_not_inTree`
  - `CLRS.Chapter12.BSTree.search_delete_self_eq_false`
  - `CLRS.Chapter12.BSTree.search_delete_eq_true_iff`
  - `CLRS.Chapter12.BSTree.successor?_delete_eq_some_iff`
  - `CLRS.Chapter12.BSTree.successor?_delete_eq_none_iff`
  - `CLRS.Chapter12.BSTree.predecessor?_delete_eq_some_iff`
  - `CLRS.Chapter12.BSTree.predecessor?_delete_eq_none_iff`
  - `CLRS.Chapter12.BSTree.searchZipper_toTree` (parent-pointer view is faithful)
  - `CLRS.Chapter12.BSTree.searchIter_eq_search` (iterative search)
  - `CLRS.Chapter12.BSTree.transplant_preserves_ordered` (TRANSPLANT)
  - `CLRS.Chapter12.BSTree.deleteViaTransplant_eq_delete` (TREE-DELETE via transplant)
  - `CLRS.Chapter12.BSTree.successorZipper_eq_successor?` (parent-pointer successor)
  - `CLRS.Chapter12.BSTree.predecessorZipper_eq_predecessor?` (parent-pointer predecessor)
- Proof pattern: inductive tree membership, bound predicates, ordered invariant,
  extremal-path recursion, iff specifications for successor/predecessor,
  successor-replacement deletion, and a zipper (cursor + context path) layer
  encoding parent pointers, with all zipper operations proved equivalent to the
  functional operations via a `toTree` reconstruction bridge
- Current gap: pointer-level in-place mutation (imperative RAM refinement)
  remains future work; the parent-pointer navigation, `TRANSPLANT`,
  `TREE-DELETE`, and parent-pointer successor/predecessor are now proved

This section proves the core ordered-tree interface: search is equivalent to
membership, minimum/maximum return actual extremal keys, functional
successor/predecessor have complete `some`/`none` specifications, insertion
exist exactly when a greater/smaller tree key exists, insertion adds exactly
one key and exposes the corresponding Boolean search theorem, and functional
deletion removes exactly the requested key while preserving the BST ordering
invariant.  Deleting a missing key is proved to leave an ordered tree
unchanged, searching for a deleted key returns false, and the full
search-after-delete wrapper says that exactly the old keys different from the
deleted key remain searchable.  The successor/predecessor-after-delete wrappers
state the same post-deletion view for extremal queries: the returned successor
or predecessor is computed over the old tree with the deleted key excluded.
The zipper refinement additionally records the root-to-focus context, proves
that iterative search reconstructs the original tree, and connects functional
subtree replacement, deletion, and parent-ascent navigation to the established
BST interface.  It deliberately stops before mutable heap or RAM semantics.

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
  - `CLRS.Chapter13.RBTree.inTree_insertFixup_leftLeft_iff`
  - `CLRS.Chapter13.RBTree.inTree_insertFixup_leftRight_iff`
  - `CLRS.Chapter13.RBTree.inTree_insertFixup_rightLeft_iff`
  - `CLRS.Chapter13.RBTree.inTree_insertFixup_rightRight_iff`
  - `CLRS.Chapter13.RBTree.blackHeight_insertFixup_leftLeft`
  - `CLRS.Chapter13.RBTree.blackHeight_insertFixup_leftRight`
  - `CLRS.Chapter13.RBTree.blackHeight_insertFixup_rightLeft`
  - `CLRS.Chapter13.RBTree.blackHeight_insertFixup_rightRight`
  - `CLRS.Chapter13.RBTree.redBlackShape_insertFixup_leftLeft`
  - `CLRS.Chapter13.RBTree.redBlackShape_insertFixup_leftRight`
  - `CLRS.Chapter13.RBTree.redBlackShape_insertFixup_rightLeft`
  - `CLRS.Chapter13.RBTree.redBlackShape_insertFixup_rightRight`
  - `CLRS.Chapter13.RBTree.insertFixupLocal_leftLeft_certificate`
  - `CLRS.Chapter13.RBTree.insertFixupLocal_leftRight_certificate`
  - `CLRS.Chapter13.RBTree.insertFixupLocal_rightLeft_certificate`
  - `CLRS.Chapter13.RBTree.insertFixupLocal_rightRight_certificate`
  - `CLRS.Chapter13.RBTree.size_add_one_ge_two_pow_blackHeight` (Lemma A)
  - `CLRS.Chapter13.RBTree.height_le_two_mul_blackHeight_of_RedBlackShape` (Lemma B)
  - `CLRS.Chapter13.RBTree.height_log_bound` (**CLRS Lemma 13.1**)
  - `CLRS.Chapter13.RBTree.inTree_deleteFixupCase1_iff` .. `_case4_iff`
    (delete-fixup cases preserve membership)
  - `CLRS.Chapter13.RBTree.deleteFixupCase4_shape` (terminating delete-fixup case)
  - `CLRS.Chapter13.RBTree.balance` (Okasaki rebalancer for deletion)
  - `CLRS.Chapter13.RBTree.sub1` (demotes a black node, decreasing bh by 1)
  - `CLRS.Chapter13.RBTree.balLeft`, `CLRS.Chapter13.RBTree.balRight` (deletion rebalancers)
  - `CLRS.Chapter13.RBTree.app` (in-order splice for two-child delete)
  - `CLRS.Chapter13.RBTree.del`, `CLRS.Chapter13.RBTree.delete` (executable RB-DELETE)
  - `CLRS.Chapter13.RBTree.AllKeys`, `CLRS.Chapter13.RBTree.Ordered` (BST ordering invariant)
  - `CLRS.Chapter13.RBTree.allKeys_of_inTree` (AllKeys distributes over InTree)
  - `CLRS.Chapter13.RBTree.inTree_balance_iff`, `CLRS.Chapter13.RBTree.inTree_sub1_iff` (key-set preservation)
  - `CLRS.Chapter13.RBTree.inTree_balLeft_iff`, `CLRS.Chapter13.RBTree.inTree_balRight_iff` (key-set preservation)
  - `CLRS.Chapter13.RBTree.inTree_app_iff` (app preserves key set)
  - `CLRS.Chapter13.RBTree.inTree_del_iff` (del removes exactly the target key)
  - `CLRS.Chapter13.RBTree.inTree_delete_iff` (headline deletion correctness)
  - `CLRS.Chapter13.RBTree.noRedRed_balance`, `CLRS.Chapter13.RBTree.balancedBlackHeight_balance` (balance shape lemmas)
  - `CLRS.Chapter13.RBTree.noRedRed_sub1`, `CLRS.Chapter13.RBTree.blackHeight_sub1_black` (sub1 shape lemmas)
- Proof pattern: local colored-tree invariants, rotations, root recoloring,
  red-red rotation repair certificates, and four insertion-fixup local
  rotation/recoloring certificates.  Each insertion-fixup case separately
  preserves local membership and black height, and establishes the bundled
  red-black shape invariant from red-black-shaped fringe subtrees with matching
  black heights.  The `insertFixupLocal` dispatcher and certificate structure
  package those three facts behind one branch-indexed interface for a future
  executable fixup.  The logarithmic-height bound (CLRS Lemma 13.1) is proved by
  the standard two-lemma decomposition: a balanced-black-height tree has at
  least `2^bh - 1` internal nodes (Lemma A), and a no-red-red tree has height at
  most twice its black height (Lemma B), combined via `Nat.log`.
  Deletion follows the Okasaki/Kahrs functional RB-DELETE design: `balance`
  repairs red-red violations, `sub1` exposes a doubly-black deficit, and
  `balLeft`/`balRight` thread the deficit upward while the `app` combinator
  handles the two-child case.  Membership correctness (`inTree_delete_iff`) is
  proved by induction using the BST ordering invariant `Ordered`.
- Current gap: RedBlackShape preservation through `del` (requires
  `RB-INSERT`/`RB-INSERT-FIXUP`; the local `RB-DELETE-FIXUP` case rewrites and
  the terminating Case-4 certificate are proved, but the fully-composed
  executable `RB-DELETE` loop (threading the doubly-black deficit through
  Cases 1-3 into Case 4) is not yet mechanized

The section builds the local invariant library needed before mechanizing the
full balancing algorithms.

## Chapter 14 - Augmenting Data Structures

### Section 14.1 - Order-statistic trees

- Lean source: `CLRSLean/Chapter_14/Section_14_1_Order_Statistic_Trees.lean`
- Status: `partial`
- Main proved theorems:
  - `CLRS.Chapter14.OSTree.storedSize_eq_realSize_of_wellSized`
  - `CLRS.Chapter14.OSTree.recomputeSizes_wellSized`
  - `CLRS.Chapter14.OSTree.keys_recomputeSizes`
  - `CLRS.Chapter14.OSTree.keys_rotateLeft`
  - `CLRS.Chapter14.OSTree.keys_rotateRight`
  - `CLRS.Chapter14.OSTree.realSize_rotateLeft`
  - `CLRS.Chapter14.OSTree.realSize_rotateRight`
  - `CLRS.Chapter14.OSTree.storedSize_rotateLeft_of_wellSized`
  - `CLRS.Chapter14.OSTree.storedSize_rotateRight_of_wellSized`
  - `CLRS.Chapter14.OSTree.rankSelect?_rotateLeft`
  - `CLRS.Chapter14.OSTree.rankSelect?_rotateRight`
  - `CLRS.Chapter14.OSTree.rotateLeft_wellSized`
  - `CLRS.Chapter14.OSTree.rotateRight_wellSized`
  - `CLRS.Chapter14.OSTree.osSelect?_eq_rankSelect?_of_wellSized`
  - `CLRS.Chapter14.OSTree.osSelect?_rotateLeft_eq_rankSelect?_of_wellSized`
  - `CLRS.Chapter14.OSTree.osSelect?_rotateRight_eq_rankSelect?_of_wellSized`
  - `CLRS.Chapter14.OSTree.osSelect?_recomputeSizes_eq_rankSelect?`
  - `CLRS.Chapter14.OSTree.realSize_recomputeSizes`
  - `CLRS.Chapter14.OSTree.rankSelect?_recomputeSizes`
  - `CLRS.Chapter14.OSTree.rotateLeft_recomputeSizes_wellSized`
  - `CLRS.Chapter14.OSTree.rotateRight_recomputeSizes_wellSized`
  - `CLRS.Chapter14.OSTree.osSelect?_rotateLeft_recomputeSizes_eq_rankSelect?`
  - `CLRS.Chapter14.OSTree.osSelect?_rotateRight_recomputeSizes_eq_rankSelect?`
  - `CLRS.Chapter14.OSRBTree.wellSized_insert`
  - `CLRS.Chapter14.OSRBTree.storedSize_insert`
  - `CLRS.Chapter14.OSRBTree.osSelect?_insert_eq_rankSelect?`
  - `CLRS.Chapter14.OSRBTree.toRB_insert`
  - `CLRS.Chapter14.OSRBTree.redBlackShape_toRB_insert`
  - `CLRS.Chapter14.OSRBTree.mem_keys_insert`
- Proof pattern: separate cached size fields from mathematical subtree size,
  prove recomputation establishes the augmentation invariant, prove local
  rotations preserve inorder keys, mathematical size, cached root size, the
  ideal rank-selection result, and the size invariant, then prove the cached
  order-statistic selector agrees with the ideal selector under that invariant.
  The recompute-then-rotate bridge removes the need for an incoming well-sized
  hypothesis when preparing a local balancing step.  The augmented red-black
  tree `OSRBTree` then threads the same size invariant through an *executable*
  red-black insertion: its `balanceLeft`/`balanceRight`/`insertFixup`/`insert`
  rebuild every node with a size-recomputing smart constructor `mk`, so
  `wellSized_insert` follows by structural induction, and the size-erasing
  projection `toRB` makes `insert` refine the Chapter 13 `RBTree.insert`,
  transferring its shape and membership theorems.
- Current gap: thread the augmentation through executable red-black *deletion*
  (blocked on the Chapter 13 executable delete loop) and package the final
  textbook-level general augmentation interface

This first pass captures the core mathematical idea of order-statistic trees:
the augmented size field is useful exactly because the selector can branch on
cached left-subtree sizes while remaining equivalent to the ideal rank selector.
The rotation layer now shows how the same size invariant can be locally
maintained during tree restructuring, and that local rotations preserve both
the ideal rank-selection semantics and the augmented selector's connection to
that ideal semantics on well-sized trees.  The recompute-then-rotate wrappers
also show that an arbitrary functional tree can be locally prepared for a
rotation and still expose the same ideal rank-selection behavior afterward.

### Section 14.3 - Interval trees and the general augmentation theorem

- Lean source: `CLRSLean/Chapter_14/Section_14_3_Interval_Trees.lean`
- Status: `proved` for the functional well-augmented BST model, the general
  augmentation theorem (CLRS Theorem 14.1), and the value-level red-black
  rotation bridge
- Main proved declarations:
  - `CLRS.Chapter14.AugmentedTree.recompute_wellAugmented`
  - `CLRS.Chapter14.AugmentedTree.storedAug_eq_realAug_of_wellAugmented`
  - `CLRS.Chapter14.AugmentedTree.rotateLeft_wellAugmented`
  - `CLRS.Chapter14.AugmentedTree.rotateRight_wellAugmented`
  - `CLRS.Chapter14.AugmentedTree.insert_wellAugmented`
  - `CLRS.Chapter14.AugmentedTree.mem_keys_insert`
  - `CLRS.Chapter14.AugmentedTree.augmentation_theorem`
  - `CLRS.Chapter14.realAug_sizeAug_eq_length`
  - `CLRS.Chapter14.Interval.overlaps_iff`
  - `CLRS.Chapter14.IntervalTree.recompute_wellAugmented`
  - `CLRS.Chapter14.IntervalTree.rotateLeft_wellAugmented`
  - `CLRS.Chapter14.IntervalTree.rotateRight_wellAugmented`
  - `CLRS.Chapter14.IntervalTree.intervalSearch?_some_overlap`
  - `CLRS.Chapter14.IntervalTree.intervalSearch?_none_noOverlap`
  - `CLRS.Chapter14.IntervalTree.intervalSearch?_spec`
  - `CLRS.Chapter14.RBBridge.rb_augmentation_bridge`
  - `CLRS.Chapter14.RBBridge.rbRealAug_sizeAug_eq_length`
- Proof pattern: use the generic `Augmentation`/`AugmentedTree` framework and
  its `IsRotationInvariant` law to maintain local cached values through
  recomputation, rotations, and BST insertion. Instantiate it with maximum
  interval high endpoints and subtree size, then prove that the CLRS
  interval-search pruning test is both sound and complete.
- Current gap: thread a stored augmentation field through Chapter 13's
  executable red-black insertion and future deletion. The semantic value is
  already proved invariant under rotations and root recoloring.

## Chapter 15 - Dynamic Programming

### Section 15.1 - Rod cutting

- Lean source: `CLRSLean/Chapter_15/Section_15_1_Rod_Cutting.lean`
- Status: `proved` for the mathematical cut-optimality layer
- Main proved theorems:
  - `CLRS.Chapter15.firstCutValue_le_of_rodCutRecurrence`
  - `CLRS.Chapter15.rodRevenue_le_of_firstCutValue_bounds`
  - `CLRS.Chapter15.price_le_revenue_of_rodCutRecurrence`
  - `CLRS.Chapter15.bottomUpRodRevenue_zero`
  - `CLRS.Chapter15.bottomUpRodRevenue_succ`
  - `CLRS.Chapter15.bottomUpRodRevenue_rodCutRecurrence`
  - `CLRS.Chapter15.rodCutTableRecurrence_of_rodCutRecurrence`
  - `CLRS.Chapter15.bottomUpRodRevenue_rodCutTableRecurrence`
  - `CLRS.Chapter15.firstCutValue_le_of_rodCutTableRecurrence`
  - `CLRS.Chapter15.rodTableValue_le_of_firstCutValue_bounds`
  - `CLRS.Chapter15.price_le_table_of_rodCutTableRecurrence`
  - `CLRS.Chapter15.planValue_le_table_of_rodCutTableRecurrence`
  - `CLRS.Chapter15.planValue_le_bottomUpRodRevenue`
  - `CLRS.Chapter15.planValue_le_revenue_of_rodCutRecurrence`
  - `CLRS.Chapter15.planValue_le_optimalPlanValue_of_same_length`
  - `CLRS.Chapter15.planValue_le_tablePlanValue_of_same_length`
  - `CLRS.Chapter15.planValue_le_bottomUpRodPlanValue_of_same_length`
- Proof pattern: state the Bellman first-cut recurrence abstractly, expose a
  finite bottom-up table-prefix recurrence, prove every admissible first cut is
  bounded by the recurrence/table value, then induct over positive-piece
  cutting plans to prove global optimality certificates
- Current gap: mutable-array and memoized implementation correctness remains a
  future refinement target

This first dynamic-programming proof establishes the textbook optimal
substructure argument and the correctness condition for a bottom-up table
prefix independently of a particular mutable-array implementation.

### Section 15.2 - Matrix-chain multiplication

- Lean source: `CLRSLean/Chapter_15/Section_15_2_Matrix_Chain_Multiplication.lean`
- Status: `proved`
- Main proved theorems:
  - `CLRS.Chapter15.ChainPlan.start_le_end`
  - `CLRS.Chapter15.MatrixChainLowerBound`
  - `CLRS.Chapter15.MatrixChainSplitOptimal`
  - `CLRS.Chapter15.matrixChain_opt_le_planCost`
  - `CLRS.Chapter15.matrixChain_reconstructed_cost_eq`
  - `CLRS.Chapter15.matrixChain_reconstructed_optimal`
  - `CLRS.Chapter15.matrixChain_reconstructed_cost_le_planCost`
  - `CLRS.Chapter15.matrixChain_reconstructed_cost_eq_of_reconstructed`
  - `CLRS.Chapter15.matrixChainOpt`
  - `CLRS.Chapter15.matrixChainReconstruct`
  - `CLRS.Chapter15.matrixChainOpt_lowerBound`
  - `CLRS.Chapter15.matrixChainSplit_optimal`
  - `CLRS.Chapter15.matrixChainOpt_splitOptimal`
  - `CLRS.Chapter15.matrixChainReconstruct_reconstructed`
  - `CLRS.Chapter15.matrixChain_correct`
- Proof pattern: represent a parenthesization as an inductive binary split
  tree, specify a candidate dynamic-programming optimum by its split lower
  bound, then prove by induction that every concrete parenthesization has cost
  at least the candidate optimum.  A second certificate layer records a tight
  split table and proves that any plan reconstructed from that split table has
  exactly the candidate cost, is globally optimal, has cost no greater than any
  competing parenthesization of the same interval, and has the same cost as any
  other plan reconstructed from the same tight split table.
- Current gap: mutable-array/memoized implementation and a RAM cost model remain
  future refinement targets; the bottom-up cost table (`matrixChainOpt`) and
  executable split reconstruction (`matrixChainReconstruct`, `matrixChain_correct`)
  are now proved
- Current gap: the entire development is now fully computable:
  `matrixChainOpt` computes the cost table by bottom-up DP,
  `matrixChainSplit` selects the minimal split point via finite-set
  minimization, and `matrixChainReconstruct` builds an optimal parenthesization
  from the split table.

### Section 15.4 - Longest common subsequence

- Lean source: `CLRSLean/Chapter_15/Section_15_4_Longest_Common_Subsequence.lean`
- Status: `proved`
- Main proved theorems:
  - `CLRS.Chapter15.LCSCertificate.seq_common`
  - `CLRS.Chapter15.LCSCertificate.commonSubsequence_length_le`
  - `CLRS.Chapter15.LCSCertificate.length_eq_of_certificates`
  - `CLRS.Chapter15.isCommonSubsequence_comm`
  - `CLRS.Chapter15.LCSTableRecurrence.nil_left`
  - `CLRS.Chapter15.LCSTableRecurrence.nil_right`
  - `CLRS.Chapter15.LCSTableRecurrence.cons_cons`
  - `CLRS.Chapter15.LCSTableRecurrence.cons_cons_self`
  - `CLRS.Chapter15.LCSTableRecurrence.cons_cons_of_eq`
  - `CLRS.Chapter15.LCSTableRecurrence.diagonal_lt_cons_cons_of_eq`
  - `CLRS.Chapter15.LCSTableRecurrence.cons_cons_of_ne`
  - `CLRS.Chapter15.LCSTableRecurrence.drop_left_le_of_ne`
  - `CLRS.Chapter15.LCSTableRecurrence.drop_right_le_of_ne`
  - `CLRS.Chapter15.LCSTableCertificate.nil_left`
  - `CLRS.Chapter15.LCSTableCertificate.nil_right`
  - `CLRS.Chapter15.LCSTableCertificate.cons_cons`
  - `CLRS.Chapter15.LCSTableCertificate.cons_cons_self`
  - `CLRS.Chapter15.LCSTableCertificate.cons_cons_of_eq`
  - `CLRS.Chapter15.LCSTableCertificate.diagonal_lt_cons_cons_of_eq`
  - `CLRS.Chapter15.LCSTableCertificate.cons_cons_of_ne`
  - `CLRS.Chapter15.LCSTableCertificate.drop_left_le_of_ne`
  - `CLRS.Chapter15.LCSTableCertificate.drop_right_le_of_ne`
  - `CLRS.Chapter15.LCSTableCertificate.commonSubsequence_length_le`
  - `CLRS.Chapter15.lcsTable_reconstruction_optimal`
  - `CLRS.Chapter15.lcsCertificate_of_table_reconstruction_length`
  - `CLRS.Chapter15.lcsLength`
  - `CLRS.Chapter15.lcsLength_upper_bound`
  - `CLRS.Chapter15.lcsReconstruct`
  - `CLRS.Chapter15.lcs_correct`
- Proof pattern: package an LCS certificate as a common subsequence plus a
  universal length upper bound, then prove all certificates for the same inputs
  agree on the optimal length.  The table-certificate layer separately records
  the CLRS recurrence, exposes that recurrence directly through
  `LCSTableCertificate`, exposes the matching-head diagonal step and the
  nonmatching-head one-sided bounds, and proves that a reconstructed common
  subsequence whose length equals a certified table entry is optimal and yields
  a certificate with exactly the table length.
- Current gap: mutable-array/memoized implementation and a RAM cost model remain
  future refinement targets; the length-table construction (`lcsLength`) and
  executable reconstruction algorithm (`lcsReconstruct`, `lcs_correct`) are now
  proved

### Section 15.5 - Optimal binary search trees

- Lean source: `CLRSLean/Chapter_15/Section_15_5_Optimal_Binary_Search_Trees.lean`
- Status: `proved`
- Main proved theorems:
  - `CLRS.Chapter15.OBST.BSTPlan.start_le_end`
  - `CLRS.Chapter15.OBST.obst_opt_le_planCost`
  - `CLRS.Chapter15.OBST.obst_reconstructed_cost_eq`
  - `CLRS.Chapter15.OBST.obst_reconstructed_optimal`
  - `CLRS.Chapter15.OBST.bottomUpOBST_obstRecurrence`
  - `CLRS.Chapter15.OBST.obstBuildPlan`
  - `CLRS.Chapter15.OBST.obstBuildPlan_reconstructed`
  - `CLRS.Chapter15.OBST.obst_correct`
- Proof pattern: represent a BST as an inductive plan over intervals, define
  expected search cost recursively, specify a candidate dynamic-programming
  optimum by the CLRS lower-bound recurrence, then prove by induction that every
  concrete plan costs at least the recurrence value.  A tight-root certificate
  layer records a root choice that attains the recurrence equality and proves
  that any plan reconstructed from it has exactly the optimum cost.  Finally,
  give a computable bottom-up function that evaluates the recurrence by interval
  length and prove that it satisfies the recurrence.
- Current gap: mutable-array/memoized implementation and a RAM cost model remain
  future refinement targets; the cost/root-table construction (`obstBuildPlan`)
  and executable reconstruction algorithm (`obstBuildPlan_reconstructed`,
  `obst_correct`) are now proved

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
  `CLRSLean/Chapter_17/Section_17_1_Amortized_Framework/Section_17_2_Stack_And_Counter.lean`,
  `CLRSLean/Chapter_17/Section_17_4_Dynamic_Tables.lean`, and
  `CLRSLean/Chapter_17/Section_17_4_Dynamic_Tables/Section_17_4_Mutable_Array_Tables.lean`
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
  - `CLRS.Chapter17.dynamicTableInsert_potential_nonneg`
  - `CLRS.Chapter17.dynamicTableDelete_potential_nonneg`
  - `CLRS.Chapter17.dynamicTableInsertCost_pos`
  - `CLRS.Chapter17.dynamicTableInsertCost_le_num_succ`
  - `CLRS.Chapter17.dynamicTableInsertCost_of_fits`
  - `CLRS.Chapter17.dynamicTableInsertCost_of_expand`
  - `CLRS.Chapter17.dynamicTableInsertSize_of_fits`
  - `CLRS.Chapter17.dynamicTableInsertSize_of_expand`
  - `CLRS.Chapter17.dynamicTableInsertSize_fits`
  - `CLRS.Chapter17.dynamicTableInsertSize_ge_size`
  - `CLRS.Chapter17.dynamicTableInsertSize_ge_double_of_expand`
  - `CLRS.Chapter17.dynamicTableInsert_valid`
  - `CLRS.Chapter17.dynamicTableInsert_num`
  - `CLRS.Chapter17.dynamicTableInsert_size`
  - `CLRS.Chapter17.dynamicTableInsert_size_of_fits`
  - `CLRS.Chapter17.dynamicTableInsert_size_of_expand`
  - `CLRS.Chapter17.dynamicTableInsert_num_pos`
  - `CLRS.Chapter17.dynamicTableInsert_num_gt`
  - `CLRS.Chapter17.dynamicTableInsert_num_ge`
  - `CLRS.Chapter17.dynamicTableInsert_capacity_fits`
  - `CLRS.Chapter17.dynamicTableInsert_capacity_pos`
  - `CLRS.Chapter17.dynamicTableInsert_capacity_ge_size`
  - `CLRS.Chapter17.dynamicTableInsert_capacity_ge_double_of_expand`
  - `CLRS.Chapter17.dynamicTableInsert_amortizedCost_eq`
  - `CLRS.Chapter17.dynamicTableInsert_amortizedBound`
  - `CLRS.Chapter17.dynamicTableDeleteCost_pos_of_nonempty`
  - `CLRS.Chapter17.dynamicTableDeleteCost_pos_iff_nonempty`
  - `CLRS.Chapter17.dynamicTableDeleteCost_zero_iff_empty`
  - `CLRS.Chapter17.dynamicTableDeleteCost_le_num`
  - `CLRS.Chapter17.dynamicTableDeleteCost_empty`
  - `CLRS.Chapter17.dynamicTableDeleteCost_of_contract`
  - `CLRS.Chapter17.dynamicTableDeleteCost_of_no_contract`
  - `CLRS.Chapter17.dynamicTableDeleteCost_eq_num_of_contract`
  - `CLRS.Chapter17.dynamicTableDeleteCost_eq_one_of_no_contract`
  - `CLRS.Chapter17.dynamicTableDeleteSize_of_contract`
  - `CLRS.Chapter17.dynamicTableDeleteSize_of_no_contract`
  - `CLRS.Chapter17.dynamicTableDeleteSize_fits`
  - `CLRS.Chapter17.dynamicTableDeleteSize_le_size`
  - `CLRS.Chapter17.dynamicTableDeleteSize_le_half_of_contract`
  - `CLRS.Chapter17.dynamicTableDelete_valid`
  - `CLRS.Chapter17.dynamicTableDelete_num`
  - `CLRS.Chapter17.dynamicTableDelete_size`
  - `CLRS.Chapter17.dynamicTableDelete_size_of_contract`
  - `CLRS.Chapter17.dynamicTableDelete_size_of_no_contract`
  - `CLRS.Chapter17.dynamicTableDelete_num_le`
  - `CLRS.Chapter17.dynamicTableDelete_num_empty`
  - `CLRS.Chapter17.dynamicTableDelete_num_pos_of_one_lt`
  - `CLRS.Chapter17.dynamicTableDelete_num_lt_of_nonempty`
  - `CLRS.Chapter17.dynamicTableDelete_capacity_fits`
  - `CLRS.Chapter17.dynamicTableDelete_capacity_pos_of_one_lt`
  - `CLRS.Chapter17.dynamicTableDelete_capacity_le_size`
  - `CLRS.Chapter17.dynamicTableDelete_capacity_le_half_of_contract`
  - `CLRS.Chapter17.dynamicTableDelete_amortizedCost_eq`
  - `CLRS.Chapter17.dynamicTableDelete_amortizedBound`
  - `CLRS.Chapter17.dynamicTable_amortizedBound`
  - `CLRS.Chapter17.growTo` (physical array copy operation)
  - `CLRS.Chapter17.growTo_size` and `CLRS.Chapter17.growTo_toList`
  - `CLRS.Chapter17.insert_copy_cost` (insertion = copy + write)
  - `CLRS.Chapter17.dynamicTableCopyCount_eq_growCopyCost` (abstract copy = physical copy)
  - `CLRS.Chapter17.arrayTable_toState_insert` and `CLRS.Chapter17.arrayTable_insertCost_eq`
  - `CLRS.Chapter17.sharpPotential` and `CLRS.Chapter17.sharpPotentialZ` (load-factor potential)
  - `CLRS.Chapter17.sharpPotentialZ_nonneg` and `CLRS.Chapter17.sharpPotential_nonneg`
  - `CLRS.Chapter17.sharpInsert_amortized_le_three` (insertion amortized <= 3)
  - `CLRS.Chapter17.sharpDelete_amortized_le_three` (deletion amortized <= 3)
  - `CLRS.Chapter17.sharpDelete_loadFactor_eq_half_of_contract` (alpha = 1/2 after contraction)
  - `CLRS.Chapter17.sharpDelete_loadFactor_ge_half_of_contract` (alpha >= 1/2 after contraction)
- Proof pattern: finite-prefix sums, accounting credit balance, potential
  telescoping, executable counter trace induction, size-level table potential
  nonnegativity, capacity feasibility/direction, post-state field equations,
  post-state allocation-size case specs, stored-count direction, positive
  insertion/deletion count/capacity wrappers, post-state capacity corollaries,
  post-transition potential nonnegativity,
  concrete amortized-cost unfolding, resize-branch capacity wrappers,
  actual-cost and capacity-choice case specs, zero/positive deletion-cost wrappers,
  premise-light deletion-cost branch wrappers,
  lower/upper bounds, and transitions
- Mutable-array copying modelled via `growTo`, `ArrayTable`, and
  `insert_copy_cost` (Sub-issue A).
- CLRS load-factor potential with constant amortized bounds (<=3)
  proved for both insertion and deletion (Sub-issue B).
- Current gap: general allocator / RAM cost semantics and amortized
  analysis over interleaved insert/delete traces.

Chapter 17 now provides the reusable amortized-analysis layer for later data
structure chapters.  The generic aggregate/accounting/potential facts are
sorry-free, and the stack, executable binary-counter trace, and dynamic-table
examples compile against stable public theorem names.  The executable counter
trace now has a multi-step potential bound and an empty-counter {lit}`2n` flip
bound.  Dynamic-table insertion and deletion/contraction now expose size-level
potential nonnegativity, capacity feasibility/direction, direct post-state
stored-count and capacity corollaries, post-transition potential
nonnegativity, concrete amortized-cost unfolding wrappers, resize-branch
capacity wrappers, post-state field equations, actual-cost and capacity-choice
case specs, exact zero/positive deletion-cost wrappers, premise-light
deletion-cost branch wrappers, positive-cost and upper-bound transition facts.
The sharper section adds a mutable-array copy model (`growTo`, `ArrayTable`,
`insert_copy_cost`) and the CLRS load-factor potential (`sharpPotential`) with
constant (<=3) amortized bounds for both insertion and deletion under the
sharper contraction strategy.

## Chapter 18 - B-Trees

- Lean source:
  `CLRSLean/Chapter_18.lean`,
  `CLRSLean/Chapter_18/Section_18_1_B_Tree_Model.lean`, and
  `CLRSLean/Chapter_18/Section_18_2_B_Tree_Insertion.lean`, and
  `CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion.lean`
- Status: `partial`
- Main proved theorems:
  - `CLRS.Chapter18.BTree.search_correct`
  - `CLRS.Chapter18.BTree.search_true_iff`
  - `CLRS.Chapter18.BTree.search_true_of_mem`
  - `CLRS.Chapter18.BTree.mem_of_search_true`
  - `CLRS.Chapter18.BTree.search_false_iff`
  - `CLRS.Chapter18.BTree.search_false_of_not_mem`
  - `CLRS.Chapter18.BTree.not_mem_of_search_false`
  - `CLRS.Chapter18.BTree.minKeys_zero`
  - `CLRS.Chapter18.BTree.minKeys_pos`
  - `CLRS.Chapter18.BTree.one_le_minKeys`
  - `CLRS.Chapter18.BTree.minKeys_lower_bound`
  - `CLRS.Chapter18.BTree.minKeys_succ`
  - `CLRS.Chapter18.BTree.minKeys_le_succ`
  - `CLRS.Chapter18.BTree.minKeys_monotone_height`
  - `CLRS.Chapter18.BTree.splitChild_preserves_model`
  - `CLRS.Chapter18.BTree.splitChild_preserves_sorted`
  - `CLRS.Chapter18.BTree.splitChild_preserves_childBounded`
  - `CLRS.Chapter18.BTree.splitChild_preserves_occupancy`
  - `CLRS.Chapter18.BTree.splitChild_preserves_sameDepth`
  - `CLRS.Chapter18.BTree.splitChild_preserves_wellFormed`
  - `CLRS.Chapter18.BTree.splitChild_keys_perm`
  - `CLRS.Chapter18.BTree.insertNonFull` (real recursive CLRS insertion, `heightOf` termination)
  - `CLRS.Chapter18.BTree.insertNonFull_keys_perm` (insertion adds exactly one key; depends on `splitChild`/`childBounded_take_of_full`/`childBounded_drop_of_full`)
  - `CLRS.Chapter18.BTree.findChild_le` / `findChild_take_le` / `findChild_drop_gt` (child-selection range correctness)
  - `CLRS.Chapter18.BTree.sortedInsert_perm` / `mem_sortedInsert` / `sortedInsert_sorted`
  - `CLRS.Chapter18.BTree.sameDepth_iff` / `heightOf_sameDepth_mem` (SameDepth infra)
  - `CLRS.Chapter18.BTree.insertNonFull_sameDepth_height` (insertNonFull preserves SameDepth + heightOf; needs ChildBounded + SameDepth) with corollaries `insertNonFull_sameDepth`, `insertNonFull_height`
  - `CLRS.Chapter18.BTree.insertNonFull_sorted` (insertNonFull preserves Sorted; needs ChildBounded + Sorted)
  - `CLRS.Chapter18.BTree.insertNonFull_childBounded` (insertNonFull preserves ChildBounded; needs ChildBounded + Sorted; split cases reuse `splitChild_preserves_childBounded` via `splitChild_full_eq` bridge)
  - `CLRS.Chapter18.BTree.insertNonFull_occupancy` (insertNonFull preserves Occupancy for both root/non-root flags; needs non-full precondition + ChildBounded)
  - `CLRS.Chapter18.BTree.insertNonFull_wellFormed` (capstone: all four invariants, needs non-full root + WellFormed)
  - `CLRS.Chapter18.BTree.splitChild_valid`
  - `CLRS.Chapter18.BTree.splitChild_mem_iff`
  - `CLRS.Chapter18.BTree.splitChild_mem_old`
  - `CLRS.Chapter18.BTree.splitChild_not_mem_iff`
  - `CLRS.Chapter18.BTree.splitChild_not_mem_old`
  - `CLRS.Chapter18.BTree.splitChild_search_iff`
  - `CLRS.Chapter18.BTree.splitChild_search_old`
  - `CLRS.Chapter18.BTree.splitChild_search_of_mem`
  - `CLRS.Chapter18.BTree.splitChild_search_false_iff`
  - `CLRS.Chapter18.BTree.splitChild_search_false_old`
  - `CLRS.Chapter18.BTree.splitChild_search_false_of_not_mem`
  - `CLRS.Chapter18.BTree.insert_preserves_model`
  - `CLRS.Chapter18.BTree.insert_valid`
  - `CLRS.Chapter18.BTree.insert_mem_iff`
  - `CLRS.Chapter18.BTree.insert_search_iff`
  - `CLRS.Chapter18.BTree.insert_mem_self`
  - `CLRS.Chapter18.BTree.insert_search_self`
  - `CLRS.Chapter18.BTree.insert_search_of_eq`
  - `CLRS.Chapter18.BTree.insert_mem_old`
  - `CLRS.Chapter18.BTree.insert_search_old`
  - `CLRS.Chapter18.BTree.insert_search_of_mem`
  - `CLRS.Chapter18.BTree.insert_not_mem_iff`
  - `CLRS.Chapter18.BTree.insert_not_mem_of_ne`
  - `CLRS.Chapter18.BTree.insert_search_false_iff`
  - `CLRS.Chapter18.BTree.insert_search_false_of_ne`
  - `CLRS.Chapter18.BTree.insert_search_false_of_not_mem_ne`
  - `CLRS.Chapter18.BTree.delete_preserves_model`
  - `CLRS.Chapter18.BTree.delete_valid`
  - `CLRS.Chapter18.BTree.delete_mem_iff`
  - `CLRS.Chapter18.BTree.delete_mem_iff_ne`
  - `CLRS.Chapter18.BTree.delete_search_iff`
  - `CLRS.Chapter18.BTree.delete_search_iff_ne`
  - `CLRS.Chapter18.BTree.delete_not_mem`
  - `CLRS.Chapter18.BTree.delete_search_deleted_false`
  - `CLRS.Chapter18.BTree.delete_search_false_of_eq`
  - `CLRS.Chapter18.BTree.delete_mem_of_ne`
  - `CLRS.Chapter18.BTree.delete_mem_of_ne_prop`
  - `CLRS.Chapter18.BTree.delete_search_of_ne`
  - `CLRS.Chapter18.BTree.delete_search_of_ne_prop`
  - `CLRS.Chapter18.BTree.delete_search_of_mem_ne`
  - `CLRS.Chapter18.BTree.delete_search_of_mem_ne_prop`
  - `CLRS.Chapter18.BTree.delete_not_mem_iff`
  - `CLRS.Chapter18.BTree.delete_not_mem_old`
  - `CLRS.Chapter18.BTree.delete_not_mem_of_eq`
  - `CLRS.Chapter18.BTree.delete_search_false_iff`
  - `CLRS.Chapter18.BTree.delete_search_false_old`
  - `CLRS.Chapter18.BTree.delete_search_false_of_not_mem`
- Proof pattern: mathematical key-set model, structural validity predicate,
  base search success/failure wrappers, minimum-key expression
  base/positivity arithmetic and height monotonicity, specification-level
  split/insert/delete wrappers, Prop-level deletion direct wrappers,
  search correctness reuse,
  direct split validity/preservation corollaries, and direct inserted/deleted-key
  plus old-key successful and unsuccessful query preservation corollaries,
  direct insertion/deletion validity short-name wrappers, equality-key
  update-query wrappers, membership-driven search-after-update wrappers, old
  failed-search preservation wrappers, exact failed membership
  specifications, and direct failed-membership preservation wrappers
- Current gap: full node occupancy/separator/same-depth invariant stack,
  node-level deletion repair, disk-page I/O, and pointer mutation remain
  strengthening targets.

Chapter 18 now has a first-pass B-tree theorem surface.  Search, split-child,
insertion, and deletion are proved against an abstract membership model, and
the update wrappers expose direct search-after-update specifications plus
direct split validity/preservation and inserted/deleted-key plus old-key query
preservation corollaries, direct insertion/deletion validity short-name
wrappers, equality-key update-query wrappers, membership-driven
search-after-update wrappers, exact unsuccessful-search specifications, and
direct old failed-search preservation wrappers.
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
  - `CLRS.Chapter19.FibHeap.makeHeap_minimum_none`
  - `CLRS.Chapter19.FibHeap.potential_makeHeap`
  - `CLRS.Chapter19.FibHeap.potential_nonneg`
  - `CLRS.Chapter19.FibHeap.minimum_correct`
  - `CLRS.Chapter19.FibHeap.minimum_mem`
  - `CLRS.Chapter19.FibHeap.minimum_le`
  - `CLRS.Chapter19.FibHeap.minimum_none_iff`
  - `CLRS.Chapter19.FibHeap.minimum_none_of_empty`
  - `CLRS.Chapter19.FibHeap.minimum_ne_none_of_nonempty`
  - `CLRS.Chapter19.FibHeap.insert_correct`
  - `CLRS.Chapter19.FibHeap.insert_valid`
  - `CLRS.Chapter19.FibHeap.insert_mem_iff`
  - `CLRS.Chapter19.FibHeap.insert_mem_self`
  - `CLRS.Chapter19.FibHeap.insert_mem_old`
  - `CLRS.Chapter19.FibHeap.insert_not_mem_iff`
  - `CLRS.Chapter19.FibHeap.insert_not_mem_of_ne`
  - `CLRS.Chapter19.FibHeap.insert_minimum_correct`
  - `CLRS.Chapter19.FibHeap.insert_minimum_mem`
  - `CLRS.Chapter19.FibHeap.insert_minimum_le_inserted`
  - `CLRS.Chapter19.FibHeap.insert_minimum_le_old`
  - `CLRS.Chapter19.FibHeap.insert_minimum_none_iff`
  - `CLRS.Chapter19.FibHeap.insert_minimum_ne_none`
  - `CLRS.Chapter19.FibHeap.union_correct`
  - `CLRS.Chapter19.FibHeap.union_valid`
  - `CLRS.Chapter19.FibHeap.union_mem_iff`
  - `CLRS.Chapter19.FibHeap.union_mem_left`
  - `CLRS.Chapter19.FibHeap.union_mem_right`
  - `CLRS.Chapter19.FibHeap.union_not_mem_iff`
  - `CLRS.Chapter19.FibHeap.union_not_mem_of_not_mem`
  - `CLRS.Chapter19.FibHeap.union_minimum_correct`
  - `CLRS.Chapter19.FibHeap.union_minimum_mem`
  - `CLRS.Chapter19.FibHeap.union_minimum_le_left`
  - `CLRS.Chapter19.FibHeap.union_minimum_le_right`
  - `CLRS.Chapter19.FibHeap.union_minimum_none_iff`
  - `CLRS.Chapter19.FibHeap.union_minimum_none_of_empty`
  - `CLRS.Chapter19.FibHeap.union_minimum_ne_none_of_left`
  - `CLRS.Chapter19.FibHeap.union_minimum_ne_none_of_right`
  - `CLRS.Chapter19.FibHeap.extractMin_correct`
  - `CLRS.Chapter19.FibHeap.extractMin_valid`
  - `CLRS.Chapter19.FibHeap.extractMin_mem_iff`
  - `CLRS.Chapter19.FibHeap.extractMin_not_mem`
  - `CLRS.Chapter19.FibHeap.extractMin_mem_of_ne`
  - `CLRS.Chapter19.FibHeap.extractMin_not_mem_iff`
  - `CLRS.Chapter19.FibHeap.extractMin_not_mem_old`
  - `CLRS.Chapter19.FibHeap.extractMin_none_iff`
  - `CLRS.Chapter19.FibHeap.extractMin_none_of_empty`
  - `CLRS.Chapter19.FibHeap.extractMin_ne_none_of_nonempty`
  - `CLRS.Chapter19.FibHeap.extractMin_remaining_minimum_correct`
  - `CLRS.Chapter19.FibHeap.extractMin_remaining_minimum_ne`
  - `CLRS.Chapter19.FibHeap.extractMin_remaining_minimum_mem`
  - `CLRS.Chapter19.FibHeap.extractMin_remaining_minimum_le_old`
  - `CLRS.Chapter19.FibHeap.extractMin_remaining_minimum_none_iff`
  - `CLRS.Chapter19.FibHeap.extractMin_remaining_minimum_none_of_all_eq`
  - `CLRS.Chapter19.FibHeap.extractMin_remaining_minimum_ne_none_of_remaining`
  - `CLRS.Chapter19.FibHeap.decreaseKey_correct`
  - `CLRS.Chapter19.FibHeap.decreaseKey_valid`
  - `CLRS.Chapter19.FibHeap.decreaseKey_mem_iff`
  - `CLRS.Chapter19.FibHeap.decreaseKey_mem_new`
  - `CLRS.Chapter19.FibHeap.decreaseKey_mem_old`
  - `CLRS.Chapter19.FibHeap.decreaseKey_oldKey_mem_iff`
  - `CLRS.Chapter19.FibHeap.decreaseKey_oldKey_not_mem_of_ne`
  - `CLRS.Chapter19.FibHeap.decreaseKey_not_mem_iff`
  - `CLRS.Chapter19.FibHeap.decreaseKey_not_mem_of_ne`
  - `CLRS.Chapter19.FibHeap.decreaseKey_minimum_correct`
  - `CLRS.Chapter19.FibHeap.decreaseKey_minimum_mem`
  - `CLRS.Chapter19.FibHeap.decreaseKey_minimum_le_new`
  - `CLRS.Chapter19.FibHeap.decreaseKey_minimum_le_old`
  - `CLRS.Chapter19.FibHeap.decreaseKey_minimum_none_iff`
  - `CLRS.Chapter19.FibHeap.decreaseKey_minimum_ne_none`
  - `CLRS.Chapter19.FibHeap.delete_correct`
  - `CLRS.Chapter19.FibHeap.delete_valid`
  - `CLRS.Chapter19.FibHeap.delete_mem_iff`
  - `CLRS.Chapter19.FibHeap.delete_not_mem`
  - `CLRS.Chapter19.FibHeap.delete_mem_of_ne`
  - `CLRS.Chapter19.FibHeap.delete_not_mem_iff`
  - `CLRS.Chapter19.FibHeap.delete_not_mem_old`
  - `CLRS.Chapter19.FibHeap.delete_not_mem_of_eq`
  - `CLRS.Chapter19.FibHeap.delete_minimum_correct`
  - `CLRS.Chapter19.FibHeap.delete_minimum_ne`
  - `CLRS.Chapter19.FibHeap.delete_minimum_mem`
  - `CLRS.Chapter19.FibHeap.delete_minimum_le_old`
  - `CLRS.Chapter19.FibHeap.delete_minimum_none_iff`
  - `CLRS.Chapter19.FibHeap.delete_minimum_none_of_all_eq`
  - `CLRS.Chapter19.FibHeap.delete_minimum_ne_none_of_remaining`
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
  characterization, direct minimum/extract-min empty-result and nonempty-result wrappers,
  direct minimum membership/lower-bound wrappers,
  insert/union/extract-min-remaining/decrease-key/delete minimum direct
  membership/lower-bound wrappers, heap-potential nonnegativity and
  Chapter 17 potential-method instantiation, direct operation-key and old-key
  preservation membership corollaries, exact failed membership specifications,
  direct failed-membership preservation wrappers, replaced-key decrease-key
  query wrappers, returned
  minimum-after-update positive and empty-result specifications,
  Fibonacci lower-bound recurrence
  plus a two-step doubling induction over even indices, a half-index bridge,
  and a conditional binary-log degree budget
- Current gap: pointer handles, heap-ordered forest/cascading-cut transition
  system, consolidation arrays, duplicate keys, and the subtree-size induction
  leading to the true Fibonacci log-degree proof remain strengthening targets.

Chapter 19 now records the operation-level Fibonacci-heap contracts against an
abstract finite key set, including empty-heap construction and empty-result
minimum/extract-min specifications, direct minimum/extract-min empty-result
and nonempty-result wrappers, direct minimum membership/lower-bound
wrappers, insert/union/extract-min-remaining/decrease-key/delete minimum direct
membership/lower-bound wrappers, plus direct
insert/union/extract-min/decrease-key/delete membership facts plus
operation-key and old-key preservation membership corollaries plus exact failed
membership specifications and direct failed-membership preservation wrappers,
direct operation-result validity wrappers, and
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
  - `CLRS.Chapter20.VEB.minimum_mem`
  - `CLRS.Chapter20.VEB.minimum_le`
  - `CLRS.Chapter20.VEB.minimum_lt_univ`
  - `CLRS.Chapter20.VEB.minimum_none_iff`
  - `CLRS.Chapter20.VEB.minimum_none_of_empty`
  - `CLRS.Chapter20.VEB.minimum_ne_none_of_nonempty`
  - `CLRS.Chapter20.VEB.maximum_correct`
  - `CLRS.Chapter20.VEB.maximum_mem`
  - `CLRS.Chapter20.VEB.le_maximum`
  - `CLRS.Chapter20.VEB.maximum_lt_univ`
  - `CLRS.Chapter20.VEB.maximum_none_iff`
  - `CLRS.Chapter20.VEB.maximum_none_of_empty`
  - `CLRS.Chapter20.VEB.maximum_ne_none_of_nonempty`
  - `CLRS.Chapter20.VEB.successor_correct`
  - `CLRS.Chapter20.VEB.successor_mem`
  - `CLRS.Chapter20.VEB.successor_gt`
  - `CLRS.Chapter20.VEB.successor_le`
  - `CLRS.Chapter20.VEB.successor_lt_univ`
  - `CLRS.Chapter20.VEB.successor_none_iff`
  - `CLRS.Chapter20.VEB.successor_none_of_no_gt`
  - `CLRS.Chapter20.VEB.successor_ne_none_of_exists_gt`
  - `CLRS.Chapter20.VEB.predecessor_correct`
  - `CLRS.Chapter20.VEB.predecessor_mem`
  - `CLRS.Chapter20.VEB.predecessor_lt`
  - `CLRS.Chapter20.VEB.le_predecessor`
  - `CLRS.Chapter20.VEB.predecessor_lt_univ`
  - `CLRS.Chapter20.VEB.predecessor_none_iff`
  - `CLRS.Chapter20.VEB.predecessor_none_of_no_lt`
  - `CLRS.Chapter20.VEB.predecessor_ne_none_of_exists_lt`
  - `CLRS.Chapter20.VEB.insert_correct`
  - `CLRS.Chapter20.VEB.insert_member_iff`
  - `CLRS.Chapter20.VEB.insert_member_lt_univ`
  - `CLRS.Chapter20.VEB.insert_member_self`
  - `CLRS.Chapter20.VEB.insert_member_old`
  - `CLRS.Chapter20.VEB.insert_member_false_iff`
  - `CLRS.Chapter20.VEB.insert_member_false_of_ne`
  - `CLRS.Chapter20.VEB.insert_minimum_correct`
  - `CLRS.Chapter20.VEB.insert_minimum_mem`
  - `CLRS.Chapter20.VEB.insert_minimum_mem_old_of_ne`
  - `CLRS.Chapter20.VEB.insert_minimum_le_inserted`
  - `CLRS.Chapter20.VEB.insert_minimum_le_old`
  - `CLRS.Chapter20.VEB.insert_minimum_lt_univ`
  - `CLRS.Chapter20.VEB.insert_minimum_none_iff`
  - `CLRS.Chapter20.VEB.insert_minimum_ne_none`
  - `CLRS.Chapter20.VEB.insert_maximum_correct`
  - `CLRS.Chapter20.VEB.insert_maximum_mem`
  - `CLRS.Chapter20.VEB.insert_maximum_mem_old_of_ne`
  - `CLRS.Chapter20.VEB.insert_maximum_inserted_le`
  - `CLRS.Chapter20.VEB.insert_maximum_old_le`
  - `CLRS.Chapter20.VEB.insert_maximum_lt_univ`
  - `CLRS.Chapter20.VEB.insert_maximum_none_iff`
  - `CLRS.Chapter20.VEB.insert_maximum_ne_none`
  - `CLRS.Chapter20.VEB.insert_successor_correct`
  - `CLRS.Chapter20.VEB.insert_successor_mem`
  - `CLRS.Chapter20.VEB.insert_successor_mem_old_of_ne`
  - `CLRS.Chapter20.VEB.insert_successor_gt`
  - `CLRS.Chapter20.VEB.insert_successor_le`
  - `CLRS.Chapter20.VEB.insert_successor_lt_univ`
  - `CLRS.Chapter20.VEB.insert_successor_none_iff`
  - `CLRS.Chapter20.VEB.insert_successor_none_of_no_gt`
  - `CLRS.Chapter20.VEB.insert_successor_none_of_insert_le_old_no_gt`
  - `CLRS.Chapter20.VEB.insert_successor_ne_none_of_insert_gt`
  - `CLRS.Chapter20.VEB.insert_successor_ne_none_of_old_gt`
  - `CLRS.Chapter20.VEB.insert_predecessor_correct`
  - `CLRS.Chapter20.VEB.insert_predecessor_mem`
  - `CLRS.Chapter20.VEB.insert_predecessor_mem_old_of_ne`
  - `CLRS.Chapter20.VEB.insert_predecessor_lt`
  - `CLRS.Chapter20.VEB.insert_le_predecessor`
  - `CLRS.Chapter20.VEB.insert_predecessor_lt_univ`
  - `CLRS.Chapter20.VEB.insert_predecessor_none_iff`
  - `CLRS.Chapter20.VEB.insert_predecessor_none_of_no_lt`
  - `CLRS.Chapter20.VEB.insert_predecessor_none_of_query_le_insert_old_no_lt`
  - `CLRS.Chapter20.VEB.insert_predecessor_ne_none_of_insert_lt`
  - `CLRS.Chapter20.VEB.insert_predecessor_ne_none_of_old_lt`
  - `CLRS.Chapter20.VEB.delete_correct`
  - `CLRS.Chapter20.VEB.delete_member_iff`
  - `CLRS.Chapter20.VEB.delete_member_lt_univ`
  - `CLRS.Chapter20.VEB.delete_member_deleted_false`
  - `CLRS.Chapter20.VEB.delete_member_of_ne`
  - `CLRS.Chapter20.VEB.delete_member_false_iff`
  - `CLRS.Chapter20.VEB.delete_member_false_old`
  - `CLRS.Chapter20.VEB.delete_member_false_of_eq`
  - `CLRS.Chapter20.VEB.delete_minimum_correct`
  - `CLRS.Chapter20.VEB.delete_minimum_ne`
  - `CLRS.Chapter20.VEB.delete_minimum_mem`
  - `CLRS.Chapter20.VEB.delete_minimum_le_old`
  - `CLRS.Chapter20.VEB.delete_minimum_lt_univ`
  - `CLRS.Chapter20.VEB.delete_minimum_none_iff`
  - `CLRS.Chapter20.VEB.delete_minimum_none_of_all_eq`
  - `CLRS.Chapter20.VEB.delete_minimum_ne_none_of_remaining`
  - `CLRS.Chapter20.VEB.delete_maximum_correct`
  - `CLRS.Chapter20.VEB.delete_maximum_ne`
  - `CLRS.Chapter20.VEB.delete_maximum_mem`
  - `CLRS.Chapter20.VEB.delete_maximum_old_le`
  - `CLRS.Chapter20.VEB.delete_maximum_lt_univ`
  - `CLRS.Chapter20.VEB.delete_maximum_none_iff`
  - `CLRS.Chapter20.VEB.delete_maximum_none_of_all_eq`
  - `CLRS.Chapter20.VEB.delete_maximum_ne_none_of_remaining`
  - `CLRS.Chapter20.VEB.delete_successor_correct`
  - `CLRS.Chapter20.VEB.delete_successor_mem`
  - `CLRS.Chapter20.VEB.delete_successor_gt`
  - `CLRS.Chapter20.VEB.delete_successor_le`
  - `CLRS.Chapter20.VEB.delete_successor_lt_univ`
  - `CLRS.Chapter20.VEB.delete_successor_none_iff`
  - `CLRS.Chapter20.VEB.delete_successor_none_of_no_gt`
  - `CLRS.Chapter20.VEB.delete_successor_none_of_old_no_gt`
  - `CLRS.Chapter20.VEB.delete_successor_ne_none_of_remaining_gt`
  - `CLRS.Chapter20.VEB.delete_predecessor_correct`
  - `CLRS.Chapter20.VEB.delete_predecessor_mem`
  - `CLRS.Chapter20.VEB.delete_predecessor_lt`
  - `CLRS.Chapter20.VEB.delete_le_predecessor`
  - `CLRS.Chapter20.VEB.delete_predecessor_lt_univ`
  - `CLRS.Chapter20.VEB.delete_predecessor_none_iff`
  - `CLRS.Chapter20.VEB.delete_predecessor_none_of_no_lt`
  - `CLRS.Chapter20.VEB.delete_predecessor_none_of_old_no_lt`
  - `CLRS.Chapter20.VEB.delete_predecessor_ne_none_of_remaining_lt`
  - `CLRS.Chapter20.VEB.operationDepth_zero`
  - `CLRS.Chapter20.VEB.operationDepth_succ`
  - `CLRS.Chapter20.VEB.operationDepth_linear`
  - `CLRS.Chapter20.VEB.operationDepth_monotone`
  - `CLRS.Chapter20.VEB.operationDepth_strict_mono`
- Proof pattern: natural-number quotient/remainder arithmetic, bounded
  high/low recomposition, finite-set representation semantics,
  extrema/successor via `Finset.min'`/`max'`, successful-query universe-bound
  bridges, direct extrema membership/lower- and upper-bound wrappers, direct
  insertion-query old-key membership wrappers, direct base/insert/delete
  neighbor membership/order wrappers, direct updated-key,
  old-key preservation, failed member queries after updates, and direct
  failed member-query preservation wrappers, direct no-neighbor query wrappers,
  premise-light no-neighbor wrappers over old represented sets, direct extrema
  empty-result wrappers, direct base extrema/neighbor nonempty-result wrappers,
  direct updated-neighbor nonempty-result wrappers,
  direct deletion-extrema nonempty-result wrappers,
  direct extrema-after-update
  membership/order wrappers, update-query
  universe-bound corollaries, and definition unfolding for
  first-pass operation-depth recurrence and monotonicity facts
- Current gap: recursive min/max-summary-cluster state, word-RAM base cases,
  and an explicit Chapter 3 asymptotic bridge for `O(log log u)` remain
  strengthening targets.

Chapter 20 now proves the high/low/index arithmetic, including both directions
of bounded high/low recomposition, and a set-specification layer for the main
vEB queries and updates.  This includes both positive and empty-result
extrema/successor/predecessor cases plus successful-query universe-bound
corollaries, direct extrema membership/lower- and upper-bound wrappers,
direct insertion-query old-key membership wrappers,
direct base/insert/delete neighbor membership/order wrappers,
membership-after-update, direct extrema-after-update membership/order wrappers,
direct updated-key and old-key member-preservation corollaries, exact failed
member-query corollaries, direct failed member-query preservation wrappers,
positive and empty-result extrema-after-update, and both positive and
no-neighbor specifications for neighbor queries after updates, plus direct
no-neighbor query wrappers, premise-light no-neighbor wrappers over old
represented sets, direct extrema empty-result wrappers, direct base
extrema/neighbor nonempty-result wrappers, direct updated-neighbor
nonempty-result wrappers, direct deletion-extrema nonempty-result wrappers,
and direct universe-bound
corollaries for successful queries after updates.  The
current operation-depth facts expose the base case, successor step, and a
linear/monotone wrapper over the universe exponent, not yet a full asymptotic
translation for the original universe size.

## Chapter 21 - Data Structures for Disjoint Sets

### Section 21.1 - Abstract Operations

- Model: `CLRS.Chapter21.Partition`, an explicit equivalence relation.
- Core interface:
  - `Partition.merge_sameSet_iff`
  - `Partition.merge_related_sameSet_iff`
  - `stepSpec_union_sameSet_iff`
  - `runSpec_append`
  - `runSpec_preserves_sameSet`
- Boundary: `FIND-SET` preserves the partition and `UNION` merges exactly two
  represented classes.

### Section 21.2 - Linked-List Representation

- Model: head and size tables over `Fin n`; weighted union redirects the
  smaller represented class and returns the pointer-rewrite charge.
- Correctness:
  - `LinkedList.State.weightedUnion_sameSet_iff`
  - `LinkedList.State.weightedUnion_refines_merge`
  - `LinkedList.State.weightedUnion_preserves_headInvariant`
- Complexity:
  - `LinkedList.State.weightedUnion_changed_doubles`
  - `LinkedList.State.move_count_le_log2`
  - `LinkedList.State.total_rewrites_le_n_mul_log2`
- Boundary: the standard aggregate `O(n log n)` representative-rewrite
  argument is proved for the table-level model.

### Section 21.3 - Disjoint-Set Forests

- Implementation: `Batteries.Data.UnionFind`, including union by rank and path
  compression.
- Initialization and find:
  - `Forest.singletonForest_equiv_iff`
  - `Forest.find_preserves_sameSet`
  - `Forest.find_returns_representative`
  - `Forest.find_compresses_path`
- Union and query:
  - `Forest.union_sameSet_iff`
  - `Forest.union_refines_merge`
  - `Forest.checkEquiv_correct`
  - `Forest.checkEquiv_preserves_sameSet`
- Boundary: executable functional correctness is complete for the represented
  Batteries API.

### Section 21.4 - Rank And Path-Compression Analysis

- Rank/path layer:
  - `Analysis.parentPath_rank_bound`
  - `Analysis.rank_le_log2`
  - `Analysis.parentPath_length_le_log2`
- Concrete Batteries execution layer:
  - `Analysis.Costed.findEdges_parentPath`
  - `Analysis.Costed.RankBudget.afterUnion`
  - `Analysis.Costed.costedFind_cost_le_log2`
  - `Analysis.Costed.costedUnion_cost_le_log2`
  - `Analysis.Costed.run_erase`
  - `Analysis.Costed.run_refines_spec`
  - `Analysis.Costed.run_rank_le_log2`
  - `Analysis.Costed.run_cost_le`
- Inverse-Ackermann/potential layer:
  - `Analysis.inverseAckermann_spec`
  - `Analysis.inverseAckermann_minimal`
  - `Analysis.total_cost_le_of_inverseAckermann_certificate`
  - `Analysis.Ackermann.potential_find_le`
  - `Analysis.Ackermann.potential_link_le_add_two`
  - `Analysis.Ackermann.costedFind_amortized_le`
  - `Analysis.Ackermann.costedUnion_amortized_le`
  - `Analysis.Ackermann.step_amortized_le`
  - `Analysis.Ackermann.run_cost_le_inverseAckermann`
  - `Analysis.Ackermann.run_cost_le_inverseAckermann_of_universe_le_ops`
- Boundary: the concrete Batteries machine now instantiates the
  inverse-Ackermann potential directly.  Its actual cost is bounded by
  `9 * (m+n) * alpha(n)`, and by `18 * m * alpha(n)` when `n <= m`.
- Closure audit: `docs/proof-audits/chapter-21-closure-2026-07-10.md`.

### Chapter 23 Bridge

- `MST.UnionFindConnectivityRefinement.checkEquiv_iff_connected`
- `MST.UnionFindConnectivityRefinement.cycleTest_correct`
- Boundary: a connectivity-faithful state family yields the existing verified
  Kruskal cycle-test interface.  Incremental state threading remains a
  performance refinement.

## Chapter 22 - Elementary Graph Algorithms

- Chapter status: `main-proof-complete-for-correctness`
- Chapter guide: `CLRSLean/Chapter_22.lean`
- Closure audit: `docs/proof-audits/chapter-22-closure-2026-07-10.md`
- Interface tests: `Tests/Chapter_22_Interface.lean`,
  `Tests/Chapter_22_Closure.lean`

The sealed Chapter 22 model uses a finite vertex set and finite adjacency
function.  All advertised functional-correctness chains for Sections 22.1-22.5
are complete.  Explicit work/RAM-cost models remain a separate refinement
track.

### Section 22.1 - Representing graphs

- Lean source:
  `CLRSLean/Chapter_22/Section_22_1_Representing_Graphs.lean`
- Status: `proved`
- Main declarations:
  - `CLRS.Chapter22.Graph`
  - `CLRS.Chapter22.Graph.Adj`
  - `CLRS.Chapter22.Graph.IsWalk`
  - `CLRS.Chapter22.Graph.IsPath`
  - `CLRS.Chapter22.Graph.IsCycle`
  - `CLRS.Chapter22.Graph.Reachable`
  - `CLRS.Chapter22.Graph.reachable_refl`
  - `CLRS.Chapter22.Graph.reachable_trans`
  - `CLRS.Chapter22.Graph.reachable_adj`
- Proof pattern: finite adjacency closure and reflexive-transitive reachability.

### Section 22.2 - Breadth-first search

- Lean source: `CLRSLean/Chapter_22/Section_22_2_BFS.lean`
- Status: `proved`
- Reachability layer:
  - `CLRS.Chapter22.Graph.bfs_sound`
  - `CLRS.Chapter22.Graph.bfs_complete`
  - `CLRS.Chapter22.Graph.bfs_closed`
- Shortest-distance layer:
  - `CLRS.Chapter22.Graph.ReachableIn`
  - `CLRS.Chapter22.Graph.IsShortestDistance`
  - `CLRS.Chapter22.Graph.BFSState`
  - `CLRS.Chapter22.Graph.BFSDistanceInvariant`
  - `CLRS.Chapter22.Graph.bfsState_distance_reachableIn`
  - `CLRS.Chapter22.Graph.bfsState_distance_le_of_reachableIn`
  - `CLRS.Chapter22.Graph.bfsState_distance_eq_some_iff`
- Predecessor-tree layer:
  - `CLRS.Chapter22.Graph.BFSParentPath`
  - `CLRS.Chapter22.Graph.bfsState_parent_spec`
  - `CLRS.Chapter22.Graph.bfsState_parent_defined_iff`
  - `CLRS.Chapter22.Graph.bfsState_parent_acyclic`
  - `CLRS.Chapter22.Graph.IsBFSPredecessorTree`
  - `CLRS.Chapter22.Graph.bfsState_isBFSPredecessorTree`
  - `CLRS.Chapter22.Graph.bfsState_correct`
- Proof pattern: project the labelled FIFO state to the verified reachability
  search, maintain nondecreasing queue levels plus a one-level queue span, use
  parent pointers for attained path lengths, and use processed-edge bounds for
  shortestness.

### Section 22.3 - Depth-first search

- Lean sources:
  - `CLRSLean/Chapter_22/Section_22_3_DFS.lean`
  - `CLRSLean/Chapter_22/Section_22_3_DFS/WhitePath.lean`
  - `CLRSLean/Chapter_22/Section_22_3_DFS/Intervals.lean`
  - `CLRSLean/Chapter_22/Section_22_3_DFS/Bridge.lean`
  - `CLRSLean/Chapter_22/Section_22_3_DFS/SCC.lean`
  - `CLRSLean/Chapter_22/Section_22_3_DFS/EdgeClassification.lean`
- Status: `proved`
- DFS and white-path layer:
  - `CLRS.Chapter22.Graph.DFSState`
  - `CLRS.Chapter22.Graph.dfsVisit`
  - `CLRS.Chapter22.Graph.dfs`
  - `CLRS.Chapter22.Graph.dfs_all_black`
  - `CLRS.Chapter22.Graph.dfsVisit_blackens_iff_whiteReachable`
- Timestamp and ancestry layer:
  - `CLRS.Chapter22.Graph.dfs_parenthesis`
  - `CLRS.Chapter22.Graph.dfs_intervals_not_cross`
  - `CLRS.Chapter22.Graph.IsDFSAncestor_reachable`
  - `CLRS.Chapter22.Graph.intervalNestedInside_dfs_iff_ancestor`
- Edge-classification layer:
  - `CLRS.Chapter22.Graph.DFSEdgeKind`
  - `CLRS.Chapter22.Graph.dfs_edge_classification_unique`
  - `CLRS.Chapter22.Graph.dfs_tree_or_forward_edge_iff_timestamps`
  - `CLRS.Chapter22.Graph.dfs_back_edge_iff_timestamps`
  - `CLRS.Chapter22.Graph.dfs_cross_edge_iff_timestamps`
  - `CLRS.Chapter22.Graph.dfs_undirected_edge_tree_or_back`
- SCC bridge layer:
  - `CLRS.Chapter22.Graph.scc_finish_time_order`
  - `CLRS.Chapter22.Graph.scc_finish_order`
- Proof pattern: fuelled DFS state invariants, white-reachable closure at
  discovery time, timestamp interval nesting, parent-forest ancestry, and edge
  case analysis.

### Section 22.4 - Topological sort

- Lean source: `CLRSLean/Chapter_22/Section_22_4_Topological_Sort.lean`
- Status: `proved`
- Kahn layer:
  - `CLRS.Chapter22.Graph.IsDAG`
  - `CLRS.Chapter22.Graph.IsTopologicalOrder`
  - `CLRS.Chapter22.Graph.topologicalSort`
  - `CLRS.Chapter22.Graph.topologicalSort_isTopologicalOrder`
- CLRS DFS finish-time layer:
  - `CLRS.Chapter22.Graph.isDAG_no_dfs_back_edge`
  - `CLRS.Chapter22.Graph.dfs_finish_time_decreases_on_dag_edge`
  - `CLRS.Chapter22.Graph.dfsTopologicalSort`
  - `CLRS.Chapter22.Graph.dfsTopologicalSort_isTopologicalOrder`
- Proof pattern: source-removal invariants for Kahn, and exclusion of DFS back
  edges plus decreasing finish times for the CLRS order.

### Section 22.5 - Strongly connected components

- Lean sources:
  - `CLRSLean/Chapter_22/Section_22_5_Strongly_Connected_Components.lean`
  - `CLRSLean/Chapter_22/Section_22_5_Strongly_Connected_Components/MergeSortCongr.lean`
- Status: `proved`
- Main declarations:
  - `CLRS.Chapter22.Graph.transpose`
  - `CLRS.Chapter22.Graph.StronglyConnected`
  - `CLRS.Chapter22.Graph.IsSCC`
  - `CLRS.Chapter22.Graph.IsSCCPartition`
  - `CLRS.Chapter22.Graph.kosarajuComponents`
  - `CLRS.Chapter22.Graph.kosarajuComponent_scc_core`
  - `CLRS.Chapter22.Graph.kosarajuComponents_eq_sccs`
  - `CLRS.Chapter22.Graph.kosarajuComponents_isSCCPartition`
- Proof pattern: decreasing first-pass finish-time order, transpose DFS
  collection, SCC monochromaticity, exact component collection, maximality,
  pairwise disjointness, and coverage.

### Chapter 22 sealed boundary

- Completed: main algorithmic correctness for graph representation, BFS, DFS,
  topological sorting, and SCC decomposition.
- Deferred without reopening the milestone: exact work counts, asymptotic
  `O(V + E)` packaging, imperative adjacency-list/RAM refinement, exercises,
  and chapter-end problems.

## Chapter 23 - Minimum Spanning Trees

### Section 23.1 - Growing a minimum spanning tree

- Lean source:
  `CLRSLean/Chapter_23/Section_23_1_Growing_Minimum_Spanning_Trees.lean`
- Status: `main-proof-complete-for-correctness`
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

This section contains the mathematical core of the CLRS MST proof.  It proves
that a light edge crossing a cut is safe once the graph-specific exchange
certificate is supplied, proves that the abstract empty-prefix optimum
specification is equivalent to the concrete finite-graph MST specification, and
derives the cut-crossing tree edge needed to preserve an accepted prefix across
a respecting cut.  Section 23.2 now discharges the exchange certificate
automatically.

### Section 23.2 - Kruskal and Prim

- Lean source: `CLRSLean/Chapter_23/Section_23_2_Kruskal_And_Prim.lean`
- Interface tests: `Tests/Chapter_23_Interface.lean`,
  `Tests/Chapter_23_Closure.lean`
- Status: `main-proof-complete-for-correctness`
- Main proved theorems:
  - `CLRS.MST.FiniteGraph.canonicalSimplePath_unique`
  - `CLRS.MST.FiniteGraph.exists_crossing_exchangePath_of_spanningTree`
  - `CLRS.MST.FiniteGraph.cutCertificate_of_lightest_crossing_auto`
  - `CLRS.MST.FiniteGraph.kruskal_minimum_spanning_tree_of_sorted_complete_exact_component_empty`
  - `CLRS.MST.FiniteGraph.prim_minimum_spanning_tree`
- Supporting theorems:
  - `CLRS.MST.Graph.selectedSimpleGraph`
  - `CLRS.MST.Graph.exists_pathExchange_of_simplePath_crosses`
  - `CLRS.MST.FiniteGraph.selectedSimpleGraph_isAcyclic`
  - `CLRS.MST.FiniteGraph.safeEdge_of_lightest_crossing_auto`
  - `CLRS.MST.FiniteGraph.cutCertificate_of_exactComponentKruskalPrefix_auto`
  - `CLRS.MST.FiniteGraph.kruskal_preserves_mst_of_sorted_exact_component`
  - `CLRS.MST.FiniteGraph.kruskal_optimal_of_sorted_complete_exact_component`
  - `CLRS.MST.FiniteGraph.PrimTrace`
  - `CLRS.MST.FiniteGraph.PrimCertificate`
  - `CLRS.MST.FiniteGraph.prim_forest_of_trace`
  - `CLRS.MST.FiniteGraph.prim_preserves_mst`
  - `CLRS.MST.FiniteGraph.prim_spanning_tree_of_certificate`
  - `CLRS.MST.FiniteGraph.prim_optimal`
- Proof pattern: Mathlib simple-path normalization, forest path uniqueness,
  automatic cut exchange, exact-component prefix accounting, local
  sorted-lightness recursion, and shared safe-edge induction for Kruskal and
  Prim.
- Closure audit: `docs/proof-audits/chapter-23-closure-2026-07-11.md`.
- Implementation refinement now proved: stateful Chapter 21 union-find
  threading for Kruskal, exact operation-trace correspondence, complete
  sorting/scan/union-find work composition, executable indexed-queue Prim,
  and binary-heap operation-count bounds.
- Deferred without reopening the milestone: semantic refinement to the
  concrete `Batteries.BinaryHeap` array and mutable/RAM write accounting.

The former manual `ExchangePath`, global-lightness, and missing-Prim gaps are
closed.  A canonical simple tree path now produces the crossing replacement
edge; the sorted Kruskal wrapper builds each local cut certificate during its
recursion; and a complete dynamic Prim light-edge trace yields a concrete MST.

## Chapter 24 - Single-Source Shortest Paths

- Chapter status: `selected-section-complete`
- Chapter guide: `CLRSLean/Chapter_24.lean`

### Section 24.1 - The Bellman-Ford algorithm

- Lean source: `CLRSLean/Chapter_24/Section_24_1_Bellman_Ford.lean`
- Status: `proved`
- Model layer:
  - `CLRS.Chapter24.WeightedGraph`
  - `CLRS.Chapter24.WeightedGraph.Adj`
  - `CLRS.Chapter24.WeightedGraph.walkWeight`
  - `CLRS.Chapter24.WeightedGraph.IsWalkFrom`
- Relaxation dynamic program:
  - `CLRS.Chapter24.WeightedGraph.relaxStep`
  - `CLRS.Chapter24.WeightedGraph.relaxDist`
  - `CLRS.Chapter24.WeightedGraph.relaxDist_succ_le`
- Correctness layer:
  - `CLRS.Chapter24.WeightedGraph.relaxDist_le_walkWeight` (upper-bound property)
  - `CLRS.Chapter24.WeightedGraph.exists_walk_of_relaxDist` (realizability)
  - `CLRS.Chapter24.WeightedGraph.NoNegCycle`
  - `CLRS.Chapter24.WeightedGraph.exists_simple_le` (cycle removal)
  - `CLRS.Chapter24.WeightedGraph.IsShortestDist`
  - `CLRS.Chapter24.WeightedGraph.relaxDist_isShortestDist` (CLRS Theorem 24.4)
  - `CLRS.Chapter24.WeightedGraph.relaxDist_stabilizes` (convergence)
- Work bound:
  - `CLRS.Chapter24.WeightedGraph.bellmanFordWork`
  - `CLRS.Chapter24.WeightedGraph.bellmanFordWork_le` (`O(V·E)`)
- Proof pattern: a synchronous `WithTop ℝ`-valued relaxation dynamic program;
  induction on the round count for the upper-bound and realizability properties;
  duplicate-vertex decomposition plus `walkWeight` additivity for cycle removal;
  and identification of `relaxDist (|V|-1)` with the shortest-path distance `δ`.

### Chapter 24 remaining work

- Deferred without a false claim: Dijkstra's algorithm (Section 24.3) with its
  greedy invariant and `O(E log V)` binary-heap work bound; SSSP in DAGs
  (Section 24.2); difference constraints (Section 24.4); per-edge relaxation
  ordering and mutable/RAM cost accounting for the abstract synchronous model.

## Deferred And Blocked Items

| Item | Status | Reason |
| --- | --- | --- |
| Union-find implementation correctness | `deferred-implementation` | Not needed for the mathematical MST correctness theorem. |
| Chapter 6 priority-queue RAM costs | `deferred-implementation` | Array heap predicates, localized heap predicates, `largest` lemmas, no-swap heapify repair, recursive fuelled `MAX-HEAPIFY` repair, bottom-up build-heap, in-place heapsort loop correctness, bundled heapsort state-correctness, swap preservation, array `HEAP-MAXIMUM`, full fuelled `HEAP-INCREASE-KEY`, array `HEAP-EXTRACT-MAX`, and index-based `HEAP-DELETE` state correctness are proved; RAM costs remain refinement targets. |
| Chapter 7 mutable-array partition | `future-work` | Stable-filter partition classification, scan-state partition-loop correctness, a returned pivot-index wrapper, an adjacent-swap trace, functional quicksort correctness, and deterministic comparison-count bounds are proved; the next refinement is the CLRS array `PARTITION` index-level loop invariant. |
| Chapter 7 randomized probability semantics | `blocked-design` | The expected-comparison recurrence and harmonic bound are proved in a recurrence model; the remaining target is a probability model for random pivots or random permutations, plus sharper tail/lower-bound packaging. |
| Chapter 8 mutable output-array implementation | `future-work` | Stable bucket correctness, count-table lengths, cumulative boundaries, and per-key reverse-scan refinement are proved; the next refinement is a single mutable output array with mutable cumulative counters connected to `countingSortBy`. |
| Chapter 8 bucket-sort expected time | `proved-abstract` | Deterministic bucket-sort correctness is proved by `bucketSortByRank_correct`; the CLRS second moment `E[Σ n_i²] = n + n(n-1)/m` is proved as a true expectation over the explicit independent uniform input distribution `Fin n → Fin m` (`expectedBucketQuadraticCost_eq_secondMoment`), and the abstract expected cost is `O(n)` (`expectedBucketSortCost_isBigO`). Remaining: RAM/step-count cost semantics. |
| Chapter 9 randomized SELECT expected time | `proved` | Proved in `CLRSLean/Chapter_09/Section_09_3_Deterministic_Select/Randomized_Select.lean`: `randSelectExpectedCost` models the uniform independent-pivot expected cost via `CLRS.Probability.expect`, `randSelectExpectedCost_recurrence` derives the CLRS recurrence, and `randomizedSelect_expected_bigO_linear` gives `E[T(n)] = O(n)` (CLRS Theorem 9.2). Remaining refinement: a joint distribution over all recursion levels and a concrete step-count cost model. |
| Chapter 9 deterministic linear-time SELECT | `proved-abstract` | Pivot-parametric deterministic SELECT correctness is proved by `deterministicSelect?_correct`; executable median-of-medians SELECT correctness is proved by `medianOfMediansSelect?_correct`; the local five-element median certificate is proved by `medianOfFive?_certificate`; executable full-input split-count bounds are proved by `fullGroupsOfFive_medianPivot_fullInput_split_counts`; the `7n/10 + O(1)` branch-size bound is proved by `medianOfMediansPivot?_partition_size_bound`; the abstract recurrence induction, linear bound, and CLRS-facing recurrence wrapper are proved by `selectRecurrence_linear_induction`, `medianOfMedians_linear_bound`, and `clrsSelectRecurrence_linear_bound`. A concrete executable cost counter `medianOfMediansSelectCost` (same recursion as `medianOfMediansSelect?`) now has the explicit linear bound `medianOfMediansSelectCost k xs ≤ 17 * xs.length` (`medianOfMediansSelectCost_linear_bound`), via the generic `selectCost_linear_bound`. Remaining refinement: a fully operational RAM step-count that also unfolds the recursive cost of computing the pivot. |
| Maximum-subarray runtime analysis | `future-work` | Exhaustive-search, crossing-helper optimality, the executable combine step, and recursive split-tree/fuelled selector correctness are proved; runtime recurrence and RAM-cost refinement remain. |
| Chapter 4 concrete all-input Master-theorem instantiation | `proved` | Floor/ceiling exact-power extraction, generic all-input transfer, adjacent-power sandwich generation, the discrete critical-power, log-critical, and tail-dominated wrappers, packaged floor/ceiling cases 1/2/3, natural-exponent polynomial wrappers for cases 1/2, the real-log bridge and named case-1 wrappers, the real-log-log bridge and named case-2 wrappers, and the case-3 regularity bridge (connecting `tailDominatedScale` to `f(n)`) are all proved. |
| Hash-table expected-time analysis | `proved-abstract` | The finite-uniform bucket toolkit proves load-factor equality, nonnegativity, and single-insert expected-cost changes; under SUHA the expected chain length `α = n/m` and expected unsuccessful-search cost `1 + α` are proved as true expectations over the explicit independent uniform hashing distribution `Fin n → Fin m` (`expectedRandomChainLength_eq_loadFactor`, `expectedRandomUnsuccessfulSearchCost`). Remaining: successful-search analysis, random hash-*function* model, RAM/probe-count semantics. |
| Pointer-level linked lists and free lists | `future-work` | Requires an imperative memory model. |
| BST transplant and parent-pointer navigation | `proved` | `Zipper`-based parent-pointer layer: `searchIter_eq_search`, `transplant_preserves_ordered` (CLRS `TRANSPLANT`), `deleteViaTransplant_eq_delete`, and `successorZipper`/`predecessorZipper` equivalences are all proved. Only pointer-level in-place mutation (RAM) remains. |
| Chapter 12 executable pointer-level BST | `deferred-implementation` | All functional BST operations (search, insert, delete, successor, predecessor) are proved complete with iff specifications; the `Zipper` layer proves parent-pointer navigation and `TRANSPLANT` functionally. Only an imperative in-place memory model remains. |
| Chapter 15 DP executable tables | `proved` | Ch 15.1: `bottomUpRodRevenue` executable. Ch 15.2: `matrixChainOpt`, `matrixChainSplit`, `matrixChainReconstruct` all fully computable. Ch 15.4: `lcsLength` and `lcsReconstruct` executable with full optimality proof. Ch 15.5: `bottomUpOBST` executable. |
| B-tree structural invariants (occupancy, depth) | `future-work` | The current B-tree model is a membership-level specification with search/split/insert/delete proved correct against abstract key sets. Full structural invariants (node occupancy bounds, same-depth property, separator ordering) require a richer node representation and are a next-pass refinement target. |
| Fibonacci heap pointer-level model | `deferred-implementation` | All Fibonacci heap operations (make, insert, union, extractMin, decreaseKey, delete) are proved correct against a finite-set model; pointer handles, heap-ordered forest, cascading cut, and consolidation array require a pointer-level model.
| Red-black deletion and height | `blocked-design` | Executable insertion is proved; deletion/fixup still needs a case-stable invariant proof, followed by the logarithmic-height theorem. |
| Automatic MST exchange-path extraction | `proved` | `canonicalSimplePath_unique` and `exists_crossing_exchangePath_of_spanningTree` extract the crossing replacement edge and residual path connections automatically. |
| Prim's algorithm | `proved` | `PrimTrace` packages dynamic light-edge choices, and `prim_minimum_spanning_tree` proves the direct finite-graph MST conclusion for a complete certified run. |
| CLRS exercises | `future-work` | Keep the first pass focused on main textbook claims; add exercises after section interfaces stabilize. |
| Chapter-end problems | `future-work` | Treat as a second track with explicit priority and difficulty labels. |
| Full RAM semantics | `future-work` | Requires an imperative machine/cost semantics rather than only mathematical functions and recurrences. |
| General merge-sort recurrence | `future-work` | Needs floor/ceiling arithmetic and an asymptotic theorem for all input sizes. |

## Publication Value

The proof map is intentionally honest.  Completed sections show theorem names
that compile.  Partial sections expose the exact missing mathematical or
representation layer.  This lets future contributors pick a section without
reverse-engineering the project state.

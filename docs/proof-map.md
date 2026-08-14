# CLRS-Lean Proof Map

This ledger records what is proved, what is partial, and what is currently
deferred.  The canonical reader and contributor view is CLRS fourth edition.
Use [`clrs-fourth-edition-map.csv`](clrs-fourth-edition-map.csv) to interpret a
canonical chapter/section and locate its current theorem-bearing source.

For a coarser planning view, see
[`proof-status-board.md`](proof-status-board.md). That board prioritizes named
fourth-edition coverage gaps without duplicating the generated chapter counts.

## Edition And Compatibility Policy

The generated dashboard and `clrs-proof-progress.csv` contain the canonical 35
fourth-edition chapter rows.  The chapter headings below inventory the current
theorem-bearing source layout, so shifted third-edition source numbers are
legacy evidence rather than an alternative public numbering scheme.  In
particular, source Chapters 19, 20, and 33 are online/supplementary material;
fourth-edition Chapters 19, 20, and 33 mean disjoint sets, elementary graph
algorithms, and machine-learning algorithms respectively.

Existing unqualified `CLRSLean.Chapter_NN` imports and declarations are
supported through all `1.x` releases and for at least six months after the
facade release.  Removal can occur only in `2.0` or later, after both gates
pass.  Declaration namespaces migrate chapter by chapter; see
[`migrations/clrs4.md`](migrations/clrs4.md) for the active import map.  The
generated progress dashboard owns live counts and status labels; no historical
completed-prefix claim overrides that ledger.

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
  - `CLRS.Chapter02.MergeSortRecurrence.theta_n_log_n_on_exact_powers`
  - `CLRS.Chapter02.MergeSortRecurrence.theta_n_log_n_all_inputs`
- Proof pattern: divide and conquer, sortedness, permutation preservation,
  recurrence solving, Master Theorem on exact powers, all-input transfer via
  the Chapter 4.6 floor/ceiling sandwich bridge
- Current gap: full RAM execution cost is a future strengthening target; the
  arbitrary-size floor/ceiling recurrence now has the all-input Θ(n log n)
  bound.

The section proves functional correctness for merge sort using Lean's verified
`List.mergeSort` implementation.  It also proves the exact closed form of the
standard recurrence on input sizes `2^k`, the Θ(n log n) bound on exact powers
via the Master Theorem, and the all-input Θ(n log n) bound
(`theta_n_log_n_all_inputs`) for any monotone cost function satisfying the
arbitrary-size floor/ceiling recurrence.

## Chapter 3 - Growth of Functions

Fourth-edition mapping: legacy §3.1 supplies fourth-edition §§3.1--3.2, while
legacy §3.2 supplies fourth-edition §3.3.  Fourth-edition §§3.1--3.3 are
represented at the current mathematical interface: the shared-threshold
two-sided Θ witness and the little-o/little-omega algebra and duality wrappers
are proved in the §3.1 source.

### Section 3.1 - Asymptotic notation

- Lean source: `CLRSLean/Chapter_03/Section_03_1_Asymptotic_Notation.lean`
- Status: `proved`
- Main theorems:
  - `CLRS.Chapter03.isBigO_iff`
  - `CLRS.Chapter03.isLittleO_iff`
  - `CLRS.Chapter03.isBigOmega_iff`
  - `CLRS.Chapter03.isLittleOmega_iff`
  - `CLRS.Chapter03.isBigTheta_trans`
  - `CLRS.Chapter03.isBigTheta_iff_sharedThreshold`
  - `CLRS.Chapter03.isLittleO_reciprocal`
  - `CLRS.Chapter03.isBigO_reciprocal`
  - `CLRS.Chapter03.isLittleO_isBigO`
  - `CLRS.Chapter03.isLittleO_add`
  - `CLRS.Chapter03.isLittleO_mul`
  - `CLRS.Chapter03.isLittleO_comp`
  - `CLRS.Chapter03.isLittleOmega_scale`
  - `CLRS.Chapter03.isLittleOmega_add_dominated`
- Proof pattern: bridge CLRS discrete witnesses to Mathlib filters
- Current gap: none.

The section gives CLRS-facing names for O, Ω, Θ, o, and ω over functions
`ℕ → ℝ`, proves the textbook-style witness forms, and collects basic algebraic
rules.

### Section 3.2 - Standard functions

- Lean source: `CLRSLean/Chapter_03/Section_03_2_Standard_Functions.lean`
- Status: `proved`
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
  - `CLRS.Chapter03.coe_fib_closed_form`
  - `CLRS.Chapter03.isBigTheta_fib_goldenRatio`
  - `CLRS.Chapter03.goldenRatio_pow_div_sqrt5_sub_fib_abs_lt_half`
  - `CLRS.Chapter03.isLittleO_fib_exp`
  - `CLRS.Chapter03.isLittleO_exp_fib`
  - `CLRS.Chapter03.lgStar_of_le_one`
  - `CLRS.Chapter03.lgStar_of_two_le`
  - `CLRS.Chapter03.lgStar_zero`
  - `CLRS.Chapter03.lgStar_one`
  - `CLRS.Chapter03.lgStar_two`
  - `CLRS.Chapter03.lgStar_two_pow`
  - `CLRS.Chapter03.lgStar_monotone`
  - `CLRS.Chapter03.lgStar_le_log_add_one`
  - `CLRS.Chapter03.natLog_two_le_two_log`
  - `CLRS.Chapter03.isLittleO_lgStar_log`
- Proof pattern: reuse Mathlib asymptotic and factorial facts through the CLRS
  wrappers; `isBigTheta_log_factorial` uses Mathlib's Stirling approximation
  (`le_log_factorial_stirling`) for the lower bound and `n! ≤ n^n` for the
  upper bound; the base-2 and base-`b` comparisons and the polynomial/factorial
  chains are obtained by instantiation and transitivity through the existing
  wrappers (`isLittleO_pow_const_exp`, `isLittleO_exp_vs_factorial`,
  `isBigTheta_log_logb`, `Real.isLittleO_log_id_atTop`).  Fibonacci growth
  restates Mathlib's Binet formula `Real.coe_fib_eq` under the wrappers, bounding
  the negligible `ψ^n` term via `|ψ| < 1 < φ`; the iterated logarithm `lgStar` is
  a fresh well-founded recursion on `Nat.log 2`, with the `o(log n)` bound obtained
  by dominating `lgStar n` with `1 + log(log n)` and chaining `isLittleO_one_log`
  and `isLittleO_loglog_log`.
- Current gap: none.  The CLRS §3.2 standard-function comparison table is complete
  for the polynomial, logarithmic, exponential, harmonic, floor/ceiling, and
  factorial rows — including the adjacent hierarchy links
  `1 ≺ log (log n) ≺ log n ≺ n ≺ n^a ≺ 2^n ≺ n!` and the `log_b` base-change
  facts — and now also covers Fibonacci-number growth `F_n = Θ(φ^n)` (eq (3.25)
  closed form and eq (3.26) closest-integer bound) and the iterated logarithm
  `lg* n` (definition, tower recurrence, monotonicity, and `lg* n = o(log n)`).

This section renders the full Chapter 3 growth-of-functions table, including the
golden-ratio Fibonacci facts and the iterated logarithm.

## Chapter 4 - Divide and Conquer

Chapter 4 is not limited to the Master-method file.  The current development
now includes a maximum-subarray specification and costed executable theorem,
Strassen's 2 by 2 block algebra correctness theorem, recurrence layers for the
substitution and recursion-tree proof methods, the exact-power Master theorem
core, and an all-input asymptotic transfer bridge.  Section 4.6 now also proves the
adjacent-power bridge that generates power-sandwich witnesses from one-step
comparison-scale bounds, discrete case-1/2/3 Master-scale wrappers, packaged
  floor/ceiling Master cases, and natural-exponent polynomial comparison wrappers
  for cases 1 and 2.  A real-log bridge now connects the case-1 discrete scale
  to the textbook `n^(log_b a)` for all `a ≥ 1` and `b > 1`, and a real-log-log
  bridge connects the case-2 discrete scale to `n^(log_b a) log n`; exact/floor/
  ceiling case-1 and case-2 wrappers are exposed directly in those textbook
  scales.  The case-3 regularity bridge now connects the discrete
  tail-dominated scale to the textbook forcing function.  The algorithm-level
  maximum-subarray and Strassen runtimes are connected to their executions;
  remaining Chapter 4 work is lower-level representation and RAM refinement.

### Section 4.1 - Multiplying square matrices (fourth edition, native)

- Lean source: `CLRSLean/FourthEdition/Chapter_04/Section_04_1_Multiplying_Square_Matrices.lean`
- Status: `proved` for the recursive eight-product multiplication and its
  `Θ(n³)` runtime
- Main proved theorems:
  - `CLRS.Chapter04.mul2_eq_mul`
  - `CLRS.Chapter04.mulRec_correct`
  - `CLRS.Chapter04.mulRec_padOne_corner`
  - `CLRS.Chapter04.mul_runtime_bigTheta`
  - `CLRS.Chapter04.realLogScale_eight_two`
- Proof pattern: define the naive `2 × 2` block product and the recursive
  eight-product `mulRec` on the shared depth-indexed `SqMat` squares; prove
  correctness by induction on depth reducing to the `2 × 2` identity; discharge
  the `T(n) = 8 T(⌊n/2⌋) + n²` work recurrence through the Master-theorem
  case-1 wrapper, and identify the comparison scale at `a = 8, b = 2` with `n³`
- Current gap: a lower-level RAM/pseudocode cost model

### Section 4.6 - Proof of the continuous master theorem (fourth edition, native)

- Lean source: `CLRSLean/FourthEdition/Chapter_04/Section_04_6_Continuous_Master_Theorem.lean`
- Status: `proved` for the real geometric-series core and the three continuous
  cases, bridged to the discrete comparison scales
- Main proved theorems:
  - `CLRS.Chapter04.geomSum_le_of_lt_one`
  - `CLRS.Chapter04.geomSum_eq_of_one`
  - `CLRS.Chapter04.geomSum_bigTheta_of_gt_one`
  - `CLRS.Chapter04.continuousWork_eq_geomSum`
  - `CLRS.Chapter04.continuous_master_case1`
  - `CLRS.Chapter04.continuous_master_case2`
  - `CLRS.Chapter04.continuous_master_case3`
  - `CLRS.Chapter04.continuous_case1_scale_eq_criticalPowerScale`
  - `CLRS.Chapter04.continuous_case2_criticalPowerLogScale_eq`
- Proof pattern: unroll the exact-division recurrence into a real geometric
  sum whose three cases are governed by the ratio `a / b^p`; factor the
  recursion-tree work as `b^(p·k)` times the geometric series; bridge the
  continuous `a^k` and `k·a^k` scales to the discrete `criticalPowerScale` and
  `criticalPowerLogScale`
- Current gap: floors, ceilings, and non-polynomial forcing remain in the
  legacy all-input file

### Section 4.7 - Akra-Bazzi recurrences (fourth edition, native)

- Lean source: `CLRSLean/FourthEdition/Chapter_04/Section_04_7_Akra_Bazzi.lean`
- Status: `proved` for the root equation, the single-branch corollary, the
  two-branch root instance, the multi-branch root uniqueness and nonnegativity,
  the scale-invariance bridge, the integral machinery, the two-sided increment
  bounds, and the recurrence-to-integral comparison — the upper bound
  `T(n) = O(n^p(1 + I n))` for arbitrary `p > 0`, `q ≥ 0`, and the matching
  lower bound (hence `Θ(n^p(1 + I n))`) in the forcing-dominated regime
  `p + 1 ≤ q`
- Main proved theorems:
  - `CLRS.Chapter04.rpow_realLogExponent`
  - `CLRS.Chapter04.akraBazziRoot_single`
  - `CLRS.Chapter04.akraBazziRoot_single_unique`
  - `CLRS.Chapter04.akraBazziRoot_two_thirds_one`
  - `CLRS.Chapter04.akraBazzi_single_branch_corollary`
  - `CLRS.Chapter04.akraBazziRoot_unique`
  - `CLRS.Chapter04.akraBazziRoot_nonneg`
  - `CLRS.Chapter04.akraBazzi_root_scale_invariance`
  - `CLRS.Chapter04.akraBazziIntegral_mono`
  - `CLRS.Chapter04.akraBazziIntegral_sub`
  - `CLRS.Chapter04.akraBazziIntegral_lower_const`
  - `CLRS.Chapter04.akraBazziIntegral_bounded_of_lt`
  - `CLRS.Chapter04.akraBazziIntegral_tail_lower`
  - `CLRS.Chapter04.akraBazziIntegral_tail_upper`
  - `CLRS.Chapter04.akraBazzi_increment_lower`
  - `CLRS.Chapter04.akraBazzi_increment_upper_single`
  - `CLRS.Chapter04.akraBazzi_increment_upper`
  - `CLRS.Chapter04.akraBazzi_increment_lower_multi`
  - `CLRS.Chapter04.akraBazzi_scale_decomp`
  - `CLRS.Chapter04.akraBazzi_T_nonneg`
  - `CLRS.Chapter04.akraBazzi_T_ge_g`
  - `CLRS.Chapter04.akraBazzi_integral_le_poly`
  - `CLRS.Chapter04.akraBazzi_upper_bound`
  - `CLRS.Chapter04.akraBazzi_lower_bound`
  - `CLRS.Chapter04.akraBazzi_bigTheta`
- Definitions: `akraBazziIntegral` / `akraBazziScale` (the discrete integral and
  scale `n^p(1 + Σ g/u^(p+1))`), `akraBazziIncrement` (the per-branch increment
  `a (n/b)^p (I n - I ⌊n/b⌋)`), `PolynomialGrowth` (the explicit
  polynomial-smoothness predicate `c n^q ≤ g n ≤ C n^q`), and
  `SatisfiesAkraBazzi` (the recurrence `T(n) = Σ aᵢ T(⌊n/bᵢ⌋) + g(n)` with floor
  perturbation and constant base case)
- Proof pattern: characterize the root `Σ aᵢ/bᵢ^p = 1`; for one branch the root
  is `p = log_b a` via the real base-power identity; uniqueness follows from
  strict monotonicity of the characteristic function; nonnegativity from
  `charFun 0 = Σ aᵢ ≥ 1`; scale invariance `Σ aᵢ (n/bᵢ)^p = n^p` is the
  fundamental bridge from the root equation to the scale `n^p`.  The
  recurrence-to-integral comparison expands one level of the tree and squeezes
  the per-level increment `Σ aᵢ (n/bᵢ)^p (I n - I ⌊n/bᵢ⌋)` against `g n` from
  both sides; the upper bound absorbs `g n` via the lower increment bound, and
  the lower bound (in the forcing-dominated regime) absorbs the scale via the
  upper increment bound and `T n ≥ g n`
- Current gap: the lower recurrence-to-integral comparison in the leaf-dominated
  and critical regimes `q ≤ p` (which requires the sub-leading floor-loss
  analysis of the deep recursion tree)

### Section 4.1 - The maximum-subarray problem

- Lean source: `CLRSLean/Chapter_04/Section_04_1_Maximum_Subarray.lean`
- Status: `proved` for functional correctness and the execution-attached
  abstract control-step runtime
- Main proved theorems:
  - `CLRS.Chapter04.mem_nonemptySubarrays_iff`
  - `CLRS.Chapter04.mem_crossingSubarrays_iff`
  - `CLRS.Chapter04.bestCandidate_correct`
  - `CLRS.Chapter04.maxCrossingSubarray_correct`
  - `CLRS.Chapter04.maxCrossingSubarray_isNonemptySubarray_append`
  - `CLRS.Chapter04.maxPrefixLinear_result_correct`
  - `CLRS.Chapter04.maxSuffixLinear_result_correct`
  - `CLRS.Chapter04.maxCrossingSubarrayLinear_result_correct`
  - `CLRS.Chapter04.subarray_append_left_or_right_or_crossing`
  - `CLRS.Chapter04.subarray_append_optimal_of_cases`
  - `CLRS.Chapter04.maxSubarrayDivideStep_correct`
  - `CLRS.Chapter04.maxSubarrayDivideTree_correct`
  - `CLRS.Chapter04.maxSubarrayDivideFuel_correct`
  - `CLRS.Chapter04.midpointSplitTree_unitLeaves`
  - `CLRS.Chapter04.maxSubarrayDivide_result_correct`
  - `CLRS.Chapter04.maxSubarrayDivideCosted_result`
  - `CLRS.Chapter04.maxSubarrayDivideCosted_correct`
  - `CLRS.Chapter04.maxPrefixLinearScoredWithCost_cost`
  - `CLRS.Chapter04.maxSuffixLinearScoredWithCost_cost`
  - `CLRS.Chapter04.maxCrossingSubarrayLinearScoredWithCost_cost`
  - `CLRS.Chapter04.maxSubarrayDivideCosted_cost_eq`
  - `CLRS.Chapter04.maxSubarrayDivideCost_unfold`
  - `CLRS.Chapter04.maxSubarrayDivideCost_monotone`
  - `CLRS.Chapter04.maxSubarrayDivideCost_power_sandwich`
  - `CLRS.Chapter04.maxSubarrayDivideCost_pow_two`
  - `CLRS.Chapter04.maxSubarrayDivideCost_isBigTheta_nlogn`
  - `CLRS.Chapter04.maxSubarray_exists_of_ne_nil`
  - `CLRS.Chapter04.maxSubarray_correct`
- Proof pattern: use exhaustive enumeration only as the specification; prove
  linear prefix/suffix/crossing scans optimal; show the midpoint tree has only
  empty or singleton leaves; prove the costed recursive execution erases to a
  correct selector; prove that the prefix/suffix/crossing counters equal the
  corresponding scan transitions; identify the recursive cost with the mixed
  recurrence `C(n / 2) + C(n - n / 2) + 3(n / 2) +
  2(n - n / 2) + 5`; and transfer exact power-of-two bounds to all inputs
  through monotonicity and adjacent-power sandwiching
- Current gap: the abstract metric counts recursive frames, scan transitions,
  and constant-size candidate choices.  It excludes explicit split-tree
  construction, integer-operation costs, `List` allocation/copying, and full
  RAM/pseudocode semantics.

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
  - `CLRS.Chapter04.master_case2_polylog_forcing`
- Proof pattern: unroll the exact-power recurrence after dividing by `a^i`,
  then prove bounded, constant, and tail-dominated normalized-forcing criteria.
  The polylog case-2 extension proves that polynomial normalized forcing
  `c·j^k ≤ forcing ≤ C·j^k` (the `f(n) = Θ(n^(log_b a)·log^k n)` textbook
  case) gives `T(b^i) = Θ((i+1)^(k+1)·a^i)`, using the
  `Σ_{j<i} j^k = Θ(i^(k+1))` sum bound.
- Current gap: none for the exact-power model.  The all-input floor/ceiling
  transfer is handled by Section 4.6, including the polylog case-2 wrapper
  `master_case2_polylog_forcing_all_input`.

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
  - `CLRS.Chapter04.criticalPowerLogPolylogScale`
  - `CLRS.Chapter04.criticalPowerLogPolylogScale_monotoneAbs`
  - `CLRS.Chapter04.criticalPowerLogPolylogScale_powerStepBound`
  - `CLRS.Chapter04.master_case2_polylog_forcing_all_input`
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

### Section 5.2 - Indicator random variables (hat-check problem)

- Lean source: `CLRSLean/Chapter_05/Section_05_2_Indicator_Random_Variables.lean`
- Status: `proved` for the uniform-permutation model over `Equiv.Perm (Fin n)`
- Main proved theorems:
  - `CLRS.Chapter05.permSendProb_eq`
  - `CLRS.Chapter05.probFixesPoint`
  - `CLRS.Chapter05.expectedFixedPoints_eq_one`
- Proof pattern: model a uniform random permutation as `Equiv.Perm (Fin n)` with
  the shared `fintypeExpect` toolkit; prove the image `π i` is uniform by
  translation invariance of the uniform measure under left multiplication by a
  transposition (`fintypeExpect_equiv`); conclude the fixed-point probability is
  `1/n`; sum the `n` fixed-point indicators with `fintypeExpect_sum` to get the
  expected number of fixed points `1` (hat-check, CLRS eq. (5.1)-(5.2))
- Current gap: none for the uniform-permutation model

### Section 5.3 - Randomized algorithms (RANDOMIZE-IN-PLACE)

- Lean source: `CLRSLean/Chapter_05/Section_05_3_Randomized_Algorithms.lean`
- Status: `proved` for the independent-swap-choice model
- Main proved theorems:
  - `CLRS.Chapter05.randomizeInPlace_injective`
  - `CLRS.Chapter05.randomizeInPlace_surjective`
  - `CLRS.Chapter05.randomizeInPlace_equiv`
  - `CLRS.Chapter05.randomizeInPlace_uniform` (Lemma 5.5: uniform random
    permutation)
- Proof pattern: model the swap choices as `ChoiceVector n = ∏_i Fin (n-i)`;
  define `randomizeInPlace` by induction on `n` using the liftPerm construction
  (swap 0 with position c0, then recurse on the remaining coordinates); prove
  injectivity by induction and surjectivity by a cardinality argument (both
  domain and codomain have cardinality n!); then the uniform measure on the
  choice space pushes forward to the uniform measure on permutations via
  `fintypeExpect_equiv`.
- Current gap: none for the current model; mutable-Array operational semantics
  for the shuffle loop remain a future refinement target.

### Section 5.4 - Probabilistic analysis

- Lean sources:
  - `CLRSLean/Chapter_05/Section_05_4_Probabilistic_Analysis.lean`
  - `CLRSLean/Chapter_05/Section_05_4_Probabilistic_Analysis/OnlineHiring.lean`
- Status: `proved` for the birthday/balls-and-bins product-uniform model, the
  longest-streak tail bound, the expected-longest-streak `Θ(log n)` upper and
  lower bounds, the executable finite on-line hiring strategy, the harmonic
  closed form of the on-line hiring success probability, and its `1/e`
  asymptotic
- Main proved theorems:
  - `CLRS.Chapter05.singleBinProb`
  - `CLRS.Chapter05.pairSameProb`
  - `CLRS.Chapter05.expectedCollisions_eq`
  - `CLRS.Chapter05.expectedBallsInBin_eq`
  - `CLRS.Chapter05.longestStreak_upperBound`
  - `CLRS.Chapter05.expectedLongestStreak_le` (`E[L] ≤ log2 n + 2`)
  - `CLRS.Chapter05.prob_noFullHeadBlock` (the exact `(1 - 2^{-k})^m` count)
  - `CLRS.Chapter05.expectedLongestStreak_lowerBound`
    (`E[L] ≥ log₂ n / 8` for `n ≥ 16`)
  - `CLRS.Chapter05.OnlineHiring.hiringStrategy_some_iff`
  - `CLRS.Chapter05.OnlineHiring.hiringStrategy_none_iff`
  - `CLRS.Chapter05.OnlineHiring.hiringStrategy_after_observation`
  - `CLRS.Chapter05.OnlineHiring.hiringStrategy_record`
  - `CLRS.Chapter05.OnlineHiring.hiringStrategy_some_iff_minInFirstK`
  - `CLRS.Chapter05.OnlineHiring.probBestAt`
  - `CLRS.Chapter05.OnlineHiring.probHireBest_eq` (the harmonic closed form)
  - `CLRS.Chapter05.OnlineHiring.probHireBest_asymptotic` (the `1/e` limit)
- Proof pattern: sample space `Fin k → Fin n` (each coordinate an independent
  uniform draw); re-derive the single-coordinate marginal (`singleBinProb = 1/n`)
  and pairwise-collision probability (`pairSameProb = 1/n`) from the toolkit's
  `fintypeExpect_equiv` / `fintypeExpect_fst` product independence; then linearity
  (`fintypeExpect_sum`) gives the birthday expectation `k(k-1)/(2n)` (CLRS
  eq. (5.8)) and the balls-in-bin occupancy `k/n` (CLRS eq. (5.10)).  For
  streaks, finite counting plus a union bound gives
  `Pr[longestStreak ≥ t] ≤ n / 2^t`, and the layer-cake identity gives
  `E[L] ≤ log2 n + 2`.  For the lower bound, partition the first `m = ⌊n/k⌋`
  positions into disjoint blocks of size `k`; the bijection
  `noFullHeadBlockBijection` (sequences ↔ per-block restrictions plus a free
  tail) gives the exact count `(2^k - 1)^m · 2^(n - m·k)` of sequences with no
  full block, so `Pr[no full block] = (1 - 2^{-k})^m`.  Since a full block is a
  run of `k` heads, `Pr[L < k] ≤ (1 - 2^{-k})^m`, and with
  `k = ⌊log₂ n / 2⌋`, `m = ⌊n/k⌋` the estimates `m ≥ 2^k` give
  `Pr[L ≥ k] ≥ 1/2`; the layer-cake lower bound `E[L] ≥ k·Pr[L ≥ k]` yields
  `E[L] ≥ log₂ n / 8` for `n ≥ 16`.  For on-line hiring, filter record
  positions after the observation threshold and select their minimum; the
  success probability conditions on the best candidate's position `j`, where
  the best is at `j` with probability `1/n` and the minimum of the first
  `j.val` positions is below the threshold `k` with probability `k/j.val` (a
  left-to-right score minimum), giving
  `probHireBest n k = (k/n)(H_{n-1} - H_{k-1})`.
- Executable definitions: `CoinFlip`, `hasRunOfLength`, `longestStreak`,
  `expectedLongestStreak`, `CLRS.Chapter05.OnlineHiring.hiringStrategy`, and
  `CLRS.Chapter05.OnlineHiring.probHireBest`
- Current gaps: none for the current model.  The expected-longest-streak lower
  bound `E[L] ≥ log₂ n / 8` (`expectedLongestStreak_lowerBound`) completes the
  `Θ(log n)` analysis; a tighter asymptotic `E[L] ∼ log₂ n` or a stronger
  constant remains optional future work.

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
- Costed source:
  `CLRSLean/Chapter_06/Section_06_4_Heapsort/CostedExecution.lean`
- Status: `proved` for the in-place CLRS loop refinement and its connected
  coarse unit control-step envelopes
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
  - `CLRS.Chapter06.maxHeapifyFuelWithCost_result`
  - `CLRS.Chapter06.maxHeapifyFuelWithCost_cost_le_fuel`
  - `CLRS.Chapter06.maxHeapifyFuelWithCost_cost_le_controlBound`
  - `CLRS.Chapter06.buildMaxHeapLoopWithCost_result`
  - `CLRS.Chapter06.buildMaxHeapLoopWithCost_cost_le`
  - `CLRS.Chapter06.arrayBuildMaxHeapWithCost_result`
  - `CLRS.Chapter06.arrayBuildMaxHeapWithCost_correct`
  - `CLRS.Chapter06.arrayBuildMaxHeapWithCost_cost_le`
  - `CLRS.Chapter06.arrayHeapSortStepWithCost_result`
  - `CLRS.Chapter06.arrayHeapSortStepWithCost_cost_le_heapSize`
  - `CLRS.Chapter06.arrayHeapSortInPlaceLoopWithCost_result`
  - `CLRS.Chapter06.arrayHeapSortInPlaceLoopWithCost_cost_le`
  - `CLRS.Chapter06.arrayHeapSortInPlaceWithCost_result`
  - `CLRS.Chapter06.arrayHeapSortInPlaceWithCost_cost_le`
  - `CLRS.Chapter06.arrayHeapSortInPlaceWithCost_correct_and_cost`
  - `CLRS.Chapter06.maxHeapifyControlBound_isBigO_n`
  - `CLRS.Chapter06.buildMaxHeapControlBound_isBigO_nsq`
  - `CLRS.Chapter06.heapSortControlBound_isBigO_nsq`
  - `CLRS.Chapter06.maxHeapifyFuelWithCost_cost_le_height`
  - `CLRS.Chapter06.maxHeapifyFuelWithCost_cost_le_log`
  - `CLRS.Chapter06.sum_heapHeight_le`
  - `CLRS.Chapter06.buildMaxHeapLoopWithCost_cost_le_height_sum`
  - `CLRS.Chapter06.buildMaxHeapLoopWithCost_cost_le_linear`
  - `CLRS.Chapter06.arrayHeapSortStepWithCost_cost_le_log`
  - `CLRS.Chapter06.arrayHeapSortInPlaceLoopWithCost_cost_le_log`
  - `CLRS.Chapter06.arrayHeapSortInPlaceWithCost_cost_le_log`
  - `CLRS.Chapter06.arrayHeapSortInPlaceWithCost_correct_and_log_cost`
  - `CLRS.Chapter06.maxHeapifyLogBound_isBigO_log`
  - `CLRS.Chapter06.buildMaxHeapLinearBound_isBigO_n`
  - `CLRS.Chapter06.heapSortNLogNBound_isBigO_nlogn`
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
  definitionally tied to this in-place loop.  The costed definitions mirror
  the same heapify, build, extraction-step, and shrinking-loop transitions;
  projection theorems recover the existing results, so correctness is reused
  rather than reproved.  The metric counts visited `MAX-HEAPIFY` frames and one
  extraction/swap transition for each nontrivial heapsort step.  Build-loop
  orchestration, guards, list operations, allocation, and calls are free in
  this model.  The tight bounds charge the same metric: a heapify run costs at
  most `floor(log2 heapSize) + 1` (each swap at least doubles `i + 1`), the
  bottom-up build costs at most `3 * heapSize` (double-counting node heights,
  `sum_heapHeight_le`), and the full heapsort costs at most
  `n * log2 n + 5 * n`.  The coarse `O(n)`, `O(n^2)`, `O(n^2)` envelopes remain
  as regression bounds.
- Current gap: the costs of guards and list operations, and a lower-level
  imperative array/RAM semantics, remain separate refinements.

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
  loop, returned pivot-index wrapper, adjacent-swap trace, and mutable-Array
  PARTITION refinement
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
  - `CLRS.Chapter07.dropLast_append_getLast`
  - `CLRS.Chapter07.perm_rotate_one`
  - `CLRS.Chapter07.partitionOnArray_size`
  - `CLRS.Chapter07.partitionOnArray_perm`
  - `CLRS.Chapter07.partitionOnArray_pivotIndex_lt`
  - `CLRS.Chapter07.partitionOnArray_left_bound`
  - `CLRS.Chapter07.partitionOnArray_right_bound`
  - `CLRS.Chapter07.partitionOnArray_correct`
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
  explicit: each partition side has length at most the original tail.  The
  mutable-Array PARTITION refinement (`partitionOnArray`) lifts the scan-state
  loop to an `Array α` interface and proves permutation preservation, pivot-index
  bounds, and prefix/suffix partition bounds via `by_cases` case analysis.
- Current gap: the probability-space interpretation of random pivots and sharper
  tail/lower-bound results are separate analysis targets

The section proves the mathematical correctness spine for quicksort before
introducing array mutation or probability.  The theorem
`CLRS.Chapter07.partitionAround_correct` packages the stable partition
classification, `CLRS.Chapter07.partitionLoop_correct` packages the scan-state
partition-loop invariant consequences,
`CLRS.Chapter07.clrsPartitionArray_correct` packages the returned pivot-index
postcondition, `CLRS.Chapter07.clrsPartitionArray_correct_with_trace` adds an
adjacent-swap trace, `CLRS.Chapter07.partitionOnArray_correct` extends the
correctness to a concrete mutable-Array `PARTITION` procedure, and
`CLRS.Chapter07.quickSort_correct` packages sortedness and permutation
preservation.  The mutable-Array refinement closes the index-level PARTITION gap,
completing the direct proof spine for Chapter 7.

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
  - `CLRS.Chapter07.expectedComparisons_isBigTheta_nlogn`
- Probability model theorems:
  - `CLRS.Chapter07.isFirst_prob` — symmetry lemma: P(s first in S) = 1/|S|
  - `CLRS.Chapter07.comparedInQuicksort` / `CLRS.Chapter07.compared_prob` — CLRS Thm 7.3
  - `CLRS.Chapter07.sum_compared_prob_eq_expectedComparisons` — the pairwise
    probability sum equals the closed-form expected-comparison sequence
- Proof pattern: define the CLRS expected-comparison sequence over rationals,
  expose the named closed form, prove the recurrence identity and telescoping
  relation, then bound the closed form by harmonic-number envelopes.
  The probability model adds uniform random permutation semantics via
  transposition-symmetry bijection on `Equiv.Perm (Fin n)`.
- Current gap: none for the selected mathematical scope.  A lower-level
  mutable-array execution-cost/RAM refinement is optional.

### Section 7.4 - Analysis of quicksort

- Lean source: `CLRSLean/Chapter_07/Section_07_4_Analysis_Of_Quicksort.lean`
- Status: `proved` for the expected running time of randomized quicksort
- Main proved theorems:
  - `CLRS.Chapter07.expectedRunningTime` — the expected running time,
    identified with the expected number of comparisons `E[X]` (each comparison
    performs O(1) work and dominates all other operations)
  - `CLRS.Chapter07.expectedRunningTime_eq_sum_compared_prob` — the indicator
    decomposition `E[X] = Σ_{i<j} P[z_i and z_j are compared] = Σ_{i<j} 2/(j-i+1)`
    (CLRS §7.4.2, connecting the §7.3 probability model to the closed form)
  - `CLRS.Chapter07.expectedRunningTime_le_two_mul` — `E[X] ≤ 2n·H_n`, an
    explicit O(n log n) upper bound
  - `CLRS.Chapter07.expectedRunningTime_isBigTheta_nlogn` — CLRS Theorem 7.1:
    the expected running time is `Θ(n log n)`
- Proof pattern: reuse the §7.3 expected-comparison closed form and the
  pairwise comparison-probability sum; the §7.4 layer frames these as the
  expected running time and restates the asymptotic bound as the expected-time
  theorem.
- Current gap: lower-level mutable-array execution-cost/RAM refinement and
  sharp tail bounds remain optional.

## Chapter 8 - Sorting in Linear Time

### Section 8.1 - Lower bounds for sorting

- Lean source: `CLRSLean/Chapter_08/Section_08_1_Lower_Bound_For_Sorting.lean`
- Status: `proved` for the decision-tree model over `Fin n` distinct elements
- Main proved theorems:
  - `CLRS.Chapter08.leafCount_le_two_pow_height`
  - `CLRS.Chapter08.run_injective_of_correctSort`
  - `CLRS.Chapter08.factorial_le_leafCount_of_correctSort`
  - `CLRS.Chapter08.height_le_logb_factorial`
  - `CLRS.Chapter08.factorial_sq_ge_pow_self`
  - `CLRS.Chapter08.logb_factorial_ge_half_mul_logb`
  - `CLRS.Chapter08.comparisonSort_worstCase_lowerBound`
- Proof pattern: model a comparison sort on `n` distinct elements as a binary
  decision tree `SortTree n` whose internal nodes compare two positions and
  whose leaves are labelled with output permutations.  Correctness of the tree
  (`CorrectSort`) means the run on input arrangement `π` reaches the leaf
  labelled `π⁻¹`, the unique sorted arrangement.  Since distinct inputs have
  distinct sorted arrangements, the run is injective; the counting lemma
  `card_le_leafCount_of_injective` then shows a correct tree has at least `n!`
  leaves.  Together with the combinatorial fact that a binary tree of height
  `h` has at most `2^h` leaves, this gives `h ≥ log₂(n!)`.  Finally the
  pairing bound `(n!)² ≥ nⁿ` (each factor pair `k`, `n+1-k` multiplies to at
  least `n`) yields `log₂(n!) ≥ (n/2)·log₂ n`, so the worst-case number of
  comparisons is at least `(n/2)·(log₂ n - 1)`, which is `Ω(n log n)`.
- Current gap: none for the decision-tree model.  RAM-level bookkeeping of
  individual comparisons through an execution semantics is out of scope.

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
  - `CLRS.Chapter08.textbookBucketSortCost`
  - `CLRS.Chapter08.fintypeExpect_textbookBucketSortCost_eq_expectedBucketSortCost`
  - `CLRS.Chapter08.expectedTextbookBucketSortCost_isBigO`
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
  `CLRS.Probability.expect_mul_of_indep`.  The random variable
  `textbookBucketSortCost` charges `n + Σⱼ nⱼ²`; its named expectation identity
  is `fintypeExpect_textbookBucketSortCost_eq_expectedBucketSortCost`, and
  `expectedTextbookBucketSortCost_isBigO` proves linear expectation.
- Current gap: a single-pass executable bucket builder, a costed per-bucket
  sorter, and a refinement theorem connecting their execution cost to the
  abstract model.  The current `bucketSortByRank` repeatedly filters the input,
  so `textbookBucketSortCost` is not an execution counter for it.

The executable wrapper `CLRS.Chapter08.bucketSortByRank` sorts each bucket with
Lean's verified `mergeSort`.  Its correctness theorem proves ordered output,
membership preservation, and permutation preservation under the deterministic
bucket interval hypothesis.  Separately,
`CLRS.Chapter08.textbookBucketSortCost` names the abstract textbook random
variable,
`CLRS.Chapter08.fintypeExpect_textbookBucketSortCost_eq_expectedBucketSortCost`
connects its expectation to the existing closed form, and
`CLRS.Chapter08.expectedTextbookBucketSortCost_isBigO` proves that expectation
is linear.  None of these theorems instruments `bucketSortByRank`.

## Chapter 9 - Medians and Order Statistics

### Section 9.1 - Minimum and maximum

- Lean source: `CLRSLean/Chapter_09/Section_09_1_Minimum_And_Maximum.lean`
- Status: `proved` for the executable pairwise simultaneous-extrema algorithm
- Main proved theorems:
  - `CLRS.Chapter09.minMax?_isSome_iff`
  - `CLRS.Chapter09.minMax?_correct`
  - `CLRS.Chapter09.minMax?_minimum_mem`
  - `CLRS.Chapter09.minMax?_maximum_mem`
  - `CLRS.Chapter09.minMax?_minimum_le`
  - `CLRS.Chapter09.minMax?_le_maximum`
  - `CLRS.Chapter09.minMax?_comparisons_le`
- Proof pattern: compare the two members of every pair once, merge the smaller
  member only with the recursive minimum, and merge the larger member only
  with the recursive maximum.  The bundled certificate proves membership and
  both extremal bounds; the recursive counter proves the CLRS bound
  `comparisons ≤ 3 * floor(n / 2)`.
- Current gap: none for the mathematical comparison model.

### Section 9.2 - Selection correctness interface

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
- Current gap: none for rank correctness or the fresh-choice expected
  comparison model.  The Section 9.2 support page proves both the CLRS
  majorizer and the actual state-dependent stochastic execution are linear.

The rank certificate handles duplicates directly.  If `selectByRank? k xs` or
`quickSelect? k xs` returns `x`, then `x ∈ xs`, the number of elements below
`x` is at most `k`, and the number of elements at most `x` is greater than
`k`.

### Section 9.3 - Selection in worst-case linear time

- Lean source: `CLRSLean/Chapter_09/Section_09_3_Deterministic_Select.lean`
- Status: `proved`; pivot-parametric and executable selector correctness,
  totality, partition-size bounds, and end-to-end comparison cost are proved
- Main proved theorems:
  - `CLRS.Chapter09.selectWithPivot?_mem`
  - `CLRS.Chapter09.selectWithPivot?_rankCorrect`
  - `CLRS.Chapter09.selectWithPivot?_correct`
  - `CLRS.Chapter09.selectWithPivot?_isSome_of_lt`
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
  - `CLRS.Chapter09.medianOfMediansPivot?_isSome_of_ne_nil`
  - `CLRS.Chapter09.medianOfMediansPivot?_partition_size_bound`
  - `CLRS.Chapter09.medianOfMediansSelect?_mem`
  - `CLRS.Chapter09.medianOfMediansSelect?_rankCorrect`
  - `CLRS.Chapter09.medianOfMediansSelect?_correct`
  - `CLRS.Chapter09.medianOfMediansSelect?_isSome_of_lt`
  - `CLRS.Chapter09.recursiveMedianOfMediansPivot?_mem`
  - `CLRS.Chapter09.recursiveMedianOfMediansPivot?_isSome_of_ne_nil`
  - `CLRS.Chapter09.recursiveMedianOfMediansPivot?_partition_size_bound`
  - `CLRS.Chapter09.recursiveMedianOfMediansSelect?_isSome_of_lt`
  - `CLRS.Chapter09.recursiveMedianOfMediansSelect?_correct`
  - `CLRS.Chapter09.deterministicPivot?_half_partition_size_bound`
  - `CLRS.Chapter09.recursiveMedianOfMediansPivotFuel?_partition_size_bound`
  - `CLRS.Chapter09.selectCost_linear_step`
  - `CLRS.Chapter09.selectCostFuel_linear_bound`
  - `CLRS.Chapter09.selectCost_linear_bound`
  - `CLRS.Chapter09.medianOfMediansPartitionPathCost_linear_bound`
  - `CLRS.Chapter09.recursiveMedianOfMediansPartitionPathCost_linear_bound`
  - `CLRS.Chapter09.recursiveMedianOfMediansComparisonCost_linear_bound`
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
  `recursiveMedianOfMediansComparisonCost` additionally charges full-group
  local work, recursive selection of the median of group medians, the current
  partition, and the selected strict branch.  A strengthened induction over
  the input size and both fuel parameters closes the concrete bound
  `recursiveMedianOfMediansComparisonCost k xs ≤ 100 * xs.length`.
- Current gap: none for the pure comparison model.

### Section 9.2 - Randomized SELECT expected running time

- Lean source: `CLRSLean/Chapter_09/Section_09_3_Deterministic_Select/Randomized_Select.lean`
- Status: `proved`; both the larger-side majorizer and fresh-choice actual
  expected comparison cost are linear
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
  - `CLRS.Chapter09.randomizedSelectMajorizer_bigO_linear`
  - `CLRS.Chapter09.freshRandomizedSelectWithRanks?_correct`
  - `CLRS.Chapter09.freshRandomizedSelectContinuationSize_le_subproblemSize`
  - `CLRS.Chapter09.freshRandomizedSelectExpectedComparisonsFuel_linear_bound`
  - `CLRS.Chapter09.freshRandomizedSelectExpectedComparisons_linear_bound`
  - `CLRS.Chapter09.randomizedSelectCostWithSchedule`
  - `CLRS.Chapter09.randomizedSelectCostWithSchedule_result`
  - `CLRS.Chapter09.randomizedSelectCostWithSchedule_rankCorrect`
  - `CLRS.Chapter09.randomizedSelectExpectedCostFuel`
  - `CLRS.Chapter09.randomizedSelectExpectedCostFuel_succ`
  - `CLRS.Chapter09.randomizedSelectExpectedCost_one`
  - `CLRS.Chapter09.randomizedSelectExpectedCost_nonneg`
  - `CLRS.Chapter09.randomizedSelectExpectedCost_le_randSelectExpectedCost`
  - `CLRS.Chapter09.randomizedSelectExpectedCost_linear_bound`
  - `CLRS.Chapter09.pivotAtIndex?_mem`
  - `CLRS.Chapter09.randomizedSelectAtIndex?_rankCorrect`
  - `CLRS.Chapter09.randomizedSelectAtIndex?_mem`
- Proof pattern: `randSelectExpectedCost c` is defined as the CLRS majorizing
  recurrence, where one step averages over a uniform pivot rank via the shared
  toolkit `CLRS.Probability.expect`
  (`expect_eq_fintypeExpect` restates that average as `CLRS.Probability.fintypeExpect`
  over the per-step sample space `Fin n`); `randSelectExpectedCost_recurrence`
  *derives* the CLRS recurrence `E[T(n+1)] = c(n+1) + expect (n+1) (fun i => E[T(max i (n-i))])`
  from that definition.  The linear bound `randSelectExpectedCost_le`
  (`E[T(n)] ≤ 4·c·n`) is the substitution method: the combinatorial core
  `four_mul_maxSideSum_le` proves `4·Σ_{i<n} max i (n-1-i) ≤ 3·n²` (via the
  two-step recurrence `maxSideSum_add_two`), which is the constant `< 1` the
  substitution needs. `randomizedSelectMajorizer_bigO_linear` packages this as
  `CLRS.Chapter03.isBigO (fun n => E[T n]) (fun n => (n : ℝ))`.
  `randomizedSelectCostWithSchedule` supplies the concrete cost-path semantics:
  every visited state consumes one occurrence rank and charges
  `c * currentLength`; exhausted or invalid schedules return `none`, and the
  result/rank-correctness theorems erase successful runs to
  `freshRandomizedSelectWithRanks?`.  The recursively nested expectation
  `randomizedSelectExpectedCostFuel` averages anew over the current `Fin n` at
  every state.  This is conditional-uniform sampling at each recursion level,
  not a flat distribution over variable-length schedules.  Rank correctness
  bounds each low or high continuation by the same larger-side recurrence term;
  `randomizedSelectExpectedCost_le_randSelectExpectedCost` proves the bridge for
  every input, rank, fuel value, and natural `c`, and
  `randomizedSelectExpectedCost_linear_bound` derives `E[C] ≤ 4 * c * n`.
  `randomizedSelectExpectedCost_one` records compatibility with the older
  unit-charge fresh-comparison expectation.
  Rank correctness is inherited by instantiating the Section 9.3
  pivot-parametric `selectWithPivot?` skeleton with an index pivot oracle
  (`randomizedSelectAtIndex?_rankCorrect`).
- Current gap: none for the finite fresh-choice partition-work model.  The
  metric does not charge `selectByRank?`'s specification sorting, RNG work,
  `List` primitives, allocation, or RAM operations, and no theorem identifies
  the nested process with a flat distribution on variable-length schedules.
  The older `randomizedSelectAtIndex? i` remains only a conditional correctness
  helper; it is not used as the probability model.

### Chapter 9 completion boundary

- Status: `main-proof-complete`.
- Stable interface test: `Tests/Chapter_09_Interface.lean`.
- Closure audit: `docs/proof-audits/chapter-09-closure-2026-07-15.md`.
- Sections 9.1--9.3 are complete for pure functional correctness and CLRS
  comparison/partition-work costs.  The randomized metric charges
  `c * currentLength` and uses nested current-state uniform choices; mutable
  arrays, concrete random-number generation, specification-selector/list costs,
  RAM timing, allocation, and instruction-level traces are later refinements.

## Chapter 10 - Elementary Data Structures

### Section 10.1 - Stacks and queues

- Lean source: `CLRSLean/Chapter_10/Section_10_1_Stacks_And_Queues.lean`
- Status: `proved` for the functional-list and array-backed models
- Main theorems:
  - `CLRS.Chapter10.pop_push`
  - `CLRS.Chapter10.dequeue_enqueue_empty`
  - `CLRS.Chapter10.dequeue_enqueue_nonempty`
  - `CLRS.Chapter10.length_enqueue`
  - `CLRS.Chapter10.arrayRead_arrayWrite_same` / `arrayRead_arrayWrite_other`
  - `CLRS.Chapter10.arrayPop_arrayPush`
  - `CLRS.Chapter10.arrayPop_empty` / `arrayPush_overflow`
  - `CLRS.Chapter10.arrayDequeue_arrayEnqueue_empty`
  - `CLRS.Chapter10.arrayDequeue_empty` / `arrayEnqueue_overflow`
  - `CLRS.Chapter10.arrayEnqueue_tail_wraps`
- Proof pattern: definitional equations over list-backed stacks and queues, and
  pointer-index equations over array-backed stores with overflow/underflow via
  `Option` and circular wrap-around via `Nat.mod`
- Current gap: none for the represented interface.  Concrete RAM execution,
  pointer mutation, and memory costs are deferred to a future execution model.

The section proves the algebraic behavior of stacks and queues using lists —
stack top is list head, and queue front is list head with enqueue at the back —
and, matching fourth-edition §10.1, the array-backed stack (top pointer) and
circular queue (head/tail pointers with wrap-around), with overflow and
underflow reported as `none`.

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

### Section 10.4 - Representing rooted trees

- Lean source: `CLRSLean/Chapter_10/Section_10_4_Rooted_Trees.lean`
- Status: `proved` for the functional rose-tree / left-child-right-sibling model
- Models: `CLRS.Chapter10.RoseTree` (multiway rooted tree: label plus
  `List (RoseTree α)` children) and `CLRS.Chapter10.LCRSTree` (binary
  left-child/right-sibling tree)
- Main theorems:
  - `CLRS.Chapter10.ofLCRSForest_toLCRSForest` (decode ∘ encode = id on forests)
  - `CLRS.Chapter10.toLCRSForest_ofLCRSForest` (encode ∘ decode = id on LCRS trees)
  - `CLRS.Chapter10.lcrsEquiv` (the round trip as an `Equiv` bijection
    `List (RoseTree α) ≃ LCRSTree α`)
  - `CLRS.Chapter10.ofLCRS_toLCRS` (single-tree round trip)
  - `CLRS.Chapter10.toLCRSForest_preorder` (preorder label sequence preserved)
  - `CLRS.Chapter10.toLCRSForest_numNodes` (node count preserved)
- Proof pattern: nested `RoseTree`/`List` recursion with `sizeOf`-based
  well-founded termination; functional induction via `toLCRSForest.induct`;
  structural induction on `LCRSTree`
- Current gap: the pointer/free-list RAM realization of the two-pointer node
  layout (imperative-memory epic); §10.3 pointers-and-objects is separate

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
  - `CLRS.Chapter11.pairCollisionProb`
  - `CLRS.Chapter11.expectedRandomSuccessfulSearchCost`
  - `CLRS.Chapter11.universal_expected_collisions`
  - `CLRS.Chapter11.universal_expected_search_cost`
- Proof pattern: deterministic bucket update/delete for a fixed hash function,
  plus a finite-uniform bucket expectation layer over `Fin m`.  The toolkit
  includes average additivity, nonnegativity, load-factor equality, and
  single-insert changes to total chain length, load factor, expected chain
  length, and unsuccessful-search cost.  The SUHA layer proves the expected
  chain length `α = n/m`, expected unsuccessful-search cost `1 + α`, the pairwise
  collision probability `1/m` (two-coordinate marginalisation of
  `CLRS.Probability.fintypeExpect` via `hashSplitPair`), and the expected
  successful-search cost `1 + (n-1)/(2m)` (CLRS Theorem 11.2), all as **true
  expectations** over the explicit independent uniform hashing distribution
  `Fin n → Fin m`.  A separate universal random-hash-*function* model
  (`IsUniversal`) bounds expected collisions by `α` and search cost by `1 + α`
  (CLRS Theorem 11.3) from the universality hypothesis alone.
- Current gap: RAM/probe-count operational semantics.

### Section 11.3 - Hash functions

- Lean source: `CLRSLean/Chapter_11/Section_11_3_Hash_Functions.lean`
- Status: `proved`
- Main proved theorems:
  - `CLRS.Chapter11.divisionHash_lt`, `CLRS.Chapter11.multiplicationHash_lt`: range bounds for the division and multiplication methods (CLRS §11.3, equations (11.1)-(11.3))
  - `CLRS.Chapter11.affineHash_isUniversal`: the exact `m = p` affine family over `ZMod p` is universal (CLRS Theorem 11.5, special case)
  - `CLRS.Chapter11.affineHash_expected_collisions`, `CLRS.Chapter11.affineHash_expected_search_cost`: expected collision and search-cost bounds for the affine family
  - `CLRS.Chapter11.affineHashMod_isUniversal`: the general mod-`m` affine family `h_{a,b}(k) = ((a·k + b) mod p) mod m` (`a ≠ 0`) is universal for any table size `m ≤ p` (CLRS Theorem 11.5, full form)
  - `CLRS.Chapter11.count_congruent_gt_le`, `CLRS.Chapter11.count_congruent_lt_le`, `CLRS.Chapter11.congruentPair_count_le`: residue-pair counting lemmas bounding the number of distinct residue pairs colliding modulo `m`
- Proof pattern: `affineHashMod_isUniversal` injectively maps colliding index pairs `(a,b)` into residue pairs `(r,s)` with `r ≠ s` and `r ≡ s (mod m)`, bounded by `p(p-1)/m`; the exact `m = p` case needs only the injectivity argument.
- Current gap: none for the represented interface; concrete bit-level hash-cost semantics remain an optional low-level refinement.

### Section 11.4 - Open addressing

- Lean source: `CLRSLean/Chapter_11/Section_11_4_Open_Addressing.lean`
- Status: `proved`
- Main proved theorems:
  - `CLRS.Chapter11.openSearch_eq_false_of_absent`, `CLRS.Chapter11.openSearch_openInsert`: functional-model correctness (absent key not found, inserted key found)
  - `CLRS.Chapter11.linearProbe_bijective`, `CLRS.Chapter11.doubleHashProbe_bijective`, `CLRS.Chapter11.quadraticProbe_zero`: the probe schemes of CLRS §11.4, equations (11.5)-(11.7)
  - `CLRS.Chapter11.probeTail_le_pow`: the per-factor uniform-hashing tail bound `(n-j)/(m-j) ≤ n/m`
  - `CLRS.Chapter11.expectedUnsuccessfulProbes_le` (Theorem 11.6): expected unsuccessful-search probes `≤ 1/(1-α)`
  - `CLRS.Chapter11.expectedInsertionProbes_le` (Corollary 11.7)
  - `CLRS.Chapter11.expectedSuccessfulProbes_le` (Theorem 11.8, harmonic form): `≤ (1/α) * ∑_{j<n} 1/(m-j) = (1/α)(H_m - H_{m-n})`
  - `CLRS.Chapter11.expectedSuccessfulProbes_le_ln` (Theorem 11.8, logarithmic form): `≤ (1/α) * ln(1/(1-α))`, obtained from the harmonic form via `CLRS.Chapter11.sum_inv_shift_le_log` (`∑_{j<n} 1/(m-j) ≤ ln(m/(m-n))`)
- Proof pattern: tail-sum expectation `E[X] = ∑_i P[X > i]` with the without-replacement tail products `probeTail`, bounded by the geometric series; the successful-search bound averages the unsuccessful-search costs over the `n` insertion times; the logarithmic form telescopes `∑_{j<n} ln((m-j)/(m-j-1))` from the bound `ln(1+x) ≥ x/(1+x)`.
- Current gap: deriving the tail probabilities from an explicit permutation sample space (via `Fintype` counting); RAM / probe-count cost semantics remain optional low-level refinements.

### Section 11.5 - Perfect Hashing

- Lean source: `CLRSLean/Chapter_11/Section_11_5_Perfect_Hashing.lean`
- Status: `proved`
- Main proved theorems:
  - `CLRS.Chapter11.PerfectHashTable` (structure)
  - `CLRS.Chapter11.perfectSearch_iff_mem`
  - `CLRS.Chapter11.perfectHash_collision_free_prob_ge_half`
  - `CLRS.Chapter11.perfectHash_expected_total_space_lt_2n`
  - `CLRS.Chapter11.perfectHash_prefix_fail_prob_le`
  - `CLRS.Chapter11.perfectHash_expected_trials_le_two`
  - `CLRS.Chapter11.exists_collision_free_secondary`
  - `CLRS.Chapter11.perfectHash_expected_bucket_cost_le`
  - `CLRS.Chapter11.perfectHash_expected_construction_time_le_const_n`
- Proof pattern: two-level perfect hash model (primary universal hash + per-bucket
  collision-free secondary hash).  Theorem 11.9 uses `pairCollisionProb` and
  `sum_upper_triangle` from §11.2 to bound the expected collision count, then
  Markov's inequality to convert to a probability bound.  Theorem 11.10 uses the
  algebraic identity `Σ_j n_j² = Σ_i Σ_k indicator(a i = a k)` and SUHA pairwise
  collision probability `1/n` to get `E[Σ_j n_j²] = 2n - 1 < 2n`.  Construction
  time chains the geometric trials bound (success probability ≥ 1/2 per
  secondary hash ⇒ expected trials ≤ 2 per bucket) with Theorem 11.10 to get
  expected O(n) total construction.
- Current gap: none for the represented interface; RAM cost semantics remain an
  optional low-level refinement.

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
  - `CLRS.Chapter12.BSTree.RepresentsW.tree_unique` (pointer heap determines a unique BST)
  - `CLRS.Chapter12.BSTree.RepresentsW.set_of_not_mem` (pointer frame rule)
  - `CLRS.Chapter12.BSTree.RepresentsW.of_agreeChild` (parent-write invisibility)
  - `CLRS.Chapter12.BSTree.transplantChild_left_representsW` (in-place TRANSPLANT, left)
  - `CLRS.Chapter12.BSTree.transplantChild_right_representsW` (in-place TRANSPLANT, right)
  - `CLRS.Chapter12.BSTree.transplantChild_left_refines_transplant` (refines functional zipper `transplant`)
  - `CLRS.Chapter12.BSTree.transplantChild_right_refines_transplant` (refines functional zipper `transplant`)
  - `CLRS.Chapter12.BSTree.insertPointer_right_representsW` (pointer TREE-INSERT leaf)
  - `CLRS.Chapter12.BSTree.searchCost_le_height` (O(h) search)
  - `CLRS.Chapter12.BSTree.minimumCost_le_height` / `maximumCost_le_height` (O(h) extrema)
  - `CLRS.Chapter12.BSTree.successorCost_le_height` / `predecessorCost_le_height` (O(h) neighbors)
  - `CLRS.Chapter12.BSTree.insertCost_le_height` (O(h) insertion)
  - `CLRS.Chapter12.BSTree.minKeyCost_le_height` / `deleteMinCost_le_height` (O(h) min extraction)
  - `CLRS.Chapter12.BSTree.deleteRootCost_le` / `deleteCost_le` (O(h) deletion, `2·height + 3`)
  - `CLRS.Chapter12.BSTree.isAncestorOf_iff_firstInInterval` (CLRS Lemma 12.3 ancestor characterization)
  - `CLRS.Chapter12.BSTree.insertAll_split` / `buildFromList_cons` (insert-order tree decomposition)
- Proof pattern: inductive tree membership, bound predicates, ordered invariant,
  extremal-path recursion, iff specifications for successor/predecessor,
  successor-replacement deletion, and a zipper (cursor + context path) layer
  encoding parent pointers, with all zipper operations proved equivalent to the
  functional operations via a `toTree` reconstruction bridge; plus an imperative
  pointer-heap layer (`Node` records with `left`/`right`/`parent` cells over a
  `Std.HashMap` store) whose `RepresentsW` abstraction bakes in acyclicity/no
  sharing, so in-place `TRANSPLANT` and `TREE-INSERT` are proved to refine the
  functional subtree-replacement specification via pointer frame rules.  The
  cost layer gives `height` and branch-faithful descent costs, each bounded by
  `height + 1` (deletion by `2·height + 3`); the randomly-built-BST layer proves
  `isAncestorOf_iff_firstInInterval` by strong induction on the list length with
  an `IsFirstInInterval` filter-invariance lemma
- Current gap: an explicit RAM cost model over the pointer operations remains
  future work; the imperative in-place child/parent pointer updates (TRANSPLANT
  and leaf TREE-INSERT) are now proved to refine the functional specification.
  The probability `P(i is an ancestor of j) = 1/(|i-j|+1)` and the resulting
  `O(log n)` expected-depth bound for a randomly built BST are not yet
  formalized; `isAncestorOf_iff_firstInInterval` is the needed foundation

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
BST interface.  Building on this, an imperative pointer-heap layer models nodes
as records with mutable `left`/`right`/`parent` cells over a `Std.HashMap`
store; the `RepresentsW` heap-to-tree abstraction bakes in the no-sharing
invariant, and in-place `TRANSPLANT` (both child sides) and leaf `TREE-INSERT`
are proved to refine functional subtree replacement.  It deliberately stops
before RAM cost semantics.

## Chapter 13 - Red-Black Trees

### Section 13.1 - Red-black trees

- Lean source: `CLRSLean/Chapter_13/Section_13_1_Red_Black_Trees.lean`
- Bundled interface:
  `CLRSLean/FourthEdition/Chapter_13/WellFormed.lean`
- Status: fourth-edition §13.1 is represented through the facade: the
  color/black-height properties and logarithmic-height theorem are proved.  The
  functional update layers for §§13.2--13.4 preserve both red-black shape and
  BST ordering; the bundled interface exposes those facts as one client-facing
  invariant.
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
  - `CLRS.Chapter13.RBTree.baldL`, `CLRS.Chapter13.RBTree.baldR`
    (deficit-absorbing deletion rebalancers)
  - `CLRS.Chapter13.RBTree.splitMin` (rebalancing minimum split)
  - `CLRS.Chapter13.RBTree.join` (in-order splice for two-child delete)
  - `CLRS.Chapter13.RBTree.del`, `CLRS.Chapter13.RBTree.delete` (executable RB-DELETE)
  - `CLRS.Chapter13.RBTree.BST` (BST ordering invariant)
  - `CLRS.Chapter13.RBTree.inTree_splitMin_mem`,
    `CLRS.Chapter13.RBTree.inTree_splitMin_iff` (splitMin membership)
  - `CLRS.Chapter13.RBTree.inTree_join_iff` (join preserves the union of key sets)
  - `CLRS.Chapter13.RBTree.inTree_del_forward`,
    `CLRS.Chapter13.RBTree.inTree_del_backward` (del membership preservation)
  - `CLRS.Chapter13.RBTree.not_inTree_del_self`,
    `CLRS.Chapter13.RBTree.not_inTree_delete_self` (the deleted key is absent)
  - `CLRS.Chapter13.RBTree.inTree_del_iff` (del removes exactly the target key)
  - `CLRS.Chapter13.RBTree.inTree_delete_iff` (headline deletion correctness)
  - `CLRS.Chapter13.RBTree.baldL_shape`, `CLRS.Chapter13.RBTree.baldR_shape`
    (rebalancers absorb a one-level black-height deficit)
  - `CLRS.Chapter13.RBTree.splitMin_invariant` (splitMin preserves the
    red-black invariants, dropping black height only at a black root)
  - `CLRS.Chapter13.RBTree.del_invariant` (inductive deletion certificate)
  - `CLRS.Chapter13.RBTree.redBlackShape_delete` (**deletion preserves
    red-black shape**)
  - `CLRS.Chapter13.RBTree.WellFormed` (red-black shape plus BST ordering)
  - `CLRS.Chapter13.RBTree.wellFormed_insert` /
    `CLRS.Chapter13.RBTree.wellFormed_delete`
  - `CLRS.Chapter13.RBTree.insert_correct` /
    `CLRS.Chapter13.RBTree.delete_correct` (bundled invariant and exact
    membership semantics)
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
  Deletion follows the Okasaki/Kahrs functional RB-DELETE design: `baldL` and
  `baldR` absorb a one-level black-height (doubly-black) deficit, `splitMin`
  rebalances on the way back up like `del`, and `join` handles the two-child
  case, rebuilding a red node directly when the right subtree is red-rooted.
  Membership correctness (`inTree_delete_iff`) is proved using the BST
  ordering invariant `BST`, and shape preservation (`redBlackShape_delete`)
  is proved from the `baldL_shape`/`baldR_shape` deficit certificates through
  the `splitMin_invariant` and `del_invariant` induction certificates.

The chapter now has executable insertion and deletion, exact key-set semantics,
the color/black-height certificate, BST preservation for rotations and both
updates, and logarithmic functional cost bounds.  `WellFormed` deliberately
bundles the otherwise separate `RedBlackShape` and `BST` predicates so clients
cannot accidentally report only half of correctness.  What remains is the
end-to-end pointer/fixup-loop refinement and a low-level RAM cost model.

### Section 13.2 (Fourth Edition) - Rotations

- Lean source: `CLRSLean/FourthEdition/Chapter_13/Section_13_2_Rotations.lean`
- Status: fourth-edition §13.2 `native`.  The pointer/sentinel red-black store
  (`RBNode`/`RBStore`), representation predicate (`StoreRepr`), and constant-cost
  pointer rotation/recolor primitives are defined, and rotations are proved to
  preserve both the inorder key list and the BST ordering invariant.
- Main proved theorems:
  - `CLRS.Chapter13.RBTree.keys_rotateLeft` / `keys_rotateRight`
  - `CLRS.Chapter13.RBTree.bst_rotateLeft` / `bst_rotateRight` / `bst_repaintRoot`
  - `CLRS.Chapter13.RBStore.get_set_eq` / `RBStore.get_set_ne` (frame)
  - `CLRS.Chapter13.rotateLeftP_cost` / `rotateRightP_cost` / `recolorP_spec`

### Section 13.3 (Fourth Edition) - Insertion

- Lean source: `CLRSLean/FourthEdition/Chapter_13/Section_13_3_Insertion.lean`
- Status: fourth-edition §13.3 `native`.  The RB-INSERT-FIXUP inorder bridge,
  BST output preservation, and the logarithmic execution-cost theorem are proved.
- Main proved theorems:
  - `CLRS.Chapter13.RBTree.keys_balanceLeft` / `keys_balanceRight`
  - `CLRS.Chapter13.RBTree.bst_balanceLeft` / `bst_balanceRight`
  - `CLRS.Chapter13.RBTree.bst_insert`
  - `CLRS.Chapter13.RBTree.insertCost_log_bound`

### Section 13.4 (Fourth Edition) - Deletion

- Lean source: `CLRSLean/FourthEdition/Chapter_13/Section_13_4_Deletion.lean`
- Status: fourth-edition §13.4 complete.  The logarithmic execution-cost
  theorem and the BST ordering preservation of the composed delete are both
  proved.
- Main proved theorems:
  - `CLRS.Chapter13.RBTree.deleteCost_log_bound`
  - `CLRS.Chapter13.RBTree.bst_delete` — RB-DELETE preserves the BST ordering
    invariant (via `bst_iff_sorted` and the `keys` sublist pipeline
    `keys_baldL`/`keys_baldR`/`keys_splitMin_cons`/`keys_join`/`keys_del_sublist`)

## Chapter 14 - Augmenting Data Structures

### Section 14.1 - Order-statistic trees

- Lean source: `CLRSLean/Chapter_14/Section_14_1_Order_Statistic_Trees.lean`
- Status: `partial` at fourth-edition §17.1.  Size augmentation and OS-SELECT are
  threaded through executable red-black insertion and deletion.
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
  - `CLRS.Chapter14.OSRBTree.wellSized_baldL`, `CLRS.Chapter14.OSRBTree.wellSized_baldR`
  - `CLRS.Chapter14.OSRBTree.wellSized_splitMin`, `CLRS.Chapter14.OSRBTree.wellSized_join`
  - `CLRS.Chapter14.OSRBTree.wellSized_del`
  - `CLRS.Chapter14.OSRBTree.wellSized_delete`
  - `CLRS.Chapter14.OSRBTree.storedSize_delete`
  - `CLRS.Chapter14.OSRBTree.osSelect?_delete_eq_rankSelect?`
  - `CLRS.Chapter14.OSRBTree.toRB_baldL`, `CLRS.Chapter14.OSRBTree.toRB_baldR`
  - `CLRS.Chapter14.OSRBTree.toRB_splitMin`, `CLRS.Chapter14.OSRBTree.toRB_join`
  - `CLRS.Chapter14.OSRBTree.toRB_del`
  - `CLRS.Chapter14.OSRBTree.toRB_delete`
  - `CLRS.Chapter14.OSRBTree.redBlackShape_toRB_delete`
  - `CLRS.Chapter14.OSRBTree.mem_keys_delete`
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
  transferring its shape and membership theorems.  The same mirroring now
  covers deletion: `baldL`/`baldR`/`splitMin`/`join`/`del`/`delete` rebuild
  every node with `mk`, so `wellSized_delete` keeps the size invariant through
  `RB-DELETE`, and `toRB_delete` refines Chapter 13's executable `RBTree.delete`,
  transferring `redBlackShape_delete` and `inTree_delete_iff`
  (`redBlackShape_toRB_delete`, `mem_keys_delete`).

This first pass captures the core mathematical idea of order-statistic trees:
the augmented size field is useful exactly because the selector can branch on
cached left-subtree sizes while remaining equivalent to the ideal rank selector.
The rotation layer now shows how the same size invariant can be locally
maintained during tree restructuring, and that local rotations preserve both
the ideal rank-selection semantics and the augmented selector's connection to
that ideal semantics on well-sized trees.  The recompute-then-rotate wrappers
also show that an arbitrary functional tree can be locally prepared for a
rotation and still expose the same ideal rank-selection behavior afterward.
OS-RANK, a combined BST/red-black/size invariant through updates, and logarithmic
query/update cost theorems remain.

### Section 14.3 - Interval trees and the general augmentation theorem

- Lean source: `CLRSLean/Chapter_14/Section_14_3_Interval_Trees.lean`
- Status: `partial` at fourth-edition §§17.2--17.3; proved for the static
  functional well-augmented BST search model, the general
  augmentation theorem (CLRS Theorem 14.1), the value-level red-black
  rotation bridge, and the general executable augmentation interface (an
  arbitrary augmentation threaded through executable red-black insertion and
  deletion; the insertion erasure refinement to Chapter 13 is also proved)
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
  - `CLRS.Chapter14.AugmentedRBTree.wellAugmented_mk`
  - `CLRS.Chapter14.AugmentedRBTree.storedAug_eq_realAug_of_wellAugmented`
  - `CLRS.Chapter14.AugmentedRBTree.wellAugmented_balanceLeft`
  - `CLRS.Chapter14.AugmentedRBTree.wellAugmented_balanceRight`
  - `CLRS.Chapter14.AugmentedRBTree.wellAugmented_insertFixup`
  - `CLRS.Chapter14.AugmentedRBTree.wellAugmented_insert`
  - `CLRS.Chapter14.AugmentedRBTree.wellAugmented_baldL`
  - `CLRS.Chapter14.AugmentedRBTree.wellAugmented_baldR`
  - `CLRS.Chapter14.AugmentedRBTree.wellAugmented_splitMin`
  - `CLRS.Chapter14.AugmentedRBTree.wellAugmented_join`
  - `CLRS.Chapter14.AugmentedRBTree.wellAugmented_del`
  - `CLRS.Chapter14.AugmentedRBTree.wellAugmented_delete`
  - `CLRS.Chapter14.AugmentedRBTree.storedAug_delete`
  - `CLRS.Chapter14.AugmentedRBTree.toRB_insertFixup`
  - `CLRS.Chapter14.AugmentedRBTree.toRB_insert`
  - `CLRS.Chapter14.AugmentedRBTree.inTree_toRB`
  - `CLRS.Chapter14.AugmentedRBTree.redBlackShape_toRB_insert`
  - `CLRS.Chapter14.AugmentedRBTree.mem_keys_insert`
  - `CLRS.Chapter14.AugmentedRBTree.sizeAug_wellAugmented_insert`
  - `CLRS.Chapter14.AugmentedRBTree.sizeAug_realAug_eq_length`
  - `CLRS.Chapter14.AugmentedRBTree.maxHighAug_wellAugmented_insert`
  - `CLRS.Chapter14.AugmentedRBTree.toRB_repaintRoot`
  - `CLRS.Chapter14.AugmentedRBTree.rootBlack_toRB`
  - `CLRS.Chapter14.AugmentedRBTree.toRB_empty_iff`
  - `CLRS.Chapter14.AugmentedRBTree.toRB_baldL`
  - `CLRS.Chapter14.AugmentedRBTree.toRB_baldR`
  - `CLRS.Chapter14.AugmentedRBTree.toRB_splitMin_min`
  - `CLRS.Chapter14.AugmentedRBTree.toRB_splitMin_tree`
  - `CLRS.Chapter14.AugmentedRBTree.toRB_join`
  - `CLRS.Chapter14.AugmentedRBTree.toRB_del`
  - `CLRS.Chapter14.AugmentedRBTree.toRB_delete`
- Proof pattern: use the generic `Augmentation`/`AugmentedTree` framework and
  its `IsRotationInvariant` law to maintain local cached values through
  recomputation, rotations, and BST insertion. Instantiate it with maximum
  interval high endpoints and subtree size, then prove that the CLRS
  interval-search pruning test is both sound and complete.  The generic
  `AugmentedRBTree` then threads an *arbitrary* augmentation through an
  executable red-black insertion whose Okasaki balancer rebuilds every node with
  the augmentation-recomputing smart constructor `mk`, so `wellAugmented_insert`
  follows by structural induction, and the augmentation-erasing projection `toRB`
  makes `insert` (at `natLt`) refine Chapter 13 `RBTree.insert`, transferring its
  shape and membership theorems.  The deletion mirror similarly rebuilds every
  node with `mk`, and `wellAugmented_delete` proves invariant preservation
  through `baldL`/`baldR`/`splitMin`/`join`/`del`/`delete`; the same erasure
  (`toRB_delete`, with the `toRB_baldL`/`toRB_baldR`/`toRB_splitMin`/
  `toRB_join`/`toRB_del` commutations) makes `delete` refine Chapter 13's
  `RBTree.delete`.  The `sizeAug` and `maxHighAug` fields are recovered as
  instances of this single interface.
- Current gaps: the generic deletion pipeline preserves the augmentation
  invariant (`wellAugmented_delete`) and refines Chapter 13's functional
  `RBTree.delete` (`toRB_delete`) for any `Augmentation`, but no theorem derives
  logarithmic update cost from a constant-time `combine`.  For interval trees,
  static search correctness and dynamic augmented red-black updates live on
  separate representations with no combined BST/red-black/max-high or
  search-after-update bridge; equal-low intervals also lack a distinct-key
  insertion policy.

### Section 17.1 (Fourth Edition) - Dynamic order statistics

- Lean source: `CLRSLean/FourthEdition/Chapter_17/Section_17_1_Dynamic_Order_Statistics.lean`
- Status: fourth-edition §17.1 `native`.  OS-RANK and its logarithmic query
  bound are proved.
- Main proved theorems:
  - `CLRS.Chapter14.OSRBTree.osRank` / `rankOf`
  - `CLRS.Chapter14.OSRBTree.osRank_eq_rankOf_of_wellSized`
  - `CLRS.Chapter14.OSRBTree.osRankCost_log_bound`

### Section 17.2 (Fourth Edition) - How to augment a data structure

- Lean source: `CLRSLean/FourthEdition/Chapter_17/Section_17_2_Augmenting_Data_Structures.lean`
- Status: fourth-edition §17.2 `native`.  The constant-time `combine` premise
  and the asymptotic augmentation update bound are proved.
- Main proved theorems:
  - `CLRS.Chapter14.augmentationUpdateCost`
  - `CLRS.Chapter14.augmentation_update_bound`

### Section 17.3 (Fourth Edition) - Interval trees

- Lean source: `CLRSLean/FourthEdition/Chapter_17/Section_17_3_Interval_Trees.lean`
- Status: fourth-edition §17.3 complete.  The dynamic/static bridge,
  search-after-update, and the Interval-keyed `O(log n)` search bound are all
  proved.
- Main proved theorems:
  - `CLRS.Chapter14.IntervalTree.intervalSearchCost_le_height`
  - `CLRS.Chapter14.AugmentedRBTree.toIntervalTree` / `wellAugmented_toIntervalTree`
  - `CLRS.Chapter14.intervalSearch_after_update`
  - `CLRS.Chapter14.AugmentedRBTree.toRB_low` / `intervalHeight_eq_toRB_height`
  - `CLRS.Chapter14.intervalSearchCost_log_bound` — interval search runs in
    `O(log n)` (composing `intervalSearchCost_le_height` with
    `RBTree.height_log_bound` via the low-keyed height erasure)

## Chapter 15 - Dynamic Programming

Fourth-edition mapping moves this legacy chapter to Chapter 14.  The four
represented examples carry their mathematical correctness results in the legacy
sources below; the native fourth-edition sections (§14.1–14.5) complete the
algorithm-and-cost boundary:

* §14.1 `CLRSLean/FourthEdition/Chapter_14/Section_14_1_Rod_Cutting.lean`:
  optimal-cut reconstruction (`rodCutFirstCut`, `rodCutPlan`), top-down
  memoization (`memoizedRodCut`), and the `O(n²)` step count (`rodCutStepCount`).
* §14.2 `CLRSLean/FourthEdition/Chapter_14/Section_14_2_Matrix_Chain_Multiplication.lean`:
  the tabulated `MATRIX-CHAIN-ORDER` time/space bounds (`matrixChainTime`,
  `matrixChainSpace`).
* §14.3 `CLRSLean/FourthEdition/Chapter_14/Section_14_3_Elements_Of_Dynamic_Programming.lean`:
  the reusable memo-cache invariant (`MemoCacheConsistent`) and the
  distinct-state cost bridge (`distinctCacheStates`).
* §14.4 `CLRSLean/FourthEdition/Chapter_14/Section_14_4_Longest_Common_Subsequence.lean`:
  the tabulated `Θ(mn)` bound (`lcsTableCells`).
* §14.5 `CLRSLean/FourthEdition/Chapter_14/Section_14_5_Optimal_Binary_Search_Trees.lean`:
  the public e/w/root tables (`obstRoot`), reconstruction (`obstReconstruct`),
  and cost bounds.

### Section 15.1 - Rod cutting

- Lean source: `CLRSLean/Chapter_15/Section_15_1_Rod_Cutting.lean`
- Status: `proved` for the mathematical cut-optimality layer and the mutable-array
  bottom-up implementation refinement
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
  - `CLRS.Chapter15.rodRevenueArrayAux_size`
  - `CLRS.Chapter15.arrGet_rodRevenueArrayAux`
  - `CLRS.Chapter15.rodRevenueArray_size`
  - `CLRS.Chapter15.rodRevenueArray_correct`
  - `CLRS.Chapter15.rodRevenueArray_full`
  - `CLRS.Chapter15.rodRevenueArray_rodCutTableRecurrence`
  - `CLRS.Chapter15.planValue_le_rodRevenueArray`
- Proof pattern: state the Bellman first-cut recurrence abstractly, expose a
  finite bottom-up table-prefix recurrence, prove every admissible first cut is
  bounded by the recurrence/table value, then induct over positive-piece
  cutting plans to prove global optimality certificates; finally build the CLRS
  `BOTTOM-UP-CUT-ROD` table as an `Array Nat` filled one `Array.push` at a time and
  prove by induction that every filled entry refines the pure recurrence value,
  from which the array read inherits `RodCutTableRecurrence` and the plan bound
- Current gap: top-down memoized-cache implementation and RAM-cost semantics remain
  future refinement targets

This first dynamic-programming proof establishes the textbook optimal
substructure argument and the correctness condition for a bottom-up table
prefix, then refines it to an executable mutable-`Array` bottom-up table whose
reads are proved equal to the pure recurrence value.

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
- Current gap: a tabulated/memoized implementation and its textbook cost model
  remain.  The pure recurrence evaluator (`matrixChainOpt`) and executable split
  reconstruction (`matrixChainReconstruct`, `matrixChain_correct`) are proved.
  The represented pure development is computable:
  `matrixChainOpt` evaluates the recurrence,
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
- Current gap: a memoized/tabulated Θ(mn) implementation and its cost theorem
  remain; the pure recurrence evaluator (`lcsLength`) and executable
  reconstruction (`lcsReconstruct`, `lcs_correct`) are proved.

### Section 15.5 - Optimal binary search trees

- Lean source: `CLRSLean/Chapter_15/Section_15_5_Optimal_Binary_Search_Trees.lean`
- Status: `proved`
- Main proved theorems:
  - `CLRS.Chapter15.OBST.BSTPlan.start_le_end`
  - `CLRS.Chapter15.OBST.obst_opt_le_planCost`
  - `CLRS.Chapter15.OBST.obst_reconstructed_cost_eq`
  - `CLRS.Chapter15.OBST.obst_reconstructed_optimal`
  - `CLRS.Chapter15.OBST.bottomUpOBST_obstRecurrence`
  - `CLRS.Chapter15.OBST.obst_correct`
- Proof pattern: represent a BST as an inductive plan over intervals, define
  expected search cost recursively, specify a candidate dynamic-programming
  optimum by the CLRS lower-bound recurrence, then prove by induction that every
  concrete plan costs at least the recurrence value.  A tight-root certificate
  layer records a root choice that attains the recurrence equality and proves
  that any plan reconstructed from it has exactly the optimum cost.  Finally,
  give a computable recurrence evaluator indexed by interval length and prove
  that it satisfies the recurrence.
- Current gap: a public executable e/w/root-table construction, reconstruction
  interface, and cost theorem remain.  The internal witness construction is
  private; the public `obst_correct` theorem proves existence of an optimal plan.

### Section 15.4 (Fourth Edition) - Offline caching

- Lean source:
  `CLRSLean/FourthEdition/Chapter_15/Section_15_4_Offline_Caching.lean`,
  split into sub-modules `S1_Cache_Model`, `S2_Farthest_In_Future`, and
  `S3_Optimality` under the same directory.  The final exchange proof is
  organized under `Optimality/Trace/A1_LegalTrace` through `A6_Iteration`.
- Status: `proved` for the mathematical finite-cache policy model.  The public
  theorem covers every finite request list and every nonempty finite initial
  cache; pointer/RAM implementations and hardware caching costs are outside
  this advertised boundary.
- Main theorems:
  - `CLRS.Caching.Policy` / `Policy.step` / `misses` / `nextUse`
  - `CLRS.Caching.Farther` / `farthestInFuture`
  - `CLRS.Caching.fifoPolicy` / `fifo_step_of_mem` / `fifo_step_fault`
  - `CLRS.Caching.fifo_step_size`
  - `CLRS.Caching.LegalTrace` / `policyTrace` /
    `traceMisses_policyTrace`: policy-independent legal executions and the
    bridge back to the original policy semantics
  - `CLRS.Caching.OnePageDiff`: exact one-page cache difference used by the
    local suffix coupling
  - `CLRS.Caching.exchange_trace`: replaces the first trace transition that
    disagrees with FIF, extends agreement by one boundary, and never increases
    total misses
  - `CLRS.Caching.exists_fully_agreeing_trace` / `fifo_optimal_trace`: finite
    iteration of the local exchange
  - `CLRS.Caching.fifo_optimal` (CLRS Theorem 15.5):
    `misses (fifoPolicy σ) C₀ σ ≤ misses π C₀ σ` for every policy `π` when
    `C₀.Nonempty`
- Proof pattern: turn policy runs into legal cache traces, couple two suffixes
  whose caches differ by exactly one page, use FIF's next-use maximality in an
  ordered phase, pay a later transformed-only miss with a local one-miss credit,
  then iterate the first-disagreement exchange over the finite request length.
- Historical note: the earlier global schedule state machine is retained only
  under `Dev/Legacy/StateMachine`.  Its known false invariants and search
  evidence are recorded in `Dev/Legacy/FAILED_APPROACHES.md`; no public module
  imports that route.  It is failure documentation, not a remaining section
  blocker.
- Current gap: none for the advertised mathematical cache-policy theorem.

## Chapter 16 - Greedy Algorithms

### Section 16.1 - Activity selection

- Lean source: `CLRSLean/FourthEdition/Chapter_15/Section_15_1_Activity_Selection.lean`
  (canonical fourth-edition Section 15.1; the legacy
  `CLRSLean/Chapter_16/Section_16_1_Activity_Selection.lean` forwards to it)
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

### Section 16.2 - Greedy-choice property and optimal substructure (meta-theorems)

- Lean source: `CLRSLean/FourthEdition/Chapter_15/Section_15_2_Greedy_Meta.lean`
  (canonical fourth-edition Section 15.2; the legacy
  `CLRSLean/Chapter_16/Section_16_2_Greedy_Meta.lean` forwards to it)
- Status: `proved` for the abstract structural lemmas
- Main results:
  - `CLRS.GreedyMeta.GreedyProblem` — abstract structure bundling the
    greedy-choice property and optimal substructure (CLRS §16.2)
  - `CLRS.GreedyMeta.gsolve` — generic recursive greedy solver
  - `CLRS.GreedyMeta.gsolve_optimal` — meta-theorem: any `GreedyProblem`
    instance admits an optimal greedy solution
  - `CLRS.GreedyMeta.GreedyChoiceProperty` — predicate form of Lemma 16.1
  - `CLRS.GreedyMeta.OptimalSubstructure` — predicate form of Lemma 16.2
- Proof pattern: the `GreedyProblem` structure packages the two §16.2
  structural lemmas as axioms; the meta-theorem `gsolve_optimal` proves
  greedy optimality by strong induction on the size measure.
- Current gap: concrete instantiations (activity selection, Huffman) are
  proved directly in their respective sections; a formal bridge recovering
  those results from the meta-theorem remains future work.

The section formalizes the CLRS §16.2 claim that any optimisation problem
with the greedy-choice property and optimal substructure can be solved
optimally by a greedy algorithm.  The abstract `GreedyProblem` structure
records the two properties as axioms; `gsolve` implements the generic
recursive greedy procedure; and `gsolve_optimal` proves its optimality by
strong induction on the problem size.

### Section 16.3 - Huffman codes

- Lean source: `CLRSLean/FourthEdition/Chapter_15/Section_15_3_Huffman_Codes.lean`
  (canonical fourth-edition Section 15.3; the legacy
  `CLRSLean/Chapter_16/Section_16_3_Huffman_Codes.lean` forwards to it)
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

### Section 16.4 - Matroids and greedy methods

- Lean source: `CLRSLean/Chapter_16/Section_16_4_Matroids.lean`
- Status: `proved`
- Reuses Mathlib's matroid library (`Mathlib.Combinatorics.Matroid.*`); does not
  redefine matroid theory.
- Main proved theorems:
  - `CLRS.Matroid16.greedy_isBasis` — the greedy output is a basis (maximal
    independent set) of the elements it scanned
  - `CLRS.Matroid16.greedy_optimal` — CLRS Theorem 16.10 / Corollary 16.11: over
    a nonincreasing-weight scan of the ground set, `greedy` returns a
    maximum-weight independent set
  - `CLRS.Matroid16.greedy_choice` — CLRS Theorem 16.6 (greedy-choice property)
  - `CLRS.Matroid16.optimal_substructure` — CLRS Lemma 16.7 (optimal
    substructure through the contraction `M ／ {x}`)
  - `CLRS.Matroid16.greedyRun_optimal` — self-contained optimality over a
    `Fintype`, sorting the ground set internally
- Proof pattern: per-threshold basis domination via `Matroid.Indep.augment_finset`
  plus a layer-cake weight decomposition; exchange for Theorem 16.6.
- Current gap: none for the current theorem statements (independent competitors
  are taken as coerced `Finset`s over a finite ground set).

The section defines a `WeightedMatroid` (a `Matroid α` with weights `w : α → ℕ`)
and the executable `greedy` fold.  The centerpiece `greedy_optimal` proves the
CLRS matroid greedy theorem: greedy restricted to each high-weight prefix is
again a greedy run, hence a basis of that threshold set, so it dominates every
independent set threshold-by-threshold; the layer-cake identity upgrades this to
weight domination.

### Section 16.5 - A task-scheduling problem as a matroid

- Lean source: `CLRSLean/Chapter_16/Section_16_5_Task_Scheduling.lean`
- Status: `proved`
- Reuses the §16.4 weighted-matroid greedy optimality theorem via
  `CLRS.Matroid16.greedyRun_optimal`.
- Main definitions:
  - `CLRS.SchedulingMatroid.scheduleIndependent` — independence predicate
    (`∀ t, N_t(A) ≤ t`, CLRS Lemma 16.12)
  - `CLRS.SchedulingMatroid.schedulingMatroid` — the task-scheduling matroid
    (CLRS Theorem 16.13)
  - `CLRS.SchedulingMatroid.Nt` — deadline-count function `N_t(A)`
- Main proved theorems:
  - `CLRS.SchedulingMatroid.schedulingMatroid` — `IndepMatroid.ofFinset`
    construction satisfying the three matroid axioms (empty, subset,
    augmentation); the augmentation proof picks a task of maximal deadline
    in `C \ A` and uses `|C| > |A|` to bound `N_t(A) + 1 ≤ N_t(C) ≤ t`
  - `CLRS.SchedulingMatroid.minPenaltySchedule_correct` — `greedyRun` on
    the scheduling matroid with penalty weights returns a maximum-penalty
    independent set (instantiation of §16.4 greedy optimality)
- Proof pattern: define `scheduleIndependent` via `N_t`; prove the finite
  matroid exchange axiom directly; construct the matroid via
  `IndepMatroid.ofFinset`; apply `greedyRun_optimal` for the optimality theorem.
- Current gap: none for the current theorem statement; an explicit
  earliest-deadline-first schedule construction remains a separate
  strengthening target.

## Chapter 17 - Amortized Analysis

- Lean source (canonical fourth-edition Sections 16.1-16.4; the legacy
  `CLRSLean/Chapter_17/Section_17_1_Amortized_Framework*` and
  `CLRSLean/Chapter_17/Section_17_4_Dynamic_Tables*` files forward to them):
  `CLRSLean/FourthEdition/Chapter_16/Section_16_1_Amortized_Framework.lean`,
  `CLRSLean/FourthEdition/Chapter_16/Section_16_1_Amortized_Framework/Section_16_2_Stack_And_Counter.lean`,
  `CLRSLean/FourthEdition/Chapter_16/Section_16_4_Dynamic_Tables.lean`, and
  `CLRSLean/FourthEdition/Chapter_16/Section_16_4_Dynamic_Tables/Section_16_4_Mutable_Array_Tables.lean`
- Status: `selected-section-complete`
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
- Optional refinements: general allocator/RAM cost semantics and broader
  amortized packaging for interleaved insert/delete traces.

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
  `CLRSLean/Chapter_18/Section_18_1_B_Tree_Model.lean`,
  `CLRSLean/Chapter_18/Section_18_1_B_Tree_Model/Search.lean`,
  `CLRSLean/Chapter_18/Section_18_1_B_Tree_Model/HeightBound.lean`,
  `CLRSLean/Chapter_18/Section_18_2_B_Tree_Insertion.lean`,
  `CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion.lean`,
  `CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/KeyMultiset.lean`,
  `CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/ExactReassembly.lean`,
  `CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/Exact.lean`, and the other
  `Section_18_3_B_Tree_Deletion/` invariant, repair, reassembly,
  preservation, projection, and root-normalization modules
- Insertion interface test: `Tests/Chapter_18_Insertion_Interface.lean`
- Height interface test: `Tests/Chapter_18_Height_Interface.lean`
- Status: `main-proof-complete-for-correctness`
- Main proved theorems:
  - `CLRS.Chapter18.BTree.search_correct`
  - `CLRS.Chapter18.BTree.search_true_iff`
  - `CLRS.Chapter18.BTree.search_true_of_mem`
  - `CLRS.Chapter18.BTree.mem_of_search_true`
  - `CLRS.Chapter18.BTree.search_false_iff`
  - `CLRS.Chapter18.BTree.search_false_of_not_mem`
  - `CLRS.Chapter18.BTree.not_mem_of_search_false`
  - `CLRS.Chapter18.BTree.findChild_localizes_mem`
  - `CLRS.Chapter18.BTree.searchExec`
  - `CLRS.Chapter18.BTree.searchExec_sound`
  - `CLRS.Chapter18.BTree.searchExec_complete`
  - `CLRS.Chapter18.BTree.searchExec_true_iff`
  - `CLRS.Chapter18.BTree.searchExec_eq_search`
  - `CLRS.Chapter18.BTree.minKeys_zero`
  - `CLRS.Chapter18.BTree.minKeys_pos`
  - `CLRS.Chapter18.BTree.one_le_minKeys`
  - `CLRS.Chapter18.BTree.minKeys_lower_bound`
  - `CLRS.Chapter18.BTree.minKeys_succ`
  - `CLRS.Chapter18.BTree.minKeys_le_succ`
  - `CLRS.Chapter18.BTree.minKeys_monotone_height`
  - `CLRS.Chapter18.BTree.totalKeys`
  - `CLRS.Chapter18.BTree.totalKeys_node`
  - `CLRS.Chapter18.BTree.nonRoot_totalKeys_add_one_lower_bound`
  - `CLRS.Chapter18.BTree.wellFormed_empty_or_totalKeys_add_one_lower_bound`
  - `CLRS.Chapter18.BTree.wellFormed_empty_or_minKeys_le_totalKeys`
  - `CLRS.Chapter18.BTree.wellFormed_minKeys_le_totalKeys`
  - `CLRS.Chapter18.BTree.wellFormed_height_log_bound`
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
  - `CLRS.Chapter18.BTree.splitRoot`
  - `CLRS.Chapter18.BTree.insertRoot`
  - `CLRS.Chapter18.BTree.splitRoot_keys_perm`
  - `CLRS.Chapter18.BTree.splitRoot_wellFormed`
  - `CLRS.Chapter18.BTree.splitRoot_height`
  - `CLRS.Chapter18.BTree.splitRoot_rootKeyCount`
  - `CLRS.Chapter18.BTree.splitRoot_nonFull`
  - `CLRS.Chapter18.BTree.insertRoot_keys_perm`
  - `CLRS.Chapter18.BTree.insertRoot_wellFormed`
  - `CLRS.Chapter18.BTree.insertRoot_height`
  - `CLRS.Chapter18.BTree.insertRoot_mem_iff`
  - `CLRS.Chapter18.BTree.insertRoot_wellFormedUnique`
  - `CLRS.Chapter18.BTree.insertRoot_mem_iff_insert`
  - `CLRS.Chapter18.BTree.insertRoot_search_eq_insert`
  - `CLRS.Chapter18.BTree.insertRoot_searchExec_true_iff`
  - `CLRS.Chapter18.BTree.insertRoot_correct`
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
  - `CLRS.Chapter18.BTree.composedDelete_packet` (one bundled induction for
    key containment, root-sensitive structural preservation, and raw height)
  - `CLRS.Chapter18.BTree.composedDelete_nonRoot_preserves`
  - `CLRS.Chapter18.BTree.composedDelete_rootResult`
  - `CLRS.Chapter18.BTree.keysOf_composedDelete_subset`
  - `CLRS.Chapter18.BTree.composedDelete_key_bound_lo`
  - `CLRS.Chapter18.BTree.composedDelete_key_bound_hi`
  - `CLRS.Chapter18.BTree.composedDelete_sameDepth_height`
  - `CLRS.Chapter18.BTree.composedDelete_sorted`
  - `CLRS.Chapter18.BTree.composedDelete_childBounded`
  - `CLRS.Chapter18.BTree.composedDelete_occupancy`
  - `CLRS.Chapter18.BTree.normalizeRoot_wellFormed`
  - `CLRS.Chapter18.BTree.composedDeleteRoot_keys_subset`
  - `CLRS.Chapter18.BTree.composedDeleteRoot_height`
  - `CLRS.Chapter18.BTree.composedDeleteRoot_wellFormed`
  - `CLRS.Chapter18.BTree.UniqueKeys`
  - `CLRS.Chapter18.BTree.WellFormedUnique`
  - `CLRS.Chapter18.BTree.findChild_pos_and_pred_eq_of_mem`
  - `CLRS.Chapter18.BTree.findChild_not_mem_child_of_ne`
  - `CLRS.Chapter18.BTree.findChild_selected_child_mem`
  - `CLRS.Chapter18.BTree.keyBag`
  - `CLRS.Chapter18.BTree.keyBag_erase_of_balance`
  - `CLRS.Chapter18.BTree.sortedRemove_keyBag`
  - `CLRS.Chapter18.BTree.mergeNodes_keyBag`
  - `CLRS.Chapter18.BTree.rotateRight_keyBag`
  - `CLRS.Chapter18.BTree.rotateLeft_keyBag`
  - `CLRS.Chapter18.BTree.replaceChild_keyBag_erase`
  - `CLRS.Chapter18.BTree.replacePredecessor_keyBag_erase`
  - `CLRS.Chapter18.BTree.replaceSuccessor_keyBag_erase`
  - `CLRS.Chapter18.BTree.spliceMerged_keyBag_erase`
  - `CLRS.Chapter18.BTree.rotateRight_reassembly_keyBag_erase`
  - `CLRS.Chapter18.BTree.rotateLeft_reassembly_keyBag_erase`
  - `CLRS.Chapter18.BTree.composedDelete_keyBag`
  - `CLRS.Chapter18.BTree.composedDelete_mem_iff_of_ne`
  - `CLRS.Chapter18.BTree.composedDelete_uniqueKeys`
  - `CLRS.Chapter18.BTree.composedDeleteRoot_keyBag`
  - `CLRS.Chapter18.BTree.composedDeleteRoot_mem_iff_of_ne`
  - `CLRS.Chapter18.BTree.composedDeleteRoot_not_mem`
  - `CLRS.Chapter18.BTree.composedDeleteRoot_mem_iff`
  - `CLRS.Chapter18.BTree.composedDeleteRoot_wellFormedUnique`
  - `CLRS.Chapter18.BTree.composedDeleteRoot_mem_iff_delete`
  - `CLRS.Chapter18.BTree.composedDeleteRoot_search_eq_delete`
  - `CLRS.Chapter18.BTree.composedDeleteRoot_correct`
- Proof pattern: mathematical key-set model, full structural invariant packet,
  base search success/failure wrappers, minimum-key expression
  base/positivity arithmetic and height monotonicity, specification-level
  split/insert/delete wrappers, Prop-level deletion direct wrappers,
  search correctness reuse,
  direct split validity/preservation corollaries, and direct inserted/deleted-key
  plus old-key successful and unsuccessful query preservation corollaries,
  direct insertion/deletion validity short-name wrappers, equality-key
  update-query wrappers, membership-driven search-after-update wrappers, old
  failed-search preservation wrappers, exact failed membership
  specifications, direct failed-membership preservation wrappers, bundled
  deletion induction, local merge/rotation repair packets, parent reassembly,
  root-sensitive raw results, one-step root normalization, exact multiset
  conservation through local reassembly, a global uniqueness layer, exact
  key-slot accounting, non-root and root augmented power lower bounds, and the
  CLRS logarithmic-height wrapper
- Top-level insertion boundary:
  - The flat `insert` operation remains the specification layer.
    `splitRoot` installs a full old root as the sole child of a transient empty
    parent and applies the existing full-child split.  The transient parent
    itself is not claimed `WellFormed`; `splitRoot_wellFormed` proves that the
    completed split output is.
  - `insertRoot` is the real top-level CLRS insertion operation.  It splits a
    full root before calling `insertNonFull`, and calls `insertNonFull` directly
    when the root is non-full.
  - `insertRoot_keys_perm` proves the exact `List.Perm` result
    `keysOf tr ++ [x]`; `insertRoot_wellFormed` proves the output invariant; and
    `insertRoot_height` gives the exact full-root conditional between unchanged
    height and height plus one.
  - `insertRoot_mem_iff` gives `y = x ∨ mem y tr`.
    `insertRoot_mem_iff_insert` and `insertRoot_search_eq_insert` prove
    specification membership/search compatibility, while
    `insertRoot_searchExec_true_iff` proves executable-search correctness.
    `insertRoot_wellFormedUnique` additionally assumes `¬ mem x tr`.
  - This is extensional compatibility only: no executable/specification
    tree-shape equality is claimed.  Section 18.2 is proved for the current
    functional correctness model.
- Exact deletion boundary:
  - For `2 ≤ t`, `composedDelete_keyBag` requires `NodeWF` and
    `composedDeleteRoot_keyBag` requires `WellFormed`; each applies
    `Multiset.erase`, removing one requested-key occurrence when present and
    changing nothing when absent.  The corresponding different-key membership
    theorems require no `UniqueKeys` premise and no premise that the requested
    key was present.
  - Raw uniqueness preservation requires only `NodeWF + UniqueKeys`.
    Root-level `WellFormedUnique` preservation, deleted-key absence, the full
    membership iff, and compatibility with specification `delete` require
    `WellFormedUnique`.  Compatibility is proved for membership and the
    membership-oracle `search`, not for executable `searchExec` or tree-shape
    equality.
- Correctness boundary: no core group remains for the current functional model.
  `totalKeys` counts `List` key slots without a uniqueness premise; the root
  theorem exposes the legal empty tree as an explicit disjunct; and
  for `2 ≤ t`, `wellFormed_height_log_bound` applies to every `WellFormed`
  tree.  Disk-page layout, pointer mutation, I/O counts, and RAM costs are
  optional lower-level refinements.

Chapter 18 now has the first-pass B-tree theorem surface, real top-level CLRS
insertion, and a structural proof for the executable CLRS deletion routine.
Search, split-child, specification insertion, and abstract deletion are proved
against a membership model, and
the update wrappers expose direct search-after-update specifications plus
direct split validity/preservation and inserted/deleted-key plus old-key query
preservation corollaries, direct insertion/deletion validity short-name
wrappers, equality-key update-query wrappers, membership-driven
search-after-update wrappers, exact unsuccessful-search specifications, and
direct old failed-search preservation wrappers.
The same specification layer now exposes exact failed membership facts for
split-child, insertion, and deletion.
Top-level `insertRoot` handles a full root by `splitRoot` followed by
`insertNonFull`; its exact add-one `List.Perm` semantics, structural
well-formedness, conditional height, membership, specification
membership/search compatibility, executable-search correctness, and
conditional uniqueness preservation are proved.  The empty wrapper used inside
`splitRoot` is transient rather than `WellFormed`, and no tree-shape equality
with flat specification `insert` is claimed.
The height expression is packaged with a height-zero base case, positivity
wrappers, an expression-level minimum-key fact and height-step recurrence,
plus adjacent and arbitrary-height monotonicity facts.  The structural
`totalKeys` theorem now connects that expression to actual B-trees: non-root
subtrees satisfy the augmented power lower bound, a well-formed root is either
the legal empty tree or satisfies the root lower bound, every nonempty
well-formed tree satisfies `minKeys`, and for `2 ≤ t` every well-formed tree
satisfies the CLRS logarithmic height theorem.  For executable deletion,
`composedDelete_packet` covers leaf, predecessor/successor, sibling rotation,
and sibling merge branches without duplicating the induction across
invariants.  A raw root may be the permitted one-child empty transient, so
only `composedDeleteRoot`, which applies `normalizeRoot` after
`composedDelete`, is stated to preserve root `WellFormed`; its height is
unchanged or decreases by one.  Under the same structural assumptions and
`2 ≤ t`, its `keyBag` is exactly the input bag after `Multiset.erase` removes
one requested-key occurrence when present, and every different key is
preserved without uniqueness or a requested-key-present premise.  Raw
uniqueness is preserved from `NodeWF + UniqueKeys`; under
`WellFormedUnique`, requested-key absence, the complete root membership
specification, combined structural/uniqueness preservation, and
membership-oracle search compatibility with `delete` are also proved.  No
`searchExec` or tree-shape equality with the specification operation is
claimed.  Together these results close Chapter 18's core correctness groups
for the current functional model.  Disk pages, pointers, I/O counts, and RAM
costs remain optional lower-level refinements.

## Legacy Source Chapter 19 - Fibonacci Heaps (Online Material)

- Lean source:
  `CLRSLean/Chapter_19.lean` and
  `CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model.lean`,
  `CLRSLean/Chapter_19/Section_19_2_Mergeable_Heap_Operations.lean`,
  `CLRSLean/Chapter_19/Section_19_3_Decreasing_A_Key_And_Deleting_A_Node.lean`,
  its `Amortized_Costs.lean` companion, and
  `CLRSLean/Chapter_19/Section_19_4_Bounding_Maximum_Degree.lean`
- Compatibility imports: the former `S1_ExecutableFibHeap`,
  `S2_CascadingCuts`, and `S3_AmortizedCosts` paths remain as import-only
  shims below Section 19.1.
- Status: `main-proof-complete-for-correctness`
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
  - `CLRS.Chapter19.FHNode.marks`
  - `CLRS.Chapter19.FHNode.forestMarks`
  - `CLRS.Chapter19.FH.cutChildAt`
  - `CLRS.Chapter19.FH.cutChildAt_keys`
  - `CLRS.Chapter19.FH.cutChildAt_heapOrdered`
  - `CLRS.Chapter19.FH.cutChildAt_wellformed`
  - `CLRS.Chapter19.FH.potential`
  - `CLRS.Chapter19.FH.potential_makeHeap`
  - `CLRS.Chapter19.FH.potential_insert`
  - `CLRS.Chapter19.FH.cutRootChildAt`
  - `CLRS.Chapter19.FH.cutRootChildAt_keys`
  - `CLRS.Chapter19.FH.cutRootChildAt_size`
  - `CLRS.Chapter19.FH.cutRootChildAt_roots_length`
  - `CLRS.Chapter19.FH.cutRootChildAt_good`
  - `CLRS.Chapter19.FH.cutRootChildAt_potential_eq`
  - `CLRS.Chapter19.FH.cutRootChildAt_potential_le`
  - `CLRS.Chapter19.FHNode.keyBag`
  - `CLRS.Chapter19.FHNode.forestKeyBag`
  - `CLRS.Chapter19.FHNode.forestSize`
  - `CLRS.Chapter19.FHNode.RootsUnmarked`
  - `CLRS.Chapter19.FH.keyBag`
  - `CLRS.Chapter19.FH.Represents`
  - `CLRS.Chapter19.FH.Valid`
  - `CLRS.Chapter19.FH.makeHeap_valid`
  - `CLRS.Chapter19.FH.insert_valid`
  - `CLRS.Chapter19.FH.union_valid`
  - `CLRS.Chapter19.FH.removeMinRoot`
  - `CLRS.Chapter19.FH.removeMinRoot_none_iff`
  - `CLRS.Chapter19.FH.removeMinRoot_perm`
  - `CLRS.Chapter19.FH.removeMinRoot_min`
  - `CLRS.Chapter19.FHNode.consolidateList_keyBag`
  - `CLRS.Chapter19.FHNode.consolidateList_forestSize`
  - `CLRS.Chapter19.FHNode.consolidateList_rootsUnmarked`
  - `CLRS.Chapter19.FH.extractMin`
  - `CLRS.Chapter19.FH.extractMin_correct`
  - `CLRS.Chapter19.FH.extractMin_keyBag`
  - `CLRS.Chapter19.FH.extractMin_valid`
  - `CLRS.Chapter19.FH.extractMin_degreeStrict`
  - `CLRS.Chapter19.FH.extractMin_size`
  - `CLRS.Chapter19.FH.extractMin_minimum`
  - `CLRS.Chapter19.FH.extractMin_mem_iff_of_ne`
  - `CLRS.Chapter19.FH.extractMin_none_iff`
  - `CLRS.Chapter19.FH.extractMin_none_iff_size_zero`
  - `CLRS.Chapter19.FH.cascadingCutRaw_correct`
  - `CLRS.Chapter19.FH.cascadingCutRaw_amortized`
  - `CLRS.Chapter19.FH.decreaseKeyAtRaw_correct`
  - `CLRS.Chapter19.FH.decreaseKeyAtRaw_amortized`
  - `CLRS.Chapter19.FH.deleteAtRaw_correct`
  - `CLRS.Chapter19.FH.Costed.extractMin_amortized_le_log`
  - `CLRS.Chapter19.FH.Costed.delete_amortized_le_log`
  - `CLRS.Chapter19.FH.Costed.traceAmortized_eq`
  - `CLRS.Chapter19.FH.Costed.run_amortized_le_bound`
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
  Fibonacci lower-bound recurrence plus a two-step doubling induction over even
  indices, a half-index bridge, a conditional binary-log degree budget, and an
  executable key-carrying forest with equal-degree bucket consolidation,
  exact multiset and real-size summaries, a global executable validity
  invariant, stable minimum-root selection, child promotion with mark clearing,
  executable extract-min through consolidation, exact one-occurrence deletion,
  index-addressed CUT, strong list-replacement balance lemmas, and exact
  root/mark potential accounting, duplicate-safe occurrence zippers,
  arbitrary-node cascading cuts, executable decrease/delete, and certified
  per-operation plus trace-level amortized costs
- Current gap: mutable circular pointer lists, allocation, and concrete RAM
  latency remain optional lower-level representation refinements.

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
even-index and half-index power-of-two lower bound.  Section 19.4 supplies the
concrete rooted-tree invariant and closes the true Fibonacci logarithmic degree
theorem; the abstract finite-set heap still uses a conservative degree budget
until it is refined to that tree model.  The executable `FHNode`/`FH` layer now
bridges those two views with an exact key multiset, real forest size, and
`FH.Valid`; its executable extract-min chooses a minimum root, promotes and
unmarks its children, invokes equal-degree `LINK`/`CONSOLIDATE`, removes exactly
one key occurrence, preserves validity, and leaves unique root degrees.  The
complete heap-level direct-child CUT preserves the represented key set, stored
size, heap order, and marked-tree wellformedness, adds exactly one root, and
changes `t(H) + 2m(H)` by exactly `1 - 2·mark(child)` (therefore by at most one).
The zipper refinement extends this to arbitrary occurrences (including
duplicate keys), implements CASCADING-CUT, decrease-key, and delete, and proves
their exact multiset/validity contracts.  The executable cost layer establishes
constant amortized decrease-key, logarithmic extract-min/delete, and a genuine
operation-trace telescope bounded by the sum of dynamic per-operation budgets.

### Section 19.1 - Fibonacci heaps

- Module: `CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model.lean`
- Model: an abstract finite key set with root/mark counters, operation
  contracts, minimum-query wrappers, and the standard potential.

### Section 19.2 - Mergeable-heap operations

- Module: `CLRSLean/Chapter_19/Section_19_2_Mergeable_Heap_Operations.lean`
- Model: persistent heap-ordered forests with exact key bags, cached minimum,
  `LINK`, degree-bucket `CONSOLIDATE`, and executable `extractMin`.

### Section 19.3 - Decreasing a key and deleting a node

- Module:
  `CLRSLean/Chapter_19/Section_19_3_Decreasing_A_Key_And_Deleting_A_Node.lean`
- Cost module:
  `CLRSLean/Chapter_19/Section_19_3_Decreasing_A_Key_And_Deleting_A_Node/Amortized_Costs.lean`
- Model: occurrence paths and zippers, arbitrary-node CUT and CASCADING-CUT,
  executable decrease-key/delete, and certified operation/trace amortized
  bounds.

### Section 19.4 - Bounding the maximum degree

- Module: `CLRSLean/Chapter_19/Section_19_4_Bounding_Maximum_Degree.lean`
- Model: a concrete rooted-tree type `CLRS.Chapter19.FTree` (a node carrying an
  ordered list of child subtrees) with `degree` and `size`, plus the CLRS
  Lemma 19.1 marked-tree invariant `CLRS.Chapter19.FTree.Wellformed`
  ("child in position `j` has degree at least `j - 1`", the invariant
  `CONSOLIDATE` and cascading cuts maintain).
- Tracked key theorems:
  - `CLRS.Chapter19.FTree.Wellformed`
  - `CLRS.Chapter19.FTree.wellformed_leaf`
  - `CLRS.Chapter19.FTree.sum_lb_from`
  - `CLRS.Chapter19.FTree.wellformed_size_ge_fibLowerBound` (Lemma 19.4:
    `size(x) ≥ F(d+2)`)
  - `CLRS.Chapter19.FTree.size_pos`
  - `CLRS.Chapter19.FTree.goldenRatio_pow_le_fibLowerBound` (`φ^d ≤ F(d+2)`)
  - `CLRS.Chapter19.FTree.wellformed_goldenRatio_pow_le_size` (`φ^d ≤ size`)
  - `CLRS.Chapter19.FTree.wellformed_degree_le_logb` (Lemma 19.5: `D(n) ≤ log_φ n`)
  - `CLRS.Chapter19.FTree.wellformed_degree_le_floor_logb` (`D(n) ≤ ⌊log_φ n⌋`)
  - `CLRS.Chapter19.FTree.wellformed_degree_le_twice_log_two` (`d ≤ 2·⌊log₂ n⌋ + 1`)
  - `CLRS.Chapter19.FTree.wellformed_append_child` (Lemma 19.1 preservation)
  - `CLRS.Chapter19.FTree.link`, `CLRS.Chapter19.FTree.link_degree`,
    `CLRS.Chapter19.FTree.link_wellformed` (the `CONSOLIDATE` equal-degree link)
  - `CLRS.Chapter19.FTree.minTree`, `CLRS.Chapter19.FTree.minTree_degree`,
    `CLRS.Chapter19.FTree.minTree_size`, `CLRS.Chapter19.FTree.minTree_wellformed`
  - `CLRS.Chapter19.FTree.exists_wellformed_size_eq_fibLowerBound` (the bound is
    tight: the extremal tree of degree `d` has size exactly `F(d+2)`)
- Proof pattern: an offset cons-induction numeric core (`sum_lb_from`) feeding a
  well-founded (`sizeOf`) tree induction for the subtree-size bound; a two-step
  strong induction using `φ² = φ + 1` for the golden-ratio bound; `Real.logb`
  monotonicity and `⌊·⌋` for the maximum-degree bound; and an append-child
  invariant-maintenance lemma reused by both `link` and the extremal `minTree`
  tightness family.
- Current gap: cached minimum pointers, stable node identity and arbitrary-node
  handles/paths, cascading cuts, executable decrease/delete, and amortized
  `O(log n)`/`O(1)` operation-cost theorems remain strengthening targets.
  Circular pointer mutation is a lower-level refinement.  The structural
  logarithmic-degree core, executable extract-min correctness, and the one-step
  direct-child CUT potential delta are sealed.

## Legacy Source Chapter 20 - van Emde Boas Trees (Online Material)

- Lean source:
  `CLRSLean/Chapter_20.lean`,
  `CLRSLean/Chapter_20/Section_20_1_VEB_Universe.lean`,
  `CLRSLean/Chapter_20/Section_20_2_VEB_Tree.lean`, and
  `CLRSLean/Chapter_20/Section_20_3_Recursive_VEB.lean`
- Status: `main-proof-complete-for-correctness`
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
  - `CLRS.Chapter20.uSize_succ` (recursive tower universe `2 ^ (2 ^ k)`)
  - `CLRS.Chapter20.VEBTree.toFinset_lt_uSize`
  - `CLRS.Chapter20.VEBTree.toFinset_empty`
  - `CLRS.Chapter20.VEBTree.member_correct` (recursive membership refinement)
  - `CLRS.Chapter20.VEBTree.insert_toFinset` (recursive insert refinement)
  - `CLRS.Chapter20.VEBTree.member_insert_iff`
  - `CLRS.Chapter20.VEBTree.member_insert_self`
  - `CLRS.Chapter20.VEBTree.memberCost_recurrence` (`T(u) = T(√u) + 1`)
  - `CLRS.Chapter20.VEBTree.memberCost_le`
  - `CLRS.Chapter20.VEBTree.log_uSize`
  - `CLRS.Chapter20.VEBTree.loglog_uSize`
  - `CLRS.Chapter20.VEBTree.depth_loglog_u`
  - `CLRS.Chapter20.VEBTree.veb_operation_bigO_loglog_u` (`O(log log u)`)
  - `CLRS.Chapter20.VEBTreeMM.MinCorrect`
  - `CLRS.Chapter20.VEBTreeMM.MaxCorrect`
  - `CLRS.Chapter20.VEBTreeMM.WellFormed`
  - `CLRS.Chapter20.VEBTreeMM.empty_wellFormed`
  - `CLRS.Chapter20.VEBTreeMM.minimum_correct`
  - `CLRS.Chapter20.VEBTreeMM.maximum_correct`
  - `CLRS.Chapter20.VEBTreeMM.insert_correct`
  - `CLRS.Chapter20.VEBTreeMM.insert_wellFormed`
  - `CLRS.Chapter20.VEBTreeMM.insert_toFinset`
  - `CLRS.Chapter20.VEBTreeMM.successor_spec`
  - `CLRS.Chapter20.VEBTreeMM.successor_correct`
  - `CLRS.Chapter20.VEBTreeMM.predecessor_spec`
  - `CLRS.Chapter20.VEBTreeMM.predecessor_correct`
  - `CLRS.Chapter20.VEBTreeMM.delete_correct` (invariant preservation and
    finite-set erasure refinement)
  - `CLRS.Chapter20.VEBTreeMM.delete_wellFormed`
  - `CLRS.Chapter20.VEBTreeMM.delete_toFinset`
  - `CLRS.Chapter20.VEBTreeMM.memberCost_le`
  - `CLRS.Chapter20.VEBTreeMM.insertCost_le`
  - `CLRS.Chapter20.VEBTreeMM.successorCost_le`
  - `CLRS.Chapter20.VEBTreeMM.predecessorCost_le`
  - `CLRS.Chapter20.VEBTreeMM.deleteCost_le`
  - `CLRS.Chapter20.VEBTreeMM.deleteDepth_le`
  - `CLRS.Chapter20.VEBTreeMM.veb_all_operations_bigO_loglog_u`
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
- Completion boundary: The recursive cached-min/max model now proves all seven
  vEB operations correct, with constant cached extrema and control-flow-aware
  O(log log u) bounds for the recursive operations. Concrete pointer/array
  allocation and hardware-level RAM timing remain a separate implementation
  refinement.

The recursive result combines a tower-universe summary/cluster representation,
detached-minimum and exact summary invariants, finite-set refinement for insert
and delete, strong least-greater/greatest-less specifications for neighbor
queries, and operation costs that follow the executable branch structure.
Deletion records work and depth separately: work counts the conditional second
summary call, while recursive depth remains at most `k + 1`.

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
  `CLRSLean/FourthEdition/Chapter_20/Section_20_1_Representing_Graphs.lean`
  (canonical fourth-edition Section 20.1; the legacy
  `CLRSLean/Chapter_22/Section_22_1_Representing_Graphs.lean` forwards to it)
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

- Lean source: `CLRSLean/FourthEdition/Chapter_20/Section_20_2_BFS.lean`
  (canonical fourth-edition Section 20.2; the legacy
  `CLRSLean/Chapter_22/Section_22_2_BFS.lean` forwards to it)
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

- Lean sources (canonical fourth-edition Section 20.3; the legacy
  `CLRSLean/Chapter_22/Section_22_3_DFS*` files forward to them):
  - `CLRSLean/FourthEdition/Chapter_20/Section_20_3_DFS.lean`
  - `CLRSLean/FourthEdition/Chapter_20/Section_20_3_DFS/S1_WhitePath.lean`
  - `CLRSLean/FourthEdition/Chapter_20/Section_20_3_DFS/S2_Intervals.lean`
  - `CLRSLean/FourthEdition/Chapter_20/Section_20_3_DFS/S3_Bridge.lean`
  - `CLRSLean/FourthEdition/Chapter_20/Section_20_3_DFS/S4_SCC.lean`
  - `CLRSLean/FourthEdition/Chapter_20/Section_20_3_DFS/S5_EdgeClassification.lean`
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

- Lean source: `CLRSLean/FourthEdition/Chapter_20/Section_20_4_Topological_Sort.lean`
  (canonical fourth-edition Section 20.4; the legacy
  `CLRSLean/Chapter_22/Section_22_4_Topological_Sort.lean` forwards to it)
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
  - `CLRSLean/FourthEdition/Chapter_20/Section_20_5_Strongly_Connected_Components.lean`
  - `CLRSLean/FourthEdition/Chapter_20/Section_20_5_Strongly_Connected_Components/MergeSortCongr.lean`
  (canonical fourth-edition Section 20.5; the legacy
  `CLRSLean/Chapter_22/Section_22_5_Strongly_Connected_Components*` files
  forward to them)
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
  `CLRSLean/FourthEdition/Chapter_21/Section_21_1_Growing_Minimum_Spanning_Trees.lean`
  (canonical fourth-edition Section 21.1; the legacy
  `CLRSLean/Chapter_23/Section_23_1_Growing_Minimum_Spanning_Trees.lean`
  forwards to it)
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

- Lean source: `CLRSLean/FourthEdition/Chapter_21/Section_21_2_Kruskal_And_Prim.lean`
  (canonical fourth-edition Section 21.2, with the nested
  `Section_21_2_Kruskal_And_Prim/S1_UnionFindBridge.lean`,
  `Section_21_2_Kruskal_And_Prim/S2_StatefulKruskal.lean`, and
  `Section_21_2_Kruskal_And_Prim/S3_ExecutablePrim.lean`; the legacy
  `CLRSLean/Chapter_23/Section_23_2_Kruskal_And_Prim*` files forward to them)
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

- Lean source: `CLRSLean/FourthEdition/Chapter_22/Section_22_1_Bellman_Ford.lean`
  (canonical fourth-edition Section 22.1; the legacy
  `CLRSLean/Chapter_24/Section_24_1_Bellman_Ford.lean` forwards to it)
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

### Section 24.2 - Single-source shortest paths in DAGs

- Lean source: `CLRSLean/FourthEdition/Chapter_22/Section_22_2_SSSP_In_DAGs.lean`
  (canonical fourth-edition Section 22.2; the legacy
  `CLRSLean/Chapter_24/Section_24_2_SSSP_In_DAGs.lean` forwards to it)
- Status: `proved`
- Topological order and acyclicity (over `WeightedGraph.Adj`):
  - `CLRS.Chapter24.WeightedGraph.IsTopoOrder`
  - `CLRS.Chapter24.WeightedGraph.IsAcyclic`
  - `CLRS.Chapter24.WeightedGraph.isAcyclic_of_isTopoOrder` (DAG hypothesis, for free)
  - `CLRS.Chapter24.WeightedGraph.idxOf_lt_of_split`
- Relaxation pass:
  - `CLRS.Chapter24.WeightedGraph.relaxFrom` (single-vertex out-edge relaxation)
  - `CLRS.Chapter24.WeightedGraph.dagRelax` (fold `relaxFrom` along the order)
  - `CLRS.Chapter24.WeightedGraph.dagRelax_respects_edge`
- Correctness:
  - `CLRS.Chapter24.WeightedGraph.le_add_walkWeight_of_respects` (path relaxation)
  - `CLRS.Chapter24.WeightedGraph.IsRealizable`
  - `CLRS.Chapter24.WeightedGraph.dagRelax_isRealizable`
  - `CLRS.Chapter24.WeightedGraph.dagRelax_isShortestDist` (CLRS §24.2 correctness)
- Work bound:
  - `CLRS.Chapter24.WeightedGraph.outdegree`
  - `CLRS.Chapter24.WeightedGraph.sum_outdegree`
  - `CLRS.Chapter24.WeightedGraph.dagSSSPWork`
  - `CLRS.Chapter24.WeightedGraph.dagSSSPWork_eq` (`Θ(V + E)`)
- Proof pattern: restate the topological-order predicate over `WeightedGraph.Adj`;
  split the fold at the processed vertex to show its estimate is already final and
  that processing it lowers each out-neighbor to `≤ d u + w u v`; telescope the
  per-edge upper bound along a walk for the lower bound; preserve realizability
  through the fold; and count `|V|` vertex visits plus `∑ outdegree = |E|` edge
  relaxations for the `Θ(V + E)` bound.

### Section 24.3 - Dijkstra's algorithm

- Lean source: `CLRSLean/FourthEdition/Chapter_22/Section_22_3_Dijkstra.lean`
  (canonical fourth-edition Section 22.3; the legacy
  `CLRSLean/Chapter_24/Section_24_3_Dijkstra.lean` forwards to it)
- Status: `proved` (greedy theorem, executable loop, and end-to-end correctness)
- Nonnegative-weight layer:
  - `CLRS.Chapter24.WeightedGraph.Nonneg`
  - `CLRS.Chapter24.WeightedGraph.walkWeight_nonneg`
  - `CLRS.Chapter24.WeightedGraph.noNegCycle_of_nonneg`
- Greedy correctness:
  - `CLRS.Chapter24.WeightedGraph.exists_crossing`
  - `CLRS.Chapter24.WeightedGraph.dijkstra_extractMin_correct` (CLRS Theorem 24.6)
- Executable state machine:
  - `CLRS.Chapter24.WeightedGraph.DijkstraState`
  - `CLRS.Chapter24.WeightedGraph.dijkstraInit` (source pre-settled with pre-relaxed edges)
  - `CLRS.Chapter24.WeightedGraph.dijkstraStep`
  - `CLRS.Chapter24.WeightedGraph.DijkstraInvariant`
  - `CLRS.Chapter24.WeightedGraph.dijkstraInit_invariant` (base case)
  - `CLRS.Chapter24.WeightedGraph.dijkstraStep_invariant` (inductive step)
  - `CLRS.Chapter24.WeightedGraph.dijkstraLoop`
  - `CLRS.Chapter24.WeightedGraph.dijkstraLoop_invariant` (loop preserves invariant)
  - `CLRS.Chapter24.WeightedGraph.dijkstraLoop_finish` (all settled after `|V|` steps)
  - `CLRS.Chapter24.WeightedGraph.dijkstraLoop_correct` (final `d v = δ v` for all `v`)
- Work bound:
  - `CLRS.Chapter24.WeightedGraph.dijkstraWork`
  - `CLRS.Chapter24.WeightedGraph.dijkstraWork_le_edge_log` (`O(E log V)`)
- Proof pattern: nonnegative walk-weight induction; frontier-crossing induction
  on the realizing shortest walk; and a `walkWeight` split at the frontier edge
  combined with the Section 24.1 shortest-distance lower bound and the Dijkstra
  relaxation invariants to force `d u = δ u` for the extracted minimum.
  `dijkstraInit` pre-settles the source (since `δ s = 0`) and pre-relaxes its
  outgoing edges so `DijkstraInvariant` holds initially; the proved step
  invariant lifts it through the loop; `dijkstraLoop_correct` composes with
  the settlement theorem to prove the final distance map equals `δ`.

- Deferred without reopening the mathematical milestone: per-edge relaxation
  ordering and mutable/RAM cost accounting for the abstract synchronous model.

### Section 24.5 - Proofs of shortest paths

- Lean source: `CLRSLean/FourthEdition/Chapter_22/Section_22_5_Shortest_Path_Properties.lean`
  (canonical fourth-edition Section 22.5; the legacy
  `CLRSLean/Chapter_24/Section_24_5_Shortest_Path_Properties.lean` forwards
  to it)
- Status: `proved` for the shortest-path distance function and the no-path,
  upper-bound, and triangle-inequality properties (CLRS Lemmas 24.11-24.13)
- Main proved theorems:
  - `CLRS.Chapter24.WeightedGraph.shortestDist`
  - `CLRS.Chapter24.WeightedGraph.shortestDist_isShortestDist`
  - `CLRS.Chapter24.WeightedGraph.noPath_iff_top`
  - `CLRS.Chapter24.WeightedGraph.shortestDist_le_walkWeight`
  - `CLRS.Chapter24.WeightedGraph.IsWalkFrom.append_edge`
  - `CLRS.Chapter24.WeightedGraph.shortestDist_triangleInequality`
- Proof pattern: define the single-source distance `δ(s, v)` as the Bellman-Ford
  relaxation after `|V| - 1` rounds (Theorem 24.4), so `shortestDist_isShortestDist`
  gives both the lower bound on every walk weight and the attainment/`⊤`
  dichotomy.  The no-path property is the `⊤` case of that dichotomy; the
  upper-bound property is the lower-bound conjunct; the triangle inequality
  appends the edge `(u, v)` to a realizing walk of `δ(s, u)` (via
  `IsWalkFrom.append_edge` and `walkWeight_append_singleton`) and applies the
  lower bound to the resulting `s → v` walk.
- Current gap: the subpath property (Lemma 24.10), convergence/path-relaxation
  (Lemmas 24.14-24.15), and predecessor-subgraph (Lemma 24.16) are not restated;
  Dijkstra correctness is proved in Section 24.3 and Bellman-Ford convergence in
  `relaxDist_stabilizes`.

## Chapter 25 - All-Pairs Shortest Paths

### Section 25.1 - All-Pairs Shortest Paths Model

- Lean source: `CLRSLean/FourthEdition/Chapter_23/Section_23_1_All_Pairs_Model.lean`
  (canonical fourth-edition Section 23.1; the legacy
  `CLRSLean/Chapter_25/Section_25_1_All_Pairs_Model.lean` forwards to it)
- Status: `proved` (under no negative-weight cycles)
- Main theorems:
  - `CLRS.Chapter24.WeightedGraph.weightMatrix` (edge-weight matrix W)
  - `CLRS.Chapter24.WeightedGraph.minPlusMul` (min-plus matrix product)
  - `CLRS.Chapter24.WeightedGraph.extendShortestPaths` (EXTEND-SHORTEST-PATHS)
  - `CLRS.Chapter24.WeightedGraph.L` (inductive distance sequence L^(m))
  - `CLRS.Chapter24.WeightedGraph.fasterAPSP` (FASTER-APSP algorithm)
  - `CLRS.Chapter24.WeightedGraph.lemma_25_1` (L^(m+1) = min_k (L^m_ik + w_kj))
  - `CLRS.Chapter24.WeightedGraph.L_sq_eq_minPlusMul` (Lemma 25.2: L^(2m) = L^m ◁ L^m)
  - `CLRS.Chapter24.WeightedGraph.fasterAPSP_eq_L` (fasterAPSP = L^(|V|-1) under NoNegCycle)
  - `CLRS.Chapter24.WeightedGraph.fasterAPSP_eq_shortestDist` (fasterAPSP = delta all-pairs)
  - `CLRS.Chapter24.WeightedGraph.minPlusMulCost` / `fasterAPSPCost` (O(V³)-per-squaring cost bound to `G`)
  - `CLRS.Chapter24.WeightedGraph.numSquarings_le_log2_add_one` (numSquarings = O(log |V|))
  - `CLRS.Chapter24.WeightedGraph.fasterAPSPCost_le_n_cubed_log` (**O(V³ log V)**)
  - `CLRS.Chapter24.WeightedGraph.fasterAPSPCost_le_n_four` (trivial O(V⁴) corollary)
- Proof pattern: min-plus algebra, repeated squaring, linking to Ch24's relaxDist for walk properties, fixpoint via monotonicity + attainability; the cost layer is bound to the actual `G` and `numSquarings` iteration count
- Current gap: none within Section 25.1.

The section builds the all-pairs shortest-path model on the Chapter 24 WeightedGraph
infrastructure.  The min-plus product and FASTER-APSP are defined, Lemmas 25.1 and
25.2 are proved as algebraic identities, and the correctness of FASTER-APSP is
established under the no-negative-cycles hypothesis by connecting L^(m) to the
Chapter 24 Bellman-Ford relaxation and proving L stabilises at |V|-1.

### Section 25.2 - Floyd-Warshall Algorithm

- Lean source: `CLRSLean/FourthEdition/Chapter_23/Section_23_2_Floyd_Warshall.lean`
  (canonical fourth-edition Section 23.2; the legacy
  `CLRSLean/Chapter_25/Section_25_2_Floyd_Warshall.lean` forwards to it)
- Status: `proved`
- Main declarations:
  - `CLRS.Chapter24.WeightedGraph.fwStep` (one Floyd-Warshall iteration)
  - `CLRS.Chapter24.WeightedGraph.D` (Floyd-Warshall DP recurrence)
  - `CLRS.Chapter24.WeightedGraph.floydWarshall` (full algorithm)
  - `CLRS.Chapter24.WeightedGraph.Pi` (predecessor matrix Π)
  - `CLRS.Chapter24.WeightedGraph.floydWarshallPi` (final predecessor matrix)
  - `CLRS.Chapter24.WeightedGraph.fwReconstructPath` (path reconstruction)
- Proved theorems:
  - `D_le_simpleWalk` (Lemma 25.7), `D_attainable`,
    `floydWarshall_isShortestDist` (Theorem 25.8)
  - `Pi_adj` (every predecessor follows a real edge)
  - `reconstructPathFuel_isWalkFrom` (the reconstructed predecessor path is a
    valid walk)
  - `reconstructPathFuel_weight_eq` (the reconstructed walk has weight
    `floydWarshall i j`)
  - `floydWarshall_nonneg_diag`, `negative_diagonal_implies_negative_cycle`
    (CLRS Theorem 25.3, negative-cycle detection)
  - `transitiveClosure_iff_exists_walk` (the Floyd-Warshall boolean variant
    exactly characterizes reachability)
  - `CLRS.Chapter24.WeightedGraph.fwStepCost` / `floydWarshallCost` (O(V³) cost model)
  - `CLRS.Chapter24.WeightedGraph.floydWarshall_O_cubed` (**O(V³)** work bound)
- Current gap: none within Section 25.2.

### Section 25.3 - Johnson's Algorithm

- Lean source: `CLRSLean/Chapter_25/Section_25_3_Johnsons_Algorithm.lean`
- Status: `proved` (reweighting algebra, potential construction, and end-to-end correctness)
- Main declarations and theorems:
  - `CLRS.Chapter24.WeightedGraph.johnsonAugmentedGraph`
  - `CLRS.Chapter24.WeightedGraph.no_incoming_to_none_johnsonAugmentedGraph`
  - `CLRS.Chapter24.WeightedGraph.isShortestDist_edge_ineq` — general triangle inequality
  - `CLRS.Chapter24.WeightedGraph.walk_johnsonAugmented_some_projection`
  - `CLRS.Chapter24.WeightedGraph.noNegCycle_johnsonAugmentedGraph` — negative-cycle preservation
  - `CLRS.Chapter24.WeightedGraph.reweightedWeight`
  - `CLRS.Chapter24.WeightedGraph.reweightedGraph`
  - `CLRS.Chapter24.WeightedGraph.reweightedWalkWeight_eq` — telescoping property
  - `CLRS.Chapter24.WeightedGraph.reweightedWeight_nonneg`
  - `CLRS.Chapter24.WeightedGraph.reweighted_isShortestDist` — shift formula
  - `CLRS.Chapter24.WeightedGraph.johnsonPotential` — Bellman-Ford potential
  - `CLRS.Chapter24.WeightedGraph.johnsonPotential_finite`
  - `CLRS.Chapter24.WeightedGraph.johnsonPotential_triangle` — Lemma 25.3
  - `CLRS.Chapter24.WeightedGraph.johnsonReweightedNonneg`
  - `CLRS.Chapter24.WeightedGraph.johnsonAllPairsDist` — Johnson distance function
  - `CLRS.Chapter24.WeightedGraph.johnsonAllPairsDist_correct` — Theorem 25.6
  - `CLRS.Chapter24.WeightedGraph.johnsonAugmentedGraph_edges_card` — the augmented
    graph has `|V| + |E|` edges
  - `CLRS.Chapter24.WeightedGraph.johnsonCost_eq` — exact `|V|·(|V|+|E|)·(log₂|V|+2)`
    running time (**O(V² log V + V E log V)**)
  - `CLRS.Chapter24.WeightedGraph.johnsonCost_le` — the `2·|V|·(|V|+|E|)·(log₂|V|+1)`
    O-bound corollary

### Chapter 25 remaining work

- Lower-level RAM / mutable-array machine-arithmetic accounting for the cost
  models; the reader-facing O(V³), O(V³ log V), and O(V² log V + V E log V)
  bounds are proved, and concrete word-level constants remain optional.

## Chapter 26 - Maximum Flow

### Section 26.1 - Flow Networks

- Lean source: `CLRSLean/FourthEdition/Chapter_24/Section_24_1_Flow_Networks.lean`
  (canonical fourth-edition Section 24.1; the legacy
  `CLRSLean/Chapter_26/Section_26_1_Flow_Networks.lean` forwards to it)
- Status: `proved`
- Model:
  - `CLRS.Chapter26.FlowNetwork` (capacity `c : V → V → ℝ`, source `s`, sink `t`,
    nonnegative capacity, zero self-loops, `s ≠ t`)
  - `CLRS.Chapter26.Flow` (feasible flow with capacity constraint,
    skew symmetry, and flow conservation)
  - `CLRS.Chapter26.Flow.value` (flow value `|f| = ∑_v f(s,v)`)
- Auxiliary lemmas:
  - `CLRS.Chapter26.Flow.self_zero` (flow on self-loop is zero)
  - `CLRS.Chapter26.Flow.nonneg_of_zero_reverse_cap`
  - `CLRS.Chapter26.Flow.nonpos_of_zero_cap`
  - `CLRS.Chapter26.Flow.range_of_zero_reverse_cap`
  - `CLRS.Chapter26.Flow.add_skew`
- Cut lemma:
  - `CLRS.Chapter26.Flow.netFlowAcrossCut` (net flow across `(S,Sᶜ)`)
  - `CLRS.Chapter26.Flow.skew_symm_cancel`
  - `CLRS.Chapter26.Flow.netFlow_eq_value` (**Lemma 26.5**: net flow
    across any cut equals the flow value)
  - `CLRS.Chapter26.Flow.value_le_cut_capacity` (flow value bounded by any cut capacity)
- Residual network:
  - `CLRS.Chapter26.Flow.residualCapacity` (`cf(u,v) = c(u,v) - f(u,v)`)
  - `CLRS.Chapter26.Flow.residualEdge` (positive residual capacity)
  - `CLRS.Chapter26.Flow.augmentingPathReachable` (reachability in the residual network)
  - `CLRS.Chapter26.Flow.hasAugmentingPath` (sink reachable from source)
- Ford-Fulkerson correctness:
  - `CLRS.Chapter26.Flow.isMaximal` (maximum flow predicate)
  - `CLRS.Chapter26.Flow.maximal_of_noAugmentingPath` (generic
    Ford-Fulkerson: no augmenting path implies maximal flow)
  - `CLRS.Chapter26.Flow.exists_cut_value_eq_of_noAugmentingPath` (the residual
    reachable set supplies a cut whose capacity equals the flow value)
- Proof pattern: Lemma 26.5 uses skew-symmetry cancellation and conservation to
  equate net cut flow with `|f|`.  The Ford-Fulkerson direction constructs a cut
  from the set of vertices reachable from `s` in the residual network, shows every
  crossing edge is saturated, and concludes maximality via the cut-capacity bound.
- Current gap: none within Section 26.1.

### Section 26.2 - Ford--Fulkerson Augmentation

- Lean source:
  `CLRSLean/FourthEdition/Chapter_24/Section_24_2_Edmonds_Karp/Ford_Fulkerson_Augmentation.lean`
  (canonical fourth-edition Section 24.2; the legacy
  `CLRSLean/Chapter_26/Section_26_2_Edmonds_Karp/Ford_Fulkerson_Augmentation.lean`
  forwards to it)
- Status: `proved` for the concrete mathematical augmentation layer
- Path and augmentation model:
  - `CLRS.Chapter26.Flow.ResidualPath`
  - `CLRS.Chapter26.Flow.AugmentingPath`
  - `CLRS.Chapter26.Flow.AugmentingPath.bottleneck`
  - `CLRS.Chapter26.Flow.augmentBy`
  - `CLRS.Chapter26.Flow.augment`
- Path and bottleneck facts:
  - `CLRS.Chapter26.Flow.ResidualPath.residualEdge_of_mem_edges`
  - `CLRS.Chapter26.Flow.AugmentingPath.edges_nonempty`
  - `CLRS.Chapter26.Flow.AugmentingPath.bottleneck_pos`
  - `CLRS.Chapter26.Flow.AugmentingPath.bottleneck_le_residualCapacity`
  - `CLRS.Chapter26.Flow.augment_residualCapacity`
  - `CLRS.Chapter26.Flow.AugmentingPath.reverse_mem_edges_of_new_residualEdge`
- Main theorems:
  - `CLRS.Chapter26.Flow.augmentBy_value`
  - `CLRS.Chapter26.Flow.augment_value`
  - `CLRS.Chapter26.Flow.value_lt_augment`
  - `CLRS.Chapter26.Flow.hasAugmentingPath_iff_nonempty_augmentingPath`
  - `CLRS.Chapter26.Flow.not_maximal_of_augmentingPath`
  - `CLRS.Chapter26.Flow.not_maximal_of_hasAugmentingPath`
- Proof pattern: represent the path by a nodup vertex list, sum a skew-symmetric
  edge delta along its consecutive pairs, and bound the update by the minimum
  residual capacity.  Cycle deletion turns a residual reachability witness into
  a simple path without changing its endpoints.
- Current gap: none for this layer.  The executable Edmonds--Karp loop and its
  analysis are proved in the companion modules documented below.

### Section 26.2 - The Edmonds-Karp Algorithm

- Lean sources: `CLRSLean/FourthEdition/Chapter_24/Section_24_2_Edmonds_Karp.lean`
  plus the submodules `Ford_Fulkerson_Augmentation`, `S1_ShortestAugmentingPath`,
  `S2_EK_Loop`, `S3_WorkAnalysis`, and `S4_ExecutableBFS` (canonical
  fourth-edition Section 24.2; the legacy
  `CLRSLean/Chapter_26/Section_26_2_Edmonds_Karp*` files forward to them).
- Status: `proved` (Lemma 26.7, the loop, the `O(VE²)` counting, and the
  executable BFS)
- Current declarations:
  - `CLRS.Chapter26.ResidualPathLength` (inductive predicate for path length in the residual network)
  - `CLRS.Chapter26.IsShortestDist` (shortest-path distance in the residual network)
  - `CLRS.Chapter26.ShortestAugmentingPath` (structure for a shortest augmenting path)
- Main lemmas:
  - `CLRS.Chapter26.isShortestDist_self` (distance from a vertex to itself is 0)
  - `CLRS.Chapter26.IsShortestDist.unique` (the shortest distance is unique)
  - `CLRS.Chapter26.isShortestDist_triangle` (triangle inequality for residual distances)
  - `CLRS.Chapter26.IsShortestDist.exists_predecessor` (a positive shortest
    distance has an incoming residual edge from a vertex one level earlier)
  - `CLRS.Chapter26.ShortestAugmentingPath.prefix_path`
  - `CLRS.Chapter26.ShortestAugmentingPath.suffix_path`
  - `CLRS.Chapter26.ShortestAugmentingPath.shortest_prefix` (each prefix of a
    shortest augmenting path is itself shortest)
  - `CLRS.Chapter26.ShortestAugmentingPath.exists_shortestDist_le_augment`
    (every finite post-augmentation distance has a no-larger pre-augmentation
    witness)
  - `CLRS.Chapter26.shortest_path_nondec` (**Lemma 26.7**: shortest residual
    distances do not decrease after shortest-path augmentation)
- Shortest-path construction (`S1_ShortestAugmentingPath`):
  - `CLRS.Chapter26.back` and its structural facts `back_head`, `back_last`,
    `back_length`, `back_nodup`, `back_getElem_shortest`, `back_chain_rev`:
    the backwards exact-predecessor walk realizing a residual distance
  - `CLRS.Chapter26.shortestFlow.ResidualPath` and
    `shortestFlow.ResidualPath_edges_length`: the assembled shortest
    source-to-sink residual path
  - `CLRS.Chapter26.exists_shortest_augmenting_path`: residual reachability
    yields an explicit shortest augmenting path
- Edmonds-Karp loop (`S2_EK_Loop`):
  - `CLRS.Chapter26.shortestAugmentingPath_iff_hasAugmentingPath`: shortest
    augmenting paths exist exactly when the sink is residual-reachable
  - `CLRS.Chapter26.ekStep` and `ekIter`: the loop; `IsIntegral_ekStep`,
    `ekStep_value_increase`, `ekIter_value_ge` keep integrality and value
    increase
  - `CLRS.Chapter26.exists_noAugmentingPath_ekIter`: termination at a flow
    without augmenting paths (value bounded by the integral cut capacity)
  - `CLRS.Chapter26.edmondsKarp_maximal`: on integral-capacity networks the
    loop reaches an integral maximal flow
- Work analysis (`S3_WorkAnalysis`):
  - `CLRS.Chapter26.Flow.AugmentingPath.isCritical` and
    `exists_critical_edge`: every augmentation saturates at least one edge
  - `CLRS.Chapter26.shortest_edge_dist`, `critical_dist_increase`, and
    `critical_dist_increase_rev` (**Lemma 26.8**: the residual distance to
    `u` grows by at least two when `(v,u)` later lies on a shortest path)
  - `CLRS.Chapter26.IsShortestDist.lt_card`: residual distances are bounded
    by `|V| - 1`
  - the timeline `ekSeq`/`ekPath`/`criticalAt` with `ekStep_dist_nondec`,
    `distAt_mono`, and `exists_recovery_step`: the recovery argument that a
    later critical occurrence is preceded by augmentation along the reverse
    edge
  - `CLRS.Chapter26.criticalAt_growth` and `criticalAt_growth_strict`:
    distances strictly grow between critical occurrences (no consecutive
    critical steps)
  - `CLRS.Chapter26.critical_count_bound`: each edge is critical at most
    `|V|` times; `augmentation_count_bound`: at most `|V|² · |V|` augmenting
    steps — the `O(VE²)` bound once each step is charged `O(E)` for BFS
- Proof pattern: define shortest distance through a length-indexed residual-path
  predicate; prove exact predecessor and shortest-prefix facts; then induct over
  a post-augmentation path.  Old residual edges use the one-edge triangle
  theorem, while genuinely new edges are reversals of edges on the selected
  augmenting path and are discharged by prefix optimality.  The counting
  argument combines the recovery-step timeline lemma with reverse distance
  monotonicity and injects critical occurrences into `Fin (Fintype.card V)`.
- Executable BFS (`S4_ExecutableBFS`):
  - `CLRS.Chapter26.residualBFS`: the fuelled breadth-first search over the
    residual network, mirroring the Chapter 22 BFS state and invariants
    (`BFSState`, `BFSClosedInv`, `BFSQueueInv`, `BFSDistanceInvariant`)
  - `CLRS.Chapter26.residualBFS_distanceInvariant` and
    `residualBFS_queue_empty`: the invariants hold and the queue exhausts
    after `|V|` steps (measure argument)
  - `CLRS.Chapter26.bfsState_distance_eq_some_iff`: the BFS distance of a
    vertex is exactly its residual shortest distance `IsShortestDist`
  - `CLRS.Chapter26.bfsParentResidualPath` and its length lemma: the parent
    chain from the sink assembles a simple residual path realizing the
    recorded distance
  - `CLRS.Chapter26.bfs_shortestAugmenting`: an executable shortest
    augmenting path whenever one exists
  - `CLRS.Chapter26.ekStep_shortest_path_bfs`: the Edmonds-Karp step
    augments along a shortest path of the same length as the BFS path
- Interface evidence: `Tests/Chapter_26_Edmonds_Karp_Interface.lean`.

### Section 26.3 - Maximum Bipartite Matching

- Lean source: `CLRSLean/FourthEdition/Chapter_24/Section_24_3_Bipartite_Matching.lean`
  (canonical fourth-edition Section 24.3; the legacy
  `CLRSLean/Chapter_26/Section_26_3_Bipartite_Matching.lean` forwards to it)
- Status: `proved`
- Represented model:
  - `CLRS.Chapter26.BipartiteGraph`
  - `CLRS.Chapter26.Matching`
  - `CLRS.Chapter26.toFlowNetwork`
  - `CLRS.Chapter26.matchingFlowFun` and `matchingFlowFunSummand`
- Flow construction (value direction):
  - `CLRS.Chapter26.matchingFlowFun_skew_symm`, `matchingFlowFun_capacity`,
    and `matchingFlowFun_conservation`: the matching-induced function is a
    feasible flow
  - `CLRS.Chapter26.matchingToFlow`: the feasible flow induced by a matching
  - `CLRS.Chapter26.matchingToFlow_value`: its value equals `|M|` (no longer
    conditional)
- Integral-flow converse:
  - `CLRS.Chapter26.Flow.IsIntegral`: integer-valued flow predicate
  - `CLRS.Chapter26.matchingFlow_lr_bounds` and
    `matchingFlow_conservation_left/right`: in the unit-capacity network the
    flow on `L→R` pairs lies in `[0,1]` and conservation holds at every
    partition vertex
  - `CLRS.Chapter26.matchingOfIntegralFlow`: the matching recovered from an
    integral flow (all `L→R` pairs carrying one unit)
  - `CLRS.Chapter26.matchingOfIntegralFlow_size`: its size equals the flow
    value
- Integral maximum flow (Ford-Fulkerson iteration):
  - `CLRS.Chapter26.zeroFlow`, `augmentOnce`, and `iterAugment`: repeated
    augmentation from the zero flow
  - `CLRS.Chapter26.bottleneck_ge_one` and `IsIntegral_augment`: integrality
    and value increase by at least one per step
  - `CLRS.Chapter26.exists_noAugmentingPath_iter`: iteration terminates at a
    flow without augmenting paths (value bound by the integral source-side
    cut capacity)
- Main theorem:
  - `CLRS.Chapter26.maxMatching_eq_maxFlow_value` (**Theorem 26.12**): there
    is a matching at least as large as every matching, and a maximal flow
    whose value is exactly its size
- Proof pattern: the disjoint partitions force every reverse capacity to
  zero, so unit-capacity bounds give `f(l,r) ∈ {0,1}` on `L→R` pairs and the
  conservation identities reduce recovery to a cardinality count.  The
  maximum-flow direction iterates augmentation from the zero flow; each step
  increases the integral value by at least one, so termination is bounded by
  the integral source-side cut capacity, and the no-augmenting-path theorem
  yields maximality.
- Current gap: none within Section 26.3.

### Theorem 26.6 - The Max-Flow Min-Cut Theorem

- Lean source: `CLRSLean/FourthEdition/Chapter_24/Section_24_6_MaxFlow_MinCut.lean`
  (canonical fourth-edition Section 24.6; the legacy
  `CLRSLean/Chapter_26/Section_26_6_MaxFlow_MinCut.lean` forwards to it)
- Status: `proved`
- Proved theorems:
  - `CLRS.Chapter26.Flow.eq_cutCapacity_implies_maximal`
    (the easy direction: equality with a cut capacity implies maximality)
  - `CLRS.Chapter26.Flow.maximal_iff_noAugmentingPath`
    (maximality is equivalent to the absence of an augmenting path)
  - `CLRS.Chapter26.Flow.maximal_iff_exists_cut_value_eq`
    (maximality is equivalent to equality with the capacity of some cut)
- Proof pattern: concrete augmentation proves that an augmenting path rules out
  maximality; the residual reachable set supplies the equal-capacity cut when
  no augmenting path exists; cut equality supplies the reverse implication.
- Current gap: none for the mathematical Max-Flow Min-Cut equivalence.

### Section 26.4 - Push-Relabel Algorithms

- Lean source: `CLRSLean/FourthEdition/Chapter_24/Section_24_4_Push_Relabel.lean`
  (canonical fourth-edition Section 24.4; the legacy
  `CLRSLean/Chapter_26/Section_26_4_Push_Relabel.lean` forwards to it)
- Status: `proved` for the preflow-push model, operations, and correctness
- Represented model:
  - `CLRS.Chapter26.Preflow` (capacity, skew symmetry, nonnegative excess off
    the source), `Preflow.excess` and `Preflow.isOverflowing`
  - `CLRS.Chapter26.IsValidHeight` and `admissibleEdge`
  - `CLRS.Chapter26.relabel` (raise a vertex to one plus the minimum height of
    its residual neighbors)
- Operations and invariant preservation:
  - `CLRS.Chapter26.Preflow.pushBy` / `Preflow.push`: push `δ` units along a
    residual edge, preserving the preflow (`pushBy`'s three axioms) and, under
    admissibility, the valid height function (`pushBy_validHeight`)
  - `CLRS.Chapter26.relabel_validHeight`: relabeling a non-source non-sink
    vertex under the relabel precondition preserves the valid height function
  - `CLRS.Chapter26.relabel_height_increase`: relabeling strictly increases
    the vertex's height
- Height bound:
  - `CLRS.Chapter26.exists_residualEdge_of_overflowing`: an overflowing vertex
    has a residual edge leaving it
  - `CLRS.Chapter26.exists_residualPath_to_source_of_overflowing` (**Lemma
    26.14**): an overflowing vertex reaches the source in the residual network
  - `CLRS.Chapter26.height_le_of_overflowing` (**Lemma 26.15**): every height
    is bounded by `2|V| - 1`
- Main theorem:
  - `CLRS.Chapter26.maximal_of_no_overflow`: a preflow with a valid height
    function and no overflowing internal vertex induces a maximum flow, via
    `Flow.maximal_of_noAugmentingPath` (the max-flow min-cut theorem)
- Proof pattern: the no-augmenting-path step bounds the height drop along a
  simple residual path by `|V| - 1`; the source-path lemma cuts at the residual
  reachable set and cancels the internal double sum by skew symmetry.
- Current gap: none for the preflow-push model; the operation count lives in
  Section 26.5.

### Section 26.5 - Relabel-to-Front

- Lean source: `CLRSLean/FourthEdition/Chapter_24/Section_24_5_Relabel_To_Front.lean`
  (canonical fourth-edition Section 24.5; the legacy
  `CLRSLean/Chapter_26/Section_26_5_Relabel_To_Front.lean` forwards to it)
- Status: `proved` for the generic push-relabel `O(V²E)` operation count and the
  relabel-to-front `O(V³)` discharge-order bound
- Represented model:
  - `CLRS.Chapter26.BasicOp`: a single basic operation (a relabel of an
    overflowing vertex, or a push from an overflowing vertex along an admissible
    edge), storing the before-state preflow and height function
  - `CLRS.Chapter26.Run`: a length-`n` run of the generic algorithm, with the
    state sequence and the before/after consistency equations
  - `CLRS.Chapter26.numEdges`: the number of directed positive-capacity edges
- Counting bounds (over *any* run):
  - `CLRS.Chapter26.Run.height_mono`: heights are nondecreasing across a run
  - `CLRS.Chapter26.Run.relabel_count_bound`: at most `2|V|²` relabel operations
  - `CLRS.Chapter26.Run.saturating_push_count_bound`: at most `O(|V|·|E|)`
    saturating pushes (between two saturating pushes on `(u,v)` the height of
    `u` grows by at least two, via the reverse-push recovery argument)
  - `CLRS.Chapter26.Run.nonsaturating_push_count_bound`: at most
    `O(|V|²(|V|+|E|))` nonsaturating pushes, via the potential
    `Φ = Σ_{overflowing u} h(u)`
  - `CLRS.Chapter26.Run.generic_step_count_bound`: the combined `O(V²E)` bound
    on the number of basic operations
- Relabel-to-front discharge order (over a `RelabelToFrontRun`):
  - `CLRS.Chapter26.BasicOp.opVertex`: the active vertex of a basic operation
  - `CLRS.Chapter26.RelabelToFrontRun`: a run respecting the §26.5 DISCHARGE
    discipline (between two relabels, no vertex is the source of more than one
    nonsaturating push)
  - `CLRS.Chapter26.RelabelToFrontRun.nonsaturating_push_count_bound`: at most
    `|V|·(relabels + 1)` nonsaturating pushes, i.e. `O(V³)`
  - `CLRS.Chapter26.RelabelToFrontRun.step_count_bound_V3`: at most `9|V|³`
    basic operations
- Proof pattern: the relabel and saturating-push counts are proved by height
  injection into `V × [0, 2|V|)` and `edge × [0, 2|V|)`; the nonsaturating count
  is an amortized potential argument over the telescoping sum
  `Φ(n) = Φ(0) + Σ (Φ(i+1) - Φ(i))`.  The discharge-order bound counts
  nonsaturating pushes by their preceding relabel count, injecting them into
  `[0, relabels] × V` via `opVertex`.

### Chapter 26 current boundary

The §26.4 push-relabel model, operations, invariants, height bound, and
correctness are proved; §26.5 supplies the generic `O(V²E)` operation-count
bound (relabel, saturating-push, and nonsaturating-push counts) over any run,
and the relabel-to-front `O(V³)` discharge-order bound.

## Chapter 27 - Multithreaded Algorithms

### Section 27.1 - The Basics of Dynamic Multithreading

- Lean sources (canonical fourth-edition Section 26.1; the legacy
  `CLRSLean/Chapter_27/Section_27_1_Multithreading_Model*` files forward to them):
  - `CLRSLean/FourthEdition/Chapter_26/Section_26_1_Multithreading_Model.lean`
  - `CLRSLean/FourthEdition/Chapter_26/Section_26_1_Multithreading_Model/S1_ComputationDAG.lean`
  - `CLRSLean/FourthEdition/Chapter_26/Section_26_1_Multithreading_Model/S2_ReadyExecution.lean`
  - `CLRSLean/FourthEdition/Chapter_26/Section_26_1_Multithreading_Model/S3_GreedyAccounting.lean`
  - `CLRSLean/FourthEdition/Chapter_26/Section_26_1_Multithreading_Model/S4_ExecutableScheduler.lean`
  - `CLRSLean/FourthEdition/Chapter_26/Section_26_1_Multithreading_Model/S5_SpawnTreeAndLoops.lean`
- Interface test: `Tests/Chapter_27_Interface.lean`
- Status: `proved` (for the represented model)
- Model:
  - `CLRS.Chapter27.CompDAG` (computation DAG with forward/topologically
    ordered edges)
  - `CLRS.Chapter27.CompDAG.work` (T₁, total work)
  - `CLRS.Chapter27.CompDAG.longestTo` / `CLRS.Chapter27.CompDAG.span`
    (T∞, honestly computed longest weighted path by DP)
  - `CLRS.Chapter27.GreedyScheduleAccounting` (aggregate complete/incomplete
    step accounting certificate)
  - `CLRS.Chapter27.GreedyScheduleTrace` (ordered complete/incomplete trace)
  - `CLRS.Chapter27.GreedyScheduleRun` (per-step work consumption and span
    decrease, with local progress obligations)
  - `CLRS.Chapter27.CompDAG.ready` / `CLRS.Chapter27.CompDAG.execute`
    (computed ready set and one-unit residual-state transition)
  - `CLRS.Chapter27.DAGScheduleStep` / `CLRS.Chapter27.DAGSchedule`
    (maximally busy greedy steps and type-safe chained executions)
  - `CLRS.Chapter27.SpawnTree` (spawn/sync tree with unit spawn overhead)
  - `CLRS.Chapter27.parallelLoopTree` (balanced parallel-loop spawn tree)
- Proved theorems:
  - `CLRS.Chapter27.CompDAG.longestTo_le`, `CLRS.Chapter27.CompDAG.span_le_work`
    (T∞ ≤ T₁ on DAGs)
  - `CLRS.Chapter27.GreedyScheduleAccounting.time_le_work_div_add_span`,
    `CLRS.Chapter27.GreedyScheduleTrace.time_le_work_div_add_span`, and
    `CLRS.Chapter27.GreedyScheduleRun.time_le_work_div_add_span`
    (`Tₚ ≤ T₁ / p + T∞` at the aggregate, ordered-trace, and local per-step
    accounting boundaries)
  - `CLRS.Chapter27.CompDAG.remainingSpan_execute_ready_add_one_le`
    (executing every ready node decreases a nonempty residual critical path)
  - `CLRS.Chapter27.DAGScheduleStep.incomplete_run_eq_ready` and
    `CLRS.Chapter27.DAGScheduleStep.incomplete_progress`
    (the greedy-step invariant derived from explicit ready-set semantics)
  - `CLRS.Chapter27.DAGSchedule.work_balance`,
    `CLRS.Chapter27.DAGSchedule.span_balance`, and
    `CLRS.Chapter27.DAGSchedule.final_work_eq_zero`, together with
    `CLRS.Chapter27.DAGSchedule.time_le_work_div_add_span`
    (completed executions, telescoping resource budgets, and the explicit-DAG
    form of CLRS Theorems 27.1/27.2)
  - `CLRS.Chapter27.CompDAG.greedySchedule_final_work_eq_zero` and
    `CLRS.Chapter27.CompDAG.greedySchedule_time_le_work_div_add_span`
    (the total executable scheduler terminates with zero residual work and
    satisfies the greedy-scheduling bound without an external completion
    certificate)
  - `CLRS.Chapter27.SpawnTree.span_le_work` (T∞ ≤ T₁ on spawn trees)
  - `CLRS.Chapter27.parallelLoop_work` (exact work `n * w + (n - 1)`)
  - `CLRS.Chapter27.parallelLoop_span` (exact span `w + depth`)
  - `CLRS.Chapter27.parallelLoopDepth_pow` (`n ≤ 2 ^ depth`, the
    span-is-logarithmic direction)
  - `CLRS.Chapter27.parallelLoopDepth_le_log`
    (`parallelLoopDepth n ≤ Nat.log 2 n + 1` on every input)
  - `CLRS.Chapter27.parallelLoop_span_le_log`
    (all-input span bound `span ≤ w + Nat.log 2 n + 1`)

### Section 27.2 - Multithreaded Matrix Multiplication

- Lean sources (canonical fourth-edition Sections 26.2--26.3; the legacy
  `CLRSLean/Chapter_27/Section_27_2_4_Algorithms*` files forward to them):
  - `CLRSLean/FourthEdition/Chapter_26/Section_26_2_4_Algorithms.lean`
  - `CLRSLean/FourthEdition/Chapter_26/Section_26_2_4_Algorithms/S1_CostModel.lean`
  - `CLRSLean/FourthEdition/Chapter_26/Section_26_2_4_Algorithms/S2_Recurrences.lean`
    (shared recurrence file containing the idealized P-MATMUL model)
  - `CLRSLean/FourthEdition/Chapter_26/Section_26_2_4_Algorithms/S3_AllInputBounds.lean`
    (shared all-input-bound file)
  - `CLRSLean/FourthEdition/Chapter_26/Section_26_2_4_Algorithms/ParallelMatrix.lean`
  - `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMatrix/Definitions.lean`
  - `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMatrix/Correctness.lean`
  - `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMatrix/Costs.lean`
  - `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMatrix/Costs/Definitions.lean`
  - `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMatrix/Costs/ExecutionEqualities.lean`
  - `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMatrix/Costs/Monotonicity.lean`
  - `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMatrix/Costs/PowerBounds.lean`
  - `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMatrix/Costs/AllInputBounds.lean`
- Interface test: `Tests/Chapter_27_Matrix_Interface.lean`
- Status: `proved` for executable P-ADD and race-free P-MATMUL correctness,
  execution-attached cost equalities, and all-input work/span asymptotics.
- Model:
  - `CLRS.Chapter27.Costed` attaches a pure value to exact work and span, with
    sequential composition and deterministic balanced `par4`/`par8` trees.
  - `CLRS.Chapter04.SqMat R k` represents a `2^k × 2^k` square matrix.
  - `pAddWork`, `pAddSpan`, `pMatMulExecWork`, and `pMatMulExecSpan` are the
    recurrences proved equal to the costs carried by executable P-ADD and
    P-MATMUL.
  - The older `pMatMulWork`/`pMatMulSpan` pair is an **idealized recurrence**
    with constant combine span.  Its logarithmic span result is not the span
    carried by executable P-MATMUL, whose sequential P-ADD phase produces
    log-squared span.
- Proved executable matrix boundary:
  - `CLRS.Chapter27.Costed.pure`, `charge`, `map`, `seq`, `par`, `par4`, and
    `par8` form the value/work/span execution layer.
  - `CLRS.Chapter27.pAdd` charges one work/span unit at scalar leaves, executes
    four quadrant additions through deterministic balanced `Costed.par4`, and
    reassembles the row-major quadrant tuple.
  - `CLRS.Chapter27.pMatMul` runs eight recursive products in balanced
    `Costed.par8`, constructs two fresh immutable temporary matrices, and then
    applies P-ADD.  The functional temporaries rule out concurrent writes and
    make the executable interpretation data-race free.
  - `CLRS.Chapter27.pAdd_value` / `CLRS.Chapter27.pAdd_correct` prove ordinary
    matrix addition; `CLRS.Chapter27.pMatMul_value` /
    `CLRS.Chapter27.pMatMul_correct` prove ordinary matrix multiplication.
    All four statements hold at every depth over any `Ring`.
  - Interface examples confirm exact scalar P-ADD/P-MATMUL work/span `1/1`,
    depth-one P-ADD work/span `7/3`, and depth-one P-MATMUL work/span `22/7`,
    together with concrete `2 × 2` values.
- Proved execution-cost connections and witnesses:
  - `CLRS.Chapter27.pAdd_work_eq` and `CLRS.Chapter27.pAdd_span_eq` identify
    the work and span carried by P-ADD with `pAddWork (2^k)` and
    `pAddSpan (2^k)` for every depth-indexed input pair.
  - `CLRS.Chapter27.pMatMul_work_eq` and `CLRS.Chapter27.pMatMul_span_eq`
    identify executable P-MATMUL with `pMatMulExecWork (2^k)` and
    `pMatMulExecSpan (2^k)` for every input pair.
  - The exact power-of-two formulas and two-sided power bounds in
    `Costs/PowerBounds.lean` provide explicit lower and upper recurrence
    witnesses.  Monotonicity and adjacent-power sandwiches then prove
    `pAddWork_allInput_bigTheta`, `pAddSpan_allInput_bigTheta`,
    `pMatMulExecWork_allInput_bigTheta`, and
    `pMatMulExecSpan_allInput_bigTheta`: Θ(n²), Θ(log n), Θ(n³), and
    Θ(log² n), respectively.
- Idealized compatibility recurrence:
  - `CLRS.Chapter27.pMatMulWork_pow_two` and `pMatMulWork_le` give the
    constant-combine model's cubic work bounds.
  - `CLRS.Chapter27.pMatMulSpan_pow_two` and `pMatMulSpan_le` give its
    logarithmic span.  This is not an executable P-MATMUL span claim: the
    actual sequential P-ADD combine is exactly why `pMatMulExecSpan` is
    log-squared.

### Section 27.3 - Multithreaded Merge Sort

- Lean sources:
  - `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/S2_Recurrences.lean`
  - `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/S3_AllInputBounds.lean`
  - `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge.lean`
  - `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/LowerBound.lean`
  - `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/PMerge/Definitions.lean`
  - `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/PMerge/Correctness/Main.lean`
  - `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/Costs/Structure.lean`
  - `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/Costs/Step.lean`
  - `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/Costs/Work/Bounds.lean`
  - `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/Costs/Span/Bounds.lean`
  - `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/Costs/Span/WitnessLists.lean`
  - `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/Costs/Span/LowerBound.lean`
  - `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMergeSort.lean`
  - `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMergeSort/Definitions.lean`
  - `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMergeSort/Correctness/Main.lean`
  - `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMergeSort/Costs/Step.lean`
  - `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMergeSort/Costs/RecurrenceLinks.lean`
  - `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMergeSort/Costs/Work/Bounds.lean`
  - `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMergeSort/Costs/Span/Bounds.lean`
  - `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMergeSort/Costs/Span/WitnessInput.lean`
  - `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMergeSort/Costs/Span/LowerBound.lean`
- Interface test: `Tests/Chapter_27_ParallelMerge_Interface.lean`
- Status: `proved` for executable P-MERGE and P-MERGE-SORT value correctness,
  exact step costs, execution-to-recurrence links, universal upper bounds, and
  explicit matching span-witness families.
- Model: `pMergeWork`, `pMergeSpan`, `pMergeSortWork`, and `pMergeSortSpan`
  are recurrence-level costs.  Executable merge sort has two-sided work links
  to `pMergeSortWork` and an upper span link to `pMergeSortSpan`; its matching
  lower span bound is proved separately on `worstMergeSortInput`.
- Proved executable P-MERGE boundary:
  - `CLRS.Chapter27.pMerge` normalizes the longer input, chooses its midpoint,
    partitions the shorter input with duplicate-sensitive binary lower bound,
    runs the lower and upper recursive merges through `Costed.par`, and joins
    them around the pivot.
  - `CLRS.Chapter27.PMergeSpec` bundles sortedness, permutation of `xs ++ ys`,
    and exact output length.
  - `CLRS.Chapter27.pMerge_correct` proves that specification for all sorted
    inputs by strong induction on total length; `pMerge_value_sorted`,
    `pMerge_value_perm`, and `pMerge_value_length` expose its projections.
  - The boundary proof handles duplicates by using the lower-bound theorem's
    strict-left/nonstrict-right partition and handles normalization swaps by an
    explicit block permutation.
  - `CLRS.Chapter27.pMerge_childSizes_add_one` proves the children partition
    every element except the pivot, while
    `CLRS.Chapter27.pMerge_childSize_le_threeQuarters` proves both actual
    children have size at most `n - n / 4`, including totals below four.
  - `CLRS.Chapter27.pMerge_work_step_eq` and
    `CLRS.Chapter27.pMerge_span_step_eq` expose exact nonempty-call costs:
    binary search plus the two children, one fork/join, and one pivot placement.
    The corresponding `*_step_le` theorems bound search by `log₂ n + 1`.
  - `CLRS.Chapter27.pMerge_work_lower` proves the total input length is at most
    executable work plus one by counting the pivot removed at each recursive
    node.
  - `CLRS.Chapter27.pMerge_work_upper` proves the pointwise bound
    `work ≤ 64 * (total + 1)`.  Its strong induction establishes the stronger
    potential invariant `work + 8 * log₂(total + 1) ≤ 64 * total`; the actual
    three-quarter child bound supplies the logarithmic credit that pays for
    every node's binary search.
  - `CLRS.Chapter27.pMerge_span_upper` proves the universal pointwise bound
    `span ≤ 64 * (log₂(total) + 1)^2`.  The monotone envelope recurs on the
    actual `n - n / 4` child bound.  Its solution unfolds three shrink levels:
    two levels do not always lower `Nat.log` (for example near 31), whereas
    three place the child below the current highest power of two above the
    finite kernel.
  - `CLRS.Chapter27.evenKeys` and `CLRS.Chapter27.oddKeys` are sorted
    interleaved witness lists.  Their lower P-MERGE child is the same family at
    half size.  The binary-search path satisfies
    `log₂(length + 1) ≤ span`; on the power-of-two witness this gives search
    span at least `k+1`, yielding the recurrence
    `2*S(k+1) ≥ 2*S(k) + (k+1) + 4` and the public matching witness
    `CLRS.Chapter27.pMerge_interleaved_span_lower`:
    `(k+1)^2 ≤ 8 * span` on inputs of size `2^k` each.
- Proved executable P-MERGE-SORT boundary:
  - `CLRS.Chapter27.pMergeSort` returns length-zero/one inputs directly and,
    for every larger list, splits at `length / 2`, runs both recursive sorts
    through `Costed.par`, and invokes executable P-MERGE sequentially.
  - `CLRS.Chapter27.PMergeSortSpec` bundles sortedness, permutation of the
    original input, and exact output length.
  - `CLRS.Chapter27.pMergeSort_correct` proves this specification for every
    input by strong induction on length.  The base proof derives sortedness
    solely from `length ≤ 1`; the recursive proof composes the two child
    specifications with `pMerge_correct` and reconstructs the input using
    `List.take_append_drop`.
  - `pMergeSort_value_sorted`, `pMergeSort_value_perm`, and
    `pMergeSort_value_length` expose the three reader-facing projections.
  - `CLRS.Chapter27.pMergeSort_work_step_eq` and
    `CLRS.Chapter27.pMergeSort_span_step_eq` expose the exact larger-input
    costs: parallel child sorts, one fork/join, and the sequential P-MERGE.
  - `CLRS.Chapter27.ParallelMergeSort.Costs.recurrenceWork_le_execution` and
    `CLRS.Chapter27.ParallelMergeSort.Costs.executionWork_le_recurrence`
    sandwich actual work between `pMergeSortWork` and a fixed multiple of it;
    the upper link uses P-MERGE's stronger logarithmic-potential invariant to
    absorb every fork charge.  The span comparison is internal to the public
    `pMergeSort_span_upper` proof and connects execution to `pMergeSortSpan`.
  - `CLRS.Chapter27.pMergeSort_work_lower` and
    `CLRS.Chapter27.pMergeSort_work_upper` prove all-input executable work is
    Θ(n log n), with explicit natural-number constants.
  - `CLRS.Chapter27.pMergeSort_span_upper` proves every execution has span at
    most `256 * (log₂(length) + 1)^3`.
  - `CLRS.Chapter27.worstMergeSortInput` recursively interleaves order-embedded
    copies of its preceding level and has exact length `2^k`.  Order-preserving
    map invariance carries the recursive critical path through the embedding;
    the interleaved P-MERGE witness contributes a quadratic term at each level.
    Consequently `CLRS.Chapter27.pMergeSort_worstFamily_span_lower` proves
    `(k+1)^3 ≤ 64 * span`, matching the cubic-log upper bound.
  - Focused executable examples cover empty and singleton costs, an odd
    reversed list, duplicate-heavy data, and small witness-family instances.
- Proved recurrence results (power-of-two closed forms):
  - `CLRS.Chapter27.pMergeWork_pow_two` (`T₁(2ᵏ) + (k+3) = 4·2ᵏ`, work Θ(n))
  - `CLRS.Chapter27.pMergeSpan_pow_two` (`2·T∞(2ᵏ) = (k+1)(k+2)`, span Θ(log² n))
  - `CLRS.Chapter27.pMergeSortWork_pow_two` (`T₁(2ᵏ) = 2ᵏ·(k+1)`, work
    Θ(n log n))
  - `CLRS.Chapter27.pMergeSortSpan_pow_two`
    (`6·T∞(2ᵏ) = 6 + k·(k² + 6k + 11)`, span Θ(log³ n))
- Proved monotonicity and adjacent-power transfer interface:
  - `CLRS.Chapter27.pMergeWork_monotone`,
    `CLRS.Chapter27.pMergeSpan_monotone`,
    `CLRS.Chapter27.pMergeSortWork_monotone`, and
    `CLRS.Chapter27.pMergeSortSpan_monotone`
  - the corresponding four `*_power_sandwich` theorems, placing every positive
    input between its adjacent power-of-two costs
- Proved all-input asymptotic theorems:
  - `CLRS.Chapter27.pMergeWork_allInput_bigTheta`: Θ(n)
  - `CLRS.Chapter27.pMergeSpan_allInput_bigTheta`: Θ(log² n)
  - `CLRS.Chapter27.pMergeSortWork_allInput_bigTheta`: Θ(n log n)
  - `CLRS.Chapter27.pMergeSortSpan_allInput_bigTheta`: Θ(log³ n)
- Proof pattern: prove each natural-valued recurrence monotone, sandwich an
  arbitrary positive input between `2 ^ log₂ n` and the next power of two,
  then reuse Chapter 4's exact-power-to-all-input transfer and scale bridges.

### Parallel Strassen Compatibility Extension

- Lean sources:
  - `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelStrassen.lean`
  - `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelStrassen/Recurrences.lean`
  - `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelStrassen/Recurrences/Definitions.lean`
  - `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelStrassen/Recurrences/Monotonicity.lean`
  - `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelStrassen/Recurrences/AllInputBounds.lean`
- Status: `proved` as a recurrence-only extension.  The legacy names remain
  available from `import CLRSLean.Chapter_27`, but this is not a Chapter 27
  main-text Section 27.4 and it has no executable matrix-value claim.
- Upper/lower witnesses and main theorems:
  - `strassenWork_pow_two` and `strassenSpan_pow_two` are exact power-of-two
    witnesses for Θ(n^(log₂ 7)) work and Θ(log n) span.
  - `strassenWork_monotone`, `strassenSpan_monotone`, and the corresponding
    `*_power_sandwich` theorems provide adjacent-power lower/upper witnesses.
  - `strassenWork_allInput_bigTheta` and `strassenSpan_allInput_bigTheta`
    package the all-input asymptotic conclusions.

- Completion boundary: the represented Chapter 27 main-text core has no open
  proof group.  The historical `Section_27_2_4_Algorithms` name is retained
  only for import compatibility; the main text ends at Section 27.3.  Mutable
  arrays, RAM-level implementation/allocation costs, exercises, and chapter-end
  problems are outside the sealed pure-functional boundary.  The separately
  labeled Strassen extension is not a remaining Chapter 27 obligation.

## Fourth Edition Chapter 27 - Online Algorithms

### Section 27.1 - Waiting for an Elevator

- Lean source: `CLRSLean/FourthEdition/Chapter_27/Section_27_1_Waiting_For_Elevator.lean`
- Status: `complete` (native fourth-edition source)
- Model:
  - `SkiRental.rentThenBuyCost`: the cost of the deterministic online strategy
    that rents for the first `a` days and, if the trip outlasts it, buys on day
    `a+1` — `T * r` when `T ≤ a`, else `a * r + p`.
  - `SkiRental.optCost`: the optimal offline cost `min (T * r) p`.
  - `SkiRental.IsCompetitive`: strategy `a` is `c`-competitive when its cost
    never exceeds `c` times the optimal offline cost on every input.
  - `Elevator.cost` / `Elevator.optCost`: the elevator instance — waiting `w`
    seconds then taking the stairs (cost `w + S` when the elevator comes late),
    versus the offline choice of the cheaper of elevator (wait + ride `t + E`)
    and stairs (`S`).
- Proved:
  - `SkiRental.rentThenBuy_two_competitive` (CLRS Theorem 27.1): any strategy
    that rents `a` days with `a * r < p ≤ (a + 1) * r` is `2`-competitive —
    the short-trip case pays exactly the optimum (renting every day), and the
    long-trip case pays at most twice the optimum (renting `a` days then
    buying).
  - `Elevator.elevator_two_competitive`: with `E ≥ 0` and `S > 0`, the
    wait-`S - E`-then-take-the-stairs strategy is `2`-competitive for every
    arrival time `t ≥ 0`.
  - `Elevator.elevator_worst_case_ratio`: when the elevator comes after the
    wait time, the strategy pays exactly `(2 - E/S) * S`, matching the
    competitive ratio stated in CLRS §27.1.
- Current gap: the lower bound that no deterministic strategy beats `2 - r/p`
  is not yet formalized.

### Section 27.2 - Maintaining a Search List

- Lean source: `CLRSLean/FourthEdition/Chapter_27/Section_27_2_Maintaining_A_Search_List.lean`
- Status: `complete` (native fourth-edition source)
- Model:
  - `SearchList.before`: strict order (`a` before `b`) in a list — `b` is
    present and `a` appears before the first occurrence of `b`.
  - `SearchList.position`: the 0-based position of a key in a list (the number
    of keys strictly before it).
  - `SearchList.invDist`: the inversion distance between two lists over the same
    element set — the number of pairs whose relative order differs.
  - `SearchList.moveToFront`: after a request, move the requested key to the
    front (`x :: L.erase x`).
  - `SearchList.scanCost` / `SearchList.mtfCost`: the per-request costs —
    scanning to the (1-based) position, and scanning plus the front swap
    (`2 * position + 1`).
  - `SearchList.potential`: the potential function `2 * invDist`.
  - `SearchList.strategyCost` / `SearchList.strategyTotalCost`: the cost of an
    arbitrary list-update strategy `A` — the scan cost plus the rearrangement
    `invDist L (A L x)` — per request and over a request sequence.
- Proved:
  - `SearchList.mtf_step_four_competitive`: the per-request amortized bound —
    for a request `x`, after MOVE-TO-FRONT moves `x` to the front and the
    adversary moves to `M'`, MTF's cost plus the change in the potential
    `2 * invDist` is at most `4` times the strategy's cost plus the previous
    potential.
  - `SearchList.mtf_four_competitive` (CLRS Theorem 27.2): MOVE-TO-FRONT is
    `4`-competitive against any list-update strategy that keeps its list a
    permutation of the initial set —
    `mtfTotalCost σ L ≤ 4 * strategyTotalCost A σ M + 2 * invDist L M`, with the
    additive term zero when both start from the same list.
  - Supporting lemmas: `SearchList.invDist_moveToFront_add_pos` (the phase-1
    potential change) and `SearchList.invDist_triangle` (the triangle inequality
    bounding the adversary's rearrangement).
### Section 27.3 - Online Caching

- Lean source: `CLRSLean/FourthEdition/Chapter_27/Section_27_3_Online_Caching.lean`
- Status: `main-proof-complete` (native fourth-edition source)
- Model:
  - `OnlineCaching.lruStep` / `OnlineCaching.lruRun` / `OnlineCaching.lruMisses`:
    the LRU policy with the cache as a most-recent-first list — a hit moves the
    page to the front, a miss prepends it, evicting the least-recently-used tail
    when the cache is full — and its miss count over a request sequence.
  - `OnlineCaching.Algorithm`: a bundled deterministic eviction algorithm over a
    `Finset` cache with laws that it loads the request, only ever adds the
    request, and keeps the cache at size at most `k`.
- Proved:
  - `OnlineCaching.distinct_fault`: a segment requesting `k + 1` distinct pages
    forces a miss for any size-`k` algorithm.
  - `OnlineCaching.resident_fault`: a page resident at the start of a segment
    that then requests `k` other distinct pages forces a miss.
  - `OnlineCaching.lru_miss_le_phases`: LRU makes at most `k` misses per phase,
    so its total miss count is bounded by `k` times the number of phases.
  - `OnlineCaching.phases_le_misses`: the number of phases is at most one more
    than the miss count of any size-`k` algorithm.
  - `OnlineCaching.lru_k_competitive` (Theorem 27.3): LRU is `k`-competitive.
  - `OnlineCaching.advSeq_misses`: the Sleator-Tarjan adversary (always request
    the page absent from the online algorithm's cache, over the `k + 1`-page
    universe `Fin (k + 1)`) faults the online algorithm on every request.
  - `OnlineCaching.offMisses_bound` / `offMisses_bound_from_full`: the
    phase-based offline schedule faults at most `(phases k σ).length + k` times
    from an empty cache, and at most once per phase from a full cache.
  - `OnlineCaching.caching_lower_bound` (Theorem 27.4): no deterministic online
    paging algorithm is better than `k`-competitive — for every `N` there is a
    request sequence of length `N` on which `A` faults `N` times while some
    offline schedule faults at most `N / k + k + 1` times.
  - `OnlineCaching.caching_no_c_competitive`: for any `c < k`, the length-`k^3`
    adversarial sequence witnesses that `c` times the offline cost is strictly
    below `A`'s miss count.
  - Supporting lemmas: `runGo_subset`, `runGo_size`,
    `missesGo_eq_zero_subset` (a run with no misses has all requested pages
    resident), `lru_head_evict`, `lru_miss_le_distinct`, and the offline
    `offlineStep` / `servePhase` / `servePhaseMisses_le` machinery.

## Chapter 28 - Matrix Operations

### Section 28.1 - Solving Systems of Linear Equations

- Lean source: `CLRSLean/FourthEdition/Chapter_28/Section_28_1_Linear_Equations.lean`
  (canonical fourth-edition Section 28.1; the legacy
  `CLRSLean/Chapter_28/Section_28_1_Linear_Equations.lean` forwards to it)
- Status: `selected-section-complete` (Theorem 28.1 proved)
- Model:
  - `CLRS.Chapter28.IsUpperTriangular` / `IsLowerTriangular` /
    `IsUnitLowerTriangular` (triangularity predicates)
  - `CLRS.Chapter28.elimination` (Gaussian-elimination step matrix)
  - `CLRS.Chapter28.finOneSumFin`: the `Fin (n+1) ≃ Fin 1 ⊕ Fin n` reindexing
    that views an `(n+1) × (n+1)` matrix as a `2 × 2` block matrix.
- Proved:
  - `exists_col_zero_ne_zero`: a nonsingular matrix has a nonzero first-column
    pivot (from `det_apply` and column-expansion).
  - `permMatrix_mul_apply`: `(σ.permMatrix * A) i j = A (σ i) j`.
  - `perm_mul_zero_zero_ne_zero`: pivoting makes the leading entry nonzero.
  - `elimination_unitLowerTriangular`, `elimination_mul_zero_zero`,
    `elimination_mul_col_zero`: the elimination step is unit lower-triangular,
    fixes the pivot, and zeroes the subdiagonal of column 0.
  - `det_unitLowerTriangular`: a unit lower-triangular matrix has determinant 1
    (via `exists_lt_of_perm_ne_id` on the permutation expansion).
  - `det_block_schur`: with the first column below the pivot zero,
    `det C = C 0 0 · det M` for the Schur complement `M`.
  - `fromBlocks_one_zero_zero_permMatrix`, `conjPermMatrix`: permutation-matrix
    bookkeeping for the block-diagonal and reindexed permutations.
  - `exists_lup_decomposition` (CLRS Theorem 28.1): every nonsingular `A` over a
    field admits `σ.permMatrix · A = L · U` with `σ` a permutation, `L` unit
    lower-triangular and `U` upper-triangular.  The proof is by induction on `n`:
    pivot the first column, apply one Gaussian-elimination step, apply the
    induction hypothesis to the (nonsingular) Schur complement, and assemble the
    block factors `L = [[1,0],[P₁·m, L₁]]`, `U = [[α,v],[0,U₁]]` with
    `σ = swap 0 p · diag(1, σ₁)`.
  - `lup_solve_correct` (CLRS §28.1, Algorithm LUP-SOLVE): if
    `σ.permMatrix · A = L · U` and the substitution equations `L·y = P·b`,
    `U·x = y` hold, then `A·x = b`.  The proof composes the two equations
    through the factorization and cancels the permutation matrix (`mulVec` of a
    permutation matrix is `v ↦ v∘σ`).
  - `forwardSubst` + `forwardSubst_spec` (CLRS Lemma 28.1): the constructive
    forward-substitution vector through a unit lower-triangular matrix,
    recursively `y₀ = b₀` then the tail through the trailing block, with
    `L·(forwardSubst L b) = b`.
  - `backSubst` + `backSubst_spec` (CLRS Lemma 28.2): the constructive
    backward-substitution vector through an upper-triangular matrix with
    nonzero diagonal, recursively `xₙ = yₙ/Uₙₙ` then the tail through the
    leading block, with `U·(backSubst U y) = y`.
  - `lupSolve` + `lupSolve_correct`: `lupSolve σ L U b` (forward-then-back
    substitution through the factors) solves `A·x = b` given an LUP
    decomposition, composing `forwardSubst_spec` and `backSubst_spec` through
    `lup_solve_correct`.
  - `exists_solution_of_nonsingular`: a nonsingular matrix over a field solves
    every linear system (`∃ x, A·x = b`), via `Matrix.isUnit_iff_isUnit_det`
    and `Matrix.mulVec_surjective_iff_isUnit`.
  - `unique_solution_of_nonsingular`, `unique_solution_unitLowerTriangular`,
    and `unique_solution_upperTriangular`: nonsingular, unit-lower-triangular,
    and upper-triangular systems with nonzero diagonal have at most one
    solution, via `mulVec_injective_iff_isUnit` (for the triangular cases,
    `det_unitLowerTriangular` and `Matrix.det_of_upperTriangular` give
    nonsingularity).
  - `det_eq_sign_mul_det_of_lup` (Corollary to Theorem 28.1): from
    `σ.permMatrix · A = L · U` with `L` unit lower-triangular,
    `det U = sign σ · det A` — determinants agree up to sign; with
    `det_ne_zero_of_lup` and `upperTriangular_diag_ne_zero_of_det_ne_zero`,
    `U` is nonsingular and has nonzero diagonal when `A` is.
  - Cost layer (`section Cost`): abstract operation counts matching the CLRS
    running times, with `isBigO` bounds — `substitutionCost_isBigO`
    (LUP-SOLVE `Θ(n²)`), `lupDecompositionCost_isBigO` (LUP `Θ(n³)`),
    `matrixInversionCost_isBigO` (inversion `Θ(n³)`), and
    `choleskyCost_isBigO` (Cholesky `Θ(n³)`).
### Section 28.2 - Inverting Matrices

- Lean source: `CLRSLean/FourthEdition/Chapter_28/Section_28_2_Inverting_Matrices.lean`
  (canonical fourth-edition Section 28.2; the legacy
  `CLRSLean/Chapter_28/Section_28_2_Inverting_Matrices.lean` forwards to it)
- Status: `selected-section-complete` (Theorem 28.2 proved)
- Proved:
  - `permMatrix_inv`: `(σ.permMatrix)⁻¹ = σ⁻¹.permMatrix`.
  - `permMatrix_mul_inv`: `(σ.permMatrix)⁻¹ * σ.permMatrix = 1`.
  - `inv_eq_lup` (CLRS Theorem 28.2): from an LUP factorization
    `σ.permMatrix · A = L · U`, `A⁻¹ = U⁻¹ · L⁻¹ · σ.permMatrix` — invert the
    triangular factors (`Matrix.mul_inv_rev`) and undo the row permutation.

### Section 28.3 - Symmetric Positive-Definite Matrices and Least Squares

- Lean source: `CLRSLean/FourthEdition/Chapter_28/Section_28_3_Symmetric_Positive_Definite.lean`
  (canonical fourth-edition Section 28.3; the legacy
  `CLRSLean/Chapter_28/Section_28_3_Symmetric_Positive_Definite.lean` forwards to it)
- Status: `complete`
- Model:
  - `IsSymPosDef`: the CLRS definition of symmetric positive-definite —
    symmetric and `xᵀAx > 0` for every nonzero `x`.
  - `residualSq`: the squared Euclidean 2-norm of the residual `A·x - b`
    (via `Matrix.dotProduct`, the Euclidean squared norm over `ℝ`).
  - `choleskySchur`: the Schur complement `A₂₂ - (v·vᵀ)/a` of the leading
    `1×1` block of `A` (the trailing block after one elimination step).
  - `IsLowerTriangularPosDiag` and `choleskyFactor`: the recursive Cholesky
    factor `L = [[√a, 0], [v/√a, L₂]]` built from `a = A 0 0`, the first
    column `v`, and the trailing factor `L₂`, with lower-triangularity and
    positive diagonal packaged as `IsLowerTriangularPosDiag`.
- Proved:
  - `isSymPosDef_iff_posDef`: SPD coincides with Mathlib's `Matrix.PosDef`,
    yielding `IsSymPosDef.det_pos` (nonsingular), `.diag_pos` (positive
    diagonal), `.mulVec_injective`, and `.isUnit`.
  - `posDef_mul_transpose`: if `A.mulVec` is injective (full column rank),
    then `AᵀA` is SPD — the nonsingularity of the Gram matrix behind the
    normal equations.
  - `normal_equations_minimizes` (CLRS Theorem 28.4): a solution of the normal
    equations `Aᵀ·(A·xh - b) = 0` minimizes the squared residual, via the
    Pythagorean decomposition `residual_sq_decomposition` (residual orthogonal
    to the column space).
  - `normal_equations_unique`: full column rank makes the minimizer unique.
  - `least_squares_closed_form` and `least_squares_closed_form_minimizes`:
    `xh = (AᵀA)⁻¹·(Aᵀ·b)` is the least-squares solution.
  - `cholesky_schur_complement`: the Schur complement of an SPD matrix is again
    SPD, proved directly via the block quadratic form `schur_quadratic_form`
    (`zᵀAz = a·t² + 2·t·(v ⬝ᵥ y) + yᵀA₂₂y` for `z = (t, y)`) and the choice
    `t = -(v ⬝ᵥ y)/a`.
  - `cholesky_decomposition` (CLRS Theorem 28.3): every SPD matrix factors as
    `A = L·Lᵀ` with `L` lower-triangular and positive diagonal.  The induction
    on `n` reuses `cholesky_schur_complement` to obtain the SPD Schur
    complement, applies the induction hypothesis to get `S = L₂·L₂ᵀ`, builds
    `L = choleskyFactor A L₂`, and proves `A = L·Lᵀ` entrywise via the block
    identities `choleskyFactor_mul_00/0_succ/succ_0/succ_succ_eq` (using
    `Real.sq_sqrt` and symmetry of `A`).
  - `cholesky_unique`: the Cholesky factor is unique — if `L₁` and `L₂` are
    lower-triangular with positive diagonal and `L₁·L₁ᵀ = L₂·L₂ᵀ`, then
    `L₁ = L₂`.  The block recursion compares `(0,0)` entries (equal squares,
    both positive), the first column, and applies the induction hypothesis to
    the trailing blocks; the entry expansions use
    `lowerTri_mul_transpose_00/0_succ/succ_succ`.

## Chapter 29 - Linear Programming

Canonical fourth-edition sources:
`CLRSLean/FourthEdition/Chapter_29/Section_29_1_Standard_And_Slack_Forms.lean`,
`CLRSLean/FourthEdition/Chapter_29/Section_29_2_Formulating_Problems_As_Linear_Programs.lean`,
and `CLRSLean/FourthEdition/Chapter_29/Section_29_3_Duality.lean` (fourth-edition
Sections 29.1--29.3; the legacy `CLRSLean/Chapter_29/Section_29_1`,
`Section_29_2`, and `Section_29_4` files forward to them).  The legacy
Sections 29.1--29.5 are main-proof-complete at the
finite real-matrix/pure-functional layer described below.  Fourth-edition
Chapter 29 remains partial under the canonical ledger: §29.1 lacks general-form
normalization and a main-text algorithm wrapper separated from online SIMPLEX;
§29.2's specialized problem predicates lack finite `StandardLP` encoding and
preservation bridges; and §29.3's strongest duality declarations still reside
in a legacy initialization module that is also cataloged as online material.
The detailed SIMPLEX algorithm (legacy Section 29.3) and the initial basic
feasible solution (legacy Section 29.5) are online material.

### Section 29.1 - Standard and Slack Forms

- Status: `main-proof-complete`.
- Model: `StandardLP`, `IsNonnegative`, `StandardLP.IsFeasible`, and
  `StandardLP.objective` over `Fin`-indexed real matrices.
- Proved: `slack_nonnegative_of_feasible`, `slack_equation`,
  `slackExtension_of_feasible`, `feasible_of_slackExtension`,
  `isFeasible_iff_exists_slackExtension`, `slackExtension_eq_slack`, and
  `existsUnique_slackExtension_iff`.
- Refinement bridge: `initialDictionary_satisfies_iff`,
  `initialDictionary_satisfies_of_slackExtension`, and
  `initialDictionary_objectiveRhs` connect the Section 29.1 model to the
  Section 29.3 dictionary layer.

### Section 29.2 - Formulating Problems as Linear Programs

- Status: `main-proof-complete`.
- Shortest path: `ShortestPathLP.IsFeasible` is the textbook edge-difference
  system with `d s = 0`; `feasible_le_walkWeight` proves every feasible target
  value is below every source-to-target walk, and `optimal_of_attained_walk`
  proves an attained bound is optimal.
- Network vocabulary: `FlowNetwork` uses one gross nonnegative flow variable
  per ordered vertex pair, with zero capacity representing a nonedge.
- Flow formulations: `MaximumFlowLP`, `MinimumCostFlowLP`, and
  `MulticommodityFlowLP` expose the textbook capacity, conservation, demand,
  aggregate-capacity, and cost objectives.  Their `*_iff` theorems expand the
  displayed LP constraints and optimality specifications exactly.

### Section 29.3 - The Simplex Algorithm

- Status: `main-proof-complete` for basic-feasible input dictionaries.
- Model: `LPVar`, `Dictionary`, a fixed row/column coefficient layout, and a
  variable-label equivalence that tracks the current basic and nonbasic sets.
- Basic-solution layer: `basicAssignment_satisfies`,
  `basicAssignment_nonnegative_iff`, and the initial-dictionary refinement
  theorems.
- PIVOT layer: the textbook `pivot` formulas, label-exchange theorems,
  `pivot_satisfies_iff`, and `pivot_objectiveRhs_eq` prove that PIVOT preserves
  exactly the represented assignments and objective expression.
- Progress layer: `IsMinimumRatio`, `pivot_isBasicFeasible`, `pivot_v_mono`,
  and `pivot_v_strict` prove the minimum-ratio feasibility and objective-value
  facts used by SIMPLEX.
- Control and exit layer: `blandEntering?`, `blandLeaving?`, `simplexStep`,
  `basicAssignment_optimal_of_reducedCosts_nonpos`, and
  `unbounded_of_entering_column` implement and justify all three textbook
  outcomes.
- Anti-cycling and termination: `bland_no_repeated_basis` formalizes the
  greatest-fickle-variable proof; `simplexRun_basisCount_not_exhausted` turns
  it into a finite bound; and `simplex_optimal_or_unbounded` is the public
  terminal-correctness theorem.
- Boundary: Section 29.5 supplies a basic-feasible start for arbitrary feasible
  standard-form inputs; Section 29.3 itself remains the reusable core for an
  already basic-feasible dictionary.

### Section 29.4 - Duality

- Status: `main-proof-complete`.
- Model: `StandardLP.IsDualFeasible` and `StandardLP.dualObjective`.
- Weak duality: dot-product monotonicity, `transpose_mulVec_dotProduct`, and
  `weak_duality` (CLRS Theorem 29.8).
- Certificate layer: `Dictionary.dualCertificate_isDualFeasible` and
  `dualCertificate_objective_eq_v` extract the terminal dual witness;
  `DictionaryBridge` transfers optimal and unbounded results to `StandardLP`.
- Strong duality: `strongDuality_or_unbounded_of_feasible`, `strongDuality`,
  and `strongDuality_of_isOptimal` prove the general textbook result through
  the finite initialized SIMPLEX construction.
- Complementary slackness: `dualityGap_eq_slackSums` proves the exact gap
  identity, and `complementarySlackness_iff_optimal` proves the unconditional
  feasible primal/dual criterion (CLRS Theorem 29.10).

### Section 29.5 - The Initial Basic Feasible Solution

- Status: `main-proof-complete`.
- Phase I: `auxiliary`, `auxiliaryPivotedDictionary_isBasicFeasible`, and
  `phaseOneRun_isOptimal` implement the artificial LP and the mandatory pivot
  from the most negative row.
- Feasibility criterion:
  `isFeasible_iff_phaseOneTerminal_v_eq_zero` proves that phase I ends at
  objective zero exactly when the original program is feasible.
- Cleanup and phase II: `lockVariable` is the fixed-dimension equivalent of
  deleting the zero artificial variable; `withObjective`, `phaseTwoStart`, and
  their equivalence theorems restore the original objective and produce a
  basic-feasible phase-II dictionary.
- Complete solver: `InitializedSimplexResult`, `initializedSimplex`, and
  `initializedSimplex_complete` certify exactly infeasible, optimal, or
  unbounded outcomes.
- Chapter boundary: Sections 29.1--29.5 are complete at the finite real-matrix
  and pure-functional tableau layer.  Mutable storage, floating-point
  stability, RAM constants, exercises, and chapter-end problems are optional
  refinements.

## Chapter 30 - Polynomials and the FFT

The sources below are the canonical fourth-edition Sections 30.1--30.3; the
legacy `CLRSLean/Chapter_30/Section_30_*` files forward to them during the
compatibility period.

### Section 30.1 - Polynomial Representations

- Lean sources:
  - `CLRSLean/FourthEdition/Chapter_30/Section_30_1_Representing_Polynomials.lean`
  - `CLRSLean/FourthEdition/Chapter_30/Section_30_1_Representing_Polynomials/S1_CoefficientVectors.lean`
  - `CLRSLean/FourthEdition/Chapter_30/Section_30_1_Representing_Polynomials/S2_PointValueInterpolation.lean`
  - `CLRSLean/FourthEdition/Chapter_30/Section_30_1_Representing_Polynomials/S3_RepresentationOperations.lean`
- Status: `proved` for the milestone's fixed-capacity representation and
  represented arithmetic-cost boundary.
- Representation bridge:
  - `CLRS.Chapter30.vectorToPolynomial_coeff`
  - `CLRS.Chapter30.coeffVector_vectorToPolynomial`
  - `CLRS.Chapter30.vectorToPolynomial_coeffVector`
  - `CLRS.Chapter30.vectorToPolynomial_degree_lt`
- Evaluation and interpolation:
  - `CLRS.Chapter30.hornerEval_correct`
  - `CLRS.Chapter30.hornerEvalWork_exact` (exact work `2 * n`)
  - `CLRS.Chapter30.pointValues_injective`
  - `CLRS.Chapter30.interpolate_pointValues`
  - `CLRS.Chapter30.interpolate_unique`
  - `CLRS.Chapter30.interpolate_pointValues_roundTrip`
- Representation operations and attached costs:
  - `CLRS.Chapter30.pointValues_add` and `CLRS.Chapter30.pointValues_mul`
  - `CLRS.Chapter30.vectorAddWork_exact` and
    `CLRS.Chapter30.pointwiseMulWork_exact`
  - `CLRS.Chapter30.schoolbookMul_correct`
  - `CLRS.Chapter30.schoolbookMul_degreeBound`
  - `CLRS.Chapter30.schoolbookMulWork_exact` (exact work `2 * (m * n)`)
- Execution boundary: `coefficientPairs_toFinset` proves that the executable
  deterministic pair list enumerates the full Cartesian product; each
  `schoolbookStep` performs one bucket update and increments both counters.

### Section 30.2 - DFT, Recursive FFT, and Polynomial Multiplication

- Lean sources:
  - `CLRSLean/Chapter_30.lean`
  - `CLRSLean/FourthEdition/Chapter_30/Section_30_2_DFT_And_FFT.lean`
  - `CLRSLean/FourthEdition/Chapter_30/Section_30_2_DFT_And_FFT/S1_RootsOfUnity.lean`
  - `CLRSLean/FourthEdition/Chapter_30/Section_30_2_DFT_And_FFT/S2_DFT.lean`
  - `CLRSLean/FourthEdition/Chapter_30/Section_30_2_DFT_And_FFT/S3_InversionAndConvolution.lean`
  - `CLRSLean/FourthEdition/Chapter_30/Section_30_2_DFT_And_FFT/RecursiveFFT.lean`
  - `CLRSLean/FourthEdition/Chapter_30/Section_30_2_DFT_And_FFT/RecursiveFFT/Definitions.lean`
  - `CLRSLean/FourthEdition/Chapter_30/Section_30_2_DFT_And_FFT/RecursiveFFT/Correctness.lean`
  - `CLRSLean/FourthEdition/Chapter_30/Section_30_2_DFT_And_FFT/RecursiveFFT/Costs.lean`
  - `CLRSLean/FourthEdition/Chapter_30/Section_30_2_DFT_And_FFT/PolynomialMultiplication.lean`
- Status: `proved` for the milestone's exact-field DFT, recursive radix-2 FFT,
  inverse, polynomial multiplication, and declared arithmetic-cost boundary;
  Section 30.3 below completes the chapter's reviewed main-text boundary.
- Roots of unity and DFT evaluation:
  - `CLRS.Chapter30.primitiveRoot_powers_injective`
  - `CLRS.Chapter30.primitiveRoot_square` and
    `CLRS.Chapter30.primitiveRoot_half_pow_eq_neg_one`
  - `CLRS.Chapter30.root_sum_orthogonality` and
    `CLRS.Chapter30.root_sum_difference_orthogonality`
  - `CLRS.Chapter30.dft_eq_pointValues`, `CLRS.Chapter30.dft_add`, and
    `CLRS.Chapter30.dft_smul`
  - `CLRS.Chapter30.complexDft_mathlib`, with Mathlib's negative-sign
    convention exposed by explicit output-index negation
- Fourier inversion and convolution:
  - `CLRS.Chapter30.idft_dft` and `CLRS.Chapter30.dft_idft`
  - `CLRS.Chapter30.dft_injective`
  - `CLRS.Chapter30.dft_cyclicConvolution` and
    `CLRS.Chapter30.idft_pointwiseMul`
  - `CLRS.Chapter30.cyclicConvolution_eq_coeffVector_mul`, under the explicit
    capacity condition that the polynomial product fits
- Recursive FFT execution and correctness:
  - `CLRS.Chapter30.recursiveFFTExec` recursively transforms the actual even
    and odd coefficient vectors, reuses the charged twiddle execution for the
    squared child root, and combines both children with one butterfly layer
  - `CLRS.Chapter30.recursiveFFTExec_value` erases the costed execution to
    `CLRS.Chapter30.recursiveFFT`
  - `CLRS.Chapter30.polynomial_evenOdd_split` supplies the polynomial identity
    used by the structural proof `CLRS.Chapter30.recursiveFFT_eq_dft`
  - `CLRS.Chapter30.recursiveIFFT_eq_idft`,
    `CLRS.Chapter30.recursiveIFFT_recursiveFFT`, and
    `CLRS.Chapter30.recursiveFFT_recursiveIFFT` connect the recursive inverse
    to both Fourier round trips
- Recursive FFT costs and padding:
  - `CLRS.Chapter30.recursiveFFTExec_addSubtractions` and
    `CLRS.Chapter30.recursiveFFTExec_multiplications` each prove the exact
    execution-field count `k * 2^k`
  - `CLRS.Chapter30.recursiveFFTWork_exact` proves exact total work
    `2 * k * 2^k` from those same fields
  - `CLRS.Chapter30.fftCapacity_ge` and
    `CLRS.Chapter30.fftCapacity_lt_two_mul` bound least-power-of-two padding
  - `CLRS.Chapter30.recursiveFFTExec_zeroPad_work` keeps padded work attached
    to an actual zero-padded recursive execution, while
    `CLRS.Chapter30.paddedFFTWork_allInput_bigTheta` proves all-input
    `Theta(n log n)`
- FFT polynomial multiplication:
  - `CLRS.Chapter30.fftMultiplyExecAt` composes two forward recursive FFTs,
    pointwise multiplication, an inverse-root recursive FFT, inverse scaling,
    and polynomial reconstruction in one execution record
  - `CLRS.Chapter30.fftMultiplyExecAt_value` erases the costed execution, and
    `CLRS.Chapter30.fftMultiplyAt_correct` proves equality with `p * q` under
    the minimal product-fit premise
  - `CLRS.Chapter30.complexFFTMultiply_correct` is unconditional: the wrapper
    computes a positive size, least power-of-two capacity, and positive-sign
    principal complex root internally
  - `CLRS.Chapter30.fftMultiplyExecution_correct` and
    `CLRS.Chapter30.fftMultiplyExecution_work_eq` put bounded-input correctness
    and cost on the same selected execution
- FFT multiplication costs:
  - `CLRS.Chapter30.fftMultiplyExecAt_work_exact` reads the actual execution
    fields and proves `3 * radix2FFTWork k + 2 * 2^k`
  - `CLRS.Chapter30.fftMultiplyWork_pow` retains the pointwise/scaling term and
    gives `(12*k + 16) * 2^k` at advertised capacity `2^k`
  - `CLRS.Chapter30.fftMultiplyWork_allInput_bigTheta` proves all-input
    `Theta(n log n)` through the Chapter 4 adjacent-power transfer

### Section 30.3 - Efficient FFT Implementations

- Lean sources:
  - `CLRSLean/FourthEdition/Chapter_30/Section_30_3_Efficient_FFT_Implementations.lean`
  - `CLRSLean/FourthEdition/Chapter_30/Section_30_3_Efficient_FFT_Implementations/BitReversal.lean`
  - `CLRSLean/FourthEdition/Chapter_30/Section_30_3_Efficient_FFT_Implementations/IterativeFFT.lean`
  - `CLRSLean/FourthEdition/Chapter_30/Section_30_3_Efficient_FFT_Implementations/IterativeFFT/Definitions.lean`
  - `CLRSLean/FourthEdition/Chapter_30/Section_30_3_Efficient_FFT_Implementations/IterativeFFT/Correctness.lean`
  - `CLRSLean/FourthEdition/Chapter_30/Section_30_3_Efficient_FFT_Implementations/IterativeFFT/Costs.lean`
  - `CLRSLean/FourthEdition/Chapter_30/Section_30_3_Efficient_FFT_Implementations/ParallelFFT.lean`
- Status: `proved` for the exact functional iterative-FFT and layered-circuit
  boundary.  The Milestone 2 closure interface contributes 17 reviewed
  headline theorem groups, bringing Chapter 30's tracked total to 46.
- Bit reversal:
  - `CLRS.Chapter30.bitReverseEquiv_even` and
    `CLRS.Chapter30.bitReverseEquiv_odd` give the recursive index structure;
    `CLRS.Chapter30.bitReverseEquiv_testBit` gives fixed-width numeric bit
    semantics and `CLRS.Chapter30.bitReverseEquiv_involutive` proves the
    permutation is its own inverse
  - `CLRS.Chapter30.bitReverseCopy_apply` and
    `CLRS.Chapter30.bitReverseCopy_involutive` specify the functional copy;
    `CLRS.Chapter30.bitReverseExec_moves` reads the exact `2^k` moves from its
    execution record
- Flat stages and correctness:
  - `CLRS.Chapter30.fftStage` applies all independent butterflies at one
    globally indexed stage; `CLRS.Chapter30.runFFTStagePrefix_join` is the
    half-factorization invariant for every prefix
  - `CLRS.Chapter30.iterativeRadix2FFT_succ` recovers the recursive butterfly
    equation, while `CLRS.Chapter30.iterativeRadix2FFT_eq_recursiveFFT` and
    `CLRS.Chapter30.iterativeRadix2FFT_eq_dft` close the algorithmic and
    algebraic correctness bridges
- Execution-attached costs:
  - stage and prefix counters are proved exact, and the complete execution has
    `k * 2^k` additions/subtractions and `k * 2^k` multiplications
  - `CLRS.Chapter30.iterativeRadix2FFTExec_arithmeticWork` proves execution
    arithmetic `2 * k * 2^k`
  - `CLRS.Chapter30.iterativeRadix2FFTExec_totalWork` additionally charges the
    bit-reversal copy, giving `2^k + 2 * k * 2^k`
  - `CLRS.Chapter30.iterativeRadix2FFTExec_zeroPad_totalWork` attaches padded
    work to the actual zero-padded execution, and
    `CLRS.Chapter30.paddedIterativeFFTWork_allInput_bigTheta` proves all-input
    `Theta(n log n)`
- Layered circuit:
  - `CLRS.Chapter30.FFTButterflyGate` stores one fixed twiddle and its `eval`
    operation performs the radix-2 butterfly; `ButterflyLayerCircuit` stores
    one such gate at every local offset
  - `CLRS.Chapter30.canonicalButterflyLayerCircuit_eval` bridges a stored gate
    family to `butterflyLayer`, and `CLRS.Chapter30.fftStageCircuit_eval`
    recursively bridges the actual stage syntax to `fftStage`
  - `CLRS.Chapter30.fftNetwork_eval` therefore proves that interpreting the
    circuits stored by the ordered network evaluates to the iterative FFT
  - `CLRS.Chapter30.fftNetwork_butterflyCount` and
    `CLRS.Chapter30.fftNetwork_butterflyDepth` fold the same stored syntax and
    prove `k * 2^(k-1)` butterflies at depth `k`
  - treating twiddle powers as fixed constants and bit reversal as wiring,
    `CLRS.Chapter30.fftNetwork_primitiveGateCount` proves primitive gates
    `3 * k * 2^(k-1)`, while
    `CLRS.Chapter30.fftNetwork_primitiveDepth` proves primitive depth `2 * k`
- Chapter boundary: Sections 30.1--30.3 are complete for exact generic ring or
  characteristic-zero field arithmetic over fixed and power-of-two vectors.
  Mutable arrays, aliasing and in-place loop semantics; RAM, cache, allocator,
  SIMD, GPU, communication, scheduler and processor costs; floating-point
  error and numerical stability; NTT specialization; code generation;
  exercises; and Problems 30-1 through 30-6 are outside the reviewed boundary.

### Chapter 30 completion boundary

- Status: `main-proof-complete`.
- Legacy source inventory: 46 proved theorem groups. The canonical
  fourth-edition Chapter 30 ledger counts 34 groups; 12 bit-reversal and
  iterative-FFT groups are recorded separately as online material.
- Stable interface and closure tests:
  - `Tests/Chapter_30_Interface.lean`
  - `Tests/Chapter_30_DFT_Interface.lean`
  - `Tests/Chapter_30_RecursiveFFT_Interface.lean`
  - `Tests/Chapter_30_PolynomialMultiplication_Interface.lean`
  - `Tests/Chapter_30_Milestone1_Closure.lean`
  - `Tests/Chapter_30_BitReversal_Interface.lean`
  - `Tests/Chapter_30_IterativeFFT_Interface.lean`
  - `Tests/Chapter_30_ParallelFFT_Interface.lean`
  - `Tests/Chapter_30_Milestone2_Closure.lean`
- Closure audits:
  - `docs/proof-audits/chapter-30-milestone-1-2026-08-05.md`
  - `docs/proof-audits/chapter-30-milestone-2-2026-08-05.md`
- The exact generic-arithmetic functional boundary is closed. Mutable and
  in-place arrays, machine-level costs, floating-point analysis, concrete
  scheduling, NTT specialization, code generation, exercises, and Problems
  30-1 through 30-6 are optional new layers, not missing Chapter 30 core work.

## Chapter 31 - Number-Theoretic Algorithms

The sources below are the canonical fourth-edition Sections 31.1--31.8; the legacy `CLRSLean/FourthEdition/Chapter_31/Section_*` files forward to them during the compatibility period.

### Section 31.1 - Elementary Number-Theoretic Notions

- Lean source: `CLRSLean/FourthEdition/Chapter_31/Section_31_1_Elementary_Number_Theory.lean`
- Status: `selected-section-complete`
- Model:
  - `IsGCD`: the greatest-common-divisor property predicate (divides both, and
    is divisible by every common divisor — the universal form).
- Proved:
  - `division_theorem` (CLRS Theorem 31.1): for `b > 0`, `a = q·b + r` with
    `r < b` has a unique `(q, r)`, via `Nat.div_add_mod`/`Nat.mod_lt` and the
    pairwise-uniqueness helper `division_unique`.
  - `nat_gcd_isGCD` / `IsGCD.eq_gcd`: `Nat.gcd` satisfies the gcd property and
    the property determines the value.
  - `divides_refl/zero/trans/mul_right/add/sub` and
    `divides_linear_combination` (CLRS Lemma 31.1): the basic divisibility
    facts.
  - `coprime_iff_gcd_eq_one` / `coprime_iff_no_common_divisor`,
    `prime_def_gt_one` / `prime_two`, and `exists_prime_ge` (Euclid's theorem:
    infinitely many primes, via `Nat.exists_infinite_primes`).

### Section 31.2 - Greatest Common Divisor

- Lean source: `CLRSLean/FourthEdition/Chapter_31/Section_31_2_Greatest_Common_Divisor.lean`
- Status: `selected-section-complete`
- Proved:
  - `euclid_recursion` / `gcd_zero_left` / `gcd_zero_right` (CLRS Theorem 31.9,
    the GCD recursion theorem):
    the Euclid recursion `gcd(a, b) = gcd(b mod a, a)` and the base cases.
  - `euclid` + `euclid_eq_gcd` + `euclid_terminates`: the EUCLID algorithm is a
    total, well-founded function and returns `Nat.gcd a b` (via
    `Nat.gcd.induction` and `Nat.gcd_succ`).
  - `gcd_is_linear_combination` (CLRS Lemma 31.3, Bezout): `gcd a b` is an
    integer linear combination of `a` and `b` (`Nat.gcd_eq_gcd_ab`).
  - `gcd_dvd_linear_combination` (CLRS Corollary 31.3): `gcd a b` divides
    every linear combination of `a` and `b`.
  - `gcd_is_smallest_positive_linear_combination` (CLRS Theorem 31.2): `gcd
    a b` is the smallest positive linear combination of `a` and `b` (when
    `a ≠ 0 ∨ b ≠ 0`), via the Bezout combination plus `Int.le_of_dvd`.
  - `gcd_eq_one_iff_coprime` / `coprime_iff_one_linear_combination` /
    `gcd_div_gcd_coprime` (CLRS Corollary 31.4): coprime characterizations,
    including `coprime (a/g) (b/g)` for `g = gcd a b`.
  - `extendedEuclid` + `extendedEuclid_spec`: EXTENDED-EUCLID returns
    `(d, x, y)` with `d = gcd a b = a·x + b·y`.
  - Running time (Lamé / Fibonacci): `euclidDivisions` counts the recursive
    calls of `EUCLID` (CLRS recursion `EUCLID(a, b) = EUCLID(b, a mod b)`).
    `fib_le_of_euclidDivisions` (CLRS Lemma 31.10): `k` calls with `a > b ≥ 1`
    force `b ≥ F_{k+1}` and `a ≥ F_{k+2}`, proved by strong induction on `b`
    (base case `a ≥ 2b` when `a mod b = 0`; step via `F_{k+3} = F_{k+1} +
    F_{k+2}` and `a ≥ b + (a mod b)`).
    `euclidDivisions_lt` (CLRS Theorem 31.11, **Lamé's theorem**): for
    `k ≥ 1`, `b < F_{k+1}` implies fewer than `k` calls (contrapositive via
    `Nat.fib_mono`).
    `euclidDivisions_le_two_log` (CLRS Corollary 31.12): at most
    `2·log₂ b + 2` calls, i.e. `O(log b)`, via the exponential growth lemmas
    `fib_two_step_ge_pow_two` and `pow_two_le_fib` (`2^(n/2) ≤ F_{n+2}`) and
    `Nat.le_log_of_pow_le`.

### Section 31.3 - Modular Arithmetic

- Lean source: `CLRSLean/FourthEdition/Chapter_31/Section_31_3_Modular_Arithmetic.lean`
- Status: `selected-section-complete`
- Proved:
  - `mod_add` / `mod_mul` (CLRS Theorem 31.5): addition and multiplication
    modulo `n` are well-defined on residues.
  - `exists_mul_inverse_mod` (CLRS Theorem 31.6): `gcd(a,n)=1` gives `a` a
    multiplicative inverse modulo `n`, via `ZMod` units.
  - `mul_left_cancel_mod` (CLRS Theorem 31.9): cancellation in `Z_n` when
    `gcd(c,n)=1`.
  - `modular_linear_solvable` (CLRS Corollary 31.21): `a·x ≡ b (mod n)` is
    solvable iff `gcd(a,n) ∣ b`, via the `ZMod` quotient hom and Bezout.

### Section 31.4 - Solving Modular Linear Equations

- Lean source: `CLRSLean/FourthEdition/Chapter_31/Section_31_4_Solving_Modular_Linear_Equations.lean`
- Status: `selected-section-complete`
- Proved:
  - `linear_congruence_shift`: `x + k·(n/gcd(a,n))` preserves solutions.
  - `linear_congruence_all_solutions`: every solution differs from any given
    solution by a multiple of `n/gcd(a,n)` — the `d = gcd(a,n)` solutions are
    `x₀ + k·(n/d)`.

### Section 31.5 - The Chinese Remainder Theorem

- Lean source: `CLRSLean/FourthEdition/Chapter_31/Section_31_5_Chinese_Remainder_Theorem.lean`
- Status: `selected-section-complete`
- Proved:
  - `chinese_remainder_two` / `chinese_remainder_unique` /
    `chinese_remainder` (CLRS Theorem 31.27, two moduli): for coprime `n m`,
    the system `x ≡ a (mod n)`, `x ≡ b (mod m)` has a unique solution modulo
    `n·m`, via `Nat.chineseRemainder`.

### Section 31.6 - Powers of an Element

- Lean source: `CLRSLean/FourthEdition/Chapter_31/Section_31_6_Powers_Of_An_Element.lean`
- Status: `selected-section-complete`
- Proved:
  - `modularExponentiation` + `modularExponentiation_spec` (CLRS
    MODULAR-EXPONENTIATION).
  - `fermat_little_theorem` (CLRS Theorem 31.31): prime `p` gives
    `a^p ≡ a (mod p)`, via `ZMod.pow_card`.
  - `euler_theorem` (CLRS Theorem 31.30): `gcd(a,n)=1` gives `a^φ(n) ≡ 1 (mod n)`.

### Section 31.7 - The RSA Public-Key Cryptosystem

- Lean source: `CLRSLean/FourthEdition/Chapter_31/Section_31_7_RSA.lean`
- Status: `selected-section-complete`
- Proved:
  - `totient_mul_prime`: `φ(p·q) = (p−1)(q−1)` for distinct primes.
  - `rsa_correct` (CLRS Theorem 31.36): `e·d ≡ 1 (mod φ(n))` and
    `gcd(m,n)=1` imply `m^(e·d) ≡ m (mod n)`.

### Section 31.8 - Primality Testing

- Lean source: `CLRSLean/FourthEdition/Chapter_31/Section_31_8_Primality_Testing.lean`
- Status: `selected-section-complete`
- Proved:
  - `fermat_test` (CLRS Theorem 31.31): prime `p` and `gcd(a,p)=1` give
    `a^(p−1) ≡ 1 (mod p)`.
  - `fermatPseudoprime`, `pseudoprime` + `pseudoprime_correct` (PSEUDOPRIME).
  - `isCarmichael` (**Carmichael numbers**): composite `n` passing the Fermat
    test `a^(n−1) ≡ 1 (mod n)` for every `a` coprime to `n`;
    `carmichael_fermatPseudoprime` shows such `n` fool the Fermat test for
    every coprime base.
  - `isCarmichael_561`: 561 is a Carmichael number — via `fermat_test` for the
    prime factors 3, 11, 17 (with `2·280`, `10·56`, `16·35` all equal to 560)
    and the helper `modeq_of_coprime_mul` combining congruences under coprime
    moduli.  This shows `PSEUDOPRIME` cannot certify primality.
  - `strongTestParams` / `strongPseudoprime` / `Witness` / `millerRabin`
    (Miller-Rabin): the `2^s·d` decomposition of `n−1` (via `Nat.factorization`),
    the STRONG-PSEUDOPRIME condition, the witness predicate, and the executable
    single-base test.  `millerRabin 561 2` evaluates to `false`: although 561 is
    a Carmichael number, base 2 witnesses that it is composite.
  - Miller-Rabin correctness: `strongPseudoprime_of_prime` (a prime is a strong
    probable prime to every coprime base), proved via Fermat, the minimal-index
    argument (`Nat.find`), and the roots-of-unity fact
    `modeq_neg_one_of_sq_eq_one` (`x² ≡ 1`, `x ≢ 1` mod prime ⇒ `x ≡ −1`).
    `not_witness_of_prime` (a prime has no witness) and `witness_not_prime`
    (a witness certifies compositeness) follow.
  - **Miller-Rabin error bound (Rabin–Monier)**: the good subgroup
    `goodUnits` = `{x : x^(2^(ν(n)−1)·t) ∈ {±1}}`, with `liar_mem_goodSet`
    showing every strong liar lies in it.  Counting `|S(n)|` via the cyclicity
    of prime-power unit groups and the CRT (`card_pow_eq_one_crt`,
    `mTorsion_eq_prod`), `goodUnits_card_le` bounds `|S(n)| ≤ (n−1)/4` by the
    three-case analysis: prime power (`n = p^e`), semiprime (`n = p·q`, with
    the `s < r` / `s = r` sub-cases and the key lemma that `d_p | t ∧ d_q | t`
    forces `p = q`), and `≥ 3` prime factors.  Hence `strongLiars_card_le`:
    **at most `(n−1)/4` of the bases are strong liars for odd composite `n`**
    (Theorem 31.39, sharpened to `(n−1)/4` by Rabin–Monier).  Deferred: the
    random-witness analysis.

### Section 31.9 - Integer Factorization

- Lean source: `CLRSLean/Chapter_31/Section_31_9_Integer_Factorization.lean`
- Status: `selected-section-complete`
- Proved:
  - `rhoStep` (Pollard's rho iteration).
  - `rho_collision_factor`: `x ≡ y (mod p)` and `p ∣ n` imply
    `p ∣ gcd(x−y, n)` — a collision forces a nontrivial divisor.
    `rho_collision_factor_dist` is the `|y−x|` (`Nat.dist`) version.
  - POLLARD-RHO: `RhoState` (tortoise-and-hare state), `pollardStep`
    (one step, reporting `gcd (|y−x|, n)`), `pollardRhoLoop` (over a step
    budget), and `pollardRho` (the full algorithm).  Soundness:
    `pollardRho_sound` — a returned value ≠ `n` is a nontrivial divisor of
    `n`; `pollardStep_collision_factor` — a mod-`p` collision at a step makes
    that step's candidate a multiple of `p`.
  - Probabilistic analysis (CLRS Theorem 31.40), inside the explicit
    i.i.d.-uniform model `Fin k → Fin p` (the CLRS "rho heuristic" made
    precise): `noCollision_prob_eq` (`P[no collision] = descFactorial p k /
    p^k`), `birthday_noCollision_le` (`≤ exp(−k(k−1)/(2p))`),
    `birthday_collision_ge`, and `birthday_collision_prob_ge_half`
    (collision with probability ≥ 1/2 once `2p ≤ k(k−1)`).
  - Expected `O(√p)` running time: the independent-rounds model with the
    geometric tail-sum gives `rho_expected_rounds_le_two` and
    `rho_expected_draws_le` (expected draws ≤ 2k for `2p ≤ k(k−1)`).
  - Detection, bound to the real construction (unconditional):
    `RhoState_valid` / `pollardStep_valid` (the `x < n ∧ y < n` invariant),
    `pollardStep_detects` / `pollardRhoLoop_terminates_on_collision` (a mod-`p`
    collision of a fresh value with the snapshot forces a nontrivial divisor).

## Chapter 32 - String Matching

The sources below are the canonical fourth-edition Sections 32.1–32.5; the legacy `CLRSLean/FourthEdition/Chapter_32/Section_*` files forward to them during the compatibility period.

### Section 32.1 - The Naive String-Matching Algorithm

- Lean sources:
  - `CLRSLean/Chapter_32.lean`
  - `CLRSLean/FourthEdition/Chapter_32/Section_32_1_String_Model.lean`
  - `CLRSLean/FourthEdition/Chapter_32/Section_32_1_String_Model/Naive_Matcher.lean`
- Status: `selected-section-complete`
- Main results: the `Text` prefix/suffix model and its 14 supporting theorems,
  plus `matchesAt`, `naiveMatcher`, `naiveMatcher_sound`,
  `naiveMatcher_complete`, and the three represented boundary theorems.

### Section 32.2 - The Rabin-Karp Algorithm

- Lean source: `CLRSLean/FourthEdition/Chapter_32/Section_32_2_Rabin_Karp.lean`
- Status: `complete` (native fourth-edition source; the full CLRS window-slide
  recurrence, eq. (32.3), is left as a named gap)
- Model:
  - `hash d q val w`: the base-`d` modular hash of `w` over the numeric values
    `val c`, computed by Horner's rule modulo `q`.
  - `rabinKarpMatcher T P d q val`: the hash-and-confirm matcher returning every
    shift where `P` occurs in `T` (hash match plus explicit comparison),
    mirroring `naiveMatcher`.
- Proved:
  - `hash_snoc`: the `O(1)` incremental update
    `hash (w ++ [c]) = (hash w · d + val c) mod q`.
  - `hash_eq_of_text_eq`: equal strings hash equal, so a real match is never
    discarded as a spurious hit.
  - `rabinKarp_sound` / `rabinKarp_complete` / `rabinKarp_correct`: the matcher
    returns exactly the valid shifts, and agrees with `naiveMatcher` on every
    shift.

### Section 32.3 - String Matching with Finite Automata

- Lean source: `CLRSLean/FourthEdition/Chapter_32/Section_32_3_Finite_Automata.lean`
- Status: `complete` (native fourth-edition source)
- Model:
  - `suffixTest p t` / `suffixLen P x`: "`p` is a suffix of `t`" and the suffix
    function `σ(x)`.
  - `delta P q a` / `deltaStar P q t`: the transition `δ(q, a) = σ(P_q a)` and
    its extension to a string.
  - `transitionTable` / `transitionLookup`: the finite-alphabet transition
    table; `dfaMatcher` / `dfaMatcherTable`: the automaton matcher and its
    table-driven refinement.
- Proved:
  - `suffixLen_snoc_le` (CLRS Lemma 32.3): `σ(xa) ≤ σ(x) + 1`.
  - `suffixLen_snoc_eq` (CLRS Lemma 32.4): `σ(xa) = σ(P_{σ(x)} a)`.
  - `deltaStar_eq_suffixLen` / `deltaStar_accepts_iff_suffix`:
    `δ*(q, T) = σ(P_q T)`, and `δ*(0, T) = |P| ↔ P` is a suffix of `T`.
  - `dfaMatcher_sound` / `dfaMatcher_complete` / `dfaMatcher_correct`: the
    all-occurrences automaton matcher is sound, complete, and equivalent to
    `naiveMatcher`.
  - `transitionLookup_eq_delta` / `dfaMatcherTable_correct`: the table lookup is
    exactly `δ`, and the table-driven matcher refines `dfaMatcher`.
  - `transitionTableBuildCost_eq` / `dfaMatcherCost_eq`: preprocessing costs
    `(|P| + 1)·|Σ|` and matching is `Θ(|T|)`.

### Section 32.4 - The Knuth-Morris-Pratt Algorithm

- Lean source: `CLRSLean/FourthEdition/Chapter_32/Section_32_4_Knuth_Morris_Pratt.lean`
- Status: `complete` (native fourth-edition source: the executable prefix
  function, the all-occurrences KMP scan, and the costed linear-time bound are
  all kernel-checked)
- Model:
  - `prefixLen P q`: the prefix function `π(q)` — the longest proper prefix of
    `P` that is a suffix of `P.take q`.
  - `computePrefixFunction P`: the executable `COMPUTE-PREFIX-FUNCTION`
    (failure-link recurrence).
  - `failureFollow`: follows failure links `π[k-1]` while `P[k] ≠ c`.
  - `kmpMatcher P T`: the executable all-occurrences `KMP-MATCHER` scan,
    maintaining the automaton state `q = δ*(0, scanned)`.
  - Cost model: one unit per failure-link traversal plus one unit per character
    processed, charged by the `*WithCost` instrumentation.
- Proved:
  - `prefixLen_satisfies` / `prefixLen_maximal`: `P.take (π q)` is the longest
    proper prefix of `P` that is a suffix of `P.take q`.
  - `prefixLen_chain_step` (CLRS Lemma 32.5): a shorter prefix-suffix of
    `P.take q` is a prefix-suffix of `P.take (π q)`.
  - `prefixLen_snoc_eq` (CLRS Lemma 32.6): `π(q+1)` extends the longest
    prefix-suffix of `P.take q` whose next character matches `P[q]`.
  - `failureFollow_eq_prefixMatchAux`: following failure links from `π(q)`
    agrees with the from-scratch search.
  - `computePrefixFunction_correct`: each entry of the executable array equals
    `prefixLen`.
  - `kmpStep_eq_delta`: one executable scan step computes the automaton
    transition `δ(q, a)`.
  - `kmpMatcher_correct` (with `kmpMatcher_sound` / `kmpMatcher_complete`):
    `kmpMatcher P T` agrees with `naiveMatcher T P`, returning all and only the
    occurrences.
  - `computePrefixFunctionWithCost_cost_le` / `kmpMatcherWithCost_cost_le`:
    the costed prefix construction and scan are each linear.
  - `kmpTotalCost_le`: the combined prefix-construction plus scan work is
    `O(|P| + |T|)`.

### Section 32.5 - Suffix Arrays

- Lean source: `CLRSLean/FourthEdition/Chapter_32/Section_32_5_Suffix_Arrays.lean`
- Status: `complete` for the suffix-array model, the `O(n log n)`
  comparison-model construction, and the `O(|p| log n)` binary-search range
  query (native fourth-edition source); the scan-based `suffixArraySearch`
  remains the proved correctness baseline.
- Model:
  - `suffixAt t i`: the suffix of `t` starting at position `i` (`t.drop i`).
  - `suffixLe t i j`: lexicographic order on suffixes with ties broken by
    starting position (decidable, total, transitive).
  - `SuffixArrayValid t sa`: `sa` is a permutation of `range t.length` sorted
    by `suffixLe`.
  - Comparison model for the fast construction: one unit of work per
    lexicographic suffix comparison (`suffixCompare`).
  - String-comparison model for the range query: a pattern–suffix probe
    (`patternLE` / `patternGT`) is charged `|p| + 1` character comparisons.
- Proved:
  - `suffixArray_valid`: the executable `suffixArray` construction returns a
    valid suffix array (permutation + sortedness via `insertionSort`).
  - `suffixArraySearch_mem_iff`: suffix-array pattern search is sound and
    complete — `i` is returned exactly when `p` is a prefix of `suffixAt t i`.
  - `mergeSortWithCost_cost_le_clog` / `_cost_le_log`: the costed merge sort
    makes at most `n · ⌈log₂ n⌉` / `n · (⌊log₂ n⌋ + 1)` comparisons.
  - `suffixArrayFast_valid`: the fast construction satisfies
    `SuffixArrayValid`.
  - `suffixArrayFast_work_le` / `suffixArrayFast_work_isBigO_nlogn`: the fast
    construction is `O(n log n)` under the comparison model.
  - `binarySearchFirst_spec` / `binarySearchFirstCost_cost_le`: the reusable
    costed binary search returns the first true index under a monotone
    predicate, in at most `⌈log₂(n+1)⌉` probes.
  - `suffixArrayRange_mem_iff`: the binary-search range query is sound and
    complete — it returns exactly the positions at which `p` occurs.
  - `suffixArrayQueryWork_le` / `suffixArrayQueryWork_isBigO_logn`: the range
    query costs at most `2 · (|p| + 1) · (⌊log₂ n⌋ + 2)` character comparisons,
    i.e. `O(|p| log n)`.

## Fourth Edition Chapter 33 - Machine-Learning Algorithms

### Section 33.1 - Clustering

- Lean source: `CLRSLean/FourthEdition/Chapter_33/Section_33_1_Clustering.lean`
- Status: `complete` (native fourth-edition source)
- Model:
  - `sumSqDist`: the within-cluster sum of squared distances to a candidate center.
  - `mean`: the centroid (average) of a finite point family over an index set.
  - `Clustering`: an assignment of each point to a cluster together with one
    centroid per cluster.
  - `kMeansCost`: the k-means cost of a clustering.
- Proved:
  - `sumSqDist_eq_add_card_mul`: the variance (parallel-axis) decomposition
    `∑ ‖P i - c‖² = ∑ ‖P i - m‖² + |S| · ‖c - m‖²`.
  - `mean_minimizes_sumSqDist` (CLRS Lemma 33.1): the mean of a cluster
    minimizes the within-cluster sum of squared distances.
  - `assignStep_cost_le` and `updateStep_cost_le`: reassigning every point to a
    *nearest* centroid, and replacing every centroid by the mean of its
    cluster, never increase the cost.
  - `lloyd_iteration_cost_le` (CLRS Theorem 33.2): one full Lloyd iteration
    (assignment, then update) never increases the k-means cost.

### Section 33.2 - Multiplicative-Weights Algorithms

- Lean source: `CLRSLean/FourthEdition/Chapter_33/Section_33_2_Multiplicative_Weights.lean`
- Status: `complete` (native fourth-edition source)
- Model:
  - `weights`: the weight of each expert after any number of days, updated
    multiplicatively by `(1 - η)^(m t i)`.
  - `potential`: the sum of the expert weights (`Φ`).
  - `expectedLoss` / `totalExpectedLoss`: the algorithm's daily and total
    expected loss under the weight-normalized distribution.
  - `expertLoss`: the total loss of a single expert.
- Proved:
  - `one_sub_rpow_le_one_sub_mul` and `neg_log_one_sub_le_add_sq`: the analytic
    inequalities `(1 - x)^y ≤ 1 - x·y` and `-ln (1 - x) ≤ x + x²` for
    `0 ≤ x ≤ 1/2` that drive the potential chain and the clean `1 + η` factor.
  - `potential_update_le_exp`: one MW update shrinks the potential
    multiplicatively: `Φ(w') ≤ Φ(w) · exp(-η · M)` for the day's expected
    loss `M`.
  - `potential_weights_le`: after `t ≤ T` days the potential is at most
    `n · exp(-η · Σ Mˢ)`, the iterated potential chain.
  - `weights_eq_rpow_expertLoss`: expert `i`'s weight after `T` days is
    `(1 - η)` raised to its total loss.
  - `totalExpectedLoss_le` (CLRS Theorem 33.3): for every expert `i`, the total
    expected loss is within an additive `ln n / η` and a multiplicative
    `(1 + η)` factor of expert `i`'s total loss.

### Section 33.3 - Gradient Descent

- Lean source: `CLRSLean/FourthEdition/Chapter_33/Section_33_3_Gradient_Descent.lean`
- Status: `complete` (native fourth-edition source)
- Model:
  - `gradientStep`: one gradient-descent update `x ↦ x - η·∇f(x)`.
  - `gdIterates`: the sequence of iterates generated from `x₀`.
  - `avgIterate`: the arithmetic mean `x̄` of the first `K` iterates (with the
    junk value `0` for `K = 0`).
- Proved:
  - `gradient_inner_le_sub`: the gradient-descent lemma — the first-order
    characterization of convexity `⟪∇f(x), y - x⟫ ≤ f(y) - f(x)`, proved by
    restricting `f` to the segment `[x, y]` and taking the convexity-chord
    limit `t → 0⁺`.
  - `gdStep_potential_le`: one step shrinks the squared distance to `x*` by at
    least `2η·(f x - f x*)`, up to the additive `η²·G²` term from the gradient
    bound `‖∇f‖ ≤ G`.
  - `gdIterates_potential_le` and `sum_suboptimality_le`: the telescoping
    potential chain over `K` steps and the resulting total-suboptimality bound.
  - `avgIterate_suboptimality_le` (CLRS Theorem 33.8): if `x*` minimizes `f`,
    the average iterate `x̄` of the first `K` iterates satisfies
    `f(x̄) - f(x*) ≤ ‖x₀ - x*‖²/(2ηK) + ηG²/2`, combining Jensen's inequality
    with the total-suboptimality bound.
- The chapter's fourth-edition sections 33.1--33.3 are all represented with no
  remaining edition-map coverage gap.

## Legacy Source Chapter 33 - Computational Geometry (Online Material)

### Section 33.1 - Line-Segment Properties

- Lean sources:
  - `CLRSLean/Chapter_33.lean`
  - `CLRSLean/Chapter_33/Section_33_1_Line_Segment_Properties.lean`
- Status: `online-material` with a partial legacy source boundary
- Proved results: the point/vector and `Segment` models; six cross-product
  antisymmetry, bilinearity, and self-product theorems; and
  `orientation_spec`.
- Current gap: `segmentIntersect`, `bboxIntersect`, and `sharesEndpoint` are
  definitions only.  Prove `segmentIntersect` soundness and completeness
  against an independent geometric-intersection specification, including the
  shared-endpoint cases.
- Remaining chapter scope: Sections 33.2--33.4 (sweep-line intersection,
  convex hulls, and closest pair) are not represented.

### Section 34.1 - Polynomial Time

- Lean sources:
  - `CLRSLean/Chapter_34.lean`
  - `CLRSLean/Chapter_34/Section_34_1_Polynomial_Time.lean`
  - `CLRSLean/Chapter_34/Section_34_1_Polynomial_Time/Composition.lean`
  - `CLRSLean/Chapter_34/Section_34_1_Polynomial_Time/AndOr.lean`
- Status: `partial` — green-field NP-completeness formalization on Mathlib's
  `Turing.TM2ComputableInPolyTime` (machine-level polynomial-time
  computability with `Polynomial ℕ` time bounds).
- Proved results: the framework — `Language` (a set of strings over an
  alphabet), `PolyTimeComputable` (polytime-computable function),
  `PolyTimeDecidable`, `ClassP` (the class of polynomial-time decidable
  languages), `mem_ClassP`, `PolyTimeComputable.comp` (composition closure,
  closing Mathlib's `proof_wanted TM2ComputableInPolyTime.comp` via the
  shared-stack two-phase `Turing.TM2Comp` construction), `ClassP_compl`
  (`P` closed under complement via the `Bool.not` machine), and the closure of
  `P` under union/intersection — `PolyTimeDecidable.union` / `ClassP_union`
  and `PolyTimeDecidable.inter` / `ClassP_inter` — via the AND/OR machine
  `Turing.TM2AndOr.andOrMachine` (a four-phase machine that duplicates the
  input onto both deciders' stacks, runs `M₁` then `M₂`, and combines the two
  `Bool` results with AND/OR).
- Current gap: the empty/universal languages (concrete machine constructions
  for `∅` and `Σ*`).
- Remaining chapter scope: Section 34.5 (NP-complete problems) is not
  represented.  The assembled SAT ≤_P 3-CNF-SAT machine reduction is proved in
  Section 34.4.  Open problems (P vs NP) are intentionally out of scope.

### Section 34.2 - Polynomial-Time Verification

- Lean sources:
  - `CLRSLean/Chapter_34/Section_34_2_Polynomial_Time_Verification.lean`
  - `CLRSLean/Chapter_34/Section_34_2_Polynomial_Time_Verification/PairProjection.lean`
- Proved results: `PolyTimeVerifiable`, `ClassNP`, `mem_ClassNP`,
  `PolyTimeVerifiable.of_decidable` and `ClassP_subset_ClassNP`
  (`P ⊆ NP`, Theorem 34.2) via the pair-projection machine
  `Turing.Prj.prjComputableInPolyTime` (a decider is a verifier that ignores
  the certificate).

### Section 34.3 - NP-Completeness and Reducibility

- Lean sources:
  - `CLRSLean/Chapter_34/Section_34_3_NP_Completeness_And_Reducibility.lean`
- Proved results: `PolyTimeReducible`, `NPHard`, `NPComplete`, `ClassNPC`,
  and `PolyTimeReducible.trans` (transitivity of `≤_P` via the composition
  closure).

### Section 34.4 - NP-Completeness Proofs

- Lean sources:
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CircuitSAT.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/Basic.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/Encoding.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/Verification.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CNFToClique.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/SatTo3CNFSat.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/SatTo3CNFMachine.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CNFToCliqueMachine.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder/Syntax.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder/Machine.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder/Macros.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/ReachableAlphabet.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Configuration.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/CircuitBuilder.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/CircuitBuilder/ConstantPool.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/CircuitBuilder/FiniteFamily.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Tableau.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Tableau/BundleCombinators.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Tableau/StackPrimitives.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Tableau/StackSemantics.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Tableau/FiniteLookup.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Tableau/StackCircuits.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Tableau/ControlCircuits.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Tableau/PrimitiveRowSemantics.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Tableau/Validity.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Tableau/Workspace.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Tableau/StatementCircuits.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Tableau/StatementCircuits/Core.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Tableau/StatementCircuits/Semantics.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Tableau/StatementCircuits/Bounds.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Tableau/TransitionCircuits.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Tableau/TransitionCircuits/Dispatch.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Tableau/TransitionCircuits/Dispatch/Core.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Tableau/TransitionCircuits/Dispatch/Semantics.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Tableau/TransitionCircuits/Core.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Tableau/TransitionCircuits/Semantics.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Tableau/TransitionCircuits/Fresh.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Tableau/TransitionCircuits/Fresh/At.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Tableau/TransitionCircuits/Fresh/Core.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Tableau/TransitionCircuits/Fresh/Semantics.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Tableau/TransitionCircuits/Fresh/Witness.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization/Assembly/Semantics.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization/Assembly/Bounds.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization/Assembly/EncodingBounds.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization/ReductionMap.lean`
  - `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/VerifierMachine.lean`
- Status: `partial` — general-circuit semantics and an honest canonical wire
  format and exact finite-certificate semantics are available.  The
  function-level Cook--Levin map is complete.  The certificate checker now has
  a total concrete TM2 implementation, but its all-input polynomial runtime
  wrapper, the map's concrete TM2 implementation, and the final
  `GeneralCircuitSAT` NP wrappers remain open.
- Proved results: the general acyclic circuit layer defines ordered Boolean
  gates with fan-out, well-formedness, evaluation, and local gate equations;
  `Circuit.evalValues_getElem_eq_gateEquation` connects execution to those
  equations.  The finite-symbol codec proves both
  `decodeCircuit_encodeCircuit` and
  `encodeCircuit_of_decodeCircuit_eq_some`, so a successful decode has exactly
  one canonical representation and no trailing data; it also proves the
  accepted-input lower bound
  `inputCount_lt_length_of_decodeCircuit_eq_some`, the well-formed encoding
  bound `encodeCircuit_length_le`, and the honest-language characterization
  `encodeCircuit_mem_generalCircuitSAT_iff`.  The executable
  `generalCircuitVerifier` accepts exactly well-formed decoded circuits with
  exact-length Boolean-symbol assignments, and
  `mem_generalCircuitSAT_iff_exists_certificate` characterizes membership by
  an accepted certificate no longer than the instance.  The phased
  `GeneralCircuitVerifier.machine` computes this exact Boolean on every input:
  `verifier_run` covers canonical and malformed encodings, and
  `generalCircuitVerifierComputable` packages total TM2 computability.
  `successfulSteps_le` gives a uniform quadratic bound for the successful
  canonical route; it intentionally does not claim a bound for every rejecting
  route.  Separately,
  `circuitSAT_reducible_to_SAT` proves `CIRCUIT-SAT ≤_P SAT` (Lemma 34.6, via
  `circuitSatisfiable_iff_satisfiable_circuitToFormula` and the `Turing.TM2CS`
  machine), `cnfSatisfiable_iff_hasClique` gives the represented Lemma 34.10
  semantic core for the specialized 3-CNF occurrence graph, and
  `threeCNFSat_reducible_to_CLIQUE` assembles the machine reduction to that
  specialized target via `Turing.TMClique`, while
  `cnfSatisfiable_to3CNF_iff` gives the Lemma 34.7 semantic core and
  `Turing.TM3CNF.sat_reducible_to_threeCNFSat` assembles the concrete
  `SAT ≤_P 3-CNF-SAT` machine reduction.  The typed
  bounded-builder core compiles exact independent-semantics runs to TM2 runs;
  its `scanCopy` macro performs two stack reversals to preserve input order,
  clears all scratch stacks, and has exact cost `3n + 3`.  Its `boundedLoop`
  macro applies a symbol-local body in forward `List.flatMap` order, clears all
  scratch stacks, and has exact cost `2n + L + 3`, where `L` is the emitted
  output length.  Its `nestedLoop` macro emits all ordered input pairs in
  row-major order, restores the inner copy after every outer row, clears all
  scratch stacks, and has exact cost `2n² + 5n + L + 4`.  All three exact runs are
  transported unchanged to their compiled TM2s.  The Cook--Levin foundation
  defines a finite reachable alphabet for every stack of a fixed bundled TM2
  and proves its preservation by finite runs.  It gives strict canonical
  bounded stack/configuration codes with proof-indexed and optional decoding,
  both codec round trips, the exact-horizon stuttering characterization of
  bounded halting, and a linear tableau-height bound whose per-step constant
  counts all pushes along a complete recursive statement path.  The canonical
  row-validity circuit enforces every one-hot field, halted/none-label
  agreement, and active-nonblank/inactive-blank stack cells via a linear
  suffix-OR mask; its public theorem identifies acceptance exactly with
  successful row decoding and gives an exact affine gate cost.  The
  Boolean constant allocation is now bundled as a reusable `BoolWirePool`:
  false and true wires are allocated once in exactly two gates, retain exact
  evaluation contracts under arbitrary builder extension, and are exposed by
  `widenCfg` for downstream transition construction.  The finite-family
  circuit kernel multiplexes `Fin n` wire families with one
  shared selector negation in exactly `3n + 1` gates and aggregates pointwise
  equality in exactly `6n + 1` gates.  Both operations carry extension,
  validity, exact evaluation, uniform empty-family, and proof-irrelevance
  contracts.  The structured tableau-bundle layer adds dependently typed
  height/cell views for each machine stack and a pure zero-gate stack
  replacement whose same-stack, different-stack, halted, label, and state
  frame laws require no unchecked casts.  A single canonical
  `cfgSlotEquivFin` flattening lifts the generic kernels to complete bounded
  rows: `cfgMux` selects all `cfgBitCount tm H` coordinates in exactly
  `3 * cfgBitCount tm H + 1` gates, while `cfgEq` recognizes equality of the
  two evaluated `CfgBits` functions in exactly
  `6 * cfgBitCount tm H + 1` gates.  Both row combinators preserve the builder
  prefix, return valid outputs, and are proof irrelevant.  The one-step
  workspace bridge widens height `H` to `H + maxPushesPerStep tm` with exactly
  two shared constant gates, and narrows without copying prefix wires while a
  `|K| * maxPushesPerStep tm + 2`-gate fit circuit rejects selected overflow
  heights.  Both bridges preserve successful canonical decoding under their
  explicit premises; narrowing requires both a successfully decoded workspace
  row and a true fit output because fit alone does not validate discarded
  physical cells.  At the raw Boolean-bundle level, fixed-width stack
  push/peek/pop primitives now have exact coordinate laws, supported-symbol
  and optional-head codec round trips, and raw one-hot preservation under the
  exact capacity premise.  Full-stack push is proved to destroy raw height
  decodability independently of symbol one-hotness, including empty reachable
  alphabets.  The public `pushStackBits_cell_zero_encodeSymbol` theorem bridges
  a supported-symbol encoding directly to the corresponding optional-head
  encoding in the new cell zero.  Canonical bounded-stack encodings now carry
  a proof-carrying list representation whose exact capacity theorem includes
  width zero and whose push/peek/pop laws are list cons, head, and tail plus
  the old head.  `evalBundle_stack_represents` additionally turns any
  successful canonical whole-row evaluation into the corresponding semantic
  representation for each machine stack.  The wire-level stack layer
  reuses one Boolean constant pool, gives zero-gate push/peek rearrangements,
  a zero/one-gate width-sensitive pop, and a one-NOT capacity query.  Its
  complete-row wrappers publish halted/label/state/other-stack frame laws and
  semantic contracts derived from successful `evalBundle` decoding.
  The finite one-hot lookup layer compiles static maps, pair maps, and Boolean
  predicates with exact gate counts and canonical one-hot evaluation laws,
  including empty-domain and noninjective cases.  The finite-control row layer
  reuses the shared Boolean pool to encode states, optional labels (including
  the reserved `none` coordinate), and the explicit halted bit without new
  gates.  Successful `evalBundle` decoding now yields an existential exact
  canonical-row equality without exposing a choice-selected code; its
  projections recover exact state, label, and halted bits.  Complete-row
  `replaceState` and synchronized halted/label `replaceStatus` operations
  preserve all other fields and decode exactly to the corresponding updated
  TM2 configuration.  The complete-row primitive bridge upgrades the existing
  selected-stack push/pop semantics to exact `evalBundle` equations for the
  whole dependent configuration: push is list cons under an explicit free-cell
  premise, pop is list tail without a capacity premise, and every nonselected
  field remains canonical.  Pop additionally returns an existential supported
  head whose evaluated bits equal `encodeHeadBits` exactly, so recursive
  statement lookup need not recover a choice-selected decoder witness.
  Peek now exposes the same exact supported-head/`encodeHeadBits` bridge,
  including height zero.  The recursive statement compiler covers all seven
  `TM2.Stmt` constructors without enumerating configurations: state, label,
  symbol, pair, and predicate functions are fixed finite truth-table data;
  branches compile both arms from the same original row and select a complete
  row with `cfgMux`.  `compileStmt_evalBundle` proves exact `TM2.stepAux`
  semantics under the explicit per-stack prefix-capacity premise, while
  `compileStmt_gate_delta` and `compileStmt_gate_count_le` give exact and
  fixed-`tm/q` affine emitted-gate bounds.
  The finite-label dispatcher serially compiles every program statement from
  the same source row, muxes each result under that row's exact label
  coordinate, and reserves `none` for whole-row stuttering.  Its semantics
  theorem identifies the complete evaluated workspace row exactly with
  `stutterStep tm c`, not merely selected projections.  The local
  `transitionCircuit` composes the two-gate widen pool, dispatch, final-fit
  narrowing, complete-row equality, and a final conjunction.  Its exact gate
  delta is `transitionCircuitGateCost tm H`, and
  `transitionCircuit_eval_iff` proves acceptance exactly when the independently
  decoded next row equals `stutterStep tm c`, without a public target-fit
  premise.
  The fresh-layout construction allocates two consecutive nonaliasing rows at
  an arbitrary external-input offset and records both row-validity proofs plus
  final transition-wire validity.  Its reusable Nat-assignment completeness
  theorem preserves a caller's bits outside the two intervals; the canonical
  `freshTransitionCircuit_complete` packages the result as
  `Fin final.inputCount → Bool`, matching `GeneralCircuitSatisfiable`.
  The exact boundary layer maps each fixed complete row through one shared
  true/false wire pool, so fixed target coordinates emit no gates and are not
  SAT-free variables.  `initialCfgCircuit_eval_iff` and
  `acceptingOutputCircuit_eval_iff` characterize successful complete-row
  decoding exactly; oversized concrete inputs and unsupported/oversized
  outputs produce a constant-false constraint.  The separate
  `symbolicInitialCfgCircuit_eval_iff` constrains main/nonhalted/initial-state,
  all empty non-input stacks, and a caller-supplied represented symbolic input
  stack, providing the certificate-linked first-row interface for assembly.
  The 8H size layer separates exact structural costs from reusable polynomial
  bounds.  `validCfgGateCost_le`, `dispatchGateCost_le`, and
  `transitionCircuitGateCost_le` use height-independent fixed-machine
  coefficients times explicit affine height/row-width expressions; their
  corresponding builder theorems bound emitted gates beyond an arbitrary
  prefix.  `validCfgCircuitFinished` and `transitionCircuitFinished` close the
  two principal predicate builders with proved `Circuit.WellFormed` and exact
  `finish_eval` bridges.
  The verifier-circuitization layer packages each
  `PolyTimeVerifiable` proof as a concrete `VerifierWitness`, proves the exact
  separator-pair input length, and derives polynomial input, execution-horizon,
  and uniform stack-height envelopes.  Its widened `outputsInHorizon` retains
  the machine run's actual step witness and changes only the upper-bound proof;
  `stutter_horizon_eq_haltList` supplies the separate exact-horizon execution
  equality used by tableau assembly.  The completed whole-tableau core
  allocates all rows, serializes validity and transition families, constrains
  the bounded certificate/input shape and both endpoint rows, and closes their
  conjunction.  `verifierCircuit_wellFormed`,
  `verifierCircuit_satisfiable_iff`, and `verifierCircuit_gate_count_le`
  provide the structural, semantic, and polynomial gate-size contracts.
  `verifierCircuit_input_count_le` and
  `verifierCircuit_encoding_length_le` extend the accounting to the declared
  inputs and complete unary circuit encoding.  The explicit
  `cookLevinMap` serializes the verifier circuit;
  `cookLevinMap_mem_generalCircuitSAT_iff` proves its exact reduction
  semantics and `cookLevinMap_length_le` proves its polynomial output bound.
- Current gaps: the certificate-checker machine still needs one uniform
  polynomial runtime theorem covering every malformed and rejecting route
  before it can be packaged as `TM2ComputableInPolyTime`; the circuit generator
  still needs its concrete polynomial-time TM2 implementation.  Consequently
  NP membership, NP-hardness, and NP-completeness wrappers for
  `GeneralCircuitSAT` remain open.
  `SatTo3CNFMachine` imports the complete compiling B1--B13 chain;
  `Dev.B12_Bounds` proves the polynomial bounds and `Dev.B13_OutputsFun`
  packages the complete run as `TM2ComputableInPolyTime`.
  `CNFToCliqueMachine` also compiles and exposes
  the assembled `threeCNFSat_reducible_to_CLIQUE` reduction to occurrence-
  CLIQUE.  The scan/copy, bounded-loop, and nested-loop macro layer over the
  bounded-builder core is complete.
- Remaining chapter scope: general graph-plus-`k` CLIQUE and Section 34.5
  (NP-complete problems) are not represented.

## Deferred And Blocked Items

| Item | Status | Reason |
| --- | --- | --- |
| Union-find implementation correctness | `proved` | Chapter 21's executable Batteries union-find and Chapter 23's stateful Kruskal bridge are proved, including the inverse-Ackermann scan bound.  Only low-level mutable-array/RAM constants remain optional. |
| Chapter 6 tight/RAM costs | `deferred-implementation` | Array heap predicates, recursive `MAX-HEAPIFY`, bottom-up build-heap, in-place heapsort, and priority-queue state correctness are proved.  Costed executions erase to heapify/build/heapsort and satisfy connected coarse `O(n)`, `O(n^2)`, and `O(n^2)` envelopes.  The metric counts heapify frames plus nontrivial extraction transitions, but not build orchestration, guards, list operations, or allocation; tight `O(log n)`, `O(n)`, and `O(n log n)` bounds and RAM refinement remain open. |
| Chapter 7 mutable-array partition | `proved` | `partitionOnArray` supplies the mutable-Array partition refinement; only optional lower-level RAM accounting remains. |
| Chapter 7 randomized probability semantics | `proved` | Random-permutation first-choice symmetry and `compared_prob = 2/(j-i+1)` are proved; `sum_compared_prob_eq_expectedComparisons` bridges pairwise probabilities to the harmonic closed form; `expectedComparisons_isBigTheta_nlogn` gives `Θ(n log n)`. |
| Chapter 8 mutable output-array implementation | `proved` | The cumulative-count reverse scan fills a physical `Array`, refines `countingSortBy`, and has a linear work bound. |
| Chapter 8 bucket-sort expected time | `proved-abstract` | Deterministic bucket-sort correctness is proved by `bucketSortByRank_correct`; `expectedBucketQuadraticCost_eq_secondMoment` proves the CLRS second moment as a true expectation over the explicit independent uniform input distribution `Fin n → Fin m`. `textbookBucketSortCost` is the CLRS unit-cost random variable, `fintypeExpect_textbookBucketSortCost_eq_expectedBucketSortCost` identifies its true finite-uniform expectation, and `expectedTextbookBucketSortCost_isBigO` proves that expectation is linear. Remaining: a single-pass executable bucket builder, a costed per-bucket sorter, and a refinement theorem connecting their execution cost to the abstract model. |
| Chapter 9 randomized SELECT expected time | `proved` | `randomizedSelectCostWithSchedule` consumes one occurrence-rank choice per visited state and charges `c * currentLength`, rejecting invalid/exhausted schedules; its erasure theorem connects successful runs to rank-correct SELECT. `randomizedSelectExpectedCostFuel` is a nested conditional-uniform process over the current `Fin n`, and `randomizedSelectExpectedCost_le_randSelectExpectedCost` couples it to the CLRS larger-side majorizer, yielding `randomizedSelectExpectedCost_linear_bound : E[C] ≤ 4 * c * n`. The metric excludes RNG, `selectByRank?` specification sorting, list primitives, and RAM work. |
| Chapter 9 deterministic linear-time SELECT | `proved` | Selector correctness and totality, five-element certificates, full-input split counts, the `7n/10 + O(1)` branch bound, and the recursively computed median-of-medians pivot are proved. `recursiveMedianOfMediansComparisonCost_linear_bound` composes group work, nested pivot selection, partition scans, and the selected strict branch into the end-to-end bound `≤ 100n`. |
| Maximum-subarray low-level cost refinement | `deferred-implementation` | The costed midpoint selector erases to a correct execution; its measured cost satisfies the actual mixed floor/ceiling recurrence and `maxSubarrayDivideCost_isBigTheta_nlogn` proves the all-input `Theta(n log n)` abstract control-step bound.  Explicit split-tree construction, integer operations, `List` allocation/copying, garbage collection, and RAM semantics remain outside the metric. |
| Chapter 4 concrete all-input Master-theorem instantiation | `proved` | Floor/ceiling exact-power extraction, generic all-input transfer, adjacent-power sandwich generation, the discrete critical-power, log-critical, and tail-dominated wrappers, packaged floor/ceiling cases 1/2/3, natural-exponent polynomial wrappers for cases 1/2, the real-log bridge and named case-1 wrappers, the real-log-log bridge and named case-2 wrappers, and the case-3 regularity bridge (connecting `tailDominatedScale` to `f(n)`) are all proved. |
| Hash-table expected-time analysis | `proved-abstract` | The finite-uniform bucket toolkit proves load-factor equality, nonnegativity, and single-insert expected-cost changes; under SUHA the expected chain length `α = n/m`, expected unsuccessful-search cost `1 + α`, pairwise collision probability `1/m`, and expected successful-search cost `1 + (n-1)/(2m)` (CLRS Theorem 11.2) are proved as true expectations over the explicit independent uniform hashing distribution `Fin n → Fin m` (`expectedRandomChainLength_eq_loadFactor`, `expectedRandomUnsuccessfulSearchCost`, `pairCollisionProb`, `expectedRandomSuccessfulSearchCost`); a universal random hash-*function* model bounds expected collisions by `α` and search cost by `1 + α` (CLRS Theorem 11.3, `IsUniversal`, `universal_expected_collisions`, `universal_expected_search_cost`). Remaining: RAM/probe-count semantics. |
| Pointer-level linked lists and free lists | `future-work` | Requires an imperative memory model. |
| BST transplant and parent-pointer navigation | `proved` | `Zipper`-based parent-pointer layer: `searchIter_eq_search`, `transplant_preserves_ordered` (CLRS `TRANSPLANT`), `deleteViaTransplant_eq_delete`, and `successorZipper`/`predecessorZipper` equivalences are all proved. Only pointer-level in-place mutation (RAM) remains. |
| Chapter 12 executable pointer-level BST | `proved` | Imperative pointer-heap model (`Node` records with `left`/`right`/`parent` cells over a `Std.HashMap` `Store`) with `RepresentsW` heap-to-tree abstraction; in-place `TRANSPLANT` (`transplantChild_left_representsW`/`transplantChild_right_representsW`) and leaf `TREE-INSERT` (`insertPointer_right_representsW`) refine functional subtree replacement. Only an explicit RAM cost model remains. |
| Chapter 15 DP executable tables | `partial` | Only rod cutting has a proved mutable-`Array` bottom-up table. Matrix chain and LCS have pure recurrence/reconstruction functions, and OBST has a pure recurrence evaluator plus an existential public optimality theorem; CLRS-style tables and their costs remain. |
| B-tree executable deletion semantics | `proved` | For `2 ≤ t`, `composedDelete_keyBag` under `NodeWF` and `composedDeleteRoot_keyBag` under `WellFormed` prove `Multiset.erase` semantics: one requested-key occurrence is removed when present, and an absent request leaves the bag unchanged. `composedDelete_mem_iff_of_ne` and `composedDeleteRoot_mem_iff_of_ne` preserve every different key without `UniqueKeys` or a requested-key-present premise. Raw uniqueness preservation needs `NodeWF + UniqueKeys`; under `WellFormedUnique`, `composedDeleteRoot_not_mem`, `composedDeleteRoot_mem_iff`, `composedDeleteRoot_wellFormedUnique`, `composedDeleteRoot_mem_iff_delete`, and `composedDeleteRoot_search_eq_delete` prove absence, full root membership behavior, combined invariant preservation, and compatibility with specification deletion and membership-oracle search. The bridge does not assert `searchExec` or tree-shape equality. Disk pages, pointers, I/O counts, and RAM costs are optional lower-level refinements. |
| Fibonacci heap pointer-level model | `deferred-implementation` | All Fibonacci heap operations are specified against an abstract finite-set model; a persistent executable heap forest now proves exact multiset representation, a global validity invariant, minimum-root selection, executable extract-min through equal-degree `CONSOLIDATE`, heap-level direct-child CUT, and the exact CUT potential delta. Cached minimum pointers, stable node identity, handles/arbitrary paths, cascading cuts, executable decrease/delete, actual costs, and circular pointer mutation remain. |
| Red-black deletion shape | `proved` | `redBlackShape_delete` proves `RedBlackShape` preservation through the composed executable `del`/`delete` pipeline, built on the `baldL_shape`/`baldR_shape` deficit certificates, `splitMin_invariant`, and `del_invariant`.  Exact deletion membership (`inTree_delete_iff`) and `height_log_bound` are also proved. |
| Generic augmentation deletion erasure | `proved` | Section 14.3 proves the generic executable deletion pipeline, `AugmentedRBTree.wellAugmented_delete`, and the `AugmentedRBTree.toRB_delete` erasure/refinement bridge to Chapter 13's `RBTree.delete`.  Pointer-level mutation and RAM accounting remain optional implementation layers. |
| Automatic MST exchange-path extraction | `proved` | `canonicalSimplePath_unique` and `exists_crossing_exchangePath_of_spanningTree` extract the crossing replacement edge and residual path connections automatically. |
| Prim's algorithm | `proved` | `PrimTrace` packages dynamic light-edge choices, and `prim_minimum_spanning_tree` proves the direct finite-graph MST conclusion for a complete certified run. |
| CLRS exercises | `future-work` | Keep the first pass focused on main textbook claims; add exercises after section interfaces stabilize. |
| Chapter-end problems | `future-work` | Treat as a second track with explicit priority and difficulty labels. |
| Full RAM semantics | `future-work` | Requires an imperative machine/cost semantics rather than only mathematical functions and recurrences. |
| General merge-sort recurrence | `proved` | `theta_n_log_n_all_inputs` proves the arbitrary-size floor/ceiling merge-sort recurrence is `Θ(n log n)` through the Chapter 4.6 adjacent-power sandwich bridge. |

## Publication Value

The proof map is intentionally honest.  Completed sections show theorem names
that compile.  Partial sections expose the exact missing mathematical or
representation layer.  This lets future contributors pick a section without
reverse-engineering the project state.

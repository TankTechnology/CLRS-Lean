import CLRSLean.Chapter_04.Section_04_2_Strassen_Algorithm

/-!
# Section 4.1 — Multiplying square matrices

This section formalizes the naive square-matrix-multiplication algorithm of CLRS
§4.1 (fourth edition).  On the depth-indexed power-of-two squares
{lit}`CLRS.Chapter04.SqMat` it defines the recursive eight-product
`SQUARE-MATRIX-MULTIPLY-RECURSIVE`, proves it computes the ordinary matrix
product at every depth, and shows the work recurrence
{lit}`T(n) = 8 T(⌊n/2⌋) + n²` is {lit}`Θ(n³)` by Master-theorem case 1.

The representation and Master-theorem infrastructure are shared with §4.2
({lit}`Section_04_2_Strassen_Algorithm`), where {lit}`SqMat R k` is a
{lit}`2^k × 2^k` block matrix and the recursive runtime analysis discharges the
floor/ceiling Master-theorem case 1 wrapper.

Main results:

- Definition {lit}`mulRec`: the recursive eight-product multiplication on
  {lit}`SqMat` (CLRS `SQUARE-MATRIX-MULTIPLY-RECURSIVE`).
- Theorem {lit}`mulRec_correct`: {lit}`mulRec R k A B = A * B` at every depth.
- Theorem {lit}`mulRec_padOne_corner`: zero-padding into the next power of two
  preserves the top-left product.
- Theorem {lit}`mul_runtime_bigTheta`: the work recurrence
  {lit}`T(n) = 8 T(⌊n/2⌋) + n²` is {lit}`Θ(n^(log₂ 8))`.
- Theorem {lit}`realLogScale_eight_two`: the comparison scale at {lit}`a = 8`,
  {lit}`b = 2` is the polynomial {lit}`n³`, so the runtime bound is exactly
  {lit}`Θ(n³)`.

Notation conventions used in this section:

- `R` : the scalar ring
- `SqMat R k` : a `2^k × 2^k` square matrix over `R`
- `mulWork`, `T` : the recursive work/cost function
-/

namespace CLRS
namespace Chapter04

/-! ## The naive 2 × 2 block product -/

section Naive2

variable {S : Type*} [Ring S]

/--
The naive {lit}`2 × 2` block product (the combine step of the recursive
algorithm): each output block is the sum of two block products, eight in total.
This is the straightforward `SQUARE-MATRIX-MULTIPLY` block arithmetic that
Strassen's seven products optimize away.
-/
def mul2 (M N : Matrix (Fin 2) (Fin 2) S) : Matrix (Fin 2) (Fin 2) S :=
  !![M 0 0 * N 0 0 + M 0 1 * N 1 0, M 0 0 * N 0 1 + M 0 1 * N 1 1;
     M 1 0 * N 0 0 + M 1 1 * N 1 0, M 1 0 * N 0 1 + M 1 1 * N 1 1]

/-- The naive block product computes the ordinary `2 × 2` matrix product. -/
theorem mul2_eq_mul (M N : Matrix (Fin 2) (Fin 2) S) : mul2 M N = M * N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mul2, Matrix.mul_apply, Fin.sum_univ_two]

end Naive2

/-! ## Recursive naive multiplication on power-of-two squares -/

/--
The recursive `SQUARE-MATRIX-MULTIPLY-RECURSIVE` algorithm.  {lit}`mulRec R 0` is
the scalar base case (conventional multiplication); {lit}`mulRec R (k+1)`
partitions both factors into four depth-`k` blocks and forms the eight recursive
block products (CLRS §4.1): each output block is the sum of two of them.
-/
def mulRec (R : Type u) [Ring R] : ∀ k, SqMat R k → SqMat R k → SqMat R k
  | 0, x, y => x * y
  | (k + 1), A, B =>
      !![mulRec R k (A 0 0) (B 0 0) + mulRec R k (A 0 1) (B 1 0),
         mulRec R k (A 0 0) (B 0 1) + mulRec R k (A 0 1) (B 1 1);
         mulRec R k (A 1 0) (B 0 0) + mulRec R k (A 1 1) (B 1 0),
         mulRec R k (A 1 0) (B 0 1) + mulRec R k (A 1 1) (B 1 1)]

/--
Correctness of the recursive naive multiplication: at every depth it returns the
ordinary matrix product `A * B`.  The proof is induction on depth; each step
rewrites the eight recursive products by the induction hypothesis and then
applies the {lit}`2 × 2` identity {name}`CLRS.Chapter04.mul2_eq_mul`.
-/
theorem mulRec_eq_mul (R : Type u) [Ring R] :
    ∀ (k : ℕ) (A B : SqMat R k), mulRec R k A B = A * B
  | 0, x, y => rfl
  | (k + 1), A, B => by
      have IH : ∀ X Y : SqMat R k, mulRec R k X Y = X * Y := mulRec_eq_mul R k
      have hstep : mulRec R (k + 1) A B = mul2 A B := by
        simp only [mulRec, mul2, IH]
      rw [hstep]
      exact mul2_eq_mul A B

/--
Reader-facing correctness theorem for the recursive algorithm: on a
{lit}`2^k × 2^k` square, {name}`CLRS.Chapter04.mulRec` produces the true matrix
product.
-/
theorem mulRec_correct (R : Type u) [Ring R] (k : ℕ) (A B : SqMat R k) :
    mulRec R k A B = A * B :=
  mulRec_eq_mul R k A B

/--
Running the recursive naive multiplication on two zero-padded inputs recovers the
padded product: padding to the next power of two does not change the meaningful
top-left product.  This composes {name}`CLRS.Chapter04.mulRec_correct` with
{name}`CLRS.Chapter04.padOne_mul`.
-/
theorem mulRec_padOne (R : Type u) [Ring R] (k : ℕ) (x y : SqMat R k) :
    mulRec R (k + 1) (padOne R k x) (padOne R k y) = padOne R k (x * y) := by
  rw [mulRec_correct, padOne_mul]

/-- Extracting the corner after a padded naive multiplication returns the
    original product `x * y`. -/
theorem mulRec_padOne_corner (R : Type u) [Ring R] (k : ℕ) (x y : SqMat R k) :
    (mulRec R (k + 1) (padOne R k x) (padOne R k y)) 0 0 = x * y := by
  rw [mulRec_padOne]
  show (!![x * y, 0; 0, 0] : Matrix (Fin 2) (Fin 2) (SqMat R k)) 0 0 = x * y
  simp

/-! ## Runtime: `T(n) = 8 T(⌊n/2⌋) + n²` is `Θ(n³)` -/

/--
The naive work recurrence {lit}`T(n) = 8 T(⌊n/2⌋) + n²`: eight recursive
subproblems of half size plus quadratic block-combination work, with base value
{lit}`T(0) = 0`.  This is the CLRS cost recurrence whose solution is the running
time of {name}`CLRS.Chapter04.mulRec`.
-/
noncomputable def mulWork : ℕ → ℝ
  | 0 => 0
  | (n + 1) => 8 * mulWork ((n + 1) / 2) + ((n + 1 : ℕ) : ℝ) ^ 2
  decreasing_by exact Nat.div_lt_self (Nat.succ_pos n) (by norm_num)

/-- Base value of the work recurrence. -/
theorem mulWork_zero : mulWork 0 = 0 := by
  rw [mulWork]

/-- One recursion step of the work recurrence at a successor argument. -/
theorem mulWork_succ (n : ℕ) :
    mulWork (n + 1) = 8 * mulWork ((n + 1) / 2) + ((n + 1 : ℕ) : ℝ) ^ 2 := by
  rw [mulWork]

/-- One recursion step of the work recurrence at any positive argument. -/
theorem mulWork_pos_step (n : ℕ) (hn : 0 < n) :
    mulWork n = 8 * mulWork (n / 2) + ((n : ℕ) : ℝ) ^ 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact mulWork_succ m

/--
The forcing term {lit}`f(n) = T(n) - 8 T(⌊n/2⌋)` of the recurrence.  Choosing
{lit}`f` as this defect makes the CLRS floor recurrence
{lit}`T(n) = 8 T(⌊n/2⌋) + f(n)` hold definitionally at every input.
-/
noncomputable def mulForcing (n : ℕ) : ℝ :=
  mulWork n - 8 * mulWork (n / 2)

/--
The work function satisfies the Chapter 4 floor-division Master recurrence with
{lit}`a = 8`, {lit}`b = 2`.
-/
theorem mulWork_floorRec :
    FloorDivideRecurrence 8 2 mulForcing mulWork := by
  refine ⟨fun n => ?_⟩
  simp only [mulForcing]
  push_cast
  ring

/-- The work function is nonnegative. -/
theorem mulWork_nonneg : ∀ n, 0 ≤ mulWork n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [mulWork_zero]
    · rw [mulWork_pos_step n hn]
      have hlt : n / 2 < n := Nat.div_lt_self hn (by norm_num)
      have hrec := ih (n / 2) hlt
      nlinarith [hrec, sq_nonneg ((n : ℕ) : ℝ)]

/-- The work function is nondecreasing across one step. -/
theorem mulWork_le_succ : ∀ n, mulWork n ≤ mulWork (n + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; rw [mulWork_zero]; exact mulWork_nonneg _
    · rw [mulWork_pos_step n hn, mulWork_pos_step (n + 1) (Nat.succ_pos n)]
      have hcast : ((n : ℕ) : ℝ) ^ 2 ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by
        have h1 : ((n : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
        have hn_nonneg : (0 : ℝ) ≤ (n : ℕ) := Nat.cast_nonneg _
        nlinarith [hn_nonneg, h1]
      rcases (by omega : (n + 1) / 2 = n / 2 ∨ (n + 1) / 2 = n / 2 + 1) with h | h
      · rw [h]; linarith [hcast]
      · rw [h]
        have hj : n / 2 < n := Nat.div_lt_self hn (by norm_num)
        have hstep := ih (n / 2) hj
        linarith [hstep, hcast]

/-- The work function is monotone. -/
theorem mulWork_monotone : Monotone mulWork :=
  monotone_nat_of_le_succ mulWork_le_succ

/-- The work function satisfies the absolute-value monotonicity interface. -/
theorem mulWork_monotoneAbs : MonotoneAbs mulWork := by
  intro m n hmn
  rw [abs_of_nonneg (mulWork_nonneg m), abs_of_nonneg (mulWork_nonneg n)]
  exact mulWork_monotone hmn

/--
The normalized forcing on exact powers is the convergent geometric sequence
{lit}`(1/2)^(k+1)`: on {lit}`n = 2^(k+1)` the forcing is exactly the block-work
{lit}`(2^(k+1))² = 4^(k+1)`, so dividing by {lit}`8^(k+1)` gives
{lit}`(4/8)^(k+1) = (1/2)^(k+1)`.  This is what places the naive recurrence in
Master case 1 (the forcing {lit}`n²` is polynomially smaller than the critical
{lit}`n^(log₂ 8) = n³`).
-/
theorem mul_normForcing (k : ℕ) :
    normalizedForcing 8 2 mulForcing k = (1 / 2 : ℝ) ^ (k + 1) := by
  have hpos : 0 < 2 ^ (k + 1) := pow_pos (by norm_num) _
  have hdiv : 2 ^ (k + 1) / 2 = 2 ^ k := by rw [pow_succ]; omega
  have hcast : ((2 ^ (k + 1) : ℕ) : ℝ) ^ 2 = (4 : ℝ) ^ (k + 1) := by
    push_cast
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm 2 (k + 1)]
  have hforcing : mulForcing (2 ^ (k + 1)) = (4 : ℝ) ^ (k + 1) := by
    unfold mulForcing
    rw [mulWork_pos_step (2 ^ (k + 1)) hpos, hdiv]
    linarith [hcast]
  unfold normalizedForcing
  rw [hforcing, ← div_pow]
  norm_num

/-- Case-1 hypothesis: the normalized forcing is nonnegative. -/
theorem mul_term_nonneg (k : ℕ) : 0 ≤ normalizedForcing 8 2 mulForcing k := by
  rw [mul_normForcing]; positivity

/-- Case-1 hypothesis: the normalized forcing is bounded by a geometric sequence. -/
theorem mul_term_upper (k : ℕ) :
    normalizedForcing 8 2 mulForcing k ≤ (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ k := by
  rw [mul_normForcing, pow_succ]
  exact le_of_eq (mul_comm _ _)

/-- Value of the work recurrence at the base input `1`. -/
theorem mulWork_one : mulWork 1 = 1 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, mulWork_succ]
  norm_num [mulWork_zero]

/-- Positivity of the normalized base value, a case-1 hypothesis. -/
theorem mul_base_pos : 0 < normalizedValue 8 2 mulWork 0 := by
  unfold normalizedValue
  norm_num [mulWork_one]

/--
**Runtime of the naive matrix-multiplication algorithm.**  The recurrence
{lit}`T(n) = 8 T(⌊n/2⌋) + n²` is {lit}`Θ(n^(log₂ 8))`.  This is the CLRS
{lit}`Θ(n³)` bound, obtained by discharging Master-theorem case 1 (the forcing
{lit}`n²` is polynomially smaller than the critical {lit}`n^(log₂ 8)`)
through the Chapter 4 wrapper
{name}`CLRS.Chapter04.floorDivide_allInput_masterCase1_realLogScale`.
-/
theorem mul_runtime_bigTheta :
    Chapter03.isBigTheta mulWork (realLogScale 8 2) :=
  floorDivide_allInput_masterCase1_realLogScale 8 2 mulForcing mulWork
    mulWork_floorRec (by norm_num) (by norm_num) mulWork_monotoneAbs
    mul_base_pos mul_term_nonneg (r := 1 / 2) (C := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num) mul_term_upper

/--
The comparison scale {name}`CLRS.Chapter04.realLogScale` at {lit}`a = 8`,
{lit}`b = 2` is the polynomial {lit}`n³`, since {lit}`log₂ 8 = 3`.  So
{name}`CLRS.Chapter04.mul_runtime_bigTheta` is exactly the CLRS {lit}`Θ(n³)`
statement.
-/
theorem realLogScale_eight_two (n : ℕ) :
    realLogScale 8 2 n = (n : ℝ) ^ 3 := by
  rw [realLogScale, realLogExponent]
  have h : Real.log (((8 : ℕ) : ℝ)) / Real.log (((2 : ℕ) : ℝ)) = 3 := by
    rw [show (((8 : ℕ) : ℝ)) = (2 : ℝ) ^ 3 by norm_num, Real.log_pow]
    have hlog : Real.log (2 : ℝ) ≠ 0 := by
      exact Real.log_ne_zero.mpr ⟨by norm_num, by norm_num, by norm_num⟩
    field_simp [hlog]
    ring
  rw [h]
  simp

end Chapter04
end CLRS

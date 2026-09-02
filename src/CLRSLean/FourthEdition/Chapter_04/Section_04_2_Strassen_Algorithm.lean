import Mathlib
import CLRSLean.Chapter_04.Section_04_6_Master_Theorem_All_Input

/-!
# CLRS Section 4.2 - Strassen's algorithm for matrix multiplication

This file formalizes Strassen's algorithm, from its algebraic 2 by 2 core all
the way to a recursive algorithm on power-of-two squares with a
{lit}`Θ(n^(log₂ 7))` runtime bound.

A {lit}`Matrix2 R` should be read as a 2 by 2 block matrix whose entries live in
an arbitrary ring.  The theorem {lit}`strassen2x2_correct` proves that
Strassen's seven block products reconstruct ordinary 2 by 2 block matrix
multiplication.

## Recursive refinement

The type {lit}`CLRS.Chapter04.SqMat` is a depth-indexed square matrix:
{lit}`SqMat R 0 = R` and {lit}`SqMat R (k+1) = Matrix (Fin 2) (Fin 2) (SqMat R k)`,
so {lit}`SqMat R k` is a genuine {lit}`2^k × 2^k` matrix ring built by nesting the
2 by 2 block structure.  {lit}`CLRS.Chapter04.strassenRec` is the recursive
seven-multiplication algorithm: it bottoms out at the scalar base case
{lit}`SqMat R 0 = R` and otherwise combines the seven Strassen products of its
four sub-blocks.  {lit}`CLRS.Chapter04.strassenRec_correct` proves it computes
the ordinary matrix product {lit}`A * B` at every depth, and
{lit}`CLRS.Chapter04.strassenRec_padOne` shows that zero-padding a matrix into
the next power-of-two block preserves the product in the top-left corner.

## Runtime

The work recurrence {lit}`CLRS.Chapter04.strassenWork` satisfies the CLRS
floor recurrence {lit}`T(n) = 7 T(⌊n/2⌋) + n²`, i.e. seven recursive products
plus quadratic block-addition work.  Feeding this into the Chapter 4 Master
theorem case-1 wrapper
{lit}`CLRS.Chapter04.floorDivide_allInput_masterCase1_realLogScale` gives
{lit}`CLRS.Chapter04.strassen_runtime_bigTheta`:
{lit}`T = Θ(n^(log₂ 7))`, the textbook {lit}`Θ(n^(lg 7))` bound.

Main results:

- Theorem `strassen2x2_correct`: the 2 by 2 block algebra core.
- Theorem `strassenRec_correct`: the recursive algorithm computes `A * B`.
- Theorem `strassenRec_padOne`: zero-padding preserves the corner product.
- Theorem `strassen_runtime_bigTheta`: `T(n) = Θ(n^(log₂ 7))`.

Notation conventions used in this section:

- `R` : the scalar ring
- `SqMat R k` : a `2^k × 2^k` square matrix over `R`
- `T`, `strassenWork` : the recursive work/cost function
-/

namespace CLRS
namespace Chapter04

/-- A 2 by 2 block matrix. -/
structure Matrix2 (R : Type*) where
  a11 : R
  a12 : R
  a21 : R
  a22 : R

namespace Matrix2

@[ext]
theorem ext {R : Type*} {A B : Matrix2 R}
    (h11 : A.a11 = B.a11) (h12 : A.a12 = B.a12)
    (h21 : A.a21 = B.a21) (h22 : A.a22 = B.a22) : A = B := by
  cases A
  cases B
  simp_all

variable {R : Type*} [Ring R]

/-- Ordinary 2 by 2 block matrix multiplication. -/
def mul (A B : Matrix2 R) : Matrix2 R :=
  { a11 := A.a11 * B.a11 + A.a12 * B.a21
    a12 := A.a11 * B.a12 + A.a12 * B.a22
    a21 := A.a21 * B.a11 + A.a22 * B.a21
    a22 := A.a21 * B.a12 + A.a22 * B.a22 }

/-- Strassen's seven-product reconstruction for 2 by 2 block matrices. -/
def strassen (A B : Matrix2 R) : Matrix2 R :=
  let p1 := A.a11 * (B.a12 - B.a22)
  let p2 := (A.a11 + A.a12) * B.a22
  let p3 := (A.a21 + A.a22) * B.a11
  let p4 := A.a22 * (B.a21 - B.a11)
  let p5 := (A.a11 + A.a22) * (B.a11 + B.a22)
  let p6 := (A.a12 - A.a22) * (B.a21 + B.a22)
  let p7 := (A.a11 - A.a21) * (B.a11 + B.a12)
  { a11 := p5 + p4 - p2 + p6
    a12 := p1 + p2
    a21 := p3 + p4
    a22 := p5 + p1 - p3 - p7 }

/-- Strassen's seven products compute the ordinary 2 by 2 block product. -/
theorem strassen_eq_mul (A B : Matrix2 R) : strassen A B = mul A B := by
  ext <;> simp [strassen, mul] <;> noncomm_ring

end Matrix2

/--
Reader-facing correctness theorem for CLRS Section 4.2: the algebraic
Strassen reconstruction is extensionally equal to ordinary 2 by 2 block
matrix multiplication.
-/
theorem strassen2x2_correct {R : Type*} [Ring R] (A B : Matrix2 R) :
    Matrix2.strassen A B = Matrix2.mul A B :=
  Matrix2.strassen_eq_mul A B

/-! ## Strassen's seven products on `Matrix (Fin 2) (Fin 2)` -/

section StrassenMatrix

variable {S : Type*} [Ring S]

/--
Strassen's seven-product reconstruction expressed directly on
{lit}`Matrix (Fin 2) (Fin 2) S`.  This is the `Matrix`-valued restatement of the
block algebra {name}`CLRS.Chapter04.Matrix2.strassen`, and it is the shape used
by the recursive algorithm below.  Each `p` is one of the seven products
`P₁…P₇` from CLRS.
-/
def strassen2 (M N : Matrix (Fin 2) (Fin 2) S) : Matrix (Fin 2) (Fin 2) S :=
  let p1 := M 0 0 * (N 0 1 - N 1 1)
  let p2 := (M 0 0 + M 0 1) * N 1 1
  let p3 := (M 1 0 + M 1 1) * N 0 0
  let p4 := M 1 1 * (N 1 0 - N 0 0)
  let p5 := (M 0 0 + M 1 1) * (N 0 0 + N 1 1)
  let p6 := (M 0 1 - M 1 1) * (N 1 0 + N 1 1)
  let p7 := (M 0 0 - M 1 0) * (N 0 0 + N 0 1)
  !![p5 + p4 - p2 + p6, p1 + p2; p3 + p4, p5 + p1 - p3 - p7]

/--
The seven Strassen products compute the ordinary `2 × 2` matrix product.  This
is the `Matrix`-valued counterpart of {name}`CLRS.Chapter04.Matrix2.strassen_eq_mul`.
-/
theorem strassen2_eq_mul (M N : Matrix (Fin 2) (Fin 2) S) : strassen2 M N = M * N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [strassen2, Matrix.mul_apply, Fin.sum_univ_two] <;>
    noncomm_ring

end StrassenMatrix

/-! ## Recursive Strassen on power-of-two squares -/

/--
Depth-indexed square matrix over `R`.  {lit}`SqMat R 0` is the scalar type `R`,
and {lit}`SqMat R (k+1)` is a `2 × 2` block matrix whose entries are depth-`k`
squares.  Thus {lit}`SqMat R k` is a `2^k × 2^k` matrix realized as a balanced
quad-tree of `2 × 2` blocks.
-/
def SqMat (R : Type u) : ℕ → Type u
  | 0 => R
  | (k + 1) => Matrix (Fin 2) (Fin 2) (SqMat R k)

/--
The ring structure on {name}`CLRS.Chapter04.SqMat`.  At depth `0` it is the
scalar ring `R`; at depth `k+1` it is the standard `2 × 2` matrix ring over the
depth-`k` ring, so ordinary multiplication on {lit}`SqMat R k` is exactly block
matrix multiplication.
-/
instance instRingSqMat (R : Type u) [Ring R] : ∀ k, Ring (SqMat R k)
  | 0 => inferInstanceAs (Ring R)
  | (k + 1) =>
      letI := instRingSqMat R k
      inferInstanceAs (Ring (Matrix (Fin 2) (Fin 2) (SqMat R k)))

/--
The recursive Strassen algorithm.  {lit}`strassenRec R 0` is the scalar base
case (conventional multiplication); {lit}`strassenRec R (k+1)` forms the seven
Strassen products of the four sub-blocks with seven recursive calls and
reassembles the four output blocks (CLRS `STRASSEN`).
-/
def strassenRec (R : Type u) [Ring R] : ∀ k, SqMat R k → SqMat R k → SqMat R k
  | 0, x, y => x * y
  | (k + 1), A, B =>
      let p1 := strassenRec R k (A 0 0) (B 0 1 - B 1 1)
      let p2 := strassenRec R k (A 0 0 + A 0 1) (B 1 1)
      let p3 := strassenRec R k (A 1 0 + A 1 1) (B 0 0)
      let p4 := strassenRec R k (A 1 1) (B 1 0 - B 0 0)
      let p5 := strassenRec R k (A 0 0 + A 1 1) (B 0 0 + B 1 1)
      let p6 := strassenRec R k (A 0 1 - A 1 1) (B 1 0 + B 1 1)
      let p7 := strassenRec R k (A 0 0 - A 1 0) (B 0 0 + B 0 1)
      !![p5 + p4 - p2 + p6, p1 + p2; p3 + p4, p5 + p1 - p3 - p7]

/--
Correctness of the recursive Strassen algorithm: at every depth it returns the
ordinary matrix product `A * B`.  The proof is induction on depth; each step
rewrites the seven recursive products by the induction hypothesis and then
applies the 2 by 2 identity {name}`CLRS.Chapter04.strassen2_eq_mul`.
-/
theorem strassenRec_eq_mul (R : Type u) [Ring R] :
    ∀ (k : ℕ) (A B : SqMat R k), strassenRec R k A B = A * B
  | 0, x, y => rfl
  | (k + 1), A, B => by
      have IH : ∀ X Y : SqMat R k, strassenRec R k X Y = X * Y := strassenRec_eq_mul R k
      have hstep : strassenRec R (k + 1) A B = strassen2 A B := by
        simp only [strassenRec, strassen2, IH]
      rw [hstep]
      exact strassen2_eq_mul A B

/--
Reader-facing correctness theorem for the recursive algorithm: on a
`2^k × 2^k` square, {name}`CLRS.Chapter04.strassenRec` produces the true matrix
product.
-/
theorem strassenRec_correct (R : Type u) [Ring R] (k : ℕ) (A B : SqMat R k) :
    strassenRec R k A B = A * B :=
  strassenRec_eq_mul R k A B

/-! ## Padding to the next power of two -/

/--
Zero-padding: embed a depth-`k` square into the top-left block of a depth-`(k+1)`
square, filling the other three blocks with zeros.  This is the padding step of
CLRS `STRASSEN`, which enlarges an `n × n` input to the next power of two.
-/
def padOne (R : Type u) [Ring R] (k : ℕ) (x : SqMat R k) : SqMat R (k + 1) :=
  !![x, 0; 0, 0]

/--
Zero-padded factors multiply block-diagonally: the top-left corner of the
product of two padded matrices is the product of the two originals, with the
rest still zero.
-/
theorem padOne_mul (R : Type u) [Ring R] (k : ℕ) (x y : SqMat R k) :
    padOne R k x * padOne R k y = padOne R k (x * y) := by
  show (!![x, 0; 0, 0] : Matrix (Fin 2) (Fin 2) (SqMat R k)) * !![y, 0; 0, 0]
      = !![x * y, 0; 0, 0]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/--
Running the recursive Strassen algorithm on two zero-padded inputs recovers the
padded product: padding to the next power of two does not change the meaningful
top-left product.  This composes {name}`CLRS.Chapter04.strassenRec_correct` with
{name}`CLRS.Chapter04.padOne_mul`.
-/
theorem strassenRec_padOne (R : Type u) [Ring R] (k : ℕ) (x y : SqMat R k) :
    strassenRec R (k + 1) (padOne R k x) (padOne R k y) = padOne R k (x * y) := by
  rw [strassenRec_correct, padOne_mul]

/--
The top-left block projection, inverse to {name}`CLRS.Chapter04.padOne` on the
padded corner.  Extracting the corner after a padded Strassen multiplication
returns the original product `x * y`.
-/
theorem strassenRec_padOne_corner (R : Type u) [Ring R] (k : ℕ) (x y : SqMat R k) :
    (strassenRec R (k + 1) (padOne R k x) (padOne R k y)) 0 0 = x * y := by
  rw [strassenRec_padOne]
  show (!![x * y, 0; 0, 0] : Matrix (Fin 2) (Fin 2) (SqMat R k)) 0 0 = x * y
  simp

/-! ## Runtime: `T(n) = 7 T(⌊n/2⌋) + n²` is `Θ(n^(log₂ 7))` -/

/--
The Strassen work recurrence {lit}`T(n) = 7 T(⌊n/2⌋) + n²`: seven recursive
subproblems of half size plus quadratic block-combination work, with base value
{lit}`T(0) = 0`.  This is the CLRS cost recurrence whose solution is the running
time of {name}`CLRS.Chapter04.strassenRec`.
-/
noncomputable def strassenWork : ℕ → ℝ
  | 0 => 0
  | (n + 1) => 7 * strassenWork ((n + 1) / 2) + ((n + 1 : ℕ) : ℝ) ^ 2
  decreasing_by exact Nat.div_lt_self (Nat.succ_pos n) (by norm_num)

/-- Base value of the work recurrence. -/
theorem strassenWork_zero : strassenWork 0 = 0 := by
  rw [strassenWork]

/-- One recursion step of the work recurrence at a successor argument. -/
theorem strassenWork_succ (n : ℕ) :
    strassenWork (n + 1) = 7 * strassenWork ((n + 1) / 2) + ((n + 1 : ℕ) : ℝ) ^ 2 := by
  rw [strassenWork]

/-- One recursion step of the work recurrence at any positive argument. -/
theorem strassenWork_pos_step (n : ℕ) (hn : 0 < n) :
    strassenWork n = 7 * strassenWork (n / 2) + ((n : ℕ) : ℝ) ^ 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact strassenWork_succ m

/--
The forcing term {lit}`f(n) = T(n) - 7 T(⌊n/2⌋)` of the recurrence.  Choosing
{lit}`f` as this defect makes the CLRS floor recurrence
{lit}`T(n) = 7 T(⌊n/2⌋) + f(n)` hold definitionally at every input.
-/
noncomputable def strassenForcing (n : ℕ) : ℝ :=
  strassenWork n - 7 * strassenWork (n / 2)

/--
The work function satisfies the Chapter 4 floor-division Master recurrence with
{lit}`a = 7`, {lit}`b = 2`.
-/
theorem strassenWork_floorRec :
    FloorDivideRecurrence 7 2 strassenForcing strassenWork := by
  refine ⟨fun n => ?_⟩
  simp only [strassenForcing]
  push_cast
  ring

/-- The work function is nonnegative. -/
theorem strassenWork_nonneg : ∀ n, 0 ≤ strassenWork n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [strassenWork_zero]
    · rw [strassenWork_pos_step n hn]
      have hlt : n / 2 < n := Nat.div_lt_self hn (by norm_num)
      have hrec := ih (n / 2) hlt
      nlinarith [hrec, sq_nonneg ((n : ℕ) : ℝ)]

/-- The work function is nondecreasing across one step. -/
theorem strassenWork_le_succ : ∀ n, strassenWork n ≤ strassenWork (n + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; rw [strassenWork_zero]; exact strassenWork_nonneg _
    · rw [strassenWork_pos_step n hn, strassenWork_pos_step (n + 1) (Nat.succ_pos n)]
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
theorem strassenWork_monotone : Monotone strassenWork :=
  monotone_nat_of_le_succ strassenWork_le_succ

/-- The work function satisfies the absolute-value monotonicity interface. -/
theorem strassenWork_monotoneAbs : MonotoneAbs strassenWork := by
  intro m n hmn
  rw [abs_of_nonneg (strassenWork_nonneg m), abs_of_nonneg (strassenWork_nonneg n)]
  exact strassenWork_monotone hmn

/--
The normalized forcing on exact powers is the convergent geometric sequence
{lit}`(4/7)^(k+1)`: on {lit}`n = 2^(k+1)` the forcing is exactly the block-work
{lit}`(2^(k+1))² = 4^(k+1)`, so dividing by {lit}`7^(k+1)` gives {lit}`(4/7)^(k+1)`.
This is what places the Strassen recurrence in Master case 1.
-/
theorem strassen_normForcing (k : ℕ) :
    normalizedForcing 7 2 strassenForcing k = (4 / 7 : ℝ) ^ (k + 1) := by
  have hpos : 0 < 2 ^ (k + 1) := pow_pos (by norm_num) _
  have hdiv : 2 ^ (k + 1) / 2 = 2 ^ k := by rw [pow_succ]; omega
  have hcast : ((2 ^ (k + 1) : ℕ) : ℝ) ^ 2 = (4 : ℝ) ^ (k + 1) := by
    push_cast
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm 2 (k + 1)]
  have hforcing : strassenForcing (2 ^ (k + 1)) = (4 : ℝ) ^ (k + 1) := by
    unfold strassenForcing
    rw [strassenWork_pos_step (2 ^ (k + 1)) hpos, hdiv]
    linarith [hcast]
  unfold normalizedForcing
  rw [hforcing, ← div_pow]
  norm_num

/-- Case-1 hypothesis: the normalized forcing is nonnegative. -/
theorem strassen_term_nonneg (k : ℕ) : 0 ≤ normalizedForcing 7 2 strassenForcing k := by
  rw [strassen_normForcing]; positivity

/-- Case-1 hypothesis: the normalized forcing is bounded by a geometric sequence. -/
theorem strassen_term_upper (k : ℕ) :
    normalizedForcing 7 2 strassenForcing k ≤ (4 / 7 : ℝ) * (4 / 7 : ℝ) ^ k := by
  rw [strassen_normForcing, pow_succ]
  exact le_of_eq (mul_comm _ _)

/-- Value of the work recurrence at the base input `1`. -/
theorem strassenWork_one : strassenWork 1 = 1 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, strassenWork_succ]
  norm_num [strassenWork_zero]

/-- Positivity of the normalized base value, a case-1 hypothesis. -/
theorem strassen_base_pos : 0 < normalizedValue 7 2 strassenWork 0 := by
  unfold normalizedValue
  norm_num [strassenWork_one]

/--
**Runtime of Strassen's algorithm.**  The recurrence
{lit}`T(n) = 7 T(⌊n/2⌋) + n²` is {lit}`Θ(n^(log₂ 7))`.  This is the CLRS
{lit}`Θ(n^(lg 7))` bound, obtained by discharging Master-theorem case 1 (the
forcing {lit}`n²` is polynomially smaller than the critical {lit}`n^(log₂ 7)`)
through the Chapter 4 wrapper
{name}`CLRS.Chapter04.floorDivide_allInput_masterCase1_realLogScale`.
-/
theorem strassen_runtime_bigTheta :
    Chapter03.isBigTheta strassenWork (realLogScale 7 2) :=
  floorDivide_allInput_masterCase1_realLogScale 7 2 strassenForcing strassenWork
    strassenWork_floorRec (by norm_num) (by norm_num) strassenWork_monotoneAbs
    strassen_base_pos strassen_term_nonneg (r := 4 / 7) (C := 4 / 7)
    (by norm_num) (by norm_num) (by norm_num) strassen_term_upper

/--
The comparison scale {name}`CLRS.Chapter04.realLogScale` at {lit}`a = 7`,
{lit}`b = 2` is the textbook power {lit}`n^(log₂ 7)`, so
{name}`CLRS.Chapter04.strassen_runtime_bigTheta` is exactly the CLRS
{lit}`Θ(n^(lg 7))` statement.
-/
theorem realLogScale_seven_two (n : ℕ) :
    realLogScale 7 2 n = (n : ℝ) ^ Real.logb 2 7 := by
  rw [realLogScale, realLogExponent, Real.logb]
  norm_num

end Chapter04
end CLRS

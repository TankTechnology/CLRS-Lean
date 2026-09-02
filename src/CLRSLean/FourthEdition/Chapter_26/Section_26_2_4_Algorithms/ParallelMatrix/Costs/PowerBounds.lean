import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.ParallelMatrix.Costs.Monotonicity

/-!
# CLRS Section 26.2 — Matrix Costs at Powers of Two

This module solves, or tightly bounds, the four execution recurrences at
matrix sizes {lit}`2^k`.  Subtraction-free balance equations are used for the
work recurrences so that the natural-number proofs remain stable.

Main results:

- Theorems {lit}`pAddWork_pow_two_bounds` and {lit}`pAddSpan_pow_two`.
- Theorems {lit}`pMatMulExecWork_pow_two_bounds` and
  {lit}`pMatMulExecSpan_pow_two`.
- Exact-power big-Theta theorems for all four costs.
-/

namespace CLRS
namespace Chapter27

/-- Halving a non-base power of two returns the preceding power. -/
private theorem powerBounds_two_pow_succ_div_two (k : ℕ) :
    2 ^ (k + 1) / 2 = 2 ^ k := by
  rw [pow_succ]
  omega

/-- A non-base power of two has size at least two. -/
private theorem powerBounds_two_le_two_pow_succ (k : ℕ) :
    2 ≤ 2 ^ (k + 1) := by
  rw [pow_succ]
  have := Nat.one_le_pow k 2 (by norm_num)
  omega

/-! ## P-ADD exact powers -/

/-- Subtraction-free closed form for P-ADD work at powers of two. -/
theorem pAddWork_pow_two_balance (k : ℕ) :
    pAddWork (2 ^ k) + 1 = 2 * 4 ^ k := by
  induction k with
  | zero =>
      rw [pAddWork]
      norm_num
  | succ k ih =>
      rw [pAddWork_unfold (powerBounds_two_le_two_pow_succ k),
        powerBounds_two_pow_succ_div_two,
        pow_succ]
      omega

/-- P-ADD work at size {lit}`2^k` is trapped within constant multiples of
{lit}`4^k`. -/
theorem pAddWork_pow_two_bounds (k : ℕ) :
    4 ^ k ≤ pAddWork (2 ^ k) ∧ pAddWork (2 ^ k) ≤ 2 * 4 ^ k := by
  have hbalance := pAddWork_pow_two_balance k
  have hpow : 1 ≤ 4 ^ k := Nat.one_le_pow k 4 (by norm_num)
  omega

/-- Exact P-ADD span at powers of two. -/
theorem pAddSpan_pow_two (k : ℕ) : pAddSpan (2 ^ k) = 2 * k + 1 := by
  induction k with
  | zero =>
      rw [pAddSpan]
      norm_num
  | succ k ih =>
      rw [pAddSpan_unfold (powerBounds_two_le_two_pow_succ k),
        powerBounds_two_pow_succ_div_two, ih]
      omega

/-! ## P-MATMUL exact powers -/

/-- Subtraction-free closed form for executable P-MATMUL work at powers of
two.  It is equivalent to the usual closed form while avoiding truncated
natural subtraction. -/
theorem pMatMulExecWork_pow_two_balance (k : ℕ) :
    7 * pMatMulExecWork (2 ^ k) + 14 * 4 ^ k + 6 = 27 * 8 ^ k := by
  induction k with
  | zero =>
      rw [pMatMulExecWork]
      norm_num
  | succ k ih =>
      rw [pMatMulExecWork_unfold (powerBounds_two_le_two_pow_succ k),
        powerBounds_two_pow_succ_div_two]
      have hadd := pAddWork_pow_two_balance (k + 1)
      rw [pow_succ] at hadd ⊢
      omega

/-- Executable P-MATMUL work at size {lit}`2^k` is trapped within constant
multiples of {lit}`8^k`. -/
theorem pMatMulExecWork_pow_two_bounds (k : ℕ) :
    8 ^ k ≤ pMatMulExecWork (2 ^ k) ∧
      pMatMulExecWork (2 ^ k) ≤ 4 * 8 ^ k := by
  constructor
  · induction k with
    | zero =>
        rw [pMatMulExecWork]
        norm_num
    | succ k ih =>
        rw [pMatMulExecWork_unfold (powerBounds_two_le_two_pow_succ k),
          powerBounds_two_pow_succ_div_two, pow_succ]
        omega
  · have hbalance := pMatMulExecWork_pow_two_balance k
    omega

/-- Exact executable P-MATMUL span at powers of two. -/
theorem pMatMulExecSpan_pow_two (k : ℕ) :
    pMatMulExecSpan (2 ^ k) = k ^ 2 + 5 * k + 1 := by
  induction k with
  | zero =>
      rw [pMatMulExecSpan]
      norm_num
  | succ k ih =>
      rw [pMatMulExecSpan_unfold (powerBounds_two_le_two_pow_succ k),
        powerBounds_two_pow_succ_div_two, ih, pAddSpan_pow_two]
      ring

/-- Executable P-MATMUL span at size {lit}`2^k` is quadratic in {lit}`k+1`. -/
theorem pMatMulExecSpan_pow_two_bounds (k : ℕ) :
    (k + 1) ^ 2 ≤ pMatMulExecSpan (2 ^ k) ∧
      pMatMulExecSpan (2 ^ k) ≤ 3 * (k + 1) ^ 2 := by
  rw [pMatMulExecSpan_pow_two]
  constructor <;> nlinarith [Nat.zero_le k]

/-! ## Exact-power asymptotics -/

/-- P-ADD work is Theta of {lit}`4^k` on exact powers of two. -/
theorem pAddWork_exactPower_bigTheta :
    Chapter03.isBigTheta
      (fun k : ℕ => (pAddWork (2 ^ k) : ℝ))
      (fun k : ℕ => (4 : ℝ) ^ k) := by
  constructor
  · refine (Chapter03.isBigO_iff _ _).mpr ⟨2, by norm_num, 0, ?_⟩
    intro k _
    rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by positivity)]
    have hreal :
        (pAddWork (2 ^ k) : ℝ) ≤ ((2 * 4 ^ k : ℕ) : ℝ) := by
      exact_mod_cast (pAddWork_pow_two_bounds k).2
    simpa [Nat.cast_mul, Nat.cast_pow] using hreal
  · refine (Chapter03.isBigOmega_iff _ _).mpr ⟨1, by norm_num, 0, ?_⟩
    intro k _
    rw [abs_of_nonneg (by positivity : 0 ≤ (4 : ℝ) ^ k),
      abs_of_nonneg (Nat.cast_nonneg _)]
    have hreal : ((4 ^ k : ℕ) : ℝ) ≤ (pAddWork (2 ^ k) : ℝ) := by
      exact_mod_cast (pAddWork_pow_two_bounds k).1
    simpa [Nat.cast_pow] using hreal

/-- P-ADD span is Theta of {lit}`k+1` on exact powers of two. -/
theorem pAddSpan_exactPower_bigTheta :
    Chapter03.isBigTheta
      (fun k : ℕ => (pAddSpan (2 ^ k) : ℝ))
      (fun k : ℕ => (k : ℝ) + 1) := by
  constructor
  · refine (Chapter03.isBigO_iff _ _).mpr ⟨2, by norm_num, 0, ?_⟩
    intro k _
    rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by positivity)]
    rw [pAddSpan_pow_two]
    push_cast
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith
  · refine (Chapter03.isBigOmega_iff _ _).mpr ⟨1, by norm_num, 0, ?_⟩
    intro k _
    rw [abs_of_nonneg (by positivity : 0 ≤ (k : ℝ) + 1),
      abs_of_nonneg (Nat.cast_nonneg _)]
    rw [pAddSpan_pow_two]
    push_cast
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith

/-- Executable P-MATMUL work is Theta of {lit}`8^k` on exact powers of two. -/
theorem pMatMulExecWork_exactPower_bigTheta :
    Chapter03.isBigTheta
      (fun k : ℕ => (pMatMulExecWork (2 ^ k) : ℝ))
      (fun k : ℕ => (8 : ℝ) ^ k) := by
  constructor
  · refine (Chapter03.isBigO_iff _ _).mpr ⟨4, by norm_num, 0, ?_⟩
    intro k _
    rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by positivity)]
    have hreal :
        (pMatMulExecWork (2 ^ k) : ℝ) ≤ ((4 * 8 ^ k : ℕ) : ℝ) := by
      exact_mod_cast (pMatMulExecWork_pow_two_bounds k).2
    simpa [Nat.cast_mul, Nat.cast_pow] using hreal
  · refine (Chapter03.isBigOmega_iff _ _).mpr ⟨1, by norm_num, 0, ?_⟩
    intro k _
    rw [abs_of_nonneg (by positivity : 0 ≤ (8 : ℝ) ^ k),
      abs_of_nonneg (Nat.cast_nonneg _)]
    have hreal : ((8 ^ k : ℕ) : ℝ) ≤ (pMatMulExecWork (2 ^ k) : ℝ) := by
      exact_mod_cast (pMatMulExecWork_pow_two_bounds k).1
    simpa [Nat.cast_pow] using hreal

/-- Executable P-MATMUL span is Theta of {lit}`(k+1)^2` on exact powers of
two. -/
theorem pMatMulExecSpan_exactPower_bigTheta :
    Chapter03.isBigTheta
      (fun k : ℕ => (pMatMulExecSpan (2 ^ k) : ℝ))
      (fun k : ℕ => ((k : ℝ) + 1) ^ 2) := by
  constructor
  · refine (Chapter03.isBigO_iff _ _).mpr ⟨3, by norm_num, 0, ?_⟩
    intro k _
    rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by positivity)]
    have hreal :
        (pMatMulExecSpan (2 ^ k) : ℝ) ≤ ((3 * (k + 1) ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast (pMatMulExecSpan_pow_two_bounds k).2
    norm_num [Nat.cast_mul, Nat.cast_pow] at hreal ⊢
    exact hreal
  · refine (Chapter03.isBigOmega_iff _ _).mpr ⟨1, by norm_num, 0, ?_⟩
    intro k _
    rw [abs_of_nonneg (by positivity : 0 ≤ ((k : ℝ) + 1) ^ 2),
      abs_of_nonneg (Nat.cast_nonneg _)]
    have hreal : (((k + 1) ^ 2 : ℕ) : ℝ) ≤
        (pMatMulExecSpan (2 ^ k) : ℝ) := by
      exact_mod_cast (pMatMulExecSpan_pow_two_bounds k).1
    norm_num [Nat.cast_pow] at hreal ⊢
    exact hreal

end Chapter27
end CLRS

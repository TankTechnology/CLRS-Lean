import Mathlib.Tactic
import CLRSLean.Chapter_27.Section_27_1_Multithreading_Model

/-!
# 27.2–27.4. Multithreaded Algorithms

This file formalizes the work/span recurrences of the parallel algorithms
from CLRS §§27.2–27.4 as executable recursive cost functions, in the style of
Chapter 4's divide-and-conquer cost analysis:

- **§27.2 P-MATMUL**: work `T₁(n) = 8 T₁(n/2) + n²`, span `T∞(n) = T∞(n/2) + 1`.
- **§27.3 P-MERGE**: work `T₁(n) = T₁(⌊n/2⌋) + T₁(⌈n/2⌉) + (⌊log₂ n⌋ + 1)`
  (two parallel recursive merges plus a binary-search combine),
  span `T∞(n) = T∞(⌈n/2⌉) + (⌊log₂ n⌋ + 1)`.
- **§27.3 P-MERGE-SORT**: work `T₁(n) = T₁(⌊n/2⌋) + T₁(⌈n/2⌉) + n`,
  span `T∞(n) = T∞(⌈n/2⌉) + (P-MERGE span)`.
- **§27.4 Parallel Strassen**: work `T₁(n) = 7 T₁(n/2) + n²`,
  span `T∞(n) = T∞(n/2) + 1`.

## Main results (exact closed forms on powers of two)

* `pMatMulWork_pow_two`: `T₁(2ᵏ) + 4ᵏ = 2·8ᵏ`, i.e. work `Θ(n³)`.
* `pMatMulWork_le`: the all-input bound `T₁(n) + n² ≤ 2n³`.
* `pMatMulSpan_pow_two`: `T∞(2ᵏ) = k + 1`, i.e. span `Θ(log n)`;
  `pMatMulSpan_le`: the all-input bound `T∞(n) ≤ ⌊log₂ n⌋ + 1`.
* `pMergeWork_pow_two`: `T₁(2ᵏ) + (k + 3) = 4·2ᵏ`, i.e. work `Θ(n)`.
* `pMergeSpan_pow_two`: `2·T∞(2ᵏ) = (k+1)(k+2)`, i.e. span `Θ(log² n)`.
* `pMergeSortWork_pow_two`: `T₁(2ᵏ) = 2ᵏ·(k+1)`, i.e. work `Θ(n log n)`.
* `pMergeSortSpan_pow_two`: `6·T∞(2ᵏ) = 6 + k·(k² + 6k + 11)`,
  i.e. span `Θ(log³ n)`.
* `strassenWork_pow_two`: `3·T₁(2ᵏ) + 4ᵏ⁺¹ = 7ᵏ⁺¹`, i.e. work
  `Θ(n^(log₂ 7))`.
* `strassenSpan_pow_two`: `T∞(2ᵏ) = k + 1`, i.e. span `Θ(log n)`.

## Deferred work

* All-input (floor/ceiling) Θ-bounds for the merge-based costs via the
  power-sandwich technique of Chapter 4 (`powerInterval_of_pos`), which
  requires monotonicity lemmas for each cost function.
* Executable P-MERGE / P-MERGE-SORT implementations refining these costs.
-/

namespace CLRS
namespace Chapter27

private theorem pow_two_succ_eq (k : ℕ) : 2 ^ (k + 1) / 2 = 2 ^ k := by
  rw [pow_succ]
  omega

private theorem pow_two_succ_sub (k : ℕ) : 2 ^ (k + 1) - 2 ^ (k + 1) / 2 = 2 ^ k := by
  rw [pow_succ]
  omega

private theorem log_two_pow (k : ℕ) : Nat.log 2 (2 ^ k) = k :=
  Nat.log_pow (by norm_num) k

private theorem two_le_two_pow_succ (k : ℕ) : 2 ≤ 2 ^ (k + 1) := by
  rw [pow_succ]
  have := Nat.one_le_pow k 2 (by norm_num)
  omega

private theorem two_pow_succ_mul (k : ℕ) : 2 ^ (k + 1) * 2 ^ (k + 1) = 4 ^ (k + 1) := by
  have h42 : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [h42, ← pow_mul, ← pow_add]
  congr 1
  omega

/-! ## §27.2: Parallel matrix multiplication (P-MATMUL) -/

/-- Work recurrence for P-MATMUL: `T₁(n) = 8 T₁(n/2) + n²`. -/
def pMatMulWork (n : ℕ) : ℕ :=
  if n ≤ 1 then
    n
  else
    8 * pMatMulWork (n / 2) + n * n
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by norm_num)

theorem pMatMulWork_unfold {n : ℕ} (hn : 2 ≤ n) :
    pMatMulWork n = 8 * pMatMulWork (n / 2) + n * n := by
  rw [pMatMulWork]
  simp [show ¬n ≤ 1 by omega]

/-- Exact work on powers of two: `T₁(2ᵏ) + 4ᵏ = 2·8ᵏ` (work `Θ(n³)`). -/
theorem pMatMulWork_pow_two (k : ℕ) :
    pMatMulWork (2 ^ k) + 4 ^ k = 2 * 8 ^ k := by
  induction k with
  | zero => native_decide
  | succ k ih =>
      rw [pMatMulWork_unfold (two_le_two_pow_succ k), pow_two_succ_eq,
        two_pow_succ_mul]
      nlinarith [ih, pow_succ (4 : ℕ) k, pow_succ (8 : ℕ) k]

/-- All-input upper bound: `T₁(n) + n² ≤ 2n³`. -/
theorem pMatMulWork_le (n : ℕ) : pMatMulWork n + n * n ≤ 2 * n * n * n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n ≤ 1
      · interval_cases n <;> native_decide
      · obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m ∨ n = 2 * m + 1 :=
          ⟨n / 2, by omega⟩
        · have hdiv : 2 * m / 2 = m := by omega
          rw [pMatMulWork_unfold (by omega), hdiv]
          have ihm := ih m (by omega)
          nlinarith [ihm]
        · have hdiv : (2 * m + 1) / 2 = m := by omega
          rw [pMatMulWork_unfold (by omega), hdiv]
          have ihm := ih m (by omega)
          nlinarith [ihm]

/-- Span recurrence for P-MATMUL: `T∞(n) = T∞(n/2) + 1`. -/
def pMatMulSpan (n : ℕ) : ℕ :=
  if n ≤ 1 then
    n
  else
    pMatMulSpan (n / 2) + 1
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by norm_num)

theorem pMatMulSpan_unfold {n : ℕ} (hn : 2 ≤ n) :
    pMatMulSpan n = pMatMulSpan (n / 2) + 1 := by
  rw [pMatMulSpan]
  simp [show ¬n ≤ 1 by omega]

/-- Exact span on powers of two: `T∞(2ᵏ) = k + 1` (span `Θ(log n)`). -/
theorem pMatMulSpan_pow_two (k : ℕ) : pMatMulSpan (2 ^ k) = k + 1 := by
  induction k with
  | zero => native_decide
  | succ k ih =>
      rw [pMatMulSpan_unfold (two_le_two_pow_succ k), pow_two_succ_eq, ih]

/-- All-input span bound: `T∞(n) ≤ ⌊log₂ n⌋ + 1`. -/
theorem pMatMulSpan_le (n : ℕ) : pMatMulSpan n ≤ Nat.log 2 n + 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n ≤ 1
      · interval_cases n <;> native_decide
      · rw [pMatMulSpan_unfold (by omega)]
        have ihm := ih (n / 2) (by omega)
        have hlog := Nat.log_div_base 2 n
        have hlogpos : 1 ≤ Nat.log 2 n :=
          Nat.le_log_of_pow_le (by norm_num) (by omega)
        omega

/-! ## §27.3: Parallel merge (P-MERGE) -/

/-- Work recurrence for P-MERGE: two parallel recursive merges on the two
halves plus a `Θ(log n)` binary-search combine,
`T₁(n) = T₁(⌊n/2⌋) + T₁(⌈n/2⌉) + (⌊log₂ n⌋ + 1)`. -/
def pMergeWork (n : ℕ) : ℕ :=
  if n ≤ 1 then
    n
  else
    pMergeWork (n / 2) + pMergeWork (n - n / 2) + (Nat.log 2 n + 1)
termination_by n
decreasing_by
  · exact Nat.div_lt_self (by omega) (by norm_num)
  · exact Nat.sub_lt (by omega) (Nat.div_pos (by omega) (by norm_num))

theorem pMergeWork_unfold {n : ℕ} (hn : 2 ≤ n) :
    pMergeWork n =
      pMergeWork (n / 2) + pMergeWork (n - n / 2) + (Nat.log 2 n + 1) := by
  rw [pMergeWork]
  simp [show ¬n ≤ 1 by omega]

/-- Exact work on powers of two: `T₁(2ᵏ) + (k + 3) = 4·2ᵏ` (work `Θ(n)`). -/
theorem pMergeWork_pow_two (k : ℕ) :
    pMergeWork (2 ^ k) + (k + 3) = 4 * 2 ^ k := by
  induction k with
  | zero => native_decide
  | succ k ih =>
      rw [pMergeWork_unfold (two_le_two_pow_succ k), pow_two_succ_sub,
        pow_two_succ_eq, log_two_pow]
      nlinarith [ih, pow_succ (2 : ℕ) k]

/-- Span recurrence for P-MERGE: the critical path follows the larger half,
`T∞(n) = T∞(⌈n/2⌉) + (⌊log₂ n⌋ + 1)`. -/
def pMergeSpan (n : ℕ) : ℕ :=
  if n ≤ 1 then
    n
  else
    pMergeSpan (n - n / 2) + (Nat.log 2 n + 1)
termination_by n
decreasing_by exact Nat.sub_lt (by omega) (Nat.div_pos (by omega) (by norm_num))

theorem pMergeSpan_unfold {n : ℕ} (hn : 2 ≤ n) :
    pMergeSpan n = pMergeSpan (n - n / 2) + (Nat.log 2 n + 1) := by
  rw [pMergeSpan]
  simp [show ¬n ≤ 1 by omega]

/-- Exact span on powers of two: `2·T∞(2ᵏ) = (k+1)(k+2)` (span `Θ(log² n)`). -/
theorem pMergeSpan_pow_two (k : ℕ) :
    2 * pMergeSpan (2 ^ k) = (k + 1) * (k + 2) := by
  induction k with
  | zero => native_decide
  | succ k ih =>
      rw [pMergeSpan_unfold (two_le_two_pow_succ k), pow_two_succ_sub,
        log_two_pow]
      nlinarith [ih]

/-! ## §27.3: Parallel merge sort (P-MERGE-SORT) -/

/-- Work recurrence for P-MERGE-SORT:
`T₁(n) = T₁(⌊n/2⌋) + T₁(⌈n/2⌉) + n`. -/
def pMergeSortWork (n : ℕ) : ℕ :=
  if n ≤ 1 then
    n
  else
    pMergeSortWork (n / 2) + pMergeSortWork (n - n / 2) + n
termination_by n
decreasing_by
  · exact Nat.div_lt_self (by omega) (by norm_num)
  · exact Nat.sub_lt (by omega) (Nat.div_pos (by omega) (by norm_num))

theorem pMergeSortWork_unfold {n : ℕ} (hn : 2 ≤ n) :
    pMergeSortWork n = pMergeSortWork (n / 2) + pMergeSortWork (n - n / 2) + n := by
  rw [pMergeSortWork]
  simp [show ¬n ≤ 1 by omega]

/-- Exact work on powers of two: `T₁(2ᵏ) = 2ᵏ·(k+1)` (work `Θ(n log n)`). -/
theorem pMergeSortWork_pow_two (k : ℕ) :
    pMergeSortWork (2 ^ k) = 2 ^ k * (k + 1) := by
  induction k with
  | zero => native_decide
  | succ k ih =>
      rw [pMergeSortWork_unfold (two_le_two_pow_succ k), pow_two_succ_sub,
        pow_two_succ_eq]
      nlinarith [ih, pow_succ (2 : ℕ) k]

/-- Span recurrence for P-MERGE-SORT:
`T∞(n) = T∞(⌈n/2⌉) + (P-MERGE span on n elements)`. -/
def pMergeSortSpan (n : ℕ) : ℕ :=
  if n ≤ 1 then
    n
  else
    pMergeSortSpan (n - n / 2) + pMergeSpan n
termination_by n
decreasing_by exact Nat.sub_lt (by omega) (Nat.div_pos (by omega) (by norm_num))

theorem pMergeSortSpan_unfold {n : ℕ} (hn : 2 ≤ n) :
    pMergeSortSpan n = pMergeSortSpan (n - n / 2) + pMergeSpan n := by
  rw [pMergeSortSpan]
  simp [show ¬n ≤ 1 by omega]

/-- Exact span on powers of two:
`6·T∞(2ᵏ) = 6 + k·(k² + 6k + 11)` (span `Θ(log³ n)`). -/
theorem pMergeSortSpan_pow_two (k : ℕ) :
    6 * pMergeSortSpan (2 ^ k) = 6 + k * (k * k + 6 * k + 11) := by
  induction k with
  | zero => native_decide
  | succ k ih =>
      rw [pMergeSortSpan_unfold (two_le_two_pow_succ k), pow_two_succ_sub]
      have hS := pMergeSpan_pow_two (k + 1)
      nlinarith [ih, hS]

/-! ## §27.4: Parallel Strassen's algorithm -/

/-- Work recurrence for parallel Strassen: `T₁(n) = 7 T₁(n/2) + n²`. -/
def strassenWork (n : ℕ) : ℕ :=
  if n ≤ 1 then
    n
  else
    7 * strassenWork (n / 2) + n * n
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by norm_num)

theorem strassenWork_unfold {n : ℕ} (hn : 2 ≤ n) :
    strassenWork n = 7 * strassenWork (n / 2) + n * n := by
  rw [strassenWork]
  simp [show ¬n ≤ 1 by omega]

/-- Exact work on powers of two: `3·T₁(2ᵏ) + 4ᵏ⁺¹ = 7ᵏ⁺¹`
(work `Θ(n^(log₂ 7))`). -/
theorem strassenWork_pow_two (k : ℕ) :
    3 * strassenWork (2 ^ k) + 4 ^ (k + 1) = 7 ^ (k + 1) := by
  induction k with
  | zero => native_decide
  | succ k ih =>
      rw [strassenWork_unfold (two_le_two_pow_succ k), pow_two_succ_eq,
        two_pow_succ_mul]
      nlinarith [ih, pow_succ (4 : ℕ) (k + 1), pow_succ (7 : ℕ) (k + 1)]

/-- Span recurrence for parallel Strassen: `T∞(n) = T∞(n/2) + 1`. -/
def strassenSpan (n : ℕ) : ℕ :=
  if n ≤ 1 then
    n
  else
    strassenSpan (n / 2) + 1
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by norm_num)

theorem strassenSpan_unfold {n : ℕ} (hn : 2 ≤ n) :
    strassenSpan n = strassenSpan (n / 2) + 1 := by
  rw [strassenSpan]
  simp [show ¬n ≤ 1 by omega]

/-- Exact span on powers of two: `T∞(2ᵏ) = k + 1` (span `Θ(log n)`). -/
theorem strassenSpan_pow_two (k : ℕ) : strassenSpan (2 ^ k) = k + 1 := by
  induction k with
  | zero => native_decide
  | succ k ih =>
      rw [strassenSpan_unfold (two_le_two_pow_succ k), pow_two_succ_eq, ih]

end Chapter27
end CLRS

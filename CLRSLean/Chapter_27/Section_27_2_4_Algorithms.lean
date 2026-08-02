import Mathlib.Tactic
import CLRSLean.Chapter_04.Section_04_6_Master_Theorem_All_Input
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

private theorem natCost_monotoneAbs {T : ℕ → ℕ} (hT : Monotone T) :
    Chapter04.MonotoneAbs (fun n => (T n : ℝ)) := by
  intro m n hmn
  rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
  change (T m : ℝ) ≤ (T n : ℝ)
  exact_mod_cast hT hmn

private theorem natCost_power_sandwich {T : ℕ → ℕ} (hT : Monotone T)
    (n : ℕ) (hn : 0 < n) :
    T (2 ^ Nat.log 2 n) ≤ T n ∧
      T n ≤ T (2 ^ (Nat.log 2 n + 1)) := by
  rcases Chapter04.powerInterval_of_pos 2 n (by norm_num) hn.ne' with ⟨hlo, hhi⟩
  exact ⟨hT hlo, hT (Nat.le_of_lt hhi)⟩

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

/-- The P-MERGE work recurrence does not decrease at a successor step. -/
private theorem pMergeWork_le_succ : ∀ n, pMergeWork n ≤ pMergeWork (n + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n ≤ 1
      · interval_cases n
        · rw [show pMergeWork 0 = 0 by rw [pMergeWork]; norm_num]
          exact Nat.zero_le _
        · have hone : pMergeWork 1 = 1 := by rw [pMergeWork]; norm_num
          rw [hone, pMergeWork_unfold (n := 2) (by norm_num)]
          norm_num [hone]
      · obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m ∨ n = 2 * m + 1 :=
          ⟨n / 2, by omega⟩
        · have hdiv0 : 2 * m / 2 = m := by omega
          have hdiv1 : (2 * m + 1) / 2 = m := by omega
          have hceil0 : 2 * m - 2 * m / 2 = m := by omega
          have hceil1 : 2 * m + 1 - (2 * m + 1) / 2 = m + 1 := by omega
          rw [pMergeWork_unfold (n := 2 * m) (by omega),
            pMergeWork_unfold (n := 2 * m + 1) (by omega),
            hceil0, hceil1, hdiv0, hdiv1]
          have ihm := ih m (by omega)
          have hlog : Nat.log 2 (2 * m) ≤ Nat.log 2 (2 * m + 1) :=
            Nat.log_mono_right (by omega)
          omega
        · have hdiv0 : (2 * m + 1) / 2 = m := by omega
          have hdiv1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
          have hceil0 : 2 * m + 1 - (2 * m + 1) / 2 = m + 1 := by omega
          have hceil1 : 2 * m + 1 + 1 - (2 * m + 1 + 1) / 2 = m + 1 := by omega
          rw [pMergeWork_unfold (n := 2 * m + 1) (by omega),
            pMergeWork_unfold (n := 2 * m + 1 + 1) (by omega),
            hceil0, hceil1, hdiv0, hdiv1]
          have ihm := ih m (by omega)
          have hlog : Nat.log 2 (2 * m + 1) ≤ Nat.log 2 (2 * m + 1 + 1) :=
            Nat.log_mono_right (by omega)
          omega

/-- P-MERGE work is monotone in the input size. -/
theorem pMergeWork_monotone : Monotone pMergeWork :=
  monotone_nat_of_le_succ pMergeWork_le_succ

/-- Every positive P-MERGE work cost lies between its adjacent power-of-two costs. -/
theorem pMergeWork_power_sandwich (n : ℕ) (hn : 0 < n) :
    pMergeWork (2 ^ Nat.log 2 n) ≤ pMergeWork n ∧
      pMergeWork n ≤ pMergeWork (2 ^ (Nat.log 2 n + 1)) :=
  natCost_power_sandwich pMergeWork_monotone n hn

/-- Exact work on powers of two: `T₁(2ᵏ) + (k + 3) = 4·2ᵏ` (work `Θ(n)`). -/
theorem pMergeWork_pow_two (k : ℕ) :
    pMergeWork (2 ^ k) + (k + 3) = 4 * 2 ^ k := by
  induction k with
  | zero =>
      rw [pMergeWork]
      norm_num
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

/-- The P-MERGE span recurrence does not decrease at a successor step. -/
private theorem pMergeSpan_le_succ : ∀ n, pMergeSpan n ≤ pMergeSpan (n + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n ≤ 1
      · interval_cases n
        · rw [show pMergeSpan 0 = 0 by rw [pMergeSpan]; norm_num]
          exact Nat.zero_le _
        · have hone : pMergeSpan 1 = 1 := by rw [pMergeSpan]; norm_num
          rw [hone, pMergeSpan_unfold (n := 2) (by norm_num)]
          norm_num [hone]
      · obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m ∨ n = 2 * m + 1 :=
          ⟨n / 2, by omega⟩
        · have hceil0 : 2 * m - 2 * m / 2 = m := by omega
          have hceil1 : 2 * m + 1 - (2 * m + 1) / 2 = m + 1 := by omega
          rw [pMergeSpan_unfold (n := 2 * m) (by omega),
            pMergeSpan_unfold (n := 2 * m + 1) (by omega),
            hceil0, hceil1]
          have ihm := ih m (by omega)
          have hlog : Nat.log 2 (2 * m) ≤ Nat.log 2 (2 * m + 1) :=
            Nat.log_mono_right (by omega)
          omega
        · have hceil0 : 2 * m + 1 - (2 * m + 1) / 2 = m + 1 := by omega
          have hceil1 : 2 * m + 1 + 1 - (2 * m + 1 + 1) / 2 = m + 1 := by omega
          rw [pMergeSpan_unfold (n := 2 * m + 1) (by omega),
            pMergeSpan_unfold (n := 2 * m + 1 + 1) (by omega),
            hceil0, hceil1]
          have hlog : Nat.log 2 (2 * m + 1) ≤ Nat.log 2 (2 * m + 1 + 1) :=
            Nat.log_mono_right (by omega)
          omega

/-- P-MERGE span is monotone in the input size. -/
theorem pMergeSpan_monotone : Monotone pMergeSpan :=
  monotone_nat_of_le_succ pMergeSpan_le_succ

/-- Every positive P-MERGE span cost lies between its adjacent power-of-two costs. -/
theorem pMergeSpan_power_sandwich (n : ℕ) (hn : 0 < n) :
    pMergeSpan (2 ^ Nat.log 2 n) ≤ pMergeSpan n ∧
      pMergeSpan n ≤ pMergeSpan (2 ^ (Nat.log 2 n + 1)) :=
  natCost_power_sandwich pMergeSpan_monotone n hn

/-- Exact span on powers of two: `2·T∞(2ᵏ) = (k+1)(k+2)` (span `Θ(log² n)`). -/
theorem pMergeSpan_pow_two (k : ℕ) :
    2 * pMergeSpan (2 ^ k) = (k + 1) * (k + 2) := by
  induction k with
  | zero =>
      rw [pMergeSpan]
      norm_num
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

/-- The P-MERGE-SORT work recurrence does not decrease at a successor step. -/
private theorem pMergeSortWork_le_succ : ∀ n, pMergeSortWork n ≤ pMergeSortWork (n + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n ≤ 1
      · interval_cases n
        · rw [show pMergeSortWork 0 = 0 by rw [pMergeSortWork]; norm_num]
          exact Nat.zero_le _
        · have hone : pMergeSortWork 1 = 1 := by rw [pMergeSortWork]; norm_num
          rw [hone, pMergeSortWork_unfold (n := 2) (by norm_num)]
          norm_num [hone]
      · obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m ∨ n = 2 * m + 1 :=
          ⟨n / 2, by omega⟩
        · have hdiv0 : 2 * m / 2 = m := by omega
          have hdiv1 : (2 * m + 1) / 2 = m := by omega
          have hceil0 : 2 * m - 2 * m / 2 = m := by omega
          have hceil1 : 2 * m + 1 - (2 * m + 1) / 2 = m + 1 := by omega
          rw [pMergeSortWork_unfold (n := 2 * m) (by omega),
            pMergeSortWork_unfold (n := 2 * m + 1) (by omega),
            hceil0, hceil1, hdiv0, hdiv1]
          have ihm := ih m (by omega)
          omega
        · have hdiv0 : (2 * m + 1) / 2 = m := by omega
          have hdiv1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
          have hceil0 : 2 * m + 1 - (2 * m + 1) / 2 = m + 1 := by omega
          have hceil1 : 2 * m + 1 + 1 - (2 * m + 1 + 1) / 2 = m + 1 := by omega
          rw [pMergeSortWork_unfold (n := 2 * m + 1) (by omega),
            pMergeSortWork_unfold (n := 2 * m + 1 + 1) (by omega),
            hceil0, hceil1, hdiv0, hdiv1]
          have ihm := ih m (by omega)
          omega

/-- P-MERGE-SORT work is monotone in the input size. -/
theorem pMergeSortWork_monotone : Monotone pMergeSortWork :=
  monotone_nat_of_le_succ pMergeSortWork_le_succ

/-- Every positive P-MERGE-SORT work cost lies between its adjacent power-of-two costs. -/
theorem pMergeSortWork_power_sandwich (n : ℕ) (hn : 0 < n) :
    pMergeSortWork (2 ^ Nat.log 2 n) ≤ pMergeSortWork n ∧
      pMergeSortWork n ≤ pMergeSortWork (2 ^ (Nat.log 2 n + 1)) :=
  natCost_power_sandwich pMergeSortWork_monotone n hn

/-- Exact work on powers of two: `T₁(2ᵏ) = 2ᵏ·(k+1)` (work `Θ(n log n)`). -/
theorem pMergeSortWork_pow_two (k : ℕ) :
    pMergeSortWork (2 ^ k) = 2 ^ k * (k + 1) := by
  induction k with
  | zero =>
      rw [pMergeSortWork]
      norm_num
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

/-- The P-MERGE-SORT span recurrence does not decrease at a successor step. -/
private theorem pMergeSortSpan_le_succ : ∀ n, pMergeSortSpan n ≤ pMergeSortSpan (n + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n ≤ 1
      · interval_cases n
        · rw [show pMergeSortSpan 0 = 0 by rw [pMergeSortSpan]; norm_num]
          exact Nat.zero_le _
        · have hone : pMergeSortSpan 1 = 1 := by rw [pMergeSortSpan]; norm_num
          rw [hone, pMergeSortSpan_unfold (n := 2) (by norm_num)]
          norm_num [hone]
      · obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m ∨ n = 2 * m + 1 :=
          ⟨n / 2, by omega⟩
        · have hceil0 : 2 * m - 2 * m / 2 = m := by omega
          have hceil1 : 2 * m + 1 - (2 * m + 1) / 2 = m + 1 := by omega
          rw [pMergeSortSpan_unfold (n := 2 * m) (by omega),
            pMergeSortSpan_unfold (n := 2 * m + 1) (by omega), hceil0, hceil1]
          have ihm := ih m (by omega)
          have hp : pMergeSpan (2 * m) ≤ pMergeSpan (2 * m + 1) :=
            pMergeSpan_monotone (by omega)
          omega
        · have hceil0 : 2 * m + 1 - (2 * m + 1) / 2 = m + 1 := by omega
          have hceil1 : 2 * m + 1 + 1 - (2 * m + 1 + 1) / 2 = m + 1 := by omega
          rw [pMergeSortSpan_unfold (n := 2 * m + 1) (by omega),
            pMergeSortSpan_unfold (n := 2 * m + 1 + 1) (by omega), hceil0, hceil1]
          have hp : pMergeSpan (2 * m + 1) ≤ pMergeSpan (2 * m + 1 + 1) :=
            pMergeSpan_monotone (by omega)
          omega

/-- P-MERGE-SORT span is monotone in the input size. -/
theorem pMergeSortSpan_monotone : Monotone pMergeSortSpan :=
  monotone_nat_of_le_succ pMergeSortSpan_le_succ

/-- Every positive P-MERGE-SORT span cost lies between its adjacent power-of-two costs. -/
theorem pMergeSortSpan_power_sandwich (n : ℕ) (hn : 0 < n) :
    pMergeSortSpan (2 ^ Nat.log 2 n) ≤ pMergeSortSpan n ∧
      pMergeSortSpan n ≤ pMergeSortSpan (2 ^ (Nat.log 2 n + 1)) :=
  natCost_power_sandwich pMergeSortSpan_monotone n hn

/-- Exact span on powers of two:
`6·T∞(2ᵏ) = 6 + k·(k² + 6k + 11)` (span `Θ(log³ n)`). -/
theorem pMergeSortSpan_pow_two (k : ℕ) :
    6 * pMergeSortSpan (2 ^ k) = 6 + k * (k * k + 6 * k + 11) := by
  induction k with
  | zero =>
      rw [pMergeSortSpan]
      norm_num
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

/-- The parallel Strassen work recurrence does not decrease at a successor step. -/
private theorem strassenWork_le_succ : ∀ n, strassenWork n ≤ strassenWork (n + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n ≤ 1
      · interval_cases n
        · rw [show strassenWork 0 = 0 by rw [strassenWork]; norm_num]
          exact Nat.zero_le _
        · have hone : strassenWork 1 = 1 := by rw [strassenWork]; norm_num
          rw [hone, strassenWork_unfold (n := 2) (by norm_num)]
          norm_num [hone]
      · obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m ∨ n = 2 * m + 1 :=
          ⟨n / 2, by omega⟩
        · have hdiv0 : 2 * m / 2 = m := by omega
          have hdiv1 : (2 * m + 1) / 2 = m := by omega
          rw [strassenWork_unfold (n := 2 * m) (by omega),
            strassenWork_unfold (n := 2 * m + 1) (by omega), hdiv0, hdiv1]
          have hsquare : (2 * m) * (2 * m) ≤ (2 * m + 1) * (2 * m + 1) := by
            nlinarith
          omega
        · have hdiv0 : (2 * m + 1) / 2 = m := by omega
          have hdiv1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
          rw [strassenWork_unfold (n := 2 * m + 1) (by omega),
            strassenWork_unfold (n := 2 * m + 1 + 1) (by omega), hdiv0, hdiv1]
          have ihm := ih m (by omega)
          have hsquare : (2 * m + 1) * (2 * m + 1) ≤
              (2 * m + 1 + 1) * (2 * m + 1 + 1) := by
            nlinarith
          omega

/-- Parallel Strassen work is monotone in the input size. -/
theorem strassenWork_monotone : Monotone strassenWork :=
  monotone_nat_of_le_succ strassenWork_le_succ

/-- Every positive parallel-Strassen work cost lies between its adjacent
power-of-two costs. -/
theorem strassenWork_power_sandwich (n : ℕ) (hn : 0 < n) :
    strassenWork (2 ^ Nat.log 2 n) ≤ strassenWork n ∧
      strassenWork n ≤ strassenWork (2 ^ (Nat.log 2 n + 1)) :=
  natCost_power_sandwich strassenWork_monotone n hn

/-- Exact work on powers of two: `3·T₁(2ᵏ) + 4ᵏ⁺¹ = 7ᵏ⁺¹`
(work `Θ(n^(log₂ 7))`). -/
theorem strassenWork_pow_two (k : ℕ) :
    3 * strassenWork (2 ^ k) + 4 ^ (k + 1) = 7 ^ (k + 1) := by
  induction k with
  | zero =>
      rw [strassenWork]
      norm_num
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

/-- The parallel Strassen span recurrence does not decrease at a successor step. -/
private theorem strassenSpan_le_succ : ∀ n, strassenSpan n ≤ strassenSpan (n + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n ≤ 1
      · interval_cases n
        · rw [show strassenSpan 0 = 0 by rw [strassenSpan]; norm_num]
          exact Nat.zero_le _
        · have hone : strassenSpan 1 = 1 := by rw [strassenSpan]; norm_num
          rw [hone, strassenSpan_unfold (n := 2) (by norm_num)]
          norm_num [hone]
      · obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m ∨ n = 2 * m + 1 :=
          ⟨n / 2, by omega⟩
        · have hdiv0 : 2 * m / 2 = m := by omega
          have hdiv1 : (2 * m + 1) / 2 = m := by omega
          rw [strassenSpan_unfold (n := 2 * m) (by omega),
            strassenSpan_unfold (n := 2 * m + 1) (by omega), hdiv0, hdiv1]
        · have hdiv0 : (2 * m + 1) / 2 = m := by omega
          have hdiv1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
          rw [strassenSpan_unfold (n := 2 * m + 1) (by omega),
            strassenSpan_unfold (n := 2 * m + 1 + 1) (by omega), hdiv0, hdiv1]
          exact Nat.add_le_add_right (ih m (by omega)) 1

/-- Parallel Strassen span is monotone in the input size. -/
theorem strassenSpan_monotone : Monotone strassenSpan :=
  monotone_nat_of_le_succ strassenSpan_le_succ

/-- Every positive parallel-Strassen span cost lies between its adjacent
power-of-two costs. -/
theorem strassenSpan_power_sandwich (n : ℕ) (hn : 0 < n) :
    strassenSpan (2 ^ Nat.log 2 n) ≤ strassenSpan n ∧
      strassenSpan n ≤ strassenSpan (2 ^ (Nat.log 2 n + 1)) :=
  natCost_power_sandwich strassenSpan_monotone n hn

/-- Exact span on powers of two: `T∞(2ᵏ) = k + 1` (span `Θ(log n)`). -/
theorem strassenSpan_pow_two (k : ℕ) : strassenSpan (2 ^ k) = k + 1 := by
  induction k with
  | zero =>
      rw [strassenSpan]
      norm_num
  | succ k ih =>
      rw [strassenSpan_unfold (two_le_two_pow_succ k), pow_two_succ_eq, ih]

/-! ## All-input work and span bounds -/

private theorem add_three_le_three_mul_pow_two (k : ℕ) :
    k + 3 ≤ 3 * 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [pow_succ]
      have hpow : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
      nlinarith

private theorem pMergeWork_exactPower_bounds (k : ℕ) :
    2 ^ k ≤ pMergeWork (2 ^ k) ∧ pMergeWork (2 ^ k) ≤ 4 * 2 ^ k := by
  have hexact := pMergeWork_pow_two k
  have hlinear := add_three_le_three_mul_pow_two k
  omega

private theorem pMergeWork_exactPower_bigTheta :
    Chapter03.isBigTheta
      (fun k : ℕ => (pMergeWork (2 ^ k) : ℝ))
      (fun k : ℕ => (2 : ℝ) ^ k) := by
  constructor
  · refine (Chapter03.isBigO_iff _ _).mpr ⟨4, by norm_num, 0, ?_⟩
    intro k _
    rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by positivity)]
    have hreal :
        (pMergeWork (2 ^ k) : ℝ) ≤ ((4 * 2 ^ k : ℕ) : ℝ) := by
      exact_mod_cast (pMergeWork_exactPower_bounds k).2
    simpa [Nat.cast_mul, Nat.cast_pow] using hreal
  · refine (Chapter03.isBigOmega_iff _ _).mpr ⟨1, by norm_num, 0, ?_⟩
    intro k _
    rw [abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ k),
      abs_of_nonneg (Nat.cast_nonneg _)]
    have hreal : ((2 ^ k : ℕ) : ℝ) ≤ (pMergeWork (2 ^ k) : ℝ) := by
      exact_mod_cast (pMergeWork_exactPower_bounds k).1
    simpa [Nat.cast_pow] using hreal

private theorem pMergeSpan_exactPower_bigTheta :
    Chapter03.isBigTheta
      (fun k : ℕ => (pMergeSpan (2 ^ k) : ℝ))
      (fun k : ℕ => ((k : ℝ) + 1) ^ 2) := by
  constructor
  · refine (Chapter03.isBigO_iff _ _).mpr ⟨1, by norm_num, 0, ?_⟩
    intro k _
    rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by positivity)]
    have hexact :
        (2 : ℝ) * (pMergeSpan (2 ^ k) : ℝ) =
          ((k : ℝ) + 1) * ((k : ℝ) + 2) := by
      exact_mod_cast pMergeSpan_pow_two k
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hproduct : 0 ≤ (k : ℝ) * ((k : ℝ) + 1) :=
      mul_nonneg hk (by positivity)
    nlinarith
  · refine (Chapter03.isBigOmega_iff _ _).mpr
      ⟨(2 : ℝ)⁻¹, by positivity, 0, ?_⟩
    intro k _
    rw [abs_of_nonneg (by positivity : 0 ≤ ((k : ℝ) + 1) ^ 2),
      abs_of_nonneg (Nat.cast_nonneg _)]
    have hexact :
        (2 : ℝ) * (pMergeSpan (2 ^ k) : ℝ) =
          ((k : ℝ) + 1) * ((k : ℝ) + 2) := by
      exact_mod_cast pMergeSpan_pow_two k
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith

private theorem pMergeSortWork_exactPower_bigTheta :
    Chapter03.isBigTheta
      (fun k : ℕ => (pMergeSortWork (2 ^ k) : ℝ))
      (fun k : ℕ => ((k : ℝ) + 1) * (2 : ℝ) ^ k) := by
  have hfun :
      (fun k : ℕ => (pMergeSortWork (2 ^ k) : ℝ)) =
        (fun k : ℕ => ((k : ℝ) + 1) * (2 : ℝ) ^ k) := by
    funext k
    rw [pMergeSortWork_pow_two]
    push_cast
    ring
  rw [hfun]
  exact Chapter03.isBigTheta_refl _

private theorem pMergeSortSpan_exactPower_closed (k : ℕ) :
    6 * pMergeSortSpan (2 ^ k) = (k + 1) * (k + 2) * (k + 3) := by
  rw [pMergeSortSpan_pow_two]
  ring

private theorem pMergeSortSpan_exactPower_bigTheta :
    Chapter03.isBigTheta
      (fun k : ℕ => (pMergeSortSpan (2 ^ k) : ℝ))
      (fun k : ℕ => ((k : ℝ) + 1) ^ 3) := by
  constructor
  · refine (Chapter03.isBigO_iff _ _).mpr ⟨1, by norm_num, 0, ?_⟩
    intro k _
    rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by positivity)]
    have hexact :
        (6 : ℝ) * (pMergeSortSpan (2 ^ k) : ℝ) =
          ((k : ℝ) + 1) * ((k : ℝ) + 2) * ((k : ℝ) + 3) := by
      exact_mod_cast pMergeSortSpan_exactPower_closed k
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hk2 : 0 ≤ (k : ℝ) * (k : ℝ) := mul_nonneg hk hk
    have hk3 : 0 ≤ (k : ℝ) * ((k : ℝ) * (k : ℝ)) := mul_nonneg hk hk2
    nlinarith
  · refine (Chapter03.isBigOmega_iff _ _).mpr
      ⟨(6 : ℝ)⁻¹, by positivity, 0, ?_⟩
    intro k _
    rw [abs_of_nonneg (by positivity : 0 ≤ ((k : ℝ) + 1) ^ 3),
      abs_of_nonneg (Nat.cast_nonneg _)]
    have hexact :
        (6 : ℝ) * (pMergeSortSpan (2 ^ k) : ℝ) =
          ((k : ℝ) + 1) * ((k : ℝ) + 2) * ((k : ℝ) + 3) := by
      exact_mod_cast pMergeSortSpan_exactPower_closed k
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hk2 : 0 ≤ (k : ℝ) * (k : ℝ) := mul_nonneg hk hk
    nlinarith

private theorem strassenWork_exactPower_bounds (k : ℕ) :
    7 ^ k ≤ strassenWork (2 ^ k) ∧ strassenWork (2 ^ k) ≤ 3 * 7 ^ k := by
  have hexact := strassenWork_pow_two k
  rw [pow_succ (4 : ℕ) k, pow_succ (7 : ℕ) k] at hexact
  have hpow : 4 ^ k ≤ 7 ^ k := Nat.pow_le_pow_left (by norm_num) k
  constructor <;> omega

private theorem strassenWork_exactPower_bigTheta :
    Chapter03.isBigTheta
      (fun k : ℕ => (strassenWork (2 ^ k) : ℝ))
      (fun k : ℕ => (7 : ℝ) ^ k) := by
  constructor
  · refine (Chapter03.isBigO_iff _ _).mpr ⟨3, by norm_num, 0, ?_⟩
    intro k _
    rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by positivity)]
    have hreal :
        (strassenWork (2 ^ k) : ℝ) ≤ ((3 * 7 ^ k : ℕ) : ℝ) := by
      exact_mod_cast (strassenWork_exactPower_bounds k).2
    simpa [Nat.cast_mul, Nat.cast_pow] using hreal
  · refine (Chapter03.isBigOmega_iff _ _).mpr ⟨1, by norm_num, 0, ?_⟩
    intro k _
    rw [abs_of_nonneg (by positivity : 0 ≤ (7 : ℝ) ^ k),
      abs_of_nonneg (Nat.cast_nonneg _)]
    have hreal : ((7 ^ k : ℕ) : ℝ) ≤ (strassenWork (2 ^ k) : ℝ) := by
      exact_mod_cast (strassenWork_exactPower_bounds k).1
    simpa [Nat.cast_pow] using hreal

private theorem strassenSpan_exactPower_bigTheta :
    Chapter03.isBigTheta
      (fun k : ℕ => (strassenSpan (2 ^ k) : ℝ))
      (fun k : ℕ => (k : ℝ) + 1) := by
  have hfun :
      (fun k : ℕ => (strassenSpan (2 ^ k) : ℝ)) =
        (fun k : ℕ => (k : ℝ) + 1) := by
    funext k
    rw [strassenSpan_pow_two]
    push_cast
    norm_num
  rw [hfun]
  exact Chapter03.isBigTheta_refl _

/-- P-MERGE has linear work on every positive input size. -/
theorem pMergeWork_allInput_bigTheta :
    Chapter03.isBigTheta (fun n : ℕ => (pMergeWork n : ℝ))
      (Chapter04.polynomialScale 1) := by
  have hcritical :
      Chapter03.isBigTheta (fun n : ℕ => (pMergeWork n : ℝ))
        (Chapter04.criticalPowerScale 2 2) :=
    Chapter04.allInput_bigTheta_of_criticalPowerScale 2 2
      (fun n : ℕ => (pMergeWork n : ℝ)) (by norm_num) (by norm_num)
      (natCost_monotoneAbs pMergeWork_monotone)
      pMergeWork_exactPower_bigTheta
  exact Chapter03.isBigTheta_trans hcritical (by
    simpa using Chapter04.criticalPowerScale_isBigTheta_polynomialScale 2 1
      (by norm_num))

/-- P-MERGE has quadratic-logarithmic span on every positive input size. -/
theorem pMergeSpan_allInput_bigTheta :
    Chapter03.isBigTheta (fun n : ℕ => (pMergeSpan n : ℝ))
      (Chapter04.criticalPowerLogPolylogScale 1 2 1) := by
  have hpower :
      Chapter03.isBigTheta
        (fun i : ℕ => (pMergeSpan (2 ^ i) : ℝ))
        (fun i : ℕ => Chapter04.criticalPowerLogPolylogScale 1 2 1 (2 ^ i)) := by
    have hscale :
        (fun i : ℕ => Chapter04.criticalPowerLogPolylogScale 1 2 1 (2 ^ i)) =
          (fun i : ℕ => ((i : ℝ) + 1) ^ 2) := by
      funext i
      simp [Chapter04.criticalPowerLogPolylogScale_exactPower]
    rw [hscale]
    exact pMergeSpan_exactPower_bigTheta
  exact Chapter04.allInput_bigTheta_of_powerStep 2
    (fun n : ℕ => (pMergeSpan n : ℝ))
    (Chapter04.criticalPowerLogPolylogScale 1 2 1) (by norm_num)
    (natCost_monotoneAbs pMergeSpan_monotone)
    (Chapter04.criticalPowerLogPolylogScale_monotoneAbs 1 2 1 (by norm_num))
    (Chapter04.criticalPowerLogPolylogScale_powerStepBound 1 2 1
      (by norm_num) (by norm_num))
    hpower

/-- P-MERGE-SORT has `n log n` work on every positive input size. -/
theorem pMergeSortWork_allInput_bigTheta :
    Chapter03.isBigTheta (fun n : ℕ => (pMergeSortWork n : ℝ))
      (Chapter04.polynomialLogScale 2 1) := by
  have hcritical :
      Chapter03.isBigTheta (fun n : ℕ => (pMergeSortWork n : ℝ))
        (Chapter04.criticalPowerLogScale 2 2) :=
    Chapter04.allInput_bigTheta_of_criticalPowerLogScale 2 2
      (fun n : ℕ => (pMergeSortWork n : ℝ)) (by norm_num) (by norm_num)
      (natCost_monotoneAbs pMergeSortWork_monotone)
      pMergeSortWork_exactPower_bigTheta
  exact Chapter03.isBigTheta_trans hcritical (by
    simpa using Chapter04.criticalPowerLogScale_isBigTheta_polynomialLogScale 2 1
      (by norm_num))

/-- P-MERGE-SORT has cubic-logarithmic span on every positive input size. -/
theorem pMergeSortSpan_allInput_bigTheta :
    Chapter03.isBigTheta (fun n : ℕ => (pMergeSortSpan n : ℝ))
      (Chapter04.criticalPowerLogPolylogScale 1 2 2) := by
  have hpower :
      Chapter03.isBigTheta
        (fun i : ℕ => (pMergeSortSpan (2 ^ i) : ℝ))
        (fun i : ℕ => Chapter04.criticalPowerLogPolylogScale 1 2 2 (2 ^ i)) := by
    have hscale :
        (fun i : ℕ => Chapter04.criticalPowerLogPolylogScale 1 2 2 (2 ^ i)) =
          (fun i : ℕ => ((i : ℝ) + 1) ^ 3) := by
      funext i
      simp [Chapter04.criticalPowerLogPolylogScale_exactPower]
    rw [hscale]
    exact pMergeSortSpan_exactPower_bigTheta
  exact Chapter04.allInput_bigTheta_of_powerStep 2
    (fun n : ℕ => (pMergeSortSpan n : ℝ))
    (Chapter04.criticalPowerLogPolylogScale 1 2 2) (by norm_num)
    (natCost_monotoneAbs pMergeSortSpan_monotone)
    (Chapter04.criticalPowerLogPolylogScale_monotoneAbs 1 2 2 (by norm_num))
    (Chapter04.criticalPowerLogPolylogScale_powerStepBound 1 2 2
      (by norm_num) (by norm_num))
    hpower

/-- Parallel Strassen has work `n^(log₂ 7)` on every positive input size. -/
theorem strassenWork_allInput_bigTheta :
    Chapter03.isBigTheta (fun n : ℕ => (strassenWork n : ℝ))
      (Chapter04.realLogScale 7 2) := by
  have hcritical :
      Chapter03.isBigTheta (fun n : ℕ => (strassenWork n : ℝ))
        (Chapter04.criticalPowerScale 7 2) :=
    Chapter04.allInput_bigTheta_of_criticalPowerScale 7 2
      (fun n : ℕ => (strassenWork n : ℝ)) (by norm_num) (by norm_num)
      (natCost_monotoneAbs strassenWork_monotone)
      strassenWork_exactPower_bigTheta
  exact Chapter03.isBigTheta_trans hcritical
    (Chapter04.criticalPowerScale_isBigTheta_realLogScale 7 2
      (by norm_num) (by norm_num))

/-- Parallel Strassen has logarithmic span on every positive input size. -/
theorem strassenSpan_allInput_bigTheta :
    Chapter03.isBigTheta (fun n : ℕ => (strassenSpan n : ℝ))
      (Chapter04.polynomialLogScale 2 0) := by
  have hcritical :
      Chapter03.isBigTheta (fun n : ℕ => (strassenSpan n : ℝ))
        (Chapter04.criticalPowerLogScale 1 2) :=
    Chapter04.allInput_bigTheta_of_criticalPowerLogScale 1 2
      (fun n : ℕ => (strassenSpan n : ℝ)) (by norm_num) (by norm_num)
      (natCost_monotoneAbs strassenSpan_monotone) (by
        simpa only [Nat.cast_one, one_pow, mul_one] using
          strassenSpan_exactPower_bigTheta)
  exact Chapter03.isBigTheta_trans hcritical (by
    simpa using Chapter04.criticalPowerLogScale_isBigTheta_polynomialLogScale 2 0
      (by norm_num))

end Chapter27
end CLRS

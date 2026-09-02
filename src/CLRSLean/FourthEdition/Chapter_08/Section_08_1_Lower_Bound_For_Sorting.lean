import Mathlib

open scoped BigOperators

/-!
# CLRS Section 8.1 - Lower bounds for sorting

This section formalizes the decision-tree lower bound of CLRS §8.1: any
comparison-based sorting algorithm on {lit}`n` distinct elements performs at
least {lit}`log₂(n!)` comparisons in the worst case, which is {lit}`Ω(n log n)`.

A comparison sort on {lit}`n` elements is modelled as a binary decision tree
{lit}`SortTree n`.  Internal nodes compare the elements stored in two
positions; leaves are labelled with an output permutation of {lit}`Fin n`.
Running the tree on an input arrangement
{lit}`π : Equiv.Perm (Fin n)` follows the outcome of each comparison and
reaches a leaf.  A tree {lit}`CorrectSort`-sorts every input if the leaf
reached on {lit}`π` is labelled with the sorted arrangement {lit}`π⁻¹`.

The lower bound then follows from three independent facts:

* **Correctness needs {lit}`n!` leaves**: distinct input arrangements
  {lit}`π` have distinct sorted arrangements {lit}`π⁻¹`, so a correct tree
  maps the {lit}`n!` permutations injectively to distinct leaves
  ({lit}`run_injective_of_correctSort` + {lit}`card_le_leafCount_of_injective`
  give {lit}`factorial_le_leafCount_of_correctSort`).
* **A binary tree of height {lit}`h` has at most {lit}`2^h` leaves**
  ({lit}`leafCount_le_two_pow_height`), so {lit}`n! ≤ 2^h` and hence
  {lit}`h ≥ log₂(n!)` ({lit}`height_le_logb_factorial`).
* **{lit}`log₂(n!) ≥ (n/2)·log₂ n`** via the pairing bound
  {lit}`(n!)² ≥ nⁿ`: the factors {lit}`k` and {lit}`n+1-k` multiply to at
  least {lit}`n` ({lit}`factorial_sq_ge_pow_self` +
  {lit}`logb_factorial_ge_half_mul_logb`).

Combining these yields the headline theorem
{lit}`comparisonSort_worstCase_lowerBound`: every correct comparison-based
sorter on {lit}`n ≥ 2` distinct elements needs at least
{lit}`(n/2)·(log₂ n - 1)` comparisons in the worst case.

## Main results

- Theorem {lit}`leafCount_le_two_pow_height`: a binary tree of height
  {lit}`h` has at most {lit}`2^h` leaves
- Theorem {lit}`run_injective_of_correctSort`: a correct sorter maps distinct
  inputs to distinct leaves
- Theorem {lit}`factorial_le_leafCount_of_correctSort`: a correct sorter has
  at least {lit}`n!` leaves
- Theorem {lit}`height_le_logb_factorial`: {lit}`log₂(n!) ≤ h`
- Theorem {lit}`factorial_sq_ge_pow_self`: {lit}`(n!)² ≥ nⁿ`
- Theorem {lit}`logb_factorial_ge_half_mul_logb`:
  {lit}`log₂(n!) ≥ (n/2)·log₂ n`
- Theorem {lit}`comparisonSort_worstCase_lowerBound` (CLRS §8.1): the
  worst-case number of comparisons of any correct comparison sort is at least
  {lit}`(n/2)·(log₂ n - 1)`, hence {lit}`Ω(n log n)`

## Current gaps

None for the decision-tree model of comparison sorts over {lit}`Fin n`.
RAM-level bookkeeping of comparisons (charging the comparison itself through
an execution semantics) is out of scope, as is the non-comparison-based
lower-bound analysis for counting/radix/bucket sort.
-/

namespace CLRS
namespace Chapter08

/-! ## Comparison decision trees -/

/--
A binary decision tree for comparison sorting of `n` distinct elements.
An internal node compares the elements in positions `i` and `j` (0-indexed)
and branches on the outcome; a leaf is labelled with the claimed output
permutation.  The number of comparisons performed on a run is the number of
internal nodes on its root-to-leaf path.
-/
inductive SortTree (n : ℕ) : Type where
  | leaf : Equiv.Perm (Fin n) → SortTree n
  | node : (i j : Fin n) → SortTree n → SortTree n → SortTree n

/-- The number of leaves of a decision tree, counting each leaf node. -/
def SortTree.leafCount : SortTree n → ℕ
  | leaf _ => 1
  | node _ _ l r => l.leafCount + r.leafCount

/--
The height of a decision tree: the largest number of internal nodes on a
root-to-leaf path.  This is the worst-case number of comparisons.
-/
def SortTree.height : SortTree n → ℕ
  | leaf _ => 0
  | node _ _ l r => 1 + max l.height r.height

/--
`t` is a leaf node occurring in the tree `T`.
-/
def SortTree.isLeafNodeOf (T : SortTree n) (t : SortTree n) : Prop :=
  match T with
  | leaf p => t = SortTree.leaf p
  | node _ _ l r => SortTree.isLeafNodeOf l t ∨ SortTree.isLeafNodeOf r t

/-- A binary tree of height `h` has at most `2^h` leaves. -/
theorem leafCount_le_two_pow_height (T : SortTree n) : T.leafCount ≤ 2 ^ T.height := by
  induction T with
  | leaf p =>
      simp [SortTree.leafCount, SortTree.height]
  | node _ _ l r ih_l ih_r =>
      have hmax_l : l.height ≤ max l.height r.height := Nat.le_max_left l.height r.height
      have hmax_r : r.height ≤ max l.height r.height := Nat.le_max_right l.height r.height
      have hpow_l : 2 ^ l.height ≤ 2 ^ max l.height r.height :=
        pow_le_pow_right₀ (by norm_num : 1 ≤ 2) hmax_l
      have hpow_r : 2 ^ r.height ≤ 2 ^ max l.height r.height :=
        pow_le_pow_right₀ (by norm_num : 1 ≤ 2) hmax_r
      have hsum_le : l.leafCount + r.leafCount ≤ 2 ^ l.height + 2 ^ r.height :=
        Nat.add_le_add ih_l ih_r
      have hsum : 2 ^ l.height + 2 ^ r.height ≤ 2 * 2 ^ max l.height r.height := by
        rw [two_mul]
        exact Nat.add_le_add hpow_l hpow_r
      have hgoal : l.leafCount + r.leafCount ≤ 2 ^ (max l.height r.height + 1) := by
        calc
          l.leafCount + r.leafCount ≤ 2 ^ l.height + 2 ^ r.height := hsum_le
          _ ≤ 2 * 2 ^ max l.height r.height := hsum
          _ = 2 ^ (max l.height r.height + 1) := by
            rw [pow_succ]
            ring_nf
      simpa [SortTree.leafCount, SortTree.height, Nat.add_comm] using hgoal

/--
Run the decision tree on the input arrangement `π` (position `k` holds the
value `π k`).  At an internal node comparing positions `i` and `j`, take the
left branch when `π i ≤ π j`.  Returns the leaf reached.
-/
def SortTree.run (T : SortTree n) (π : Equiv.Perm (Fin n)) : SortTree n :=
  match T with
  | leaf p => SortTree.leaf p
  | node i j l r =>
      if π i ≤ π j then SortTree.run l π else SortTree.run r π

/--
A decision tree correctly sorts every input if, on input arrangement `π`, it
reaches the leaf labelled with the sorted arrangement `π⁻¹` (the unique
permutation `σ` with `π (σ k) = k`).
-/
def CorrectSort (T : SortTree n) : Prop :=
  ∀ π : Equiv.Perm (Fin n), SortTree.run T π = SortTree.leaf (π⁻¹)

/-- A correct sorter maps distinct input arrangements to distinct leaves. -/
theorem run_injective_of_correctSort {T : SortTree n} (hT : CorrectSort T) :
    Function.Injective (SortTree.run T) := by
  intro π₁ π₂ h
  have h1 : SortTree.run T π₁ = SortTree.leaf (π₁⁻¹) := hT π₁
  have h2 : SortTree.run T π₂ = SortTree.leaf (π₂⁻¹) := hT π₂
  have hleaves : SortTree.leaf (π₁⁻¹) = SortTree.leaf (π₂⁻¹) := by
    rw [← h1, ← h2]
    exact h
  have hinv : π₁⁻¹ = π₂⁻¹ := by
    injection hleaves
  calc
    π₁ = (π₁⁻¹)⁻¹ := by simp
    _ = (π₂⁻¹)⁻¹ := by rw [hinv]
    _ = π₂ := by simp

/-- The run of a tree always ends at a leaf of that tree. -/
theorem run_isLeafNodeOf (T : SortTree n) (π : Equiv.Perm (Fin n)) :
    SortTree.isLeafNodeOf T (SortTree.run T π) := by
  induction T with
  | leaf p =>
      simp [SortTree.isLeafNodeOf, SortTree.run]
  | node i j l r ih_l ih_r =>
      by_cases h : π i ≤ π j
      · simp [SortTree.run, SortTree.isLeafNodeOf, h]
        exact Or.inl ih_l
      · simp [SortTree.run, SortTree.isLeafNodeOf, h]
        exact Or.inr ih_r

/-- A finite set of leaves of `T` has cardinality at most the leaf count of `T`. -/
theorem card_le_leafCount_of_leaves
    {T : SortTree n} (S : Finset (SortTree n))
    (hS : ∀ t ∈ S, SortTree.isLeafNodeOf T t) :
    S.card ≤ T.leafCount := by
  classical
  induction T generalizing S with
  | leaf p =>
      have hsub : S ⊆ {SortTree.leaf p} := by
        intro t ht
        simp
        exact hS t ht
      exact (Finset.card_le_card hsub).trans (by simp [SortTree.leafCount])
  | node _ _ l r ih_l ih_r =>
      let Sl : Finset (SortTree n) := S.filter (fun t => SortTree.isLeafNodeOf l t)
      let Sr : Finset (SortTree n) := S.filter (fun t => SortTree.isLeafNodeOf r t)
      have hcover : S ⊆ Sl ∪ Sr := by
        intro t ht
        have hleaf := hS t ht
        rw [SortTree.isLeafNodeOf] at hleaf
        rcases hleaf with hl | hr
        · simp [Sl, ht, hl]
        · simp [Sr, ht, hr]
      have hcard_cover : S.card ≤ Sl.card + Sr.card := by
        exact le_trans (Finset.card_le_card hcover) (Finset.card_union_le Sl Sr)
      have hcard_l : Sl.card ≤ l.leafCount := by
        exact ih_l Sl (fun t ht => by
          simp [Sl] at ht
          exact ht.2)
      have hcard_r : Sr.card ≤ r.leafCount := by
        exact ih_r Sr (fun t ht => by
          simp [Sr] at ht
          exact ht.2)
      have hfinal : S.card ≤ l.leafCount + r.leafCount := by
        omega
      simpa [SortTree.leafCount] using hfinal

/--
If an injective map sends a finite type into the leaves of `T`, then its
cardinality is at most the leaf count of `T`.
-/
theorem card_le_leafCount_of_injective
    {n : ℕ} {T : SortTree n} {β : Type} [Fintype β]
    (f : β → SortTree n)
    (hf : Function.Injective f)
    (hmem : ∀ x, SortTree.isLeafNodeOf T (f x)) :
    Fintype.card β ≤ T.leafCount := by
  classical
  let S : Finset (SortTree n) := Finset.univ.image f
  have hcard : S.card = Fintype.card β := by
    change (Finset.univ.image f).card = Fintype.card β
    rw [Finset.card_image_of_injective (Finset.univ : Finset β) hf]
    simp
  have hS : ∀ t ∈ S, SortTree.isLeafNodeOf T t := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨x, _, rfl⟩
    exact hmem x
  calc
    Fintype.card β = S.card := hcard.symm
    _ ≤ T.leafCount := card_le_leafCount_of_leaves S hS

/-- A correct comparison sorter on `n` distinct elements has at least `n!` leaves. -/
theorem factorial_le_leafCount_of_correctSort {T : SortTree n} (hT : CorrectSort T) :
    n.factorial ≤ T.leafCount := by
  have hcard : Fintype.card (Equiv.Perm (Fin n)) = n.factorial := by
    simp [Fintype.card_perm]
  rw [← hcard]
  exact card_le_leafCount_of_injective (SortTree.run T) (run_injective_of_correctSort hT)
    (fun π => run_isLeafNodeOf T π)

/--
A correct sorter for `n` distinct elements performs at least `log₂(n!)`
comparisons in the worst case: its decision tree needs `n!` leaves, and a tree
of height `h` has at most `2^h` leaves.
-/
theorem height_le_logb_factorial {T : SortTree n} (hT : CorrectSort T) :
    Real.logb 2 (n.factorial : ℝ) ≤ (T.height : ℝ) := by
  have hfac : n.factorial ≤ T.leafCount := factorial_le_leafCount_of_correctSort hT
  have hlc : T.leafCount ≤ 2 ^ T.height := leafCount_le_two_pow_height T
  have hmain : (n.factorial : ℝ) ≤ ((2 : ℝ) ^ T.height) := by
    exact_mod_cast (le_trans hfac hlc)
  have hpos : (0 : ℝ) < (n.factorial : ℝ) := by positivity
  have hmono := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hpos hmain
  have hrhs : Real.logb 2 ((2 : ℝ) ^ T.height) = (T.height : ℝ) := by
    simp [Real.logb_pow, Real.logb_self_eq_one]
  simpa [hrhs] using hmono

/-! ## Factorial growth -/

/--
The pairing bound `(n!)² ≥ nⁿ`: the factors `k` and `n + 1 - k` of `n!` are
both at least `n` in aggregate, since `k · (n + 1 - k) ≥ n` for `1 ≤ k ≤ n`.
-/
theorem factorial_sq_ge_pow_self (n : ℕ) : n ^ n ≤ (n.factorial) ^ 2 := by
  have h1 : (∏ k ∈ Finset.Icc 1 n, k) = n.factorial := by
    induction n with
    | zero =>
        simp
    | succ n ih =>
        have hrec : (∏ k ∈ Finset.Icc 1 (n + 1), k) = (∏ k ∈ Finset.Icc 1 n, k) * (n + 1) := by
          exact Finset.prod_Icc_succ_top (by omega) (fun k => k)
        rw [hrec, ih]
        simp [Nat.factorial_succ, mul_comm]
  have h2 : (∏ k ∈ Finset.Icc 1 n, (n + 1 - k)) = n.factorial := by
    rw [← h1]
    exact Finset.prod_bij' (s := Finset.Icc 1 n) (t := Finset.Icc 1 n)
      (fun k _ => n + 1 - k) (fun k _ => n + 1 - k)
      (by intro k hk; rw [Finset.mem_Icc] at hk ⊢; omega)
      (by intro k hk; rw [Finset.mem_Icc] at hk ⊢; omega)
      (by intro k hk; rw [Finset.mem_Icc] at hk; omega)
      (by intro k hk; rw [Finset.mem_Icc] at hk; omega)
      (by intro k hk; rfl)
  have hfactor : ∀ k ∈ Finset.Icc 1 n, n ≤ k * (n + 1 - k) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkn : k ≤ n := (Finset.mem_Icc.mp hk).2
    have hsub1 : n + 1 - k = (n - k) + 1 := by omega
    have hsub2 : n = (n - k) + k := by omega
    have hk2 : k = (k - 1) + 1 := by omega
    have hmain : k * (n + 1 - k) = n + (k - 1) * (n - k) := by
      nlinarith
    rw [hmain]
    exact Nat.le_add_right n ((k - 1) * (n - k))
  have hcard_Icc : (Finset.Icc 1 n).card = n := by
    rw [Nat.card_Icc]
    omega
  calc
    n ^ n = (∏ k ∈ Finset.Icc 1 n, n) := by
      rw [Finset.prod_const, hcard_Icc]
    _ ≤ ∏ k ∈ Finset.Icc 1 n, k * (n + 1 - k) := by
      exact Finset.prod_le_prod' (fun k hk => hfactor k hk)
    _ = (n.factorial) ^ 2 := by
      rw [Finset.prod_mul_distrib, h1, h2, pow_two]

/--
`log₂(n!) ≥ (n/2) · log₂ n`, from the pairing bound `(n!)² ≥ nⁿ`.
-/
theorem logb_factorial_ge_half_mul_logb (n : ℕ) (hn : 0 < n) :
    ((n : ℝ) / 2) * Real.logb 2 (n : ℝ) ≤ Real.logb 2 (n.factorial : ℝ) := by
  have hpow : (n : ℝ) ^ n ≤ ((n.factorial : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast (factorial_sq_ge_pow_self n)
  have hpos : (0 : ℝ) < (n : ℝ) ^ n := by positivity
  have hmono := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hpos hpow
  have hl : Real.logb 2 (((n.factorial : ℕ) : ℝ) ^ 2) = 2 * Real.logb 2 (n.factorial : ℝ) := by
    rw [Real.logb_pow]
    norm_num
  have hr : Real.logb 2 ((n : ℝ) ^ n) = (n : ℝ) * Real.logb 2 (n : ℝ) := by
    rw [Real.logb_pow]
  have h2 : (n : ℝ) * Real.logb 2 (n : ℝ) ≤ 2 * Real.logb 2 (n.factorial : ℝ) := by
    rw [← hr, ← hl]
    exact hmono
  rw [div_mul_eq_mul_div]
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  simpa [mul_comm] using h2

/-! ## The lower bound -/

/--
**Worst-case comparison lower bound** (CLRS §8.1): any correct comparison-based
sorting algorithm on `n ≥ 2` distinct elements needs at least
`(n/2)·(log₂ n - 1)` comparisons in the worst case, which is `Ω(n log n)`.
-/
theorem comparisonSort_worstCase_lowerBound (n : ℕ) (hn : 2 ≤ n)
    {T : SortTree n} (hT : CorrectSort T) :
    ((n : ℝ) / 2) * (Real.logb 2 (n : ℝ) - 1) ≤ (T.height : ℝ) := by
  have hn0 : 0 < n := by omega
  have h2a : ((n : ℝ) / 2) * (Real.logb 2 (n : ℝ) - 1) ≤ ((n : ℝ) / 2) * Real.logb 2 (n : ℝ) := by
    exact mul_le_mul_of_nonneg_left
      (by linarith : Real.logb 2 (n : ℝ) - 1 ≤ Real.logb 2 (n : ℝ))
      (by positivity : 0 ≤ (n : ℝ) / 2)
  have h2b : ((n : ℝ) / 2) * Real.logb 2 (n : ℝ) ≤ Real.logb 2 (n.factorial : ℝ) :=
    logb_factorial_ge_half_mul_logb n hn0
  have h2c : Real.logb 2 (n.factorial : ℝ) ≤ (T.height : ℝ) :=
    height_le_logb_factorial hT
  exact le_trans (le_trans h2a h2b) h2c

end Chapter08
end CLRS

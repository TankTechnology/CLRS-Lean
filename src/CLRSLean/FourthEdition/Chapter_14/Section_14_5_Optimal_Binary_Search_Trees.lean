import CLRSLean.Chapter_15.Section_15_5_Optimal_Binary_Search_Trees
import CLRSLean.FourthEdition.Chapter_14.Section_14_2_Matrix_Chain_Multiplication

/-!
# Section 14.5 — Optimal binary search trees

The legacy {name}`CLRS.Chapter15.OBST.bottomUpOBST` evaluates a recursive
optimal-cost specification and repeats intervals. The {lit}`obstRoot` and
{lit}`obstReconstruct` interfaces here are likewise specification-based
selectors/reconstruction; the dimension formulas alone do not bound their runtime.

The {lit}`Execution` companion stores interval costs, weights, and selected
roots in arrays, using strictly shorter previously stored intervals. Each
interval computes its weight by one cached weight update before scanning roots.
Reconstruction reads those stored roots and never reruns the old recursive
oracle. The execution refines the recurrence and gives optimal plans, with
cell/candidate counts attached to the same fill.

Weights {lit}`p q : Nat → Nat` are nonnegative integer frequencies, including
zero. They are not arbitrary normalized real probabilities, and no general
scaling-to-probabilities theorem is provided. Natural arithmetic and array
access are primitive events; bit arithmetic, persistent copying, and allocation
are outside the cost model.

Notation conventions used in this section:

- `p` : successful-search integer weights
- `q` : unsuccessful-search (dummy key) integer weights
- `i`, `j` : the interval of keys {lit}`i+1, ..., j`
-/

namespace CLRS
namespace Chapter15
namespace OBST

open Finset

/-! ## The computable root table -/

private lemma exists_inf'_eq (s : Finset ℕ) (h : s.Nonempty) (f : ℕ → ℕ) :
    ∃ a ∈ s, f a = s.inf' h f := by
  induction' s using Finset.induction with a s has ih
  · exact absurd h (by simp)
  · by_cases hs : s.Nonempty
    · rcases ih hs with ⟨b, hb, hb_eq⟩
      rw [Finset.inf'_insert hs f]
      by_cases hle : f a ≤ s.inf' hs f
      · rw [min_eq_left hle]
        exact ⟨a, Finset.mem_insert_self a s, rfl⟩
      · rw [min_eq_right (by omega : s.inf' hs f ≤ f a)]
        rw [← hb_eq]
        exact ⟨b, Finset.mem_insert_of_mem hb, rfl⟩
    · have hsingleton : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst hsingleton
      simp

/--
A recurrence-based root selector (not a cached table): for interval {lit}`i < j`, it selects
the smallest admissible root {lit}`r ∈ [i+1, j]` that attains the recurrence
minimum; the diagonal is the junk value {lit}`i`.
-/
def obstRoot (p q : Nat → Nat) (i j : Nat) : Nat :=
  if h : i < j then
    (Finset.Icc (i + 1) j).filter
      (fun r =>
        bottomUpOBST p q i (r - 1) + bottomUpOBST p q r j + weight p q i j =
          bottomUpOBST p q i j) |>.min'
      (by
        have h_nonempty : (Finset.Icc (i + 1) j).Nonempty := by
          use i + 1; simp [Finset.mem_Icc]; exact h
        let f (r : ℕ) := bottomUpOBST p q i (r - 1) + bottomUpOBST p q r j + weight p q i j
        have h_rec : bottomUpOBST p q i j = (Finset.Icc (i + 1) j).inf' h_nonempty f :=
          (bottomUpOBST_obstRecurrence p q).2 h
        have h_exists := exists_inf'_eq (Finset.Icc (i + 1) j) h_nonempty f
        rw [← h_rec] at h_exists
        rcases h_exists with ⟨r, hr, hr_eq⟩
        exact ⟨r, Finset.mem_filter.mpr ⟨hr, hr_eq⟩⟩)
  else
    i

/--
The computable root table is tight for {name}`CLRS.Chapter15.OBST.bottomUpOBST`: each
non-singleton interval chooses an admissible root that attains the recurrence
equality.
-/
theorem obstRoot_optimal (p q : Nat → Nat) :
    OBSTRootOptimal p q (bottomUpOBST p q) (obstRoot p q) := by
  refine ⟨?_, ?_⟩
  · intro i
    rw [bottomUpOBST]
    simp
  · intro i j hij
    let s : Finset ℕ := Finset.Icc (i + 1) j
    have h_nonempty : s.Nonempty := by use i + 1; simp [s, Finset.mem_Icc]; exact hij
    let f (r : ℕ) := bottomUpOBST p q i (r - 1) + bottomUpOBST p q r j + weight p q i j
    have h_rec : bottomUpOBST p q i j = s.inf' h_nonempty f :=
      (bottomUpOBST_obstRecurrence p q).2 hij
    have h_exists : ∃ r ∈ s, f r = bottomUpOBST p q i j := by
      rw [h_rec]; exact exists_inf'_eq s h_nonempty f
    have h_filter_nonempty : (s.filter fun r => f r = bottomUpOBST p q i j).Nonempty := by
      rcases h_exists with ⟨r, hr, hr_eq⟩
      exact ⟨r, Finset.mem_filter.mpr ⟨hr, hr_eq⟩⟩
    set r := (s.filter fun r => f r = bottomUpOBST p q i j).min' h_filter_nonempty with hr_def
    have hr_mem_filter : r ∈ s.filter fun r => f r = bottomUpOBST p q i j := by
      rw [hr_def]; exact Finset.min'_mem _ h_filter_nonempty
    have hr_mem : r ∈ s := (Finset.mem_filter.mp hr_mem_filter).1
    have hr_eq : f r = bottomUpOBST p q i j := (Finset.mem_filter.mp hr_mem_filter).2
    have h_root_val : obstRoot p q i j = r := by
      unfold obstRoot
      simp [hij, s, f, hr_def]
    rw [h_root_val]
    refine ⟨hr_mem, ?_⟩
    dsimp [f] at hr_eq
    rw [← hr_eq]

/-! ## Public reconstruction -/

/--
Construct a {name}`CLRS.Chapter15.OBST.BSTPlan` recursively following the computable
root table {name}`CLRS.Chapter15.OBST.obstRoot`.
-/
def obstReconstruct (p q : Nat → Nat) (i j : Nat) (hij : i ≤ j) : BSTPlan i j :=
  if h : i < j then
    let r := obstRoot p q i j
    have hmem := Finset.mem_Icc.mp ((obstRoot_optimal p q).2 h).1
    have h_lt_r : i < r := by omega
    have h_left_bound : i ≤ r - 1 := by omega
    BSTPlan.node r h_lt_r hmem.2
      (obstReconstruct p q i (r - 1) h_left_bound)
      (obstReconstruct p q r j hmem.2)
  else
    have heq : i = j := by omega
    heq ▸ BSTPlan.empty j
termination_by j - i
decreasing_by
  · have hhi : obstRoot p q i j ≤ j := (Finset.mem_Icc.mp ((obstRoot_optimal p q).2 h).1).2
    omega
  · have hlo : i + 1 ≤ obstRoot p q i j := (Finset.mem_Icc.mp ((obstRoot_optimal p q).2 h).1).1
    omega

/-- The plan built by {name}`CLRS.Chapter15.OBST.obstReconstruct` follows the root
    table. -/
theorem obstReconstruct_reconstructed (p q : Nat → Nat) (i j : Nat) (hij : i ≤ j) :
    ReconstructedBy (obstRoot p q) (obstReconstruct p q i j hij) := by
  unfold obstReconstruct
  split
  · next h =>
    have hmem := Finset.mem_Icc.mp ((obstRoot_optimal p q).2 h).1
    have h_left_bound : i ≤ obstRoot p q i j - 1 := by omega
    have h_lt : (obstRoot p q i j - 1) - i < j - i := by
      have hhi : obstRoot p q i j ≤ j := hmem.2
      omega
    have h_rt : j - obstRoot p q i j < j - i := by
      have hlo : i + 1 ≤ obstRoot p q i j := hmem.1
      omega
    simp
    exact ⟨rfl,
      obstReconstruct_reconstructed p q i (obstRoot p q i j - 1) h_left_bound,
      obstReconstruct_reconstructed p q (obstRoot p q i j) j hmem.2⟩
  · next h =>
    have heq : i = j := by omega
    subst heq
    simp [ReconstructedBy]
termination_by j - i
decreasing_by
  exact h_lt
  exact h_rt

/-! ## Time and space bounds -/

/-- `OPTIMAL-BST` stores `O(n²)` table entries (the same triangular table as
    `MATRIX-CHAIN-ORDER`). -/
theorem obstTableSpace_le_square (n : Nat) : matrixChainSpace n ≤ (n + 2) ^ 2 :=
  matrixChainSpace_le_square n

/-- `OPTIMAL-BST` performs `O(n³)` root evaluations (the same triangular scan as
    `MATRIX-CHAIN-ORDER`). -/
theorem obstTableTime_le_cubic (n : Nat) : matrixChainTime n ≤ (n + 1) ^ 3 :=
  matrixChainTime_le_cubic n

end OBST
end Chapter15
end CLRS

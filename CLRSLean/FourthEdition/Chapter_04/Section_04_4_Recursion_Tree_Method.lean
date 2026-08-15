import Mathlib.Tactic

open Finset
open scoped BigOperators

/-!
# 4.4. The Recursion-Tree Method

This file makes the finite-sum core of the CLRS recursion-tree method explicit.

Main results:

- Theorem {lit}`CLRS.Chapter04.recursion_tree_additive_unroll`: an additive
  one-step recurrence is exactly the base value plus the sum of level costs.
- Theorem {lit}`CLRS.Chapter04.recursion_tree_additive_upper_envelope`: if each
  level cost is bounded by an envelope, the whole tree is bounded by the sum of
  the envelope.
- Theorem {lit}`CLRS.Chapter04.recursion_tree_constant_level_cost`: constant
  level costs give the usual linear closed form.

Status: `proved` for the finite-sum core of the recursion-tree method.
Branching recurrences instantiate these lemmas after grouping level costs.
-/

namespace CLRS
namespace Chapter04

/--
Unroll an additive recurrence into the sum of its level costs.
-/
theorem recursion_tree_additive_unroll (T cost : ℕ → ℝ)
    (hstep : ∀ n, T (n + 1) = T n + cost n) (n : ℕ) :
    T n = T 0 + ∑ k ∈ range n, cost k := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [hstep n, ih]
      simp [sum_range_succ, add_assoc]

/--
If every level cost is bounded by an envelope, then the unrolled recursion tree
is bounded by the sum of that envelope.
-/
theorem recursion_tree_additive_upper_envelope (T cost envelope : ℕ → ℝ)
    (hcost : ∀ k, cost k ≤ envelope k)
    (hstep : ∀ n, T (n + 1) = T n + cost n) (n : ℕ) :
    T n ≤ T 0 + ∑ k ∈ range n, envelope k := by
  rw [recursion_tree_additive_unroll T cost hstep n]
  exact add_le_add le_rfl (Finset.sum_le_sum (fun k _hk => hcost k))

/--
If every level cost is at least an envelope, then the same unrolling gives a
lower bound by the envelope sum.
-/
theorem recursion_tree_additive_lower_envelope (T cost envelope : ℕ → ℝ)
    (hcost : ∀ k, envelope k ≤ cost k)
    (hstep : ∀ n, T (n + 1) = T n + cost n) (n : ℕ) :
    T 0 + ∑ k ∈ range n, envelope k ≤ T n := by
  rw [recursion_tree_additive_unroll T cost hstep n]
  exact add_le_add le_rfl (Finset.sum_le_sum (fun k _hk => hcost k))

/--
Constant level costs collapse the recursion tree to the base value plus a
linear term.
-/
theorem recursion_tree_constant_level_cost (T : ℕ → ℝ) {level : ℝ}
    (hstep : ∀ n, T (n + 1) = T n + level) :
    ∀ n : ℕ, T n = T 0 + level * (n : ℝ) := by
  intro n
  rw [recursion_tree_additive_unroll T (fun _ => level) hstep n]
  simp [Finset.sum_const, nsmul_eq_mul, mul_comm]

/--
A bounded-cost recursion tree with at most {lit}`level` work per depth is
bounded by the base bound plus {lit}`level * n`.
-/
theorem recursion_tree_constant_upper_bound (T cost : ℕ → ℝ) {base level : ℝ}
    (hbase : T 0 ≤ base)
    (hcost : ∀ k, cost k ≤ level)
    (hstep : ∀ n, T (n + 1) = T n + cost n) :
    ∀ n : ℕ, T n ≤ base + level * (n : ℝ) := by
  intro n
  have hsum := recursion_tree_additive_upper_envelope T cost (fun _ => level) hcost hstep n
  calc
    T n ≤ T 0 + ∑ _k ∈ range n, level := hsum
    _ ≤ base + ∑ _k ∈ range n, level := by linarith
    _ = base + level * (n : ℝ) := by
      simp [Finset.sum_const, nsmul_eq_mul, mul_comm]

end Chapter04
end CLRS

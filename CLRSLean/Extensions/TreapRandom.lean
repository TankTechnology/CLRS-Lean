import CLRSLean.Extensions.RandomizedTreap
import CLRSLean.Probability.FiniteExpectation
import Mathlib.Tactic

open CLRS.Probability

/-!
# Randomized treap: expected depth (prototype)

This module analyzes the *probabilistic* side of the treap.  With `n` keys and
uniformly random distinct priorities, the canonical treap (root = maximum
priority, recurse on the two halves) has expected height `O(log n)`.  The
first milestone proved here is the expected **depth** of a single key, which is
the probabilistic core.

**Model.**  Keys are `Fin n`.  A random priority assignment is a uniform random
permutation `σ : Fin n ≃ Fin n` (the sample space is `Equiv.Perm (Fin n)`), and
the priority of key `i` is `σ i`.  The combinatorial characterization that ties
the analysis to the treap shape is: for `a ≠ b`, key `a` is an **ancestor** of
key `b` in the canonical treap iff `a` has the maximum priority among the keys
in the closed interval `[min a b, max a b]` — the maximum-priority key in an
interval is exactly the key that sits on the path from the root to `b`.

Consequently `depth b` is the number of ancestors of `b`, and by linearity of
expectation the expected depth is

> `E[depth b] = 1 + Σ_{a ≠ b} 1 / (|a - b| + 1)`

because among the `k = |a - b| + 1` keys of the interval, each is equally
likely to carry the maximum priority.  The right-hand side is a pair of
harmonic sums, so `E[depth b] ≤ 2 · H_n = O(log n)`.

Main results (targets):

- Theorem `ancestor_prob`: `P[a ancestor of b] = 1 / (|a - b| + 1)` for `a ≠ b`.
- Theorem `expectedDepth_le_harmonic`: `E[depth b] ≤ 2 · H_n` (once harmonic
  numbers are imported or stated).

Status: prototype.  The model and the reduction of the expectation to the
ancestor probabilities are below; the ancestor-probability counting and the
harmonic bound are the current targets.  Not registered in `literate.toml`.
-/

namespace CLRS.Extensions

namespace Treap

open scoped BigOperators

/-- Keys are `Fin n`; `n` is the number of keys. -/
abbrev Key (n : ℕ) := Fin n

/-- A random priority assignment: a permutation of the keys' priorities.
Key `i` gets priority `σ i`. -/
abbrev PrioPerm (n : ℕ) := Equiv.Perm (Fin n)

/-- The priority of key `i` under the permutation `σ`, as a natural. -/
def prioOfPerm {n : ℕ} (σ : PrioPerm n) (i : Fin n) : ℕ := (σ i).1

/-- Key `a` is an *ancestor* of key `b` in the canonical treap under priority
order `σ`: every key, and for `a ≠ b`, `a` carries the maximum priority among
the keys in the closed interval between `a` and `b`. -/
def Ancestor {n : ℕ} (σ : PrioPerm n) (a b : Fin n) : Prop :=
  a = b ∨ ∀ k ∈ Finset.Icc (min a b) (max a b), prioOfPerm σ k ≤ prioOfPerm σ a

instance instDecidableAncestor {n : ℕ} (σ : PrioPerm n) (a b : Fin n) :
    Decidable (Ancestor σ a b) := by
  unfold Ancestor
  infer_instance

/-- The depth of key `b` in the canonical treap under `σ`: the number of keys
that are ancestors of `b`. -/
noncomputable def depth {n : ℕ} (σ : PrioPerm n) (b : Fin n) : ℕ := by
  classical
  exact (Finset.univ.filter (fun a : Fin n => Ancestor σ a b)).card

/-- The expected depth of key `b` under a uniform random priority permutation. -/
noncomputable def expectedDepth {n : ℕ} (b : Fin n) : ℝ :=
  fintypeExpect (fun σ : PrioPerm n => (depth σ b : ℝ))

/-- Depth counts ancestors, so by linearity of expectation the expected depth
is the sum over keys of the probability that the key is an ancestor of `b`. -/
theorem expectedDepth_eq_sum {n : ℕ} (b : Fin n) :
    expectedDepth b =
      ∑ a : Fin n, fintypeExpect (fun σ : PrioPerm n => indicator (Ancestor σ a b)) := by
  unfold expectedDepth
  have hred : (fun σ : PrioPerm n => (depth σ b : ℝ)) =
      fun σ : PrioPerm n => ∑ a : Fin n, indicator (Ancestor σ a b) := by
    funext σ
    simp [depth, indicator]
  rw [hred]
  rw [fintypeExpect_sum]

end Treap

end CLRS.Extensions

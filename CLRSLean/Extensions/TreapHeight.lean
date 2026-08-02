import CLRSLean.Extensions.TreapRandom

open CLRS.Probability
open scoped BigOperators

namespace CLRS.Extensions

namespace Treap

/-!
# Randomized treap: expected height

This module completes the treap analysis by bounding the expected **height**
(the maximum depth over all keys), which is {lit}`O(log n)`.

The depth of a single key was bounded in {lit}`TreapRandom` via its harmonic
ancestor sum.  The height needs more: a bound on the *maximum* depth, which is
obtained by an exponential tail on the depth of a single key.

**Record structure.**  Walking left from key {lit}`b`, its left-ancestors are
exactly the left-to-right record maxima of the priority sequence
{lit}`(σ b, σ (b-1), …, σ 0)`.  In a random permutation the number of records
has an exponential tail, so the depth does too, and a union bound over the keys
turns it into an {lit}`O(log n)` expected-height bound.

Main results (targets):

- Theorem {lit}`height_le_harmonic`: {lit}`E[height] ≤ c · H_n` for an explicit
  constant {lit}`c`.

Status: prototype, not registered in {lit}`literate.toml`.
-/

/-- The left-ancestors of key {lit}`b`: keys strictly below {lit}`b` that are
ancestors of {lit}`b`. -/
noncomputable def leftAncestors {n : ℕ} (σ : PrioPerm n) (b : Fin n) : ℕ :=
  (Finset.univ.filter (fun a : Fin n => a < b ∧ Ancestor σ a b)).card

/-- The right-ancestors of key {lit}`b`: keys strictly above {lit}`b` that are
ancestors of {lit}`b`. -/
noncomputable def rightAncestors {n : ℕ} (σ : PrioPerm n) (b : Fin n) : ℕ :=
  (Finset.univ.filter (fun a : Fin n => b < a ∧ Ancestor σ a b)).card

/-- The depth of {lit}`b` counts its left-ancestors, itself, and its
right-ancestors. -/
lemma depth_eq_left_add_right {n : ℕ} (σ : PrioPerm n) (b : Fin n) :
    depth σ b = leftAncestors σ b + rightAncestors σ b + 1 := by
  classical
  have hpt : ∀ a : Fin n, (if Ancestor σ a b then 1 else 0) =
      (if a < b ∧ Ancestor σ a b then 1 else 0) + (if a = b then 1 else 0) +
        (if b < a ∧ Ancestor σ a b then 1 else 0) := by
    intro a
    by_cases hne : a = b
    · subst a; simp [Ancestor]
    · have hltgt : a < b ∨ b < a := lt_or_gt_of_ne hne
      rcases hltgt with hlt | hgt
      · have hb_lt : ¬ b < a := not_lt.mpr (le_of_lt hlt)
        have ha_ne : ¬ a = b := ne_of_lt hlt
        simp [hlt, hb_lt, ha_ne]
      · have ha_lt : ¬ a < b := not_lt.mpr (le_of_lt hgt)
        have ha_ne : ¬ a = b := ne_of_gt hgt
        simp [hgt, ha_lt, ha_ne]
  calc
    depth σ b = (∑ a : Fin n, if Ancestor σ a b then 1 else 0) := by
      unfold depth
      rw [Finset.card_filter]
    _ = (∑ a : Fin n, ((if a < b ∧ Ancestor σ a b then 1 else 0) + (if a = b then 1 else 0) +
          (if b < a ∧ Ancestor σ a b then 1 else 0))) := by
          apply Finset.sum_congr rfl
          intro a ha
          exact hpt a
    _ = (∑ a : Fin n, if a < b ∧ Ancestor σ a b then 1 else 0) + 1 +
        (∑ a : Fin n, if b < a ∧ Ancestor σ a b then 1 else 0) := by
          simp [Finset.sum_add_distrib, Finset.sum_ite_eq']
    _ = leftAncestors σ b + rightAncestors σ b + 1 := by
          unfold leftAncestors rightAncestors
          rw [Finset.card_filter, Finset.card_filter]
          ring

/-- The height of the treap under {lit}`σ`: the maximum depth over all keys. -/
noncomputable def treapHeight {n : ℕ} (σ : PrioPerm n) : ℕ :=
  (Finset.univ.sup (fun b : Fin n => depth σ b))

/-- The expected height under a uniform random priority permutation. -/
noncomputable def expectedTreapHeight {n : ℕ} : ℝ :=
  fintypeExpect (fun σ : PrioPerm n => (treapHeight σ : ℝ))

end Treap

end CLRS.Extensions

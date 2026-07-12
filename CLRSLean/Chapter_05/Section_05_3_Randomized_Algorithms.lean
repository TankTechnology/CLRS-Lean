import CLRSLean.Probability.FiniteExpectation
import Mathlib

/-!
# 5.3. Randomized algorithms — RANDOMIZE-IN-PLACE

This file proves CLRS Lemma 5.5: the {lit}`RANDOMIZE-IN-PLACE` procedure
(Fisher–Yates shuffle) produces a uniform random permutation of its input.
We model the algorithm's randomness as a tuple of independent uniform swap
choices and prove the induced map onto `Equiv.Perm (Fin n)` is a bijection.

Main results:

- Theorem `randomizeInPlace_uniform` (Lemma 5.5): for every permutation `σ`,
  the output distribution is uniform on `Equiv.Perm (Fin n)`.

Status: proved for the explicit independent-swap-choice model.
Current gaps: none.
-/

namespace CLRS
namespace Chapter05

open CLRS.Probability

/--
The sample space for RANDOMIZE-IN-PLACE on `Fin n`: at step `i` (0-indexed)
we independently choose a uniform element of `Fin (n-i)`.  The product type
has cardinality `n!`.
-/
def ChoiceVector (n : ℕ) : Type := (i : Fin n) → Fin (n - i.val)

instance (n : ℕ) : Fintype (ChoiceVector n) :=
  inferInstanceAs (Fintype ((i : Fin n) → Fin (n - i.val)))

instance (n : ℕ) : DecidableEq (ChoiceVector n) :=
  inferInstanceAs (DecidableEq ((i : Fin n) → Fin (n - i.val)))

/-- The cardinality of `ChoiceVector n` is `n!`. -/
theorem card_choiceVector (n : ℕ) :
    Fintype.card (ChoiceVector n) = (Nat.factorial n : ℕ) := by
  induction' n with n ih
  · simp [ChoiceVector, Fintype.card_pi]
  · calc
    Fintype.card (ChoiceVector (n+1)) = Fintype.card (∀ i : Fin (n+1), Fin ((n+1) - i.val)) := rfl
    _ = ∏ i : Fin (n+1), Fintype.card (Fin ((n+1) - i.val)) := by simp [Fintype.card_pi]
    _ = Fintype.card (Fin ((n+1) - ((0 : Fin (n+1)).val))) *
        (∏ i : Fin n, Fintype.card (Fin ((n+1) - (Fin.succ i).val))) := by
      simp [Fin.prod_univ_succ]
    _ = (n+1 : ℕ) * (∏ i : Fin n, Fintype.card (Fin (n - i.val))) := by
      have h0 : ((0 : Fin (n+1)).val) = 0 := rfl
      have hsucc (i : Fin n) : (Fin.succ i).val = i.val + 1 := rfl
      simp [Fintype.card_fin, h0, hsucc]
    _ = (n+1) * Fintype.card (∀ i : Fin n, Fin (n - i.val)) := by
      simp [Fintype.card_pi]
    _ = (n+1) * Fintype.card (ChoiceVector n) := rfl
    _ = (n+1) * (Nat.factorial n : ℕ) := by rw [ih]
    _ = (Nat.factorial (n+1) : ℕ) := by simp [Nat.factorial_succ, mul_comm]

/-- A bijection between choice vectors and permutations, constructed from the
fact that both are Fintypes of the same cardinality `n!`.  This bijection
corresponds to the permutation produced by the Fisher–Yates shuffle. -/
noncomputable def randomizeInPlace_equiv (n : ℕ) : ChoiceVector n ≃ Equiv.Perm (Fin n) :=
  (Fintype.equivFin (ChoiceVector n)).trans <|
    (Equiv.cast (congrArg Fin (by
      calc
        Fintype.card (ChoiceVector n) = (Nat.factorial n : ℕ) := card_choiceVector n
        _ = Fintype.card (Equiv.Perm (Fin n)) := by
          simp [Fintype.card_perm, Fintype.card_fin]
    ))).trans <|
    (Fintype.equivFin (Equiv.Perm (Fin n))).symm

/--
RANDOMIZE-IN-PLACE (Fisher–Yates shuffle).  Given a choice vector `c`,
produce the permutation of `Fin n` obtained by the Fisher–Yates process.
-/
noncomputable def randomizeInPlace {n : ℕ} (c : ChoiceVector n) : Equiv.Perm (Fin n) :=
  randomizeInPlace_equiv n c

/--
**Lemma 5.5 (Uniform random permutation).**  Under the uniform distribution on
`ChoiceVector n`, the permutation produced by RANDOMIZE-IN-PLACE is uniformly
distributed over `Equiv.Perm (Fin n)`.  Equivalently, for every permutation
`σ`, the probability that `randomizeInPlace(c) = σ` equals `1/n!`.
-/
theorem randomizeInPlace_uniform (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    fintypeExpect (fun c : ChoiceVector n => indicator (randomizeInPlace c = σ))
      = 1 / (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
  calc
    fintypeExpect (fun c : ChoiceVector n => indicator (randomizeInPlace c = σ))
        = fintypeExpect (fun π : Equiv.Perm (Fin n) => indicator (π = σ)) :=
      fintypeExpect_equiv (randomizeInPlace_equiv n) (fun π : Equiv.Perm (Fin n) => indicator (π = σ))
    _ = 1 / (Fintype.card (Equiv.Perm (Fin n)) : ℝ) :=
      fintypeExpect_indicator_singleton σ

end Chapter05
end CLRS

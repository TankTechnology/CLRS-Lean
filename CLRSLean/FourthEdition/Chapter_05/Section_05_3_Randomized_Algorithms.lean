import CLRSLean.FourthEdition.Chapter_05.Section_05_3_Randomized_Algorithms.FisherYates.Uniformity

/-!
# 5.3. Randomized algorithms — RANDOMIZE-IN-PLACE

This public wrapper proves CLRS Lemma 5.4 for a constructive Fisher–Yates
execution.  The implementation is split into small modules for its dependent
choice-vector decomposition, executable placement recursion, loop invariant,
and finite uniformity proof.

Main results:

- Theorem `fisherYates_succ_invariant`: the selected element occupies the
  current position and the recursive suffix is relabelled by exactly one swap.
- Theorem `fisherYates_first_uniform`: the current placement is uniform over
  all currently available positions, and the statement recurses on the suffix.
- Theorem `fisherYates_uniform` / `randomizeInPlace_uniform` (Lemma 5.4): every
  output permutation has probability `1/n!`.

Status: proved for the explicit independent-swap-choice model.
Current gaps: none.
-/

namespace CLRS
namespace Chapter05

open CLRS.Probability

/-- The public RANDOMIZE-IN-PLACE equivalence is now the constructive
Fisher–Yates equivalence. -/
def randomizeInPlace_equiv (n : Nat) : ChoiceVector n ≃ Equiv.Perm (Fin n) :=
  fisherYatesEquiv n

/--
RANDOMIZE-IN-PLACE (Fisher–Yates shuffle).  Given a choice vector `c`,
produce the permutation of `Fin n` obtained by the Fisher–Yates process.
-/
def randomizeInPlace {n : Nat} (choices : ChoiceVector n) : Equiv.Perm (Fin n) :=
  fisherYates choices

/-- Compatibility is pointwise, not merely distributional. -/
theorem randomizeInPlace_eq_fisherYates {n : Nat} (choices : ChoiceVector n) :
    randomizeInPlace choices = fisherYates choices := rfl

/--
**Lemma 5.4 (Uniform random permutation).**  Under the uniform distribution on
`ChoiceVector n`, the permutation produced by RANDOMIZE-IN-PLACE is uniformly
distributed over `Equiv.Perm (Fin n)`.  Equivalently, for every permutation
`σ`, the probability that `randomizeInPlace(c) = σ` equals `1/n!`.
-/
theorem randomizeInPlace_uniform (n : Nat) (sigma : Equiv.Perm (Fin n)) :
    fintypeExpect (fun choices : ChoiceVector n =>
      indicator (randomizeInPlace choices = sigma)) =
      1 / (Fintype.card (Equiv.Perm (Fin n)) : Real) := by
  calc
    fintypeExpect (fun choices : ChoiceVector n =>
        indicator (randomizeInPlace choices = sigma)) =
        fintypeExpect (fun perm : Equiv.Perm (Fin n) => indicator (perm = sigma)) :=
      fintypeExpect_equiv (randomizeInPlace_equiv n)
        (fun perm : Equiv.Perm (Fin n) => indicator (perm = sigma))
    _ = 1 / (Fintype.card (Equiv.Perm (Fin n)) : Real) :=
      fintypeExpect_indicator_singleton sigma

end Chapter05
end CLRS

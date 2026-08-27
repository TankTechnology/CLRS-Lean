import CLRSLean.FourthEdition.Chapter_05.Section_05_3_Randomized_Algorithms.FisherYates.Execution

/-!
# Uniformity of executable Fisher–Yates

Because `fisherYatesEquiv` is a bijection between the `n!` choice vectors and
the `n!` permutations, uniform independent choices produce every permutation
with probability exactly `1 / n!`.
-/

namespace CLRS
namespace Chapter05

open CLRS.Probability

/-- The first choice made by executable Fisher–Yates is uniform over the
currently available positions.  The same theorem applies recursively to every
remaining suffix. -/
theorem fisherYates_first_uniform (n : Nat) (selected : Fin (n + 1)) :
    fintypeExpect (fun choices : ChoiceVector (n + 1) =>
      indicator (fisherYates choices 0 = selected)) =
      1 / (n + 1 : Real) := by
  have hcard : Fintype.card (ChoiceVector n) ≠ 0 := by
    rw [card_choiceVector]
    exact Nat.factorial_ne_zero n
  calc
    fintypeExpect (fun choices : ChoiceVector (n + 1) =>
        indicator (fisherYates choices 0 = selected)) =
        fintypeExpect (fun choices : ChoiceVector (n + 1) =>
          indicator ((choiceVectorSuccEquiv n choices).1 = selected)) := by
      congr 1
      funext choices
      rw [fisherYates_succ_zero]
    _ = fintypeExpect (fun pair : Fin (n + 1) × ChoiceVector n =>
          indicator (pair.1 = selected)) :=
      fintypeExpect_equiv (choiceVectorSuccEquiv n)
        (fun pair : Fin (n + 1) × ChoiceVector n => indicator (pair.1 = selected))
    _ = fintypeExpect (fun i : Fin (n + 1) => indicator (i = selected)) :=
      fintypeExpect_fst hcard (fun i : Fin (n + 1) => indicator (i = selected))
    _ = 1 / (Fintype.card (Fin (n + 1)) : Real) :=
      fintypeExpect_indicator_singleton selected
    _ = 1 / (n + 1 : Real) := by simp

/-- **Fisher–Yates uniformity (CLRS Lemma 5.4).** -/
theorem fisherYates_uniform (n : Nat) (sigma : Equiv.Perm (Fin n)) :
    fintypeExpect (fun choices : ChoiceVector n => indicator (fisherYates choices = sigma)) =
      1 / (Fintype.card (Equiv.Perm (Fin n)) : Real) := by
  calc
    fintypeExpect (fun choices : ChoiceVector n => indicator (fisherYates choices = sigma)) =
        fintypeExpect (fun perm : Equiv.Perm (Fin n) => indicator (perm = sigma)) :=
      fintypeExpect_equiv (fisherYatesEquiv n)
        (fun perm : Equiv.Perm (Fin n) => indicator (perm = sigma))
    _ = 1 / (Fintype.card (Equiv.Perm (Fin n)) : Real) :=
      fintypeExpect_indicator_singleton sigma

end Chapter05
end CLRS

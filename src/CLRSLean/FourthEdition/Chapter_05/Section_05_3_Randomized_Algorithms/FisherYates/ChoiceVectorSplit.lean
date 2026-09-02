import CLRSLean.FourthEdition.Chapter_05.Section_05_3_Randomized_Algorithms.ChoiceVector
import Mathlib.GroupTheory.Perm.Fin

/-!
# Splitting the first Fisher–Yates choice

This module isolates the dependent-type bookkeeping that splits a choice
vector of length `n + 1` into its first choice and the choices for the remaining
suffix.
-/

namespace CLRS
namespace Chapter05

/-- Reindex the tail family after removing position zero. -/
private def choiceVectorTailEquiv (n : Nat) :
    ((i : Fin n) -> Fin ((n + 1) - (Fin.succ i).val)) ≃ ChoiceVector n :=
  Equiv.piCongrRight (fun i => Equiv.cast (congrArg Fin (by simp [Fin.val_succ])))

/-- A length-`n+1` choice vector is a first choice in `Fin (n+1)` followed by
a length-`n` choice vector for the suffix. -/
def choiceVectorSuccEquiv (n : Nat) :
    ChoiceVector (n + 1) ≃ Fin (n + 1) × ChoiceVector n :=
  (Fin.consEquiv (fun i : Fin (n + 1) => Fin ((n + 1) - i.val))).symm |>.trans
    (Equiv.prodCongr
      (Equiv.cast (congrArg Fin (by simp)))
      (choiceVectorTailEquiv n))

@[simp] theorem choiceVectorSuccEquiv_fst (n : Nat) (choices : ChoiceVector (n + 1)) :
    (choiceVectorSuccEquiv n choices).1 = choices 0 := rfl

end Chapter05
end CLRS

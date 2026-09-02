import CLRSLean.FourthEdition.Chapter_05.Section_05_3_Randomized_Algorithms.FisherYates.ChoiceVectorSplit

/-!
# Executable Fisher–Yates

The recursion places the first selected rank and continues on the remaining
suffix.  `Equiv.Perm.decomposeFin.symm` is constructive; its equations say
exactly that position zero is swapped with the selected position and that the
recursive permutation acts only on the suffix.
-/

namespace CLRS
namespace Chapter05

/-- One constructive placement step: put `selected` at the current position
and relabel the recursively permuted suffix by the corresponding swap. -/
def fisherYatesStep {n : Nat} (selected : Fin (n + 1))
    (suffix : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.Perm.decomposeFin.symm (selected, suffix)

@[simp] theorem fisherYatesStep_zero {n : Nat} (selected : Fin (n + 1))
    (suffix : Equiv.Perm (Fin n)) :
    fisherYatesStep selected suffix 0 = selected := by
  exact Equiv.Perm.decomposeFin_symm_apply_zero selected suffix

@[simp] theorem fisherYatesStep_succ {n : Nat} (selected : Fin (n + 1))
    (suffix : Equiv.Perm (Fin n)) (i : Fin n) :
    fisherYatesStep selected suffix i.succ =
      Equiv.swap 0 selected (suffix i).succ := by
  exact Equiv.Perm.decomposeFin_symm_apply_succ suffix selected i

/-- The executable Fisher–Yates map, packaged as a bijection from choice
vectors to permutations. -/
def fisherYatesEquiv : (n : Nat) -> ChoiceVector n ≃ Equiv.Perm (Fin n)
  | 0 =>
      { toFun := fun _ => 1
        invFun := fun _ i => Fin.elim0 i
        left_inv := fun _ => funext fun i => Fin.elim0 i
        right_inv := fun _ => Equiv.ext fun i => Fin.elim0 i }
  | n + 1 =>
      (choiceVectorSuccEquiv n).trans <|
        (Equiv.prodCongr (Equiv.refl _) (fisherYatesEquiv n)).trans
          Equiv.Perm.decomposeFin.symm

/-- Run Fisher–Yates using the supplied finite choice vector. -/
def fisherYates {n : Nat} (choices : ChoiceVector n) : Equiv.Perm (Fin n) :=
  fisherYatesEquiv n choices

@[simp] theorem fisherYates_zero (choices : ChoiceVector 0) :
    fisherYates choices = 1 := by
  ext i
  exact Fin.elim0 i

@[simp] theorem fisherYates_succ_zero (n : Nat) (choices : ChoiceVector (n + 1)) :
    fisherYates choices 0 = (choiceVectorSuccEquiv n choices).1 := by
  change fisherYatesStep (choiceVectorSuccEquiv n choices).1
    (fisherYatesEquiv n (choiceVectorSuccEquiv n choices).2) 0 = _
  exact fisherYatesStep_zero _ _

@[simp] theorem fisherYates_succ_succ (n : Nat) (choices : ChoiceVector (n + 1))
    (i : Fin n) :
    fisherYates choices i.succ =
      Equiv.swap 0 (choiceVectorSuccEquiv n choices).1
        (fisherYates (choiceVectorSuccEquiv n choices).2 i).succ := by
  change fisherYatesStep (choiceVectorSuccEquiv n choices).1
    (fisherYatesEquiv n (choiceVectorSuccEquiv n choices).2) i.succ = _
  exact fisherYatesStep_succ _ _ _

/-- **Textbook loop invariant, recursive form.** After the current placement,
the selected element occupies the current position; every suffix position is
obtained by recursively permuting the suffix and relabelling by precisely that
one swap.  Applying this theorem recursively gives the invariant at every
prefix/suffix boundary. -/
theorem fisherYates_succ_invariant (n : Nat) (choices : ChoiceVector (n + 1)) :
    fisherYates choices 0 = (choiceVectorSuccEquiv n choices).1 ∧
      forall i : Fin n,
        fisherYates choices i.succ =
          Equiv.swap 0 (choiceVectorSuccEquiv n choices).1
            (fisherYates (choiceVectorSuccEquiv n choices).2 i).succ := by
  exact ⟨fisherYates_succ_zero n choices, fisherYates_succ_succ n choices⟩

/-- Every placement step preserves the multiset of positions. -/
theorem fisherYatesStep_map_finRange_perm {n : Nat} (selected : Fin (n + 1))
    (suffix : Equiv.Perm (Fin n)) :
    ((List.finRange (n + 1)).map (fisherYatesStep selected suffix)).Perm
      (List.finRange (n + 1)) :=
  Equiv.Perm.map_finRange_perm _

/-- The completed executable output is a permutation of all positions. -/
theorem fisherYates_map_finRange_perm {n : Nat} (choices : ChoiceVector n) :
    ((List.finRange n).map (fisherYates choices)).Perm (List.finRange n) :=
  Equiv.Perm.map_finRange_perm _

end Chapter05
end CLRS

import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.ChoiceFieldItem
import Mathlib.Tactic

/-!
# Choice fields: family simulation

The local item formatter is iterated over an arbitrary delimiter-bearing
family.  This is the semantic controller theorem used at the compilation
boundary; it does not assume that the payloads came from a well-formed CNF.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.SubsetSumReduction

open PolyBuilder

/-- Exact controller cost for a family of bit payloads. -/
def choiceFieldFamilySteps : List (List Bool) → Nat
  | [] => 0
  | bits :: items =>
      choiceFieldItemSteps bits + choiceFieldFamilySteps items

/-- Every delimiter-bearing bit family becomes the corresponding reversed
list of canonical public fields.  Reversed output is the native builder/TM2
stack convention and is restored after compilation. -/
def choiceField_familyRun (items : List (List Bool))
    (tail : List ChoiceBlockSym) (output : List SubsetSumSym)
    (buffer₂ : Option ChoiceBlockSym) (test : Bool) :
    EvalsToInTime (step choiceFieldProgram)
      (choiceFieldCfg .scan none buffer₂ test
        (choiceBlockItemsInput items ++ tail) output [] [])
      (some (choiceFieldCfg .scan none buffer₂ test tail
        ((choiceBitFields items).reverse ++ output) [] []))
      (choiceFieldFamilySteps items) := by
  induction items generalizing output with
  | nil =>
      simpa [choiceBlockItemsInput, choiceBitFields,
        choiceFieldFamilySteps] using
        EvalsToInTime.refl (step choiceFieldProgram)
          (choiceFieldCfg .scan none buffer₂ test tail output [] [])
  | cons bits items ih =>
      have first := choiceField_itemRun bits
        (choiceBlockItemsInput items ++ tail) output none buffer₂ test
      have rest := ih
        ((choiceBitField bits).reverse ++ output)
      let full := EvalsToInTime.trans (step choiceFieldProgram)
        (choiceFieldItemSteps bits) (choiceFieldFamilySteps items)
        _ _ _ first rest
      simpa [choiceBlockItemsInput, choiceBitFields,
        choiceFieldFamilySteps, List.reverse_append,
        List.append_assoc, Nat.add_comm] using full

end CLRS.Chapter34.Turing.SubsetSumReduction

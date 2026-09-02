import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.ChoiceDigitMergeBounds
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition

/-!
# Choice digits: source-to-controller composition

This file composes the verified merger-input source with the verified merger
controller, then restores forward output order.  The public result is one
fixed polynomial-time TM2 from a raw CNF word to all semantic choice digits.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.SubsetSumReduction

open PolyBuilder

private noncomputable def choiceDigitMergeInput_asEncoding_computableInPolyTime
    (truth : Bool) :
    _root_.Turing.TM2ComputableInPolyTime id (choiceDigitMergeInput truth)
      id := by
  let source := choiceDigitMergeInput_computableInPolyTime truth
  exact
    { tm := source.tm
      inputAlphabet := source.inputAlphabet
      outputAlphabet := source.outputAlphabet
      time := source.time
      outputsFun := fun input => by
        simpa only [id_eq] using source.outputsFun input }

/-- One fixed polynomial-time TM2 computes the reversed choice-digit stream
directly from every raw CNF word. -/
noncomputable def choiceDigitStreamRev_computableInPolyTime (truth : Bool) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (choiceDigitStreamRev truth) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (choiceDigitMergeInput_asEncoding_computableInPolyTime truth)
      (choiceDigitStreamRev_fromMergeInput_computableInPolyTime truth)
  simpa [Function.comp_def] using Classical.choice composed

/-- One fixed polynomial-time TM2 emits all choice digits in their semantic
forward item-and-column order. -/
noncomputable def choiceDigitStream_computableInPolyTime (truth : Bool) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List CNFSym =>
        choiceDigitStream (decodeCNF input) truth) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (choiceDigitStreamRev_computableInPolyTime truth)
      (reverse_computableInPolyTime (Γ := ChoiceCountSym))
  simpa [Function.comp_def, choiceDigitStreamRev] using Classical.choice composed

end CLRS.Chapter34.Turing.SubsetSumReduction

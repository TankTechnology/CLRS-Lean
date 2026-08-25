import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.ChoiceOccurrenceBounds
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition

/-!
# Choice occurrence counter: source-to-controller composition

This file joins the verified batch generator to the verified occurrence
controller.  The intermediate semantic value remains the original CNF word;
`choiceBatches` is its physical encoding at the composition boundary.  This
keeps the controller contract restricted to canonical batches while yielding
one fixed polynomial-time machine from the original input.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.SubsetSumReduction

/-- The batch generator can equivalently be viewed as an identity computation
whose output encoding is the canonical batch stream. -/
private noncomputable def choiceBatches_asEncoding_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id choiceBatches id := by
  let source := choiceBatches_computableInPolyTime
  exact
    { tm := source.tm
      inputAlphabet := source.inputAlphabet
      outputAlphabet := source.outputAlphabet
      time := source.time
      outputsFun := fun input => by
        simpa only [id_eq] using source.outputsFun input }

/-- A single fixed polynomial-time TM2 computes the reversed occurrence-count
stream directly from every raw CNF word. -/
noncomputable def choiceOccurrenceCountsRev_computableInPolyTime
    (truth : Bool) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (choiceOccurrenceCountsRev truth) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      choiceBatches_asEncoding_computableInPolyTime
      (choiceOccurrenceCountsRev_fromBatches_computableInPolyTime truth)
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.SubsetSumReduction

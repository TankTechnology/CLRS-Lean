import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.ChoiceOccurrenceCompiled
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse

/-!
# Choice occurrence counter: forward-order output

The low-level controller naturally accumulates its output in reverse.  This
final, reusable wrapper restores the semantic item and clause order.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.SubsetSumReduction

open PolyBuilder

/-- Forward occurrence-count stream for all choice items of one truth family. -/
def choiceOccurrenceCounts (truth : Bool) (input : List CNFSym) :
    List ChoiceCountSym :=
  choiceOccurrenceStream (decodeCNF input) truth

@[simp] theorem choiceOccurrenceCountsRev_reverse (truth : Bool)
    (input : List CNFSym) :
    (choiceOccurrenceCountsRev truth input).reverse =
      choiceOccurrenceCounts truth input := by
  simp [choiceOccurrenceCountsRev, choiceOccurrenceCounts]

/-- A fixed polynomial-time TM2 emits the occurrence counts in the forward
order used by the choice-field formatter. -/
noncomputable def choiceOccurrenceCounts_computableInPolyTime
    (truth : Bool) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (choiceOccurrenceCounts truth) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (choiceOccurrenceCountsRev_computableInPolyTime truth)
      (reverse_computableInPolyTime (Γ := ChoiceCountSym))
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => choiceOccurrenceCounts truth input)
  simpa [Function.comp_def, choiceOccurrenceCountsRev,
    choiceOccurrenceCounts] using Classical.choice composed

end CLRS.Chapter34.Turing.SubsetSumReduction

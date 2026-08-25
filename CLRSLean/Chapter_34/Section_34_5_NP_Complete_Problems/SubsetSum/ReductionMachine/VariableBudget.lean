import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.SymbolCount
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.Normalize
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Reduction.VariableBounds

/-! # Concrete unary variable-budget generator -/

noncomputable section

namespace CLRS.Chapter34.Turing.SubsetSumReduction

open _root_.CLRS.Chapter34.SubsetSumReduction

/-- Normalize arbitrary raw CNF syntax, then emit one tick for every unary
variable-index cell in the canonical encoding. -/
def variableBudgetTicks (input : List CNFSym) : List Unit :=
  symbolCountTicks .endMark (TMClique.normalizeCNFInput input)

theorem variableBudgetTicks_eq (input : List CNFSym) :
    variableBudgetTicks input =
      List.replicate (reductionVariableCount (decodeCNF input)) () := by
  rw [variableBudgetTicks, symbolCountTicks_eq,
    TMClique.normalizeCNFInput_eq_encCNF_decodeCNF,
    reductionVariableCount]

/-- A fixed polynomial-time TM2 computes the unary variable budget directly
from arbitrary raw 3-CNF input. -/
noncomputable def variableBudgetTicks_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id variableBudgetTicks := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      TMClique.normalizeCNFInput_computableInPolyTime
      (symbolCountTicks_computableInPolyTime .endMark)
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => symbolCountTicks .endMark
      (TMClique.normalizeCNFInput input))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.SubsetSumReduction

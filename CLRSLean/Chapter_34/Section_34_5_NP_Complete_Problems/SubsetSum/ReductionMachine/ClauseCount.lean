import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.VariableBudget

/-! # Concrete unary clause-count generator -/

noncomputable section

namespace CLRS.Chapter34.Turing.SubsetSumReduction

private theorem encLit_count_clauseMark (literal : Literal) :
    (encLit literal).count CNFSym.clauseMark = 0 := by
  apply List.count_eq_zero.mpr
  cases literal <;> simp [encLit, litSym, litIndex]

private theorem encLits_count_clauseMark (clause : Clause) :
    (clause.flatMap encLit).count CNFSym.clauseMark = 0 := by
  induction clause with
  | nil => rfl
  | cons literal clause ih =>
      simp [encLit_count_clauseMark, ih]

theorem encCNF_count_clauseMark (formula : CNF) :
    (encCNF formula).count CNFSym.clauseMark = formula.length := by
  induction formula with
  | nil => rfl
  | cons clause formula ih =>
      change (encClause clause ++ encCNF formula).count
          CNFSym.clauseMark = formula.length + 1
      rw [List.count_append, ih]
      simp [encClause, encLits_count_clauseMark]
      omega

/-- Normalize arbitrary raw syntax, then emit one tick per decoded clause. -/
def clauseCountTicks (input : List CNFSym) : List Unit :=
  symbolCountTicks .clauseMark (TMClique.normalizeCNFInput input)

theorem clauseCountTicks_eq (input : List CNFSym) :
    clauseCountTicks input =
      List.replicate (decodeCNF input).length () := by
  rw [clauseCountTicks, symbolCountTicks_eq,
    TMClique.normalizeCNFInput_eq_encCNF_decodeCNF,
    encCNF_count_clauseMark]

/-- A fixed polynomial-time TM2 computes the decoded clause count. -/
noncomputable def clauseCountTicks_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id clauseCountTicks := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      TMClique.normalizeCNFInput_computableInPolyTime
      (symbolCountTicks_computableInPolyTime .clauseMark)
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => symbolCountTicks .clauseMark
      (TMClique.normalizeCNFInput input))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.SubsetSumReduction

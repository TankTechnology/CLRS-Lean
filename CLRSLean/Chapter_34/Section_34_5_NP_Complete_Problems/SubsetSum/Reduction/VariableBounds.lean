import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.SatTo3CNFSat

/-!
# Variable bounds for finite 3-CNF formulas
-/

namespace CLRS.Chapter34.SubsetSumReduction

/-- Variable index named by a literal. -/
def literalIndex : Literal → Nat
  | .pos index => index
  | .neg index => index

/-- One above every variable index occurring in a clause. -/
def clauseVarCount : Clause → Nat
  | [] => 0
  | literal :: rest => max (literalIndex literal + 1) (clauseVarCount rest)

/-- One above every variable index occurring in a CNF formula. -/
def cnfVarCount : CNF → Nat
  | [] => 0
  | clause :: rest => max (clauseVarCount clause) (cnfVarCount rest)

/-- Machine-facing variable budget: the number of unary index cells in the
canonical CNF encoding.  It bounds the largest variable code but, unlike a
maximum, is obtained by a single finite-state counting pass.  Extra unused
variable slots do not affect satisfiability. -/
@[irreducible] def reductionVariableCount (formula : CNF) : Nat :=
  (encCNF formula).count .endMark

theorem literalIndex_lt_clauseVarCount
    {literal : Literal} {clause : Clause} (hmem : literal ∈ clause) :
    literalIndex literal < clauseVarCount clause := by
  induction clause with
  | nil => simp at hmem
  | cons head rest ih =>
      simp only [List.mem_cons] at hmem
      simp only [clauseVarCount]
      rcases hmem with rfl | hmem
      · exact lt_of_lt_of_le (by omega) (Nat.le_max_left _ _)
      · exact lt_of_lt_of_le (ih hmem) (Nat.le_max_right _ _)

theorem clauseVarCount_le_cnfVarCount
    {clause : Clause} {formula : CNF} (hmem : clause ∈ formula) :
    clauseVarCount clause ≤ cnfVarCount formula := by
  induction formula with
  | nil => simp at hmem
  | cons head rest ih =>
      simp only [List.mem_cons] at hmem
      simp only [cnfVarCount]
      rcases hmem with rfl | hmem
      · exact Nat.le_max_left _ _
      · exact le_trans (ih hmem) (Nat.le_max_right _ _)

theorem literalIndex_lt_cnfVarCount
    {literal : Literal} {clause : Clause} {formula : CNF}
    (hclause : clause ∈ formula) (hliteral : literal ∈ clause) :
    literalIndex literal < cnfVarCount formula :=
  lt_of_lt_of_le (literalIndex_lt_clauseVarCount hliteral)
    (clauseVarCount_le_cnfVarCount hclause)

@[simp] theorem encLit_count_endMark (literal : Literal) :
    (encLit literal).count CNFSym.endMark = literalIndex literal + 1 := by
  cases literal <;> simp [encLit, litSym, litIndex, literalIndex]

theorem clauseVarCount_le_encClause_count (clause : Clause) :
    clauseVarCount clause ≤ (encClause clause).count CNFSym.endMark := by
  induction clause with
  | nil => simp [clauseVarCount, encClause]
  | cons literal clause ih =>
      have ih' : clauseVarCount clause ≤
          (clause.flatMap encLit).count CNFSym.endMark := by
        simpa [encClause] using ih
      simp only [clauseVarCount, encClause, List.flatMap_cons,
        List.count_cons, List.count_append, encLit_count_endMark]
      omega

theorem cnfVarCount_le_reductionVariableCount (formula : CNF) :
    cnfVarCount formula ≤ reductionVariableCount formula := by
  induction formula with
  | nil => simp [cnfVarCount, reductionVariableCount, encCNF]
  | cons clause formula ih =>
      have ih' : cnfVarCount formula ≤
          (encCNF formula).count CNFSym.endMark := by
        simpa [reductionVariableCount] using ih
      have hrest : cnfVarCount formula ≤
          (formula.flatMap encClause).count CNFSym.endMark := by
        simpa [encCNF] using ih'
      simp only [cnfVarCount, reductionVariableCount, encCNF,
        List.flatMap_cons, List.count_append]
      have hclause := clauseVarCount_le_encClause_count clause
      omega

theorem literalIndex_lt_reductionVariableCount
    {literal : Literal} {clause : Clause} {formula : CNF}
    (hclause : clause ∈ formula) (hliteral : literal ∈ clause) :
    literalIndex literal < reductionVariableCount formula :=
  lt_of_lt_of_le (literalIndex_lt_cnfVarCount hclause hliteral)
    (cnfVarCount_le_reductionVariableCount formula)

end CLRS.Chapter34.SubsetSumReduction

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

end CLRS.Chapter34.SubsetSumReduction

import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.OccurrenceRowsSemantics
import Mathlib.Tactic

/-!
# Indexed occurrence rows: polynomial bounds

The quadratic envelope below is stated in the length of the actual graph-
symbol stream consumed by the fixed controller.
-/

noncomputable section

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

/-- Exact descriptor length of one occurrence. -/
theorem occurrenceLiteralDescriptor_length (literal : Literal) :
    (occurrenceLiteralDescriptor literal).length =
      occurrenceVariableCode literal + 3 := by
  cases literal <;>
    simp [occurrenceLiteralDescriptor, occurrenceVariableCode]

@[simp] private theorem occurrenceClauseDescriptor_length_cons
    (literal : Literal) (clause : Clause) :
    (occurrenceClauseDescriptor (literal :: clause)).length =
      (occurrenceLiteralDescriptor literal).length +
        (occurrenceClauseDescriptor clause).length := by
  simp [occurrenceClauseDescriptor]

private theorem occurrenceVariableCode_le_clauseDescriptor
    {literal : Literal} {clause : Clause} (hliteral : literal ∈ clause) :
    occurrenceVariableCode literal ≤
      (occurrenceClauseDescriptor clause).length := by
  induction clause with
  | nil => simp at hliteral
  | cons head clause ih =>
      simp only [List.mem_cons] at hliteral
      rw [occurrenceClauseDescriptor_length_cons]
      rcases hliteral with hliteral | hliteral
      · subst literal
        rw [occurrenceLiteralDescriptor_length]
        omega
      · have htail := ih hliteral
        omega

private theorem clause_length_le_occurrenceClauseDescriptor
    (clause : Clause) :
    clause.length ≤ (occurrenceClauseDescriptor clause).length := by
  induction clause with
  | nil => simp [occurrenceClauseDescriptor]
  | cons literal clause ih =>
      rw [occurrenceClauseDescriptor_length_cons]
      simp only [List.length_cons]
      rw [occurrenceLiteralDescriptor_length]
      omega

private theorem occurrenceRows_relabel_encCNF_length_cons
    (clause : Clause) (formula : CNF) :
    (relabel (encCNF (clause :: formula))).length =
      1 + (occurrenceClauseDescriptor clause).length +
        (relabel (encCNF formula)).length := by
  rw [occurrenceRows_relabel_encCNF_cons]
  simp only [List.length_cons, List.length_append]
  omega

/-- The literal count is bounded by the consumed descriptor-stream length. -/
theorem cnfLiteralCount_le_relabel_encCNF_length (formula : CNF) :
    cnfLiteralCount formula ≤ (relabel (encCNF formula)).length := by
  induction formula with
  | nil => simp [cnfLiteralCount, encCNF, relabel]
  | cons clause formula ih =>
      rw [occurrenceRows_relabel_encCNF_length_cons]
      rw [cnfLiteralCount_cons]
      have hclause := clause_length_le_occurrenceClauseDescriptor clause
      omega

/-- The clause count is bounded by the explicit clause markers. -/
theorem formula_length_le_relabel_encCNF_length (formula : CNF) :
    formula.length ≤ (relabel (encCNF formula)).length := by
  induction formula with
  | nil => simp [encCNF, relabel]
  | cons clause formula ih =>
      rw [occurrenceRows_relabel_encCNF_length_cons]
      simp only [List.length_cons]
      omega

/-- Every unary variable code in a formula fits in the whole consumed stream. -/
theorem occurrenceVariableCode_le_relabel_encCNF_length
    {formula : CNF} {clause : Clause} (hclause : clause ∈ formula)
    {literal : Literal} (hliteral : literal ∈ clause) :
    occurrenceVariableCode literal ≤
      (relabel (encCNF formula)).length := by
  induction formula with
  | nil => simp at hclause
  | cons head formula ih =>
      rw [occurrenceRows_relabel_encCNF_length_cons]
      simp only [List.mem_cons] at hclause
      rcases hclause with rfl | hclause
      · have := occurrenceVariableCode_le_clauseDescriptor hliteral
        omega
      · have := ih hclause
        omega

private theorem occurrenceRowsLiteralSteps_le {vertex clauseIndex bound : Nat}
    {literal : Literal} {hasBoundary : Bool}
    (hvertex : vertex ≤ bound) (hclause : clauseIndex ≤ bound)
    (hvariable : occurrenceVariableCode literal ≤ bound) :
    occurrenceRowsLiteralSteps vertex clauseIndex literal hasBoundary ≤
      17 * (bound + 1) := by
  cases literal <;> cases hasBoundary <;>
    simp [occurrenceRowsLiteralSteps, occurrenceVariableCode,
      occurrencePolarityCode] at * <;> omega

private theorem occurrenceRowsClauseSteps_le (vertex clauseIndex bound : Nat)
    (clause : Clause) (suffix : List GraphSym)
    (hvertex : vertex + clause.length ≤ bound)
    (hclause : clauseIndex ≤ bound)
    (hvariable : ∀ literal ∈ clause,
      occurrenceVariableCode literal ≤ bound) :
    occurrenceRowsClauseSteps vertex clauseIndex clause suffix ≤
      clause.length * (17 * (bound + 1)) := by
  induction clause generalizing vertex with
  | nil => simp [occurrenceRowsClauseSteps]
  | cons literal clause ih =>
      simp only [List.length_cons] at hvertex
      have hliteral := hvariable literal (by simp)
      have hvertexHead : vertex ≤ bound := by omega
      have hvertexTail : vertex + 1 + clause.length ≤ bound := by omega
      have hvariableTail : ∀ value ∈ clause,
          occurrenceVariableCode value ≤ bound := by
        intro value hvalue
        exact hvariable value (by simp [hvalue])
      have hhead := occurrenceRowsLiteralSteps_le
        (hasBoundary := occurrenceRowsHasBoundary
          (occurrenceClauseDescriptor clause ++ suffix))
        hvertexHead hclause hliteral
      have htail := ih (vertex + 1) hvertexTail hvariableTail
      simp only [occurrenceRowsClauseSteps, List.length_cons]
      calc
        occurrenceRowsLiteralSteps vertex clauseIndex literal
              (occurrenceRowsHasBoundary
                (occurrenceClauseDescriptor clause ++ suffix)) +
            occurrenceRowsClauseSteps (vertex + 1) clauseIndex clause suffix ≤
          17 * (bound + 1) + clause.length * (17 * (bound + 1)) :=
            Nat.add_le_add hhead htail
        _ = (clause.length + 1) * (17 * (bound + 1)) := by ring

private def OccurrenceVariablesBounded (formula : CNF) (bound : Nat) : Prop :=
  ∀ clause ∈ formula, ∀ literal ∈ clause,
    occurrenceVariableCode literal ≤ bound

private theorem occurrenceRowsFormulaPayloadSteps_le
    (vertex clauseIndex bound : Nat) (clause : Clause) (formula : CNF)
    (hvertex : vertex + cnfLiteralCount (clause :: formula) ≤ bound)
    (hclause : clauseIndex + formula.length ≤ bound)
    (hcurrent : ∀ literal ∈ clause,
      occurrenceVariableCode literal ≤ bound)
    (hformula : OccurrenceVariablesBounded formula bound) :
    occurrenceRowsFormulaPayloadSteps vertex clauseIndex clause formula ≤
      cnfLiteralCount (clause :: formula) * (17 * (bound + 1)) +
        2 * formula.length := by
  induction formula generalizing vertex clauseIndex clause with
  | nil =>
      have hclauseSteps := occurrenceRowsClauseSteps_le vertex clauseIndex
        bound clause [] (by simpa [cnfLiteralCount] using hvertex)
        (by simpa using hclause) hcurrent
      simpa [occurrenceRowsFormulaPayloadSteps, cnfLiteralCount] using
        hclauseSteps
  | cons next formula ih =>
      have hfirstVertex : vertex + clause.length ≤ bound := by
        rw [cnfLiteralCount_cons] at hvertex
        omega
      have hclauseIndex : clauseIndex ≤ bound := by omega
      have hfirst := occurrenceRowsClauseSteps_le vertex clauseIndex bound
        clause (relabel (encCNF (next :: formula))) hfirstVertex
        hclauseIndex hcurrent
      have hnext : ∀ literal ∈ next,
          occurrenceVariableCode literal ≤ bound := by
        intro literal hliteral
        exact hformula next (by simp) literal hliteral
      have hrest : OccurrenceVariablesBounded formula bound := by
        intro restClause hrestClause literal hliteral
        exact hformula restClause (by simp [hrestClause]) literal hliteral
      have hremaining := ih (vertex + clause.length) (clauseIndex + 1)
        next (by
          rw [cnfLiteralCount_cons] at hvertex
          omega) (by
          simp only [List.length_cons] at hclause
          omega) hnext hrest
      simp only [occurrenceRowsFormulaPayloadSteps, List.length_cons,
        cnfLiteralCount_cons]
      calc
        occurrenceRowsClauseSteps vertex clauseIndex clause
              (relabel (encCNF (next :: formula))) + 2 +
            occurrenceRowsFormulaPayloadSteps (vertex + clause.length)
              (clauseIndex + 1) next formula ≤
          clause.length * (17 * (bound + 1)) + 2 +
            (cnfLiteralCount (next :: formula) * (17 * (bound + 1)) +
              2 * formula.length) :=
            Nat.add_le_add (Nat.add_le_add_right hfirst 2) hremaining
        _ = (clause.length + cnfLiteralCount (next :: formula)) *
              (17 * (bound + 1)) + 2 * (formula.length + 1) := by ring

/-- Quadratic bound in the actual canonical descriptor-stream length. -/
theorem occurrenceRowsFormulaSteps_le_input (formula : CNF) :
    occurrenceRowsFormulaSteps formula ≤
      20 * ((relabel (encCNF formula)).length + 1) ^ 2 := by
  cases formula with
  | nil => simp [occurrenceRowsFormulaSteps]
  | cons clause formula =>
      let bound := (relabel (encCNF (clause :: formula))).length
      have hliterals : cnfLiteralCount (clause :: formula) ≤ bound :=
        cnfLiteralCount_le_relabel_encCNF_length _
      have hallClauses :=
        formula_length_le_relabel_encCNF_length (clause :: formula)
      have hclauses : formula.length ≤ bound := by
        change formula.length + 1 ≤ bound at hallClauses
        omega
      have hvariables : OccurrenceVariablesBounded
          (clause :: formula) bound := by
        intro current hcurrent literal hliteral
        exact occurrenceVariableCode_le_relabel_encCNF_length hcurrent hliteral
      have hpayload := occurrenceRowsFormulaPayloadSteps_le 0 0 bound
        clause formula (by simpa using hliterals) (by simpa using hclauses)
        (by
          intro literal hliteral
          exact hvariables clause (by simp) literal hliteral)
        (by
          intro current hcurrent literal hliteral
          exact hvariables current (by simp [hcurrent]) literal hliteral)
      simp only [occurrenceRowsFormulaSteps]
      have hlinear :
          cnfLiteralCount (clause :: formula) * (17 * (bound + 1)) +
              2 * formula.length + 1 ≤
            20 * (bound + 1) ^ 2 := by
        nlinarith
      exact (Nat.add_le_add_left hpayload 1).trans (by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlinear)

private theorem occurrenceRowsFinalClause_le_formula_length (formula : CNF) :
    occurrenceRowsFinalClause formula ≤ formula.length := by
  cases formula <;> simp [occurrenceRowsFinalClause]

/-- The complete cleanup-and-halt run remains quadratic in machine input. -/
theorem occurrenceRowsRevSteps_le_input (formula : CNF) :
    occurrenceRowsRevSteps formula ≤
      24 * ((relabel (encCNF formula)).length + 1) ^ 2 := by
  let bound := (relabel (encCNF formula)).length
  have hformula := occurrenceRowsFormulaSteps_le_input formula
  have hliterals := cnfLiteralCount_le_relabel_encCNF_length formula
  have hclauses := formula_length_le_relabel_encCNF_length formula
  have hfinal : occurrenceRowsFinalClause formula ≤ bound := by
    exact (occurrenceRowsFinalClause_le_formula_length formula).trans hclauses
  simp only [occurrenceRowsRevSteps]
  nlinarith

end TMClique
end Turing
end Chapter34
end CLRS

import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.OccurrenceRowsRows
import Mathlib.Tactic

/-!
# Indexed occurrence rows: formula simulation

This layer crosses clause markers, advances the clause counter exactly once
between adjacent clauses, and lifts the clause simulation to a whole CNF.
-/

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

/-- Relabeling a nonempty encoded CNF exposes one clause marker followed by
the current clause descriptors and the remaining encoded formula. -/
theorem occurrenceRows_relabel_encCNF_cons (clause : Clause) (formula : CNF) :
    relabel (encCNF (clause :: formula)) =
      .clauseMark :: occurrenceClauseDescriptor clause ++
        relabel (encCNF formula) := by
  rw [encCNF, List.flatMap_cons, encClause, occurrenceRows_relabel_append]
  simp [encCNF, relabel, occurrenceClauseDescriptor_eq_relabel,
    List.append_assoc]

/-- Every encoded formula suffix is a legal boundary after a literal. -/
theorem validOccurrenceSuffix_relabel_encCNF (formula : CNF) :
    ValidOccurrenceSuffix (relabel (encCNF formula)) := by
  cases formula with
  | nil => simp [encCNF, relabel, ValidOccurrenceSuffix]
  | cons clause formula =>
      rw [occurrenceRows_relabel_encCNF_cons]
      simp

/-- Exact cost after the first clause marker has already been consumed. -/
def occurrenceRowsFormulaPayloadSteps : Nat → Nat → Clause → CNF → Nat
  | vertex, clauseIndex, clause, [] =>
      occurrenceRowsClauseSteps vertex clauseIndex clause []
  | vertex, clauseIndex, clause, next :: formula =>
      occurrenceRowsClauseSteps vertex clauseIndex clause
          (relabel (encCNF (next :: formula))) + 2 +
        occurrenceRowsFormulaPayloadSteps (vertex + clause.length)
          (clauseIndex + 1) next formula

/-- Starting on the payload of a current clause, process it and every
remaining clause, hiding only final buffer and test-bit values. -/
def occurrenceRows_formulaPayloadRun (vertex clauseIndex : Nat)
    (clause : Clause) (formula : CNF)
    (buffer : Option GraphSym) (test : Bool)
    (output : List UnaryFrameSym) :
    Σ finalBuffer, Σ finalTest,
      EvalsToInTime (step occurrenceRowsRevProgram)
        (occurrenceRowsCfg (.scan true) buffer test
          (occurrenceClauseDescriptor clause ++ relabel (encCNF formula))
          output [] vertex clauseIndex 0)
        (some (occurrenceRowsCfg (.scan true) finalBuffer finalTest []
          ((encodeIndexedOccurrenceRowsFrom vertex clauseIndex
            (clause :: formula)).reverse ++ output) []
          (vertex + cnfLiteralCount (clause :: formula))
          (clauseIndex + formula.length) 0))
        (occurrenceRowsFormulaPayloadSteps vertex clauseIndex clause formula) := by
  induction formula generalizing vertex clauseIndex clause buffer test output with
  | nil =>
      let clauseRun := occurrenceRows_clauseRun vertex clauseIndex clause
        buffer test [] validOccurrenceSuffix_nil output
      refine ⟨occurrenceRowsClauseEndBuffer clause [] buffer,
        occurrenceRowsClauseEndTest clause test, ?_⟩
      simpa [encCNF, relabel, occurrenceRowsFormulaPayloadSteps,
        encodeIndexedOccurrenceRowsFrom, cnfLiteralCount,
        Nat.add_assoc] using clauseRun
  | cons next formula ih =>
      let suffix := relabel (encCNF (next :: formula))
      let first := occurrenceRows_clauseRun vertex clauseIndex clause
        buffer test suffix (validOccurrenceSuffix_relabel_encCNF _) output
      let afterClauseBuffer := occurrenceRowsClauseEndBuffer clause suffix buffer
      let afterClauseTest := occurrenceRowsClauseEndTest clause test
      have advance : EvalsToInTime (step occurrenceRowsRevProgram)
          (occurrenceRowsCfg (.scan true) afterClauseBuffer afterClauseTest
            suffix
            ((encodeIndexedClauseRowsFrom vertex clauseIndex clause).reverse ++
              output) [] (vertex + clause.length) clauseIndex 0)
          (some (occurrenceRowsCfg (.scan true) (some .clauseMark)
            afterClauseTest
            (occurrenceClauseDescriptor next ++ relabel (encCNF formula))
            ((encodeIndexedClauseRowsFrom vertex clauseIndex clause).reverse ++
              output) [] (vertex + clause.length) (clauseIndex + 1) 0)) 2 := by
        rw [show suffix = .clauseMark :: occurrenceClauseDescriptor next ++
            relabel (encCNF formula) by
          exact occurrenceRows_relabel_encCNF_cons next formula]
        exact ⟨⟨2, rfl⟩, le_rfl⟩
      rcases ih (vertex + clause.length) (clauseIndex + 1) next
          (some .clauseMark) afterClauseTest
          ((encodeIndexedClauseRowsFrom vertex clauseIndex clause).reverse ++
            output) with ⟨finalBuffer, finalTest, remaining⟩
      refine ⟨finalBuffer, finalTest, ?_⟩
      let h₁ := EvalsToInTime.trans (step occurrenceRowsRevProgram)
        (occurrenceRowsClauseSteps vertex clauseIndex clause suffix) 2
        _ _ _ first advance
      let full := EvalsToInTime.trans (step occurrenceRowsRevProgram)
        _ (occurrenceRowsFormulaPayloadSteps (vertex + clause.length)
          (clauseIndex + 1) next formula) _ _ _ h₁ remaining
      simpa [suffix, occurrenceRowsFormulaPayloadSteps,
        encodeIndexedOccurrenceRowsFrom, cnfLiteralCount,
        List.reverse_append, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

/-- Exact total formula cost, including the first clause marker. -/
def occurrenceRowsFormulaSteps : CNF → Nat
  | [] => 0
  | clause :: formula =>
      1 + occurrenceRowsFormulaPayloadSteps 0 0 clause formula

/-- Final clause-counter value of the zero-based scan. -/
def occurrenceRowsFinalClause : CNF → Nat
  | [] => 0
  | _ :: formula => formula.length

/-- The whole encoded formula is converted to reverse-order indexed rows.
The output-independent controller state is existentially hidden. -/
def occurrenceRows_formulaRun (formula : CNF) :
    Σ started, Σ finalBuffer, Σ finalTest,
      EvalsToInTime (step occurrenceRowsRevProgram)
        (initialCfg occurrenceRowsRevProgram (relabel (encCNF formula)))
        (some (occurrenceRowsCfg (.scan started) finalBuffer finalTest []
          (encodeIndexedOccurrenceRows formula).reverse []
          (cnfLiteralCount formula) (occurrenceRowsFinalClause formula) 0))
        (occurrenceRowsFormulaSteps formula) := by
  cases formula with
  | nil =>
      refine ⟨false, none, false, ?_⟩
      exact ⟨⟨0, by simp [initialCfg, occurrenceRowsCfg,
        occurrenceRowsRevProgram, encCNF, relabel, encodeIndexedOccurrenceRows,
        encodeIndexedOccurrenceRowsFrom, occurrenceRowsFinalClause,
        occurrenceRowsFormulaSteps, cnfLiteralCount]⟩, le_rfl⟩
  | cons clause formula =>
      have firstMarker : EvalsToInTime (step occurrenceRowsRevProgram)
          (initialCfg occurrenceRowsRevProgram
            (relabel (encCNF (clause :: formula))))
          (some (occurrenceRowsCfg (.scan true) (some .clauseMark) false
            (occurrenceClauseDescriptor clause ++ relabel (encCNF formula))
            [] [] 0 0 0)) 1 := by
        rw [occurrenceRows_relabel_encCNF_cons]
        exact ⟨⟨1, rfl⟩, le_rfl⟩
      rcases occurrenceRows_formulaPayloadRun 0 0 clause formula
          (some .clauseMark) false [] with
        ⟨finalBuffer, finalTest, remaining⟩
      refine ⟨true, finalBuffer, finalTest, ?_⟩
      let full := EvalsToInTime.trans (step occurrenceRowsRevProgram)
        1 (occurrenceRowsFormulaPayloadSteps 0 0 clause formula)
        _ _ _ firstMarker remaining
      simpa [initialCfg, occurrenceRowsCfg, occurrenceRowsRevProgram,
        occurrenceRowsFormulaSteps, occurrenceRowsFinalClause,
        encodeIndexedOccurrenceRows, cnfLiteralCount,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

end TMClique
end Turing
end Chapter34
end CLRS

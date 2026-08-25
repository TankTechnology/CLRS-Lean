import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.ChoiceOccurrenceLiteral
import Mathlib.Tactic

/-!
# Choice occurrence counter: one clause

The verified one-literal contract is iterated over a canonical clause.  The
machine leaves the following clause/item boundary untouched and its unary
counter becomes the exact multiplicity of the selected literal.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.SubsetSumReduction

open PolyBuilder
open _root_.CLRS.Chapter34.SubsetSumReduction

/-- Canonical batch input occupied by the literals of one clause, excluding
the leading clause marker. -/
def choiceOccurrenceClauseInput (clause : Clause) : List ChoiceBatchSym :=
  clause.flatMap choiceOccurrenceLiteralInput

@[simp] theorem choiceOccurrenceClauseInput_cons
    (literal : Literal) (clause : Clause) :
    choiceOccurrenceClauseInput (literal :: clause) =
      choiceOccurrenceLiteralInput literal ++
        choiceOccurrenceClauseInput clause := by
  simp [choiceOccurrenceClauseInput]

/-- Sum of the verified per-literal budgets. -/
def choiceOccurrenceClauseSteps (index : Nat) (clause : Clause) : Nat :=
  (clause.map (choiceOccurrenceLiteralSteps index)).sum

@[simp] theorem choiceOccurrenceClauseSteps_cons
    (index : Nat) (literal : Literal) (clause : Clause) :
    choiceOccurrenceClauseSteps index (literal :: clause) =
      choiceOccurrenceLiteralSteps index literal +
        choiceOccurrenceClauseSteps index clause := by
  simp [choiceOccurrenceClauseSteps]

private theorem choiceOccurrence_count_cons (base : Nat)
    (target literal : Literal) (clause : Clause) :
    (base + if target = literal then 1 else 0) + clause.count target =
      base + (literal :: clause).count target := by
  by_cases heq : target = literal
  · subst literal
    simp [Nat.add_comm, Nat.add_left_comm]
  · have hne : literal ≠ target := Ne.symm heq
    simp [heq, hne]

/-- Scanning a complete canonical clause computes the exact selected-literal
multiplicity and restores the following non-code boundary. -/
def choiceOccurrence_clauseRun (truth : Bool)
    (index clauseCount : Nat) (literal : Literal) (clause : Clause)
    (boundary : ChoiceBatchSym)
    (hboundary : boundary ≠ .formula .endMark)
    (tail work₁ work₂ : List ChoiceBatchSym)
    (output : List ChoiceCountSym)
    (buffer₁ buffer₂ : Option ChoiceBatchSym) (test : Bool) :
    EvalsToInTime (step (choiceOccurrenceProgram truth))
      (choiceOccurrenceCfg truth (.scan true)
        buffer₁ buffer₂ test
        (choiceOccurrenceClauseInput (literal :: clause) ++ boundary :: tail)
        output work₁ work₂ (index + 1) clauseCount 0)
      (some (choiceOccurrenceCfg truth (.scan true)
        (some boundary) buffer₂ false (boundary :: tail)
        output work₁ work₂ (index + 1)
        (clauseCount + (literal :: clause).count (itemLiteral index truth)) 0))
      (choiceOccurrenceClauseSteps index (literal :: clause)) := by
  induction clause generalizing literal clauseCount buffer₁ test with
  | nil =>
      have run := choiceOccurrence_literalRun truth index clauseCount
        literal boundary hboundary tail work₁ work₂ output
        buffer₁ buffer₂ test
      have hcount := choiceOccurrence_count_cons clauseCount
        (itemLiteral index truth) literal []
      have hcount' :
          clauseCount + (if itemLiteral index truth = literal then 1 else 0) =
            clauseCount + [literal].count (itemLiteral index truth) := by
        simpa using hcount
      rw [hcount'] at run
      simpa [choiceOccurrenceClauseInput, choiceOccurrenceClauseSteps]
        using run
  | cons next clause ih =>
      let increment := if itemLiteral index truth = literal then 1 else 0
      let nextTail : List ChoiceBatchSym :=
        .formula .varMark ::
          (List.replicate (litIndex next + 1) (.formula .endMark) ++
            (choiceOccurrenceClauseInput clause ++ boundary :: tail))
      have hnext :
          ChoiceBatchSym.formula (litSym next) ≠
            .formula .endMark := by
        cases next <;> simp [litSym]
      have firstRaw := choiceOccurrence_literalRun truth index clauseCount
        literal (.formula (litSym next)) hnext nextTail work₁ work₂
        output buffer₁ buffer₂ test
      have first : EvalsToInTime (step (choiceOccurrenceProgram truth))
          (choiceOccurrenceCfg truth (.scan true)
            buffer₁ buffer₂ test
            (choiceOccurrenceClauseInput (literal :: next :: clause) ++
              boundary :: tail)
            output work₁ work₂ (index + 1) clauseCount 0)
          (some (choiceOccurrenceCfg truth (.scan true)
            (some (.formula (litSym next))) buffer₂ false
            (choiceOccurrenceClauseInput (next :: clause) ++
              boundary :: tail)
            output work₁ work₂ (index + 1)
            (clauseCount + increment) 0))
          (choiceOccurrenceLiteralSteps index literal) := by
        simpa [choiceOccurrenceClauseInput, choiceOccurrenceLiteralInput,
          encLit, nextTail, increment, List.append_assoc]
          using firstRaw
      have rest := ih (literal := next)
        (clauseCount := clauseCount + increment)
        (buffer₁ := some (.formula (litSym next))) (test := false)
      let full := EvalsToInTime.trans (step (choiceOccurrenceProgram truth))
        (choiceOccurrenceLiteralSteps index literal)
        (choiceOccurrenceClauseSteps index (next :: clause))
        _ _ _ first rest
      have hcount := choiceOccurrence_count_cons clauseCount
        (itemLiteral index truth) literal (next :: clause)
      dsimp [increment] at full
      rw [hcount] at full
      simpa [choiceOccurrenceClauseSteps, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using full

end CLRS.Chapter34.Turing.SubsetSumReduction

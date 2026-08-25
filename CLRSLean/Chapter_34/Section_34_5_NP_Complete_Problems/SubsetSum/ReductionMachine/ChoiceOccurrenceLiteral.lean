import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.ChoiceOccurrenceDispatch
import Mathlib.Tactic

/-!
# Choice occurrence counter: one literal

The local reversible comparison is lifted to the complete canonical encoding
of a literal.  The resulting contract is phrased directly with the textbook
choice-item literal, hiding polarity markers and positive unary codes from the
later clause induction.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.SubsetSumReduction

open PolyBuilder
open _root_.CLRS.Chapter34.SubsetSumReduction

/-- Canonically encoded literal embedded in the choice-batch alphabet. -/
def choiceOccurrenceLiteralInput (literal : Literal) : List ChoiceBatchSym :=
  (encLit literal).map .formula

/-- Whether the literal polarity belongs to the fixed truth family. -/
def choiceOccurrencePolarityMatches (truth : Bool) : Literal → Bool
  | .pos _ => truth
  | .neg _ => !truth

/-- Budget for entering and completing one literal comparison. -/
def choiceOccurrenceLiteralSteps (index : Nat) (literal : Literal) : Nat :=
  choiceOccurrenceComparisonSteps (index + 1) (litIndex literal + 1) + 2

private theorem choiceOccurrence_matchCondition (truth : Bool)
    (index : Nat) (literal : Literal) :
    (choiceOccurrencePolarityMatches truth literal &&
        decide (litIndex literal + 1 = index + 1)) =
      decide (itemLiteral index truth = literal) := by
  cases literal <;> cases truth <;>
    simp [choiceOccurrencePolarityMatches, itemLiteral, litIndex] <;> omega

/-- Scanning one canonical literal restores the positive variable index and
increments the clause count exactly when this choice item represents it. -/
def choiceOccurrence_literalRun (truth : Bool)
    (index clauseCount : Nat) (literal : Literal)
    (boundary : ChoiceBatchSym)
    (hboundary : boundary ≠ .formula .endMark)
    (tail work₁ work₂ : List ChoiceBatchSym)
    (output : List ChoiceCountSym)
    (buffer₁ buffer₂ : Option ChoiceBatchSym) (test : Bool) :
    EvalsToInTime (step (choiceOccurrenceProgram truth))
      (choiceOccurrenceCfg truth (.scan true)
        buffer₁ buffer₂ test
        (choiceOccurrenceLiteralInput literal ++ boundary :: tail)
        output work₁ work₂ (index + 1) clauseCount 0)
      (some (choiceOccurrenceCfg truth (.scan true)
        (some boundary) buffer₂ false (boundary :: tail)
        output work₁ work₂ (index + 1)
        (clauseCount + if itemLiteral index truth = literal then 1 else 0) 0))
      (choiceOccurrenceLiteralSteps index literal) := by
  let polarity := choiceOccurrencePolarityMatches truth literal
  let after := choiceOccurrenceCfg truth (.compare polarity false)
    (some (.formula .varMark)) buffer₂ test
    (List.replicate (litIndex literal + 1) (.formula .endMark) ++
      boundary :: tail)
    output work₁ work₂ (index + 1) clauseCount 0
  have enter : EvalsToInTime (step (choiceOccurrenceProgram truth))
      (choiceOccurrenceCfg truth (.scan true)
        buffer₁ buffer₂ test
        (choiceOccurrenceLiteralInput literal ++ boundary :: tail)
        output work₁ work₂ (index + 1) clauseCount 0)
      (some after) 2 := by
    cases literal <;>
      exact ⟨⟨2, by
        simp [Function.iterate_succ_apply, after, polarity,
          choiceOccurrenceLiteralInput, choiceOccurrencePolarityMatches,
          encLit, litSym, flip, step, choiceOccurrenceProgram,
          choiceOccurrenceCfg, stepOp]⟩, le_rfl⟩
  have compare := choiceOccurrence_literalComparisonRun truth polarity
    (index + 1) (litIndex literal + 1) clauseCount boundary hboundary
    tail work₁ work₂ output (some (.formula .varMark)) buffer₂ test
  let full := EvalsToInTime.trans (step (choiceOccurrenceProgram truth))
    2 (choiceOccurrenceComparisonSteps (index + 1) (litIndex literal + 1))
    _ after _ enter compare
  have hmatch := choiceOccurrence_matchCondition truth index literal
  rw [hmatch] at full
  simpa [choiceOccurrenceLiteralSteps, polarity,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

end CLRS.Chapter34.Turing.SubsetSumReduction

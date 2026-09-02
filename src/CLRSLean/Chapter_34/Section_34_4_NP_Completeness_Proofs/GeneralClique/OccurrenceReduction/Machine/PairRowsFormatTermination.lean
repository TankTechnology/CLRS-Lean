import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.PairRowsFormatRows
import Mathlib.Tactic

/-!
# Formatting triangular pair rows: termination

This file closes the reverse-output builder run by consuming empty input,
clearing the row counter, and halting with every scratch component empty.
-/

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

/-- The public triangular-row input is the recursive stream used by the exact
simulation. -/
theorem pairRowsFormatInput_eq_from (count : Nat) :
    pairRowsFormatInput count =
      unaryFrameAffinePrefixRowsStreamFrom 0
        (encodeUnaryFrame (List.range 0)) count := by
  simp [pairRowsFormatInput, unaryFrameAffinePrefixRowsStream_eq_from,
    encodeUnaryFrame]

private theorem pairRows_clearRow_eval (row : Nat)
    (buffer : Option UnaryFrameSym) (test : Bool)
    (output : List CliqueSym) :
    (flip Option.bind (step pairRowsFormatRevProgram))^[row + 1]
      (some (pairRowsFormatCfg .clearRow buffer test [] output row 0)) =
      some (pairRowsFormatCfg .halt buffer false [] output 0 0) := by
  induction row generalizing test with
  | zero => rfl
  | succ row ih =>
      rw [show row + 1 + 1 = (row + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step pairRowsFormatRevProgram))^[row + 1]
          (some (pairRowsFormatCfg .clearRow buffer true [] output row 0)) = _
      exact ih true

/-- Exact full reverse-output cost on a canonical vertex-count input. -/
def pairRowsFormatRevSteps (count : Nat) : Nat :=
  pairRowsFormatRowsSteps 0 count + count + 3

/-- The complete reverse-output builder emits every normalized candidate pair
and reaches a fully cleared successful halt configuration. -/
def pairRowsFormatRev_run (count : Nat) :
    EvalsToInTime (step pairRowsFormatRevProgram)
      (initialCfg pairRowsFormatRevProgram (pairRowsFormatInput count))
      (some (haltCfg pairRowsFormatRevProgram
        (completePairEdgeStream count).reverse))
      (pairRowsFormatRevSteps count) := by
  rcases pairRowsFormat_rowsRun 0 count none false [] [] with
    ⟨finalBuffer, finalTest, rows⟩
  have rows' : EvalsToInTime (step pairRowsFormatRevProgram)
      (initialCfg pairRowsFormatRevProgram (pairRowsFormatInput count))
      (some (pairRowsFormatCfg .scan finalBuffer finalTest []
        (completePairEdgeStream count).reverse count 0))
      (pairRowsFormatRowsSteps 0 count) := by
    simpa [initialCfg, pairRowsFormatCfg, pairRowsFormatRevProgram,
      pairRowsFormatInput_eq_from, pairRowsFormatEdgesFrom_zero] using rows
  let afterScan := pairRowsFormatCfg .clearRow none finalTest []
    (completePairEdgeStream count).reverse count 0
  have scanEmpty : EvalsToInTime (step pairRowsFormatRevProgram)
      (pairRowsFormatCfg .scan finalBuffer finalTest []
        (completePairEdgeStream count).reverse count 0)
      (some afterScan) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let beforeHalt := pairRowsFormatCfg .halt none false []
    (completePairEdgeStream count).reverse 0 0
  have clearRow : EvalsToInTime (step pairRowsFormatRevProgram)
      afterScan (some beforeHalt) (count + 1) :=
    ⟨⟨count + 1, by
      simpa [afterScan, beforeHalt] using
        pairRows_clearRow_eval count none finalTest
          (completePairEdgeStream count).reverse⟩, le_rfl⟩
  have halt : EvalsToInTime (step pairRowsFormatRevProgram)
      beforeHalt
      (some (haltCfg pairRowsFormatRevProgram
        (completePairEdgeStream count).reverse)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let h₁ := EvalsToInTime.trans (step pairRowsFormatRevProgram)
    (pairRowsFormatRowsSteps 0 count) 1 _ _ _ rows' scanEmpty
  let h₂ := EvalsToInTime.trans (step pairRowsFormatRevProgram)
    _ (count + 1) _ _ _ h₁ clearRow
  let full := EvalsToInTime.trans (step pairRowsFormatRevProgram)
    _ 1 _ _ _ h₂ halt
  refine ⟨full.toEvalsTo, ?_⟩
  exact full.steps_le_m.trans (by
    simp [pairRowsFormatRevSteps]
    omega)

end TMClique
end Turing
end Chapter34
end CLRS

import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityStack
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ValidityRow

/-!
# Continuous arithmetic row-validity generation

This module instantiates the fixed whole-row controller with the exact
arithmetic one-hot, halted-agreement, stack-canonicality, and final-conjunction
data of one Cook--Levin tableau row.
-/

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder
open StateTransition

noncomputable section

/-- Exact runtime frame for all validity phases of one arithmetic tableau row. -/
noncomputable def arithmeticValidityRowFrame
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    AffineValidityRowFrame :=
  { oneHotFrames := arithmeticRawOneHotFrames tm H start rowBase
    haltedStart := arithmeticHaltedMatchStart tm H start
    haltedLeft := rowBase
    haltedRight := arithmeticNoneLabelWire tm rowBase
    tailFrame := arithmeticValidityTailFrame tm H start rowBase }

/-- Interpreting the complete runtime frame yields byte-for-byte the canonical
semantic validity stream of the arithmetic row. -/
theorem arithmeticValidityRowGateStream_eq_semantic
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    affineValidityRowGateStream
        (arithmeticValidityRowFrame tm H start rowBase) =
      validityRowGateStreamAt tm H start rowBase := by
  rw [validityRowGateStreamAt_eq_rawOneHot_append_post,
    arithmeticValidityPostOneHot_eq_haltedMatch_append_post]
  unfold arithmeticValidityRowFrame affineValidityRowGateStream
  rw [arithmeticRawOneHotFrames_gateStream,
    arithmeticValidityTailGateStream_eq_postHaltedMatch]
  simp [arithmeticValidityRowFrame, arithmeticHaltedMatchGateStream,
    List.append_assoc]

/-- One fixed program executes the complete canonical validity suffix for one
arithmetic row, with no intermediate halt. -/
noncomputable def arithmeticValidityRowRev_runFrom
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat)
    (output : List CircuitSym) :
    EvalsToInTime (step affineValidityRowRevProgram)
      (affineValidityRowLoopCfg
        (encodeAffineValidityRowFrame
          (arithmeticValidityRowFrame tm H start rowBase)) output)
      (some (haltCfg affineValidityRowRevProgram
        ((validityRowGateStreamAt tm H start rowBase).reverse ++ output)))
      (affineValidityRowRevSteps
        (arithmeticValidityRowFrame tm H start rowBase)) := by
  simpa [arithmeticValidityRowGateStream_eq_semantic] using
    affineValidityRow_run
      (arithmeticValidityRowFrame tm H start rowBase) output

/-- The concrete arithmetic row inherits the controller's explicit quadratic
bound in its exact delimiter-bearing runtime frame. -/
theorem arithmeticValidityRowRev_steps_le
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    affineValidityRowRevSteps
        (arithmeticValidityRowFrame tm H start rowBase) ≤
      2500 * (encodeAffineValidityRowFrame
        (arithmeticValidityRowFrame tm H start rowBase)).length ^ 2 + 20 :=
  affineValidityRowRev_steps_le _

end

end CLRS.Chapter34.Turing.CookLevin

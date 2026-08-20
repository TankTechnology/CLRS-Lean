import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRoutePushFrames
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRoutePopFrames
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementTerminalStackActionBounds

/-!
# Unified raw-input compiler for one selected stack action

The two concrete primitive machines are packaged behind the static selected
action type.  A one-action push-count bound supplies exactly the positivity
needed by the affine push table; pop requires no extra premise.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Raw-input value rows for one verifier-fixed selected action. -/
noncomputable def verifierTransitionSelectedStackActionValueFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (labelOffset : TransitionAffineNat)
    (action : TransitionStmtSelectedStackAction W.machine.tm k)
    (_hbound : action.pushCount W.machine.tm k ≤
      maxPushesPerStep W.machine.tm)
    (input : List Γ) : List UnaryFrameSym :=
  match action with
  | .push symbolOffsets =>
      verifierTransitionStackRoutePushValueFrames W k labelOffset
        symbolOffsets input
  | .pop heightWireOffset =>
      verifierTransitionStackRoutePopValueFrames W k labelOffset
        heightWireOffset input

/-- The unified primitive compiler produces the established routed value row
for every runtime transition seed. -/
theorem verifierTransitionSelectedStackActionValueFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (labelOffset : TransitionAffineNat)
    (action : TransitionStmtSelectedStackAction W.machine.tm k)
    (hbound : action.pushCount W.machine.tm k ≤
      maxPushesPerStep W.machine.tm)
    (input : List Γ) :
    verifierTransitionSelectedStackActionValueFrames
        W k labelOffset action hbound input =
      encodeUnaryFrameFixedPrefixDropInput
        ((verifierTransitionRowSeeds W input).map fun seed =>
          action.routeValues W.machine.tm k
            (seed.start + labelOffset.eval seed.height) seed) := by
  cases action with
  | push symbolOffsets =>
      change verifierTransitionStackRoutePushValueFrames
          W k labelOffset symbolOffsets input = _
      rw [verifierTransitionStackRoutePushValueFrames_eq]
      · rfl
      · simp [TransitionStmtSelectedStackAction.pushCount] at hbound
        omega
  | pop heightWireOffset =>
      change verifierTransitionStackRoutePopValueFrames
          W k labelOffset heightWireOffset input = _
      exact verifierTransitionStackRoutePopValueFrames_eq W k labelOffset
        heightWireOffset input

/-- One fixed polynomial-time TM2 computes any verifier-fixed selected action
from the original verifier word. -/
noncomputable def
    verifierTransitionSelectedStackActionValueFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (labelOffset : TransitionAffineNat)
    (action : TransitionStmtSelectedStackAction W.machine.tm k)
    (hbound : action.pushCount W.machine.tm k ≤
      maxPushesPerStep W.machine.tm) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionSelectedStackActionValueFrames
        W k labelOffset action hbound) := by
  cases action with
  | push symbolOffsets =>
      exact verifierTransitionStackRoutePushValueFrames_computableInPolyTime
        W k labelOffset symbolOffsets
  | pop heightWireOffset =>
      exact verifierTransitionStackRoutePopValueFrames_computableInPolyTime
        W k labelOffset heightWireOffset

end CLRS.Chapter34.Turing.CookLevin

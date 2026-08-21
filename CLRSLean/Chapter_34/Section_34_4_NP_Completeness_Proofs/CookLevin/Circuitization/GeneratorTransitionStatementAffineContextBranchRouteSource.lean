import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextBranchRoute
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionAffineSegmentRows
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxTrueArmAffineSpanFrames

/-!
# Raw-input source for branch-ending statement routes

A final statement mux returns consecutive configuration coordinates at stride
three.  This file presents that row as one fixed affine segment and thereby
reuses the generic affine-segment compiler to obtain a concrete polynomial-
time TM2 from the original verifier input.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- The complete output route of a branch-ending statement is one stride-three
affine segment. -/
noncomputable def transitionStmtBranchRouteSegment
    (tm : _root_.Turing.FinTM2)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm)
    (offset : TransitionAffineNat) : TransitionWidenedFallbackSegment :=
  transitionDispatchBranchOutputSegment tm labelOffset
    (context.gateOffset.add offset)

/-- The fixed segment spells exactly the canonical branch route. -/
theorem transitionStmtBranchRouteSegment_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm)
    (offset : TransitionAffineNat) :
    transitionWidenedFallbackSegmentValues seed
        (transitionStmtBranchRouteSegment tm labelOffset context offset) =
      transitionStmtBranchRouteValues tm seed labelOffset context offset := by
  unfold transitionStmtBranchRouteSegment
  rw [transitionDispatchBranchOutputSegment_values]
  unfold transitionProgressionFirstValues
    transitionDispatchBranchOutputProgression transitionStmtBranchRouteValues
  rw [affineUnaryTripleProgressionRows_eq_ofFn, List.map_ofFn]
  apply List.ofFn_inj.mpr
  funext coordinate
  simp [TransitionAffineNat.eval_add, TransitionAffineNat.eval_shiftInput,
    workHeight]
  omega

/-- Raw marked rows for the branch route at every verifier transition seed. -/
noncomputable def verifierTransitionStmtBranchRouteFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext W.machine.tm)
    (offset : TransitionAffineNat)
    (input : List Γ) : List UnaryFrameSym :=
  verifierTransitionAffineSegmentRowFrames W
    [transitionStmtBranchRouteSegment W.machine.tm labelOffset context offset]
    input

/-- The concrete source emits one complete branch-route frame per transition
seed. -/
theorem verifierTransitionStmtBranchRouteFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext W.machine.tm)
    (offset : TransitionAffineNat) :
    verifierTransitionStmtBranchRouteFrames W labelOffset context offset input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        encodeUnaryFrame
          (transitionStmtBranchRouteValues W.machine.tm seed labelOffset
            context offset) ++ [.frameEnd] := by
  unfold verifierTransitionStmtBranchRouteFrames
  rw [verifierTransitionAffineSegmentRowFrames_eq]
  unfold encodeUnaryFrameFixedGroupPrefixDropInput
    transitionAffineSegmentValueRows
  simp only [List.flatMap_map, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil]
  apply List.flatMap_congr
  intro seed hseed
  rw [transitionStmtBranchRouteSegment_values]
  simp

/-- A concrete fixed polynomial-time TM2 generates every semantic branch
route directly from the original verifier word. -/
noncomputable def
    verifierTransitionStmtBranchRouteFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext W.machine.tm)
    (offset : TransitionAffineNat) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionStmtBranchRouteFrames W labelOffset context offset) :=
  verifierTransitionAffineSegmentRowFrames_computableInPolyTime W
    [transitionStmtBranchRouteSegment W.machine.tm labelOffset context offset]

end CLRS.Chapter34.Turing.CookLevin

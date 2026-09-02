import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRoutePopAffine

/-!
# Concrete raw-input machine for a primitive stack pop

The separated affine segment source is followed by the fixed-position prefix
drop controller.  For the actual verifier row family, whose public tableau
height is positive, this produces exactly one complete primitive pop block per
transition seed.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Raw-input execution of one verifier-fixed primitive pop table. -/
noncomputable def verifierTransitionStackRoutePopValueFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K)
    (labelOffset heightWireOffset : TransitionAffineNat)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFrameFixedGroupPrefixDrop
    (transitionStackRoutePopDropAmounts W.machine.tm k)
    (transitionStackRoutePopDropAmounts_nonempty W.machine.tm k)
    (verifierTransitionAffineSegmentRowFrames W
      (transitionStackRoutePopSegments W.machine.tm k
        labelOffset heightWireOffset) input)

/-- The concrete machine output is exactly one primitive pop result per
runtime transition seed. -/
theorem verifierTransitionStackRoutePopValueFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K)
    (labelOffset heightWireOffset : TransitionAffineNat)
    (input : List Γ) :
    verifierTransitionStackRoutePopValueFrames
        W k labelOffset heightWireOffset input =
      encodeUnaryFrameFixedPrefixDropInput
        ((verifierTransitionRowSeeds W input).map fun seed =>
          transitionStackRoutePopBlockValues W.machine.tm seed k
            ((seed.start + labelOffset.eval seed.height) +
              heightWireOffset.eval
                (workHeight W.machine.tm seed.height))) := by
  unfold verifierTransitionStackRoutePopValueFrames
  rw [verifierTransitionAffineSegmentRowFrames_eq]
  rw [rewriteUnaryFrameFixedGroupPrefixDrop_groups]
  · unfold encodeUnaryFrameFixedGroupPrefixDropOutput
      encodeUnaryFrameFixedPrefixDropInput
    rw [List.flatMap_map, List.flatMap_map]
    apply List.flatMap_congr
    intro seed hseed
    congr 1
    rw [transitionStackRoutePopSegments_values]
    rw [verifierTransitionRowSeeds_height_eq W input seed hseed]
    exact verifierHeight_eval_pos W input.length
  · intro group hgroup
    rw [List.mem_map] at hgroup
    obtain ⟨seed, hseed, rfl⟩ := hgroup
    unfold transitionAffineSegmentValueRows
    rw [List.length_map,
      transitionStackRoutePopSegments_length,
      transitionStackRoutePopDropAmounts_length]

/-- One fixed polynomial-time TM2 computes the complete primitive pop row
from the original verifier input. -/
noncomputable def
    verifierTransitionStackRoutePopValueFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K)
    (labelOffset heightWireOffset : TransitionAffineNat) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionStackRoutePopValueFrames
        W k labelOffset heightWireOffset) := by
  let source :=
    verifierTransitionAffineSegmentRowFrames_computableInPolyTime W
      (transitionStackRoutePopSegments W.machine.tm k
        labelOffset heightWireOffset)
  let transformed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch source
      (unaryFrameFixedGroupPrefixDrop_computableInPolyTime
        (transitionStackRoutePopDropAmounts W.machine.tm k)
        (transitionStackRoutePopDropAmounts_nonempty W.machine.tm k))
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => rewriteUnaryFrameFixedGroupPrefixDrop
      (transitionStackRoutePopDropAmounts W.machine.tm k)
      (transitionStackRoutePopDropAmounts_nonempty W.machine.tm k)
      (verifierTransitionAffineSegmentRowFrames W
        (transitionStackRoutePopSegments W.machine.tm k
          labelOffset heightWireOffset) input))
  simpa [Function.comp_def] using Classical.choice transformed

end CLRS.Chapter34.Turing.CookLevin

import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRoutePushAffine

/-!
# Concrete raw-input machine for a primitive stack push

The generic affine-segment compiler executes the complete push segment table
as one marked row per transition seed.  Its output is the exact flattened
primitive push route, including both inserted prefixes and shortened suffixes.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Raw-input execution of one verifier-fixed primitive push table. -/
noncomputable def verifierTransitionStackRoutePushValueFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K)
    (labelOffset : TransitionAffineNat)
    (symbolOffsets :
      Fin (reachableAlphabet W.machine.tm k).card → TransitionAffineNat)
    (input : List Γ) : List UnaryFrameSym :=
  verifierTransitionAffineSegmentValueFrames W
    (transitionStackRoutePushSegments W.machine.tm k
      labelOffset symbolOffsets)
    (transitionStackRoutePushSegments_nonempty W.machine.tm k
      labelOffset symbolOffsets)
    input

/-- At positive push slack, the concrete machine output is exactly one
primitive push result per runtime transition seed. -/
theorem verifierTransitionStackRoutePushValueFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K)
    (labelOffset : TransitionAffineNat)
    (symbolOffsets :
      Fin (reachableAlphabet W.machine.tm k).card → TransitionAffineNat)
    (hpush : 0 < maxPushesPerStep W.machine.tm)
    (input : List Γ) :
    verifierTransitionStackRoutePushValueFrames
        W k labelOffset symbolOffsets input =
      encodeUnaryFrameFixedPrefixDropInput
        ((verifierTransitionRowSeeds W input).map fun seed =>
          transitionStackRoutePushBlockValues W.machine.tm seed k
            (fun target =>
              (seed.start + labelOffset.eval seed.height) +
                (symbolOffsets target).eval
                  (workHeight W.machine.tm seed.height))) := by
  unfold verifierTransitionStackRoutePushValueFrames
  rw [verifierTransitionAffineSegmentValueFrames_eq]
  congr 1
  apply List.map_congr_left
  intro seed hseed
  exact transitionStackRoutePushSegments_values W.machine.tm seed k
    labelOffset symbolOffsets hpush

/-- One fixed polynomial-time TM2 computes the complete primitive push row
from the original verifier input. -/
noncomputable def
    verifierTransitionStackRoutePushValueFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K)
    (labelOffset : TransitionAffineNat)
    (symbolOffsets :
      Fin (reachableAlphabet W.machine.tm k).card → TransitionAffineNat) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionStackRoutePushValueFrames
        W k labelOffset symbolOffsets) := by
  exact verifierTransitionAffineSegmentValueFrames_computableInPolyTime W
    (transitionStackRoutePushSegments W.machine.tm k
      labelOffset symbolOffsets)
    (transitionStackRoutePushSegments_nonempty W.machine.tm k
      labelOffset symbolOffsets)

end CLRS.Chapter34.Turing.CookLevin

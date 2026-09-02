import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionAffineOrFrames
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Statement

/-!
# Complete affine stack-pop statement phases

The statement controller uses the seed-free OR component for stack pop.  A
zero-height stack contributes no OR payload, while every positive-height stack
contributes one frame.  This module serializes either fixed symbolic family
together with the pop tag and proves that one fixed TM2 emits the complete
phase directly from the original verifier input.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Affine fields for a complete tagged pop phase. -/
def transitionAffinePopPhaseFieldForms
    (frames : List TransitionAffineOrPairForm) :
    List AffineUnaryTripleForm :=
  [transitionZeroForm, transitionZeroForm, transitionZeroForm] ++
    transitionAffineOrFieldForms frames

/-- Fixed delimiter table for a complete tagged pop phase. -/
def transitionAffinePopPhaseDelimiters
    (frames : List TransitionAffineOrPairForm) : List UnaryFrameSym :=
  [.tick, .frameEnd, .tick] ++ transitionAffineOrDelimiters frames

theorem transitionAffinePopPhase_lengths
    (frames : List TransitionAffineOrPairForm) :
    (transitionAffinePopPhaseFieldForms frames).length =
      (transitionAffinePopPhaseDelimiters frames).length := by
  simp [transitionAffinePopPhaseFieldForms,
    transitionAffinePopPhaseDelimiters]

theorem transitionAffinePopPhaseDelimiters_nonempty
    (frames : List TransitionAffineOrPairForm) :
    0 < (transitionAffinePopPhaseDelimiters frames).length := by
  simp [transitionAffinePopPhaseDelimiters]

/-- Fixed-delimiter evaluation is exactly the official complete pop phase,
including the empty payload used at stack height zero. -/
theorem transitionAffinePopPhase_fixed_encoding
    (frames : List TransitionAffineOrPairForm)
    (seed : AffineUnaryTripleSeed) :
    encodeUnaryFrameWithFixedDelimiters
        (affineUnaryTripleMap
          (transitionAffinePopPhaseFieldForms frames) seed)
        (transitionAffinePopPhaseDelimiters frames) =
      encodeAffineStmtControllerPhase
        (.pop (frames.map fun frame => frame.eval seed)) := by
  rw [show transitionAffinePopPhaseFieldForms frames =
      [transitionZeroForm, transitionZeroForm, transitionZeroForm] ++
        transitionAffineOrFieldForms frames by rfl]
  rw [affineUnaryTripleMap, List.map_append]
  rw [show transitionAffinePopPhaseDelimiters frames =
      [.tick, .frameEnd, .tick] ++ transitionAffineOrDelimiters frames by rfl]
  rw [encodeUnaryFrameWithFixedDelimiters_append _ _ _ _ (by simp)]
  change _ ++ encodeUnaryFrameWithFixedDelimiters
      (affineUnaryTripleMap (transitionAffineOrFieldForms frames) seed)
      (transitionAffineOrDelimiters frames) = _
  rw [transitionAffineOr_fixed_encoding]
  simp [encodeAffineStmtControllerPhase, affineStmtPhaseTagCode,
    affineStmtPhasePayload, transitionZeroForm,
    affineUnaryTripleFormValue, encodeUnaryFrameWithFixedDelimiters]

/-- One transition seed's complete pop phase has the expected semantic
payload. -/
theorem transitionAffinePopPhaseRow_eq_encoding
    (frames : List TransitionAffineOrPairForm)
    (seed : TransitionRowSeed) :
    transitionAffineDelimitedMapRow
        (transitionAffinePopPhaseFieldForms frames)
        (transitionAffinePopPhaseDelimiters frames) seed =
      encodeAffineStmtControllerPhase
        (.pop (frames.map fun frame =>
          frame.eval (transitionTailAffineSeed seed))) := by
  unfold transitionAffineDelimitedMapRow
  exact transitionAffinePopPhase_fixed_encoding frames
    (transitionTailAffineSeed seed)

/-- Raw-input target containing one complete tagged pop phase per transition
row. -/
noncomputable def verifierTransitionAffinePopPhase
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (frames : List TransitionAffineOrPairForm)
    (input : List Γ) : List UnaryFrameSym :=
  verifierTransitionAffineDelimitedMapFrames W
    (transitionAffinePopPhaseFieldForms frames)
    (transitionAffinePopPhaseDelimiters frames)
    (transitionAffinePopPhaseDelimiters_nonempty frames) input

/-- Exact row-major semantics of the complete pop-phase compiler. -/
theorem verifierTransitionAffinePopPhase_eq_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (frames : List TransitionAffineOrPairForm)
    (input : List Γ) :
    verifierTransitionAffinePopPhase W frames input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        encodeAffineStmtControllerPhase
          (.pop (frames.map fun frame =>
            frame.eval (transitionTailAffineSeed seed))) := by
  unfold verifierTransitionAffinePopPhase
  rw [verifierTransitionAffineDelimitedMapFrames_eq_rows W
    (transitionAffinePopPhaseFieldForms frames)
    (transitionAffinePopPhaseDelimiters frames)
    (transitionAffinePopPhaseDelimiters_nonempty frames)
    (transitionAffinePopPhase_lengths frames)]
  apply List.flatMap_congr
  intro seed hseed
  exact transitionAffinePopPhaseRow_eq_encoding frames seed

/-- One fixed polynomial-time TM2 emits the complete tagged pop phase
directly from the original verifier input. -/
noncomputable def verifierTransitionAffinePopPhase_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (frames : List TransitionAffineOrPairForm) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionAffinePopPhase W frames) :=
  verifierTransitionAffineDelimitedMapFrames_computableInPolyTime W
    (transitionAffinePopPhaseFieldForms frames)
    (transitionAffinePopPhaseDelimiters frames)
    (transitionAffinePopPhaseDelimiters_nonempty frames)

end CLRS.Chapter34.Turing.CookLevin

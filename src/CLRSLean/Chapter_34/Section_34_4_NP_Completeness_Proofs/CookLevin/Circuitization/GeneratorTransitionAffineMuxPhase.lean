import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionAffinePopPhase

/-!
# Complete affine finite-multiplexer statement phases

Every mux coordinate carries its two source wires and the three fresh gate
coordinates following the shared selector negation.  This module represents
all of those operands by affine transition-seed forms, verifies the exact
delimiter-bearing serialization, and supplies a fixed polynomial-time TM2
from the original verifier input to complete tagged mux phases.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Symbolic affine operands of one finite-mux coordinate. -/
structure TransitionAffineMuxPairForm where
  whenTrue : AffineUnaryTripleForm
  whenFalse : AffineUnaryTripleForm
  selector : AffineUnaryTripleForm
  selectorNot : AffineUnaryTripleForm
  trueArm : AffineUnaryTripleForm
  falseArm : AffineUnaryTripleForm
deriving DecidableEq, Repr

/-- Evaluate one symbolic mux coordinate on a transition seed. -/
def TransitionAffineMuxPairForm.eval
    (frame : TransitionAffineMuxPairForm)
    (seed : AffineUnaryTripleSeed) : AffineMuxFinPairFrame :=
  { whenTrue := affineUnaryTripleFormValue frame.whenTrue seed
    whenFalse := affineUnaryTripleFormValue frame.whenFalse seed
    selector := affineUnaryTripleFormValue frame.selector seed
    selectorNot := affineUnaryTripleFormValue frame.selectorNot seed
    trueArm := affineUnaryTripleFormValue frame.trueArm seed
    falseArm := affineUnaryTripleFormValue frame.falseArm seed }

/-- Thirteen affine fields encoding one explicit mux coordinate. -/
def transitionAffineMuxPairFieldForms
    (frame : TransitionAffineMuxPairForm) :
    List AffineUnaryTripleForm :=
  [ transitionZeroForm,
    frame.whenTrue, transitionZeroForm, frame.selector, transitionZeroForm,
    frame.whenFalse, transitionZeroForm, frame.selectorNot, transitionZeroForm,
    frame.trueArm, transitionZeroForm,
      transitionAffineFormAddConst frame.falseArm 1, transitionZeroForm ]

/-- Fixed delimiter table for one explicit mux coordinate. -/
def transitionAffineMuxPairDelimiters : List UnaryFrameSym :=
  [ .frameEnd,
    .separator, .separator, .separator, .frameEnd,
    .separator, .separator, .separator, .frameEnd,
    .separator, .separator, .separator, .frameEnd ]

@[simp] theorem transitionAffineMuxPairFieldForms_length
    (frame : TransitionAffineMuxPairForm) :
    (transitionAffineMuxPairFieldForms frame).length = 13 := rfl

@[simp] theorem transitionAffineMuxPairDelimiters_length :
    transitionAffineMuxPairDelimiters.length = 13 := rfl

/-- One symbolic coordinate serializes to the official concrete coordinate
frame after evaluation. -/
theorem transitionAffineMuxPair_fixed_encoding
    (frame : TransitionAffineMuxPairForm)
    (seed : AffineUnaryTripleSeed) :
    encodeUnaryFrameWithFixedDelimiters
        (affineUnaryTripleMap
          (transitionAffineMuxPairFieldForms frame) seed)
        transitionAffineMuxPairDelimiters =
      encodeAffineMuxFinPairFrame (frame.eval seed) := by
  simp only [transitionAffineMuxPairFieldForms, affineUnaryTripleMap,
    List.map_cons, List.map_nil]
  rw [transitionAffineFormAddConst_value]
  simp [transitionAffineMuxPairDelimiters,
    TransitionAffineMuxPairForm.eval, transitionZeroForm,
    affineUnaryTripleFormValue, encodeUnaryFrameWithFixedDelimiters,
    encodeAffineMuxFinPairFrame, encodeUnaryFrame, encodeUnaryFrameBlock,
    List.append_assoc]

/-- Flattened affine field table for a mux coordinate family, excluding the
shared selector header. -/
def transitionAffineMuxPairFamilyFieldForms
    (frames : List TransitionAffineMuxPairForm) :
    List AffineUnaryTripleForm :=
  frames.flatMap transitionAffineMuxPairFieldForms

/-- Flattened delimiter table for a mux coordinate family. -/
def transitionAffineMuxPairFamilyDelimiters
    (frames : List TransitionAffineMuxPairForm) : List UnaryFrameSym :=
  frames.flatMap fun _ => transitionAffineMuxPairDelimiters

@[simp] theorem transitionAffineMuxPairFamilyFieldForms_length
    (frames : List TransitionAffineMuxPairForm) :
    (transitionAffineMuxPairFamilyFieldForms frames).length =
      13 * frames.length := by
  simp [transitionAffineMuxPairFamilyFieldForms]
  omega

@[simp] theorem transitionAffineMuxPairFamilyDelimiters_length
    (frames : List TransitionAffineMuxPairForm) :
    (transitionAffineMuxPairFamilyDelimiters frames).length =
      13 * frames.length := by
  simp [transitionAffineMuxPairFamilyDelimiters]
  omega

private theorem transitionAffineMuxPairFamily_fixed_encoding
    (frames : List TransitionAffineMuxPairForm)
    (seed : AffineUnaryTripleSeed) :
    encodeUnaryFrameWithFixedDelimiters
        (affineUnaryTripleMap
          (transitionAffineMuxPairFamilyFieldForms frames) seed)
        (transitionAffineMuxPairFamilyDelimiters frames) =
      frames.flatMap fun frame =>
        encodeAffineMuxFinPairFrame (frame.eval seed) := by
  induction frames with
  | nil => rfl
  | cons frame frames ih =>
      rw [show transitionAffineMuxPairFamilyFieldForms (frame :: frames) =
          transitionAffineMuxPairFieldForms frame ++
            transitionAffineMuxPairFamilyFieldForms frames by rfl]
      rw [affineUnaryTripleMap, List.map_append]
      rw [show transitionAffineMuxPairFamilyDelimiters (frame :: frames) =
          transitionAffineMuxPairDelimiters ++
            transitionAffineMuxPairFamilyDelimiters frames by rfl]
      rw [encodeUnaryFrameWithFixedDelimiters_append _ _ _ _ (by simp)]
      change encodeUnaryFrameWithFixedDelimiters
          (affineUnaryTripleMap
            (transitionAffineMuxPairFieldForms frame) seed)
          transitionAffineMuxPairDelimiters ++
        encodeUnaryFrameWithFixedDelimiters
          (affineUnaryTripleMap
            (transitionAffineMuxPairFamilyFieldForms frames) seed)
          (transitionAffineMuxPairFamilyDelimiters frames) = _
      rw [transitionAffineMuxPair_fixed_encoding, ih]
      rfl

/-- Affine fields for the selector header followed by every mux coordinate. -/
def transitionAffineMuxFramesFieldForms
    (selector : AffineUnaryTripleForm)
    (frames : List TransitionAffineMuxPairForm) :
    List AffineUnaryTripleForm :=
  [transitionZeroForm, transitionZeroForm, selector, transitionZeroForm] ++
    transitionAffineMuxPairFamilyFieldForms frames

/-- Fixed delimiters for the selector header and mux coordinates. -/
def transitionAffineMuxFramesDelimiters
    (frames : List TransitionAffineMuxPairForm) : List UnaryFrameSym :=
  [.separator, .separator, .separator, .frameEnd] ++
    transitionAffineMuxPairFamilyDelimiters frames

theorem transitionAffineMuxFrames_lengths
    (selector : AffineUnaryTripleForm)
    (frames : List TransitionAffineMuxPairForm) :
    (transitionAffineMuxFramesFieldForms selector frames).length =
      (transitionAffineMuxFramesDelimiters frames).length := by
  simp [transitionAffineMuxFramesFieldForms,
    transitionAffineMuxFramesDelimiters]

/-- Symbolic selector header and coordinates serialize exactly as the
established finite-mux controller input. -/
theorem transitionAffineMuxFrames_fixed_encoding
    (selector : AffineUnaryTripleForm)
    (frames : List TransitionAffineMuxPairForm)
    (seed : AffineUnaryTripleSeed) :
    encodeUnaryFrameWithFixedDelimiters
        (affineUnaryTripleMap
          (transitionAffineMuxFramesFieldForms selector frames) seed)
        (transitionAffineMuxFramesDelimiters frames) =
      encodeAffineMuxFinFrames
        (affineUnaryTripleFormValue selector seed)
        (frames.map fun frame => frame.eval seed) := by
  rw [show transitionAffineMuxFramesFieldForms selector frames =
      [transitionZeroForm, transitionZeroForm, selector, transitionZeroForm] ++
        transitionAffineMuxPairFamilyFieldForms frames by rfl]
  rw [affineUnaryTripleMap, List.map_append]
  rw [show transitionAffineMuxFramesDelimiters frames =
      [.separator, .separator, .separator, .frameEnd] ++
        transitionAffineMuxPairFamilyDelimiters frames by rfl]
  rw [encodeUnaryFrameWithFixedDelimiters_append _ _ _ _ (by simp)]
  change _ ++ encodeUnaryFrameWithFixedDelimiters
      (affineUnaryTripleMap
        (transitionAffineMuxPairFamilyFieldForms frames) seed)
      (transitionAffineMuxPairFamilyDelimiters frames) = _
  rw [transitionAffineMuxPairFamily_fixed_encoding]
  simp [encodeAffineMuxFinFrames, encodeAffineMuxFinHeader,
    transitionZeroForm, affineUnaryTripleFormValue,
    encodeUnaryFrameWithFixedDelimiters, encodeUnaryFrame,
    encodeUnaryFrameBlock, List.append_assoc]
  rw [List.flatMap_map]

/-- Affine fields for a complete tagged mux phase. -/
def transitionAffineMuxPhaseFieldForms
    (selector : AffineUnaryTripleForm)
    (frames : List TransitionAffineMuxPairForm) :
    List AffineUnaryTripleForm :=
  [transitionZeroForm, transitionZeroForm, transitionZeroForm] ++
    transitionAffineMuxFramesFieldForms selector frames

/-- Fixed delimiter table for a complete tagged mux phase. -/
def transitionAffineMuxPhaseDelimiters
    (frames : List TransitionAffineMuxPairForm) : List UnaryFrameSym :=
  [.tick, .frameEnd, .frameEnd] ++
    transitionAffineMuxFramesDelimiters frames

theorem transitionAffineMuxPhase_lengths
    (selector : AffineUnaryTripleForm)
    (frames : List TransitionAffineMuxPairForm) :
    (transitionAffineMuxPhaseFieldForms selector frames).length =
      (transitionAffineMuxPhaseDelimiters frames).length := by
  simp [transitionAffineMuxPhaseFieldForms,
    transitionAffineMuxPhaseDelimiters, transitionAffineMuxFrames_lengths]

theorem transitionAffineMuxPhaseDelimiters_nonempty
    (frames : List TransitionAffineMuxPairForm) :
    0 < (transitionAffineMuxPhaseDelimiters frames).length := by
  simp [transitionAffineMuxPhaseDelimiters]

/-- Fixed-delimiter evaluation is exactly the official complete mux phase. -/
theorem transitionAffineMuxPhase_fixed_encoding
    (selector : AffineUnaryTripleForm)
    (frames : List TransitionAffineMuxPairForm)
    (seed : AffineUnaryTripleSeed) :
    encodeUnaryFrameWithFixedDelimiters
        (affineUnaryTripleMap
          (transitionAffineMuxPhaseFieldForms selector frames) seed)
        (transitionAffineMuxPhaseDelimiters frames) =
      encodeAffineStmtControllerPhase
        (.mux (affineUnaryTripleFormValue selector seed)
          (frames.map fun frame => frame.eval seed)) := by
  rw [show transitionAffineMuxPhaseFieldForms selector frames =
      [transitionZeroForm, transitionZeroForm, transitionZeroForm] ++
        transitionAffineMuxFramesFieldForms selector frames by rfl]
  rw [affineUnaryTripleMap, List.map_append]
  rw [show transitionAffineMuxPhaseDelimiters frames =
      [.tick, .frameEnd, .frameEnd] ++
        transitionAffineMuxFramesDelimiters frames by rfl]
  rw [encodeUnaryFrameWithFixedDelimiters_append _ _ _ _ (by simp)]
  change _ ++ encodeUnaryFrameWithFixedDelimiters
      (affineUnaryTripleMap
        (transitionAffineMuxFramesFieldForms selector frames) seed)
      (transitionAffineMuxFramesDelimiters frames) = _
  rw [transitionAffineMuxFrames_fixed_encoding]
  simp [encodeAffineStmtControllerPhase, affineStmtPhaseTagCode,
    affineStmtPhasePayload, transitionZeroForm,
    affineUnaryTripleFormValue, encodeUnaryFrameWithFixedDelimiters]

/-- One transition seed's complete mux phase has the expected semantic
payload. -/
theorem transitionAffineMuxPhaseRow_eq_encoding
    (selector : AffineUnaryTripleForm)
    (frames : List TransitionAffineMuxPairForm)
    (seed : TransitionRowSeed) :
    transitionAffineDelimitedMapRow
        (transitionAffineMuxPhaseFieldForms selector frames)
        (transitionAffineMuxPhaseDelimiters frames) seed =
      encodeAffineStmtControllerPhase
        (.mux
          (affineUnaryTripleFormValue selector (transitionTailAffineSeed seed))
          (frames.map fun frame =>
            frame.eval (transitionTailAffineSeed seed))) := by
  unfold transitionAffineDelimitedMapRow
  exact transitionAffineMuxPhase_fixed_encoding selector frames
    (transitionTailAffineSeed seed)

/-- Raw-input target containing one complete tagged mux phase per transition
row. -/
noncomputable def verifierTransitionAffineMuxPhase
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (selector : AffineUnaryTripleForm)
    (frames : List TransitionAffineMuxPairForm)
    (input : List Γ) : List UnaryFrameSym :=
  verifierTransitionAffineDelimitedMapFrames W
    (transitionAffineMuxPhaseFieldForms selector frames)
    (transitionAffineMuxPhaseDelimiters frames)
    (transitionAffineMuxPhaseDelimiters_nonempty frames) input

/-- Exact row-major semantics of the complete mux-phase compiler. -/
theorem verifierTransitionAffineMuxPhase_eq_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (selector : AffineUnaryTripleForm)
    (frames : List TransitionAffineMuxPairForm)
    (input : List Γ) :
    verifierTransitionAffineMuxPhase W selector frames input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        encodeAffineStmtControllerPhase
          (.mux
            (affineUnaryTripleFormValue selector
              (transitionTailAffineSeed seed))
            (frames.map fun frame =>
              frame.eval (transitionTailAffineSeed seed))) := by
  unfold verifierTransitionAffineMuxPhase
  rw [verifierTransitionAffineDelimitedMapFrames_eq_rows W
    (transitionAffineMuxPhaseFieldForms selector frames)
    (transitionAffineMuxPhaseDelimiters frames)
    (transitionAffineMuxPhaseDelimiters_nonempty frames)
    (transitionAffineMuxPhase_lengths selector frames)]
  apply List.flatMap_congr
  intro seed hseed
  exact transitionAffineMuxPhaseRow_eq_encoding selector frames seed

/-- One fixed polynomial-time TM2 emits the complete tagged mux phase
directly from the original verifier input. -/
noncomputable def verifierTransitionAffineMuxPhase_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (selector : AffineUnaryTripleForm)
    (frames : List TransitionAffineMuxPairForm) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionAffineMuxPhase W selector frames) :=
  verifierTransitionAffineDelimitedMapFrames_computableInPolyTime W
    (transitionAffineMuxPhaseFieldForms selector frames)
    (transitionAffineMuxPhaseDelimiters frames)
    (transitionAffineMuxPhaseDelimiters_nonempty frames)

end CLRS.Chapter34.Turing.CookLevin

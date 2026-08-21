import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionAffineDelimitedMap
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OrFin

/-!
# Affine OR-frame transition sources

The statement controller uses the same five-field byte protocol for one-hot
maps, predicates, and pop folds.  This module packages one fixed list of
symbolic affine OR frames, proves that evaluation commutes with its canonical
serialization, and connects the result to the raw-input delimiter compiler.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- A symbolic OR frame whose two wire operands are affine in the runtime
transition seed. -/
structure TransitionAffineOrPairForm where
  left : AffineUnaryTripleForm
  right : AffineUnaryTripleForm
deriving DecidableEq, Repr

/-- Add a verifier-fixed natural offset to an affine triple form. -/
def transitionAffineFormAddConst (form : AffineUnaryTripleForm)
    (offset : Nat) : AffineUnaryTripleForm :=
  { form with constant := form.constant + offset }

@[simp] theorem transitionAffineFormAddConst_value
    (form : AffineUnaryTripleForm) (offset : Nat)
    (seed : AffineUnaryTripleSeed) :
    affineUnaryTripleFormValue (transitionAffineFormAddConst form offset)
        seed =
      affineUnaryTripleFormValue form seed + offset := by
  simp [transitionAffineFormAddConst, affineUnaryTripleFormValue]
  omega

/-- Concrete frame obtained by evaluating both symbolic operands. -/
def TransitionAffineOrPairForm.eval
    (frame : TransitionAffineOrPairForm) (seed : AffineUnaryTripleSeed) :
    AffineOrFinPairFrame :=
  { left := affineUnaryTripleFormValue frame.left seed
    right := affineUnaryTripleFormValue frame.right seed }

/-- Five affine fields whose fixed-delimiter encoding is one OR frame. -/
def transitionAffineOrPairFieldForms
    (frame : TransitionAffineOrPairForm) : List AffineUnaryTripleForm :=
  [transitionZeroForm, frame.left, transitionZeroForm,
    transitionAffineFormAddConst frame.right 1, transitionZeroForm]

/-- One delimiter block for the OR loader's five fields. -/
def transitionAffineOrPairDelimiterTable : List UnaryFrameSym :=
  [.frameEnd, .separator, .separator, .separator, .frameEnd]

@[simp] theorem transitionAffineOrPairDelimiterTable_length :
    transitionAffineOrPairDelimiterTable.length = 5 := rfl

/-- Flattened affine field table for a fixed family of OR frames. -/
def transitionAffineOrFieldForms
    (frames : List TransitionAffineOrPairForm) :
    List AffineUnaryTripleForm :=
  frames.flatMap transitionAffineOrPairFieldForms

/-- Matching flattened delimiter table for a fixed OR-frame family. -/
def transitionAffineOrDelimiters
    (frames : List TransitionAffineOrPairForm) : List UnaryFrameSym :=
  frames.flatMap fun _ => transitionAffineOrPairDelimiterTable

@[simp] theorem transitionAffineOrFieldForms_length
    (frames : List TransitionAffineOrPairForm) :
    (transitionAffineOrFieldForms frames).length = 5 * frames.length := by
  simp [transitionAffineOrFieldForms, transitionAffineOrPairFieldForms]
  omega

@[simp] theorem transitionAffineOrDelimiters_length
    (frames : List TransitionAffineOrPairForm) :
    (transitionAffineOrDelimiters frames).length = 5 * frames.length := by
  simp [transitionAffineOrDelimiters]
  omega

theorem transitionAffineOrDelimiters_nonempty
    {frames : List TransitionAffineOrPairForm} (hnonempty : frames ≠ []) :
    0 < (transitionAffineOrDelimiters frames).length := by
  rw [transitionAffineOrDelimiters_length]
  have : 0 < frames.length := List.length_pos_iff.mpr hnonempty
  omega

/-- Evaluating the flattened symbolic table yields the five loader values of
the evaluated concrete frame family. -/
theorem transitionAffineOrFieldForms_value
    (frames : List TransitionAffineOrPairForm)
    (seed : AffineUnaryTripleSeed) :
    affineUnaryTripleMap (transitionAffineOrFieldForms frames) seed =
      frames.flatMap fun frame =>
        let concrete := frame.eval seed
        [0, concrete.left, 0, concrete.right + 1, 0] := by
  induction frames with
  | nil => rfl
  | cons frame frames ih =>
      rw [show transitionAffineOrFieldForms (frame :: frames) =
          transitionAffineOrPairFieldForms frame ++
            transitionAffineOrFieldForms frames by rfl]
      rw [affineUnaryTripleMap, List.map_append]
      change _ ++ affineUnaryTripleMap
          (transitionAffineOrFieldForms frames) seed = _
      rw [ih]
      simp only [transitionAffineOrPairFieldForms,
        TransitionAffineOrPairForm.eval,
        List.map_cons, List.map_nil, List.flatMap_cons]
      rw [transitionAffineFormAddConst_value]
      simp [transitionZeroForm, affineUnaryTripleFormValue]

/-- Fixed-delimiter evaluation of a symbolic frame table is exactly the
canonical concrete OR-frame encoding. -/
theorem transitionAffineOr_fixed_encoding
    (frames : List TransitionAffineOrPairForm)
    (seed : AffineUnaryTripleSeed) :
    encodeUnaryFrameWithFixedDelimiters
        (affineUnaryTripleMap (transitionAffineOrFieldForms frames) seed)
        (transitionAffineOrDelimiters frames) =
      encodeAffineOrFinFrames (frames.map fun frame => frame.eval seed) := by
  induction frames with
  | nil => rfl
  | cons frame frames ih =>
      rw [show transitionAffineOrFieldForms (frame :: frames) =
          transitionAffineOrPairFieldForms frame ++
            transitionAffineOrFieldForms frames by rfl]
      rw [affineUnaryTripleMap]
      rw [List.map_append]
      rw [show transitionAffineOrDelimiters (frame :: frames) =
          transitionAffineOrPairDelimiterTable ++
            transitionAffineOrDelimiters frames by rfl]
      rw [encodeUnaryFrameWithFixedDelimiters_append _ _ _ _
        (by simp [transitionAffineOrPairFieldForms])]
      change _ ++ encodeUnaryFrameWithFixedDelimiters
          (affineUnaryTripleMap (transitionAffineOrFieldForms frames) seed)
          (transitionAffineOrDelimiters frames) = _
      rw [ih]
      simp only [transitionAffineOrPairFieldForms, List.map_cons,
        List.map_nil]
      rw [transitionAffineFormAddConst_value]
      simp [transitionAffineOrPairDelimiterTable,
        TransitionAffineOrPairForm.eval, transitionZeroForm,
        affineUnaryTripleFormValue, encodeUnaryFrameWithFixedDelimiters,
        encodeAffineOrFinFrames,
        encodeAffineOrFinPairFrame, encodeUnaryFrame, encodeUnaryFrameBlock,
        List.append_assoc]

/-- One transition row's affine OR-frame family is byte-for-byte the
canonical input expected by the verified OR controller. -/
theorem transitionAffineOrRow_eq_encoding
    (frames : List TransitionAffineOrPairForm)
    (seed : TransitionRowSeed) :
    transitionAffineDelimitedMapRow
        (transitionAffineOrFieldForms frames)
        (transitionAffineOrDelimiters frames) seed =
      encodeAffineOrFinFrames
        (frames.map fun frame => frame.eval (transitionTailAffineSeed seed)) := by
  exact transitionAffineOr_fixed_encoding frames
    (transitionTailAffineSeed seed)

/-- Raw-input target consisting of one fixed affine OR-frame family per
adjacent tableau-row seed. -/
noncomputable def verifierTransitionAffineOrFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (frames : List TransitionAffineOrPairForm) (hnonempty : frames ≠ [])
    (input : List Γ) : List UnaryFrameSym :=
  verifierTransitionAffineDelimitedMapFrames W
    (transitionAffineOrFieldForms frames)
    (transitionAffineOrDelimiters frames)
    (transitionAffineOrDelimiters_nonempty hnonempty) input

/-- The concrete target is the row-major canonical OR-frame encoding. -/
theorem verifierTransitionAffineOrFrames_eq_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (frames : List TransitionAffineOrPairForm) (hnonempty : frames ≠ [])
    (input : List Γ) :
    verifierTransitionAffineOrFrames W frames hnonempty input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        encodeAffineOrFinFrames
          (frames.map fun frame =>
            frame.eval (transitionTailAffineSeed seed)) := by
  unfold verifierTransitionAffineOrFrames
  rw [verifierTransitionAffineDelimitedMapFrames_eq_rows W
    (transitionAffineOrFieldForms frames)
    (transitionAffineOrDelimiters frames)
    (transitionAffineOrDelimiters_nonempty hnonempty)
    (by simp)]
  apply List.flatMap_congr
  intro seed hseed
  exact transitionAffineOrRow_eq_encoding frames seed

/-- A single fixed polynomial-time TM2 emits the canonical affine OR-frame
family directly from the original verifier input. -/
noncomputable def verifierTransitionAffineOrFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (frames : List TransitionAffineOrPairForm) (hnonempty : frames ≠ []) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionAffineOrFrames W frames hnonempty) :=
  verifierTransitionAffineDelimitedMapFrames_computableInPolyTime W
    (transitionAffineOrFieldForms frames)
    (transitionAffineOrDelimiters frames)
    (transitionAffineOrDelimiters_nonempty hnonempty)

end CLRS.Chapter34.Turing.CookLevin

import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionEqFrames
import Mathlib.Tactic

/-!
# Row-sentinel transition equality coordinates

The original equality source flattens all transition rows.  This module adds
one fixed zero-coordinate progression after each row.  The existing generic
progression and affine-map machines can carry that sentinel without learning
the runtime tableau height; a later finite-state pass turns it back into an
outer row boundary.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- One affine constant-one form used by the sentinel count field. -/
def transitionOneForm : AffineUnaryTripleForm :=
  { constant := 1, first := 0, second := 0, third := 0 }

/-- Seven fixed fields encoding a one-row all-zero triple progression. -/
def transitionEqSentinelDescriptorForms : List AffineUnaryTripleForm :=
  [ transitionZeroForm, transitionZeroForm, transitionZeroForm,
    transitionZeroForm, transitionZeroForm, transitionZeroForm,
    transitionOneForm ]

/-- The progression emits exactly the coordinate triple `(0, 0, 0)`. -/
def transitionEqSentinelProgression : AffineUnaryTripleProgression :=
  { base₁ := 0, base₂ := 0, base₃ := 0
    step₁ := 0, step₂ := 0, step₃ := 0
    count := 1 }

/-- Existing segment descriptors followed by one fixed row sentinel. -/
noncomputable def transitionEqRowMarkedDescriptorForms
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  transitionEqProgressionDescriptorForms tm ++
    transitionEqSentinelDescriptorForms

/-- Existing row progressions followed by the sentinel progression. -/
noncomputable def transitionEqRowMarkedProgressions
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List AffineUnaryTripleProgression :=
  transitionEqProgressions tm seed ++ [transitionEqSentinelProgression]

@[simp] theorem transitionEqSentinelDescriptorForms_value
    (seed : AffineUnaryTripleSeed) :
    affineUnaryTripleMap transitionEqSentinelDescriptorForms seed =
      [0, 0, 0, 0, 0, 0, 1] := by
  simp [transitionEqSentinelDescriptorForms, transitionZeroForm,
    transitionOneForm, affineUnaryTripleMap,
    affineUnaryTripleFormValue]

/-- The fixed marked table evaluates to all semantic row descriptors and the
one sentinel descriptor. -/
theorem transitionEqRowMarkedDescriptorForms_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    affineUnaryTripleMap (transitionEqRowMarkedDescriptorForms tm)
        (transitionTailAffineSeed seed) =
      (transitionEqRowMarkedProgressions tm seed).flatMap fun progression =>
        [ progression.base₁, progression.base₂, progression.base₃,
          progression.step₁, progression.step₂, progression.step₃,
          progression.count ] := by
  unfold transitionEqRowMarkedDescriptorForms
    transitionEqRowMarkedProgressions
  rw [show affineUnaryTripleMap
          (transitionEqProgressionDescriptorForms tm ++
            transitionEqSentinelDescriptorForms)
          (transitionTailAffineSeed seed) =
        affineUnaryTripleMap (transitionEqProgressionDescriptorForms tm)
            (transitionTailAffineSeed seed) ++
          affineUnaryTripleMap transitionEqSentinelDescriptorForms
            (transitionTailAffineSeed seed) by
      simp [affineUnaryTripleMap]]
  rw [transitionEqProgressionDescriptorForms_value,
    transitionEqSentinelDescriptorForms_value]
  simp [transitionEqSentinelProgression]

/-- One row's marked affine table has exactly the generic progression-family
byte encoding. -/
theorem encode_transitionEqRowMarkedDescriptorForms
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    encodeUnaryFrame
        (affineUnaryTripleMap (transitionEqRowMarkedDescriptorForms tm)
          (transitionTailAffineSeed seed)) =
      encodeAffineUnaryTripleProgressionFamily
        (transitionEqRowMarkedProgressions tm seed) := by
  rw [transitionEqRowMarkedDescriptorForms_value]
  unfold encodeUnaryFrame
  induction transitionEqRowMarkedProgressions tm seed with
  | nil => rfl
  | cons progression rest ih =>
      simp only [List.flatMap_cons,
        encodeAffineUnaryTripleProgressionFamily,
        encodeAffineUnaryTripleProgression, List.flatMap_append]
      rw [ih]
      simp [encodeUnaryFrame, List.append_assoc]

/-- Raw-input descriptor bytes with a fixed sentinel after every verifier
transition row. -/
noncomputable def verifierTransitionEqRowMarkedDescriptorFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  verifierTransitionAffineMapFrames W
    (transitionEqRowMarkedDescriptorForms W.machine.tm) input

/-- Exact structured semantics of the marked descriptor source. -/
theorem verifierTransitionEqRowMarkedDescriptorFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionEqRowMarkedDescriptorFrames W input =
      encodeAffineUnaryTripleProgressionFamily
        ((verifierTransitionRowSeeds W input).flatMap
          (transitionEqRowMarkedProgressions W.machine.tm)) := by
  unfold verifierTransitionEqRowMarkedDescriptorFrames
    verifierTransitionAffineMapFrames verifierTransitionTailAffineSeeds
    affineUnaryTripleMapFamily encodeUnaryFrame
  rw [List.flatMap_map]
  generalize verifierTransitionRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [List.flatMap_cons, List.flatMap_append]
      have hseed := encode_transitionEqRowMarkedDescriptorForms
        W.machine.tm seed
      unfold encodeUnaryFrame at hseed
      rw [hseed, ih]
      induction transitionEqRowMarkedProgressions W.machine.tm seed with
      | nil => rfl
      | cons progression progressions segmentIh =>
          simp [encodeAffineUnaryTripleProgressionFamily, segmentIh]

/-- The marked descriptor stream is emitted by one fixed polynomial-time
TM2 directly from the raw verifier word. -/
noncomputable def
    verifierTransitionEqRowMarkedDescriptorFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionEqRowMarkedDescriptorFrames W) := by
  exact verifierTransitionAffineMapFrames_computableInPolyTime W
    (transitionEqRowMarkedDescriptorForms W.machine.tm)

/-- Seed representation of the all-zero row sentinel. -/
def transitionEqSentinelCoordinateSeed : AffineUnaryTripleSeed :=
  { first := 0, second := 0, third := 0 }

/-- Coordinate seeds of one row followed by the all-zero sentinel. -/
noncomputable def transitionEqRowMarkedCoordinateSeeds
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List AffineUnaryTripleSeed :=
  transitionEqCoordinateSeeds tm seed ++
    [transitionEqSentinelCoordinateSeed]

private theorem rowSentinel_progression_frameStream :
    affineUnaryTripleProgressionFrameStream
        transitionEqSentinelProgression =
      encodeAffineUnaryTripleSeedFamily
        [transitionEqSentinelCoordinateSeed] := by
  rfl

private theorem rowSentinel_progressionFamilyFrameStream_append
    (left right : List AffineUnaryTripleProgression) :
    affineUnaryTripleProgressionFamilyFrameStream (left ++ right) =
      affineUnaryTripleProgressionFamilyFrameStream left ++
        affineUnaryTripleProgressionFamilyFrameStream right := by
  induction left with
  | nil => rfl
  | cons progression rest ih =>
      simp [affineUnaryTripleProgressionFamilyFrameStream, ih,
        List.append_assoc]

private theorem rowSentinel_seedFamily_append
    (left right : List AffineUnaryTripleSeed) :
    encodeAffineUnaryTripleSeedFamily (left ++ right) =
      encodeAffineUnaryTripleSeedFamily left ++
        encodeAffineUnaryTripleSeedFamily right := by
  induction left with
  | nil => rfl
  | cons seed rest ih =>
      simp [encodeAffineUnaryTripleSeedFamily, ih, List.append_assoc]

/-- Executing the marked progression family for one row emits its canonical
coordinate seeds followed by the zero sentinel seed. -/
theorem transitionEqRowMarkedProgressionFrameStream_eq_coordinateSeeds
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    affineUnaryTripleProgressionFamilyFrameStream
        (transitionEqRowMarkedProgressions tm seed) =
      encodeAffineUnaryTripleSeedFamily
        (transitionEqRowMarkedCoordinateSeeds tm seed) := by
  unfold transitionEqRowMarkedProgressions
    transitionEqRowMarkedCoordinateSeeds
  rw [rowSentinel_progressionFamilyFrameStream_append,
    transitionEqProgressionFrameStream_eq_coordinateSeeds,
    rowSentinel_seedFamily_append]
  simp [affineUnaryTripleProgressionFamilyFrameStream,
    encodeAffineUnaryTripleSeedFamily,
    rowSentinel_progression_frameStream]

/-- Flat coordinate stream retaining one zero sentinel after each source
row. -/
noncomputable def verifierTransitionEqRowMarkedCoordinateFrameStream
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  affineUnaryTripleProgressionFamilyFrameStream
    ((verifierTransitionRowSeeds W input).flatMap
      (transitionEqRowMarkedProgressions W.machine.tm))

/-- The complete marked coordinate stream is literally the generic seed
encoding of the row-marked coordinate family. -/
theorem verifierTransitionEqRowMarkedCoordinateFrameStream_eq_seedEncoding
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionEqRowMarkedCoordinateFrameStream W input =
      encodeAffineUnaryTripleSeedFamily
        ((verifierTransitionRowSeeds W input).flatMap
          (transitionEqRowMarkedCoordinateSeeds W.machine.tm)) := by
  unfold verifierTransitionEqRowMarkedCoordinateFrameStream
  generalize verifierTransitionRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [List.flatMap_cons]
      rw [rowSentinel_progressionFamilyFrameStream_append,
        transitionEqRowMarkedProgressionFrameStream_eq_coordinateSeeds,
        ih, rowSentinel_seedFamily_append]

/-- One fixed polynomial-time TM2 compiles and executes the marked
progression descriptors from the raw verifier word. -/
noncomputable def
    verifierTransitionEqRowMarkedCoordinateFrameStream_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionEqRowMarkedCoordinateFrameStream W) := by
  let descriptors :=
    verifierTransitionEqRowMarkedDescriptorFrames_computableInPolyTime W
  let structured : _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineUnaryTripleProgressionFamily
      (fun input =>
        (verifierTransitionRowSeeds W input).flatMap
          (transitionEqRowMarkedProgressions W.machine.tm)) :=
    { tm := descriptors.tm
      inputAlphabet := descriptors.inputAlphabet
      outputAlphabet := descriptors.outputAlphabet
      time := descriptors.time
      outputsFun := fun input => by
        have run := descriptors.outputsFun input
        simpa only [id_eq,
          verifierTransitionEqRowMarkedDescriptorFrames_eq W input]
          using run }
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch structured
      affineUnaryTripleProgressionFamilyFrameStream_computableInPolyTime
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [Function.comp_apply, id_eq,
          verifierTransitionEqRowMarkedCoordinateFrameStream] using run }

end CLRS.Chapter34.Turing.CookLevin

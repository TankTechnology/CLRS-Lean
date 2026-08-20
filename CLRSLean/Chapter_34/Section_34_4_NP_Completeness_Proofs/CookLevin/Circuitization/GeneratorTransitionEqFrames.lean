import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionEqSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameDelimiterMap
import Mathlib.Tactic

/-!
# Concrete transition equality-frame source

This module executes the runtime segment progressions compiled from the raw
verifier word.  Their `(previous, left, right)` rows are transformed by a
fixed affine map and a fixed delimiter cycle into the exact byte encoding of
`AffineEqFinPairFrame`s.  No public coordinate or wire index is stored in
finite control.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Repackage one progression row as the seed format of the generic affine
triple-map source. -/
def transitionEqCoordinateSeed
    (row : Nat × Nat × Nat) : AffineUnaryTripleSeed :=
  { first := row.1, second := row.2.1, third := row.2.2 }

/-- All coordinate triples emitted for one transition row, in segment-major
and then public-coordinate order. -/
noncomputable def transitionEqCoordinateSeeds
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List AffineUnaryTripleSeed :=
  (transitionEqProgressions tm seed).flatMap fun progression =>
    (affineUnaryTripleProgressionRows progression).map
      transitionEqCoordinateSeed

private theorem progressionFrameStream_eq_seedEncoding
    (progression : AffineUnaryTripleProgression) :
    affineUnaryTripleProgressionFrameStream progression =
      encodeAffineUnaryTripleSeedFamily
        ((affineUnaryTripleProgressionRows progression).map
          transitionEqCoordinateSeed) := by
  unfold affineUnaryTripleProgressionFrameStream
  generalize affineUnaryTripleProgressionRows progression = rows
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      rcases row with ⟨first, second, third⟩
      simp only [List.flatMap_cons, List.map_cons,
        encodeAffineUnaryTripleSeedFamily]
      rw [ih]
      rfl

private theorem progressionFamilyFrameStream_append
    (left right : List AffineUnaryTripleProgression) :
    affineUnaryTripleProgressionFamilyFrameStream (left ++ right) =
      affineUnaryTripleProgressionFamilyFrameStream left ++
        affineUnaryTripleProgressionFamilyFrameStream right := by
  induction left with
  | nil => rfl
  | cons progression rest ih =>
      simp [affineUnaryTripleProgressionFamilyFrameStream, ih,
        List.append_assoc]

private theorem affineUnaryTripleSeedFamily_append
    (left right : List AffineUnaryTripleSeed) :
    encodeAffineUnaryTripleSeedFamily (left ++ right) =
      encodeAffineUnaryTripleSeedFamily left ++
        encodeAffineUnaryTripleSeedFamily right := by
  induction left with
  | nil => rfl
  | cons seed rest ih =>
      simp [encodeAffineUnaryTripleSeedFamily, ih, List.append_assoc]

/-- Executing all progressions of one transition row produces literally the
generic seed-family encoding of all coordinate triples. -/
theorem transitionEqProgressionFrameStream_eq_coordinateSeeds
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    affineUnaryTripleProgressionFamilyFrameStream
        (transitionEqProgressions tm seed) =
      encodeAffineUnaryTripleSeedFamily
        (transitionEqCoordinateSeeds tm seed) := by
  unfold transitionEqCoordinateSeeds
  induction transitionEqProgressions tm seed with
  | nil => rfl
  | cons progression rest ih =>
      simp only [affineUnaryTripleProgressionFamilyFrameStream,
        List.flatMap_cons]
      rw [progressionFrameStream_eq_seedEncoding, ih]
      clear ih
      induction (affineUnaryTripleProgressionRows progression).map
          transitionEqCoordinateSeed with
      | nil => rfl
      | cons coordinate coordinates coordinateIh =>
          simp [encodeAffineUnaryTripleSeedFamily, coordinateIh]

/-- Forward coordinate stream for every transition row of the verifier. -/
noncomputable def verifierTransitionEqCoordinateFrameStream
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  affineUnaryTripleProgressionFamilyFrameStream
    ((verifierTransitionRowSeeds W input).flatMap
      (transitionEqProgressions W.machine.tm))

/-- A fixed polynomial-time TM2 compiles and executes all segment
progressions directly from the raw verifier word. -/
noncomputable def
    verifierTransitionEqCoordinateFrameStream_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionEqCoordinateFrameStream W) := by
  let descriptors :=
    verifierTransitionEqProgressionDescriptorFrames_computableInPolyTime W
  let structured : _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineUnaryTripleProgressionFamily
      (fun input =>
        (verifierTransitionRowSeeds W input).flatMap
          (transitionEqProgressions W.machine.tm)) :=
    { tm := descriptors.tm
      inputAlphabet := descriptors.inputAlphabet
      outputAlphabet := descriptors.outputAlphabet
      time := descriptors.time
      outputsFun := fun input => by
        have run := descriptors.outputsFun input
        simpa only [id_eq,
          verifierTransitionEqProgressionDescriptorFrames_eq W input]
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
          verifierTransitionEqCoordinateFrameStream] using run }

/-- The complete coordinate stream is the generic seed encoding of the
row-major generated coordinate family. -/
theorem verifierTransitionEqCoordinateFrameStream_eq_seedEncoding
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionEqCoordinateFrameStream W input =
      encodeAffineUnaryTripleSeedFamily
        ((verifierTransitionRowSeeds W input).flatMap
          (transitionEqCoordinateSeeds W.machine.tm)) := by
  unfold verifierTransitionEqCoordinateFrameStream
  generalize verifierTransitionRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [List.flatMap_cons]
      rw [progressionFamilyFrameStream_append,
        transitionEqProgressionFrameStream_eq_coordinateSeeds, ih,
        affineUnaryTripleSeedFamily_append]

/-- Fixed affine selectors and offsets turning `(previous, left, right)` into
the nine ordinary values needed by one equality invocation.  Zero positions
materialize the three `frameEnd`s without placing markers in the value source. -/
def transitionEqInvocationForms : List AffineUnaryTripleForm :=
  [ transitionZeroForm,
    { constant := 1, first := 1, second := 0, third := 0 },
    { constant := 0, first := 0, second := 1, third := 0 },
    { constant := 0, first := 0, second := 0, third := 1 },
    transitionZeroForm,
    { constant := 5, first := 1, second := 0, third := 0 },
    transitionZeroForm,
    { constant := 0, first := 1, second := 0, third := 0 },
    transitionZeroForm ]

/-- Equality frame denoted by one generated coordinate triple. -/
def transitionEqCoordinateFrame
    (seed : AffineUnaryTripleSeed) : AffineEqFinPairFrame :=
  { eqStart := seed.first + 1
    left := seed.second
    right := seed.third
    matched := seed.first + 5
    previous := seed.first }

/-- Generated equality frames for one transition row. -/
noncomputable def transitionEqGeneratedFrames
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List AffineEqFinPairFrame :=
  (transitionEqCoordinateSeeds tm seed).map transitionEqCoordinateFrame

@[simp] theorem transitionEqInvocationForms_value
    (seed : AffineUnaryTripleSeed) :
    affineUnaryTripleMap transitionEqInvocationForms seed =
      let frame := transitionEqCoordinateFrame seed
      [0, frame.eqStart, frame.left, frame.right, 0,
        frame.matched, 0, frame.previous, 0] := by
  simp [transitionEqInvocationForms, transitionZeroForm,
    transitionEqCoordinateFrame, affineUnaryTripleMap,
    affineUnaryTripleFormValue]
  omega

/-- Ordinary unary values for every generated equality frame. -/
noncomputable def verifierTransitionEqInvocationValueFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  encodeUnaryFrame
    (affineUnaryTripleMapFamily transitionEqInvocationForms
      ((verifierTransitionRowSeeds W input).flatMap
        (transitionEqCoordinateSeeds W.machine.tm)))

/-- A fixed polynomial-time TM2 emits all ordinary equality invocation
values from the raw verifier word. -/
noncomputable def
    verifierTransitionEqInvocationValueFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionEqInvocationValueFrames W) := by
  let coordinates :=
    verifierTransitionEqCoordinateFrameStream_computableInPolyTime W
  let structured : _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineUnaryTripleSeedFamily
      (fun input =>
        (verifierTransitionRowSeeds W input).flatMap
          (transitionEqCoordinateSeeds W.machine.tm)) :=
    { tm := coordinates.tm
      inputAlphabet := coordinates.inputAlphabet
      outputAlphabet := coordinates.outputAlphabet
      time := coordinates.time
      outputsFun := fun input => by
        have run := coordinates.outputsFun input
        simpa only [id_eq,
          verifierTransitionEqCoordinateFrameStream_eq_seedEncoding W input]
          using run }
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch structured
      (affineUnaryTripleMapFamily_computableInPolyTime
        transitionEqInvocationForms)
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [Function.comp_apply, id_eq,
          verifierTransitionEqInvocationValueFrames] using run }

/-- Fixed nine-position delimiter cycle of one `AffineEqFinPairFrame`. -/
def transitionEqInvocationDelimiterTable : List UnaryFrameSym :=
  [.frameEnd, .separator, .separator, .separator, .frameEnd,
    .separator, .separator, .separator, .frameEnd]

@[simp] theorem transitionEqInvocationDelimiterTable_length :
    transitionEqInvocationDelimiterTable.length = 9 := rfl

theorem transitionEqInvocationDelimiterTable_nonempty :
    0 < transitionEqInvocationDelimiterTable.length := by simp

private theorem transitionEqInvocationDelimiter_frames
    (frames : List AffineEqFinPairFrame) :
    encodeUnaryFrameWithDelimiterCycle
        transitionEqInvocationDelimiterTable
        transitionEqInvocationDelimiterTable_nonempty
        (frames.flatMap fun frame =>
          [0, frame.eqStart, frame.left, frame.right, 0,
            frame.matched, 0, frame.previous, 0]) =
      encodeAffineEqFinFrames frames := by
  induction frames with
  | nil => rfl
  | cons frame frames ih =>
      simp [encodeUnaryFrameWithDelimiterCycle,
        encodeUnaryFrameWithDelimiterCycleFrom,
        transitionEqInvocationDelimiterTable,
        unaryFrameDelimiterNext, encodeAffineEqFinFrames,
        encodeAffineEqFinPairFrame, encodeUnaryFrame,
        encodeUnaryFrameBlock, List.append_assoc]
      change encodeUnaryFrameWithDelimiterCycle
          transitionEqInvocationDelimiterTable
          transitionEqInvocationDelimiterTable_nonempty
          (frames.flatMap fun frame =>
            [0, frame.eqStart, frame.left, frame.right, 0,
              frame.matched, 0, frame.previous, 0]) =
        encodeAffineEqFinFrames frames
      exact ih

/-- Complete delimiter-exact equality invocation input compiled from the raw
verifier word. -/
noncomputable def verifierTransitionEqInvocationInput
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFrameDelimiters transitionEqInvocationDelimiterTable
    transitionEqInvocationDelimiterTable_nonempty
    (verifierTransitionEqInvocationValueFrames W input)

/-- Byte-exact semantics of the generated equality source. -/
theorem verifierTransitionEqInvocationInput_eq_generatedFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionEqInvocationInput W input =
      encodeAffineEqFinFrames
        ((verifierTransitionRowSeeds W input).flatMap
          (transitionEqGeneratedFrames W.machine.tm)) := by
  unfold verifierTransitionEqInvocationInput
    verifierTransitionEqInvocationValueFrames
  rw [rewriteUnaryFrameDelimiters_encodeUnaryFrame]
  unfold affineUnaryTripleMapFamily transitionEqGeneratedFrames
  rw [← List.map_flatMap]
  have hvalues :
      ((verifierTransitionRowSeeds W input).flatMap
        (transitionEqCoordinateSeeds W.machine.tm)).flatMap
          (affineUnaryTripleMap transitionEqInvocationForms) =
        ((verifierTransitionRowSeeds W input).flatMap
          (transitionEqCoordinateSeeds W.machine.tm)).flatMap fun seed =>
            let frame := transitionEqCoordinateFrame seed
            [0, frame.eqStart, frame.left, frame.right, 0,
              frame.matched, 0, frame.previous, 0] := by
    apply List.flatMap_congr
    intro seed _
    exact transitionEqInvocationForms_value seed
  rw [hvalues]
  simpa only [List.flatMap_map] using
    transitionEqInvocationDelimiter_frames
      (((verifierTransitionRowSeeds W input).flatMap
        (transitionEqCoordinateSeeds W.machine.tm)).map
          transitionEqCoordinateFrame)

/-- One fixed polynomial-time TM2 emits the complete generated equality frame
stream directly from the raw verifier input. -/
noncomputable def
    verifierTransitionEqInvocationInput_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionEqInvocationInput W) := by
  let values :=
    verifierTransitionEqInvocationValueFrames_computableInPolyTime W
  let delimiters := unaryFrameDelimiterMap_computableInPolyTime
    transitionEqInvocationDelimiterTable
    transitionEqInvocationDelimiterTable_nonempty
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      values delimiters
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [Function.comp_def,
          verifierTransitionEqInvocationInput] using run }

end CLRS.Chapter34.Turing.CookLevin

import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionEqRowSentinel
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionEqSegmentAlignment
import Mathlib.Tactic

/-!
# Phase-carrying transition equality sentinels

For assembly of a complete local-transition tail, one coordinate is inserted
before and after each row's equality coordinates.  The prefix coordinate has
tag zero, the suffix coordinate has tag one, and both retain the runtime
`height` and `start`.  Genuine equality coordinates begin strictly later and
are separated in the following routing stage.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Select the runtime height field of a transition row seed. -/
def transitionSeedHeightForm : AffineUnaryTripleForm :=
  { constant := 0, first := 1, second := 0, third := 0 }

/-- Select the runtime local gate start field of a transition row seed. -/
def transitionSeedStartForm : AffineUnaryTripleForm :=
  { constant := 0, first := 0, second := 1, third := 0 }

/-- Descriptor fields for the prefix coordinate `(0, height, start)`. -/
def transitionEqPrefixSentinelDescriptorForms :
    List AffineUnaryTripleForm :=
  [ transitionZeroForm, transitionSeedHeightForm, transitionSeedStartForm,
    transitionZeroForm, transitionZeroForm, transitionZeroForm,
    transitionOneForm ]

/-- Descriptor fields for the suffix coordinate `(1, height, start)`. -/
def transitionEqSuffixSentinelDescriptorForms :
    List AffineUnaryTripleForm :=
  [ transitionOneForm, transitionSeedHeightForm, transitionSeedStartForm,
    transitionZeroForm, transitionZeroForm, transitionZeroForm,
    transitionOneForm ]

/-- Runtime prefix sentinel of one transition row. -/
def transitionEqPrefixSentinelProgression (seed : TransitionRowSeed) :
    AffineUnaryTripleProgression :=
  { base₁ := 0, base₂ := seed.height, base₃ := seed.start
    step₁ := 0, step₂ := 0, step₃ := 0
    count := 1 }

/-- Runtime suffix sentinel of one transition row. -/
def transitionEqSuffixSentinelProgression (seed : TransitionRowSeed) :
    AffineUnaryTripleProgression :=
  { base₁ := 1, base₂ := seed.height, base₃ := seed.start
    step₁ := 0, step₂ := 0, step₃ := 0
    count := 1 }

/-- Fixed descriptor table for prefix, equality segments, and suffix. -/
noncomputable def transitionEqPhaseDescriptorForms
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  transitionEqPrefixSentinelDescriptorForms ++
    transitionEqProgressionDescriptorForms tm ++
      transitionEqSuffixSentinelDescriptorForms

/-- Runtime progression family retaining both phase sentinels. -/
noncomputable def transitionEqPhaseProgressions
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List AffineUnaryTripleProgression :=
  [transitionEqPrefixSentinelProgression seed] ++
    transitionEqProgressions tm seed ++
      [transitionEqSuffixSentinelProgression seed]

@[simp] theorem transitionEqPrefixSentinelDescriptorForms_value
    (seed : TransitionRowSeed) :
    affineUnaryTripleMap transitionEqPrefixSentinelDescriptorForms
        (transitionTailAffineSeed seed) =
      [0, seed.height, seed.start, 0, 0, 0, 1] := by
  simp [transitionEqPrefixSentinelDescriptorForms,
    transitionSeedHeightForm, transitionSeedStartForm,
    transitionZeroForm, transitionOneForm, transitionTailAffineSeed,
    affineUnaryTripleMap, affineUnaryTripleFormValue]

@[simp] theorem transitionEqSuffixSentinelDescriptorForms_value
    (seed : TransitionRowSeed) :
    affineUnaryTripleMap transitionEqSuffixSentinelDescriptorForms
        (transitionTailAffineSeed seed) =
      [1, seed.height, seed.start, 0, 0, 0, 1] := by
  simp [transitionEqSuffixSentinelDescriptorForms,
    transitionSeedHeightForm, transitionSeedStartForm,
    transitionZeroForm, transitionOneForm, transitionTailAffineSeed,
    affineUnaryTripleMap, affineUnaryTripleFormValue]

/-- The fixed phase table evaluates to exactly the structured progression
descriptors of one row. -/
theorem transitionEqPhaseDescriptorForms_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    affineUnaryTripleMap (transitionEqPhaseDescriptorForms tm)
        (transitionTailAffineSeed seed) =
      (transitionEqPhaseProgressions tm seed).flatMap fun progression =>
        [ progression.base₁, progression.base₂, progression.base₃,
          progression.step₁, progression.step₂, progression.step₃,
          progression.count ] := by
  unfold transitionEqPhaseDescriptorForms transitionEqPhaseProgressions
  rw [show affineUnaryTripleMap
          (transitionEqPrefixSentinelDescriptorForms ++
            transitionEqProgressionDescriptorForms tm ++
              transitionEqSuffixSentinelDescriptorForms)
          (transitionTailAffineSeed seed) =
        affineUnaryTripleMap transitionEqPrefixSentinelDescriptorForms
            (transitionTailAffineSeed seed) ++
          affineUnaryTripleMap (transitionEqProgressionDescriptorForms tm)
              (transitionTailAffineSeed seed) ++
            affineUnaryTripleMap transitionEqSuffixSentinelDescriptorForms
              (transitionTailAffineSeed seed) by
      simp [affineUnaryTripleMap, List.map_append]]
  rw [transitionEqPrefixSentinelDescriptorForms_value,
    transitionEqProgressionDescriptorForms_value,
    transitionEqSuffixSentinelDescriptorForms_value]
  simp [transitionEqPrefixSentinelProgression,
    transitionEqSuffixSentinelProgression]

theorem encode_transitionEqPhaseDescriptorForms
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    encodeUnaryFrame
        (affineUnaryTripleMap (transitionEqPhaseDescriptorForms tm)
          (transitionTailAffineSeed seed)) =
      encodeAffineUnaryTripleProgressionFamily
        (transitionEqPhaseProgressions tm seed) := by
  rw [transitionEqPhaseDescriptorForms_value]
  unfold encodeUnaryFrame
  induction transitionEqPhaseProgressions tm seed with
  | nil => rfl
  | cons progression rest ih =>
      simp only [List.flatMap_cons,
        encodeAffineUnaryTripleProgressionFamily,
        encodeAffineUnaryTripleProgression, List.flatMap_append]
      rw [ih]
      simp [encodeUnaryFrame, List.append_assoc]

/-- Raw phase-descriptor bytes for every transition row. -/
noncomputable def verifierTransitionEqPhaseDescriptorFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  verifierTransitionAffineMapFrames W
    (transitionEqPhaseDescriptorForms W.machine.tm) input

theorem verifierTransitionEqPhaseDescriptorFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionEqPhaseDescriptorFrames W input =
      encodeAffineUnaryTripleProgressionFamily
        ((verifierTransitionRowSeeds W input).flatMap
          (transitionEqPhaseProgressions W.machine.tm)) := by
  unfold verifierTransitionEqPhaseDescriptorFrames
    verifierTransitionAffineMapFrames verifierTransitionTailAffineSeeds
    affineUnaryTripleMapFamily encodeUnaryFrame
  rw [List.flatMap_map]
  generalize verifierTransitionRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [List.flatMap_cons, List.flatMap_append]
      have hseed := encode_transitionEqPhaseDescriptorForms W.machine.tm seed
      unfold encodeUnaryFrame at hseed
      rw [hseed, ih]
      induction transitionEqPhaseProgressions W.machine.tm seed with
      | nil => rfl
      | cons progression progressions progressionIh =>
          simp [encodeAffineUnaryTripleProgressionFamily, progressionIh]

noncomputable def
    verifierTransitionEqPhaseDescriptorFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionEqPhaseDescriptorFrames W) := by
  exact verifierTransitionAffineMapFrames_computableInPolyTime W
    (transitionEqPhaseDescriptorForms W.machine.tm)

/-- Prefix sentinel seed retaining `(height, start)`. -/
def transitionEqPrefixSentinelCoordinateSeed (seed : TransitionRowSeed) :
    AffineUnaryTripleSeed :=
  { first := 0, second := seed.height, third := seed.start }

/-- Suffix sentinel seed retaining `(height, start)`. -/
def transitionEqSuffixSentinelCoordinateSeed (seed : TransitionRowSeed) :
    AffineUnaryTripleSeed :=
  { first := 1, second := seed.height, third := seed.start }

/-- One phase-carrying row: prefix, genuine equality coordinates, suffix. -/
noncomputable def transitionEqPhaseCoordinateSeeds
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List AffineUnaryTripleSeed :=
  transitionEqPrefixSentinelCoordinateSeed seed ::
    (transitionEqCoordinateSeeds tm seed ++
      [transitionEqSuffixSentinelCoordinateSeed seed])

/-- Genuine equality coordinates cannot be confused with either fixed phase
tag `0` or `1`. -/
theorem transitionEqCoordinateSeed_first_gt_one
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (coordinate : AffineUnaryTripleSeed)
    (hcoordinate : coordinate ∈ transitionEqCoordinateSeeds tm seed)
    (hwork : 0 < workHeight tm seed.height) :
    1 < coordinate.first := by
  rw [transitionEqCoordinateSeeds_eq_slots tm seed hwork] at hcoordinate
  simp only [List.mem_map] at hcoordinate
  rcases hcoordinate with ⟨slot, _, rfl⟩
  simp only [transitionEqSlotSeed, transitionEqStart,
    transitionNarrowStart]
  omega

private theorem phaseSentinels_progressionFamily_append
    (left right : List AffineUnaryTripleProgression) :
    affineUnaryTripleProgressionFamilyFrameStream (left ++ right) =
      affineUnaryTripleProgressionFamilyFrameStream left ++
        affineUnaryTripleProgressionFamilyFrameStream right := by
  induction left with
  | nil => rfl
  | cons progression rest ih =>
      simp [affineUnaryTripleProgressionFamilyFrameStream, ih,
        List.append_assoc]

private theorem phaseSentinels_seedFamily_append
    (left right : List AffineUnaryTripleSeed) :
    encodeAffineUnaryTripleSeedFamily (left ++ right) =
      encodeAffineUnaryTripleSeedFamily left ++
        encodeAffineUnaryTripleSeedFamily right := by
  induction left with
  | nil => rfl
  | cons coordinate rest ih =>
      simp [encodeAffineUnaryTripleSeedFamily, ih, List.append_assoc]

private theorem phaseSentinels_progressionFamily_singleton
    (progression : AffineUnaryTripleProgression) :
    affineUnaryTripleProgressionFamilyFrameStream [progression] =
      affineUnaryTripleProgressionFrameStream progression := by
  simp [affineUnaryTripleProgressionFamilyFrameStream]

private theorem prefixSentinel_progressionFrameStream
    (seed : TransitionRowSeed) :
    affineUnaryTripleProgressionFrameStream
        (transitionEqPrefixSentinelProgression seed) =
      encodeAffineUnaryTripleSeedFamily
        [transitionEqPrefixSentinelCoordinateSeed seed] := by
  rfl

private theorem suffixSentinel_progressionFrameStream
    (seed : TransitionRowSeed) :
    affineUnaryTripleProgressionFrameStream
        (transitionEqSuffixSentinelProgression seed) =
      encodeAffineUnaryTripleSeedFamily
        [transitionEqSuffixSentinelCoordinateSeed seed] := by
  rfl

/-- Executing one three-phase progression family yields the literal canonical
seed encoding of prefix, equality coordinates, and suffix. -/
theorem transitionEqPhaseProgressionFrameStream_eq_coordinateSeeds
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    affineUnaryTripleProgressionFamilyFrameStream
        (transitionEqPhaseProgressions tm seed) =
      encodeAffineUnaryTripleSeedFamily
        (transitionEqPhaseCoordinateSeeds tm seed) := by
  unfold transitionEqPhaseProgressions transitionEqPhaseCoordinateSeeds
  rw [phaseSentinels_progressionFamily_append]
  rw [phaseSentinels_progressionFamily_append]
  rw [phaseSentinels_progressionFamily_singleton]
  rw [phaseSentinels_progressionFamily_singleton]
  rw [transitionEqProgressionFrameStream_eq_coordinateSeeds,
    prefixSentinel_progressionFrameStream,
    suffixSentinel_progressionFrameStream]
  simp [encodeAffineUnaryTripleSeedFamily, List.append_assoc]
  rw [phaseSentinels_seedFamily_append]
  simp [encodeAffineUnaryTripleSeedFamily]

/-- Raw three-phase coordinate stream for the full transition family. -/
noncomputable def verifierTransitionEqPhaseCoordinateFrameStream
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  affineUnaryTripleProgressionFamilyFrameStream
    ((verifierTransitionRowSeeds W input).flatMap
      (transitionEqPhaseProgressions W.machine.tm))

theorem verifierTransitionEqPhaseCoordinateFrameStream_eq_seedEncoding
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionEqPhaseCoordinateFrameStream W input =
      encodeAffineUnaryTripleSeedFamily
        ((verifierTransitionRowSeeds W input).flatMap
          (transitionEqPhaseCoordinateSeeds W.machine.tm)) := by
  unfold verifierTransitionEqPhaseCoordinateFrameStream
  generalize verifierTransitionRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [List.flatMap_cons]
      rw [phaseSentinels_progressionFamily_append,
        transitionEqPhaseProgressionFrameStream_eq_coordinateSeeds,
        ih, phaseSentinels_seedFamily_append]

/-- One fixed polynomial-time TM2 emits the phase-carrying coordinates from
the raw verifier input. -/
noncomputable def
    verifierTransitionEqPhaseCoordinateFrameStream_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionEqPhaseCoordinateFrameStream W) := by
  let descriptors :=
    verifierTransitionEqPhaseDescriptorFrames_computableInPolyTime W
  let structured : _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineUnaryTripleProgressionFamily
      (fun input =>
        (verifierTransitionRowSeeds W input).flatMap
          (transitionEqPhaseProgressions W.machine.tm)) :=
    { tm := descriptors.tm
      inputAlphabet := descriptors.inputAlphabet
      outputAlphabet := descriptors.outputAlphabet
      time := descriptors.time
      outputsFun := fun input => by
        have run := descriptors.outputsFun input
        simpa only [id_eq,
          verifierTransitionEqPhaseDescriptorFrames_eq W input] using run }
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
          verifierTransitionEqPhaseCoordinateFrameStream] using run }

end CLRS.Chapter34.Turing.CookLevin

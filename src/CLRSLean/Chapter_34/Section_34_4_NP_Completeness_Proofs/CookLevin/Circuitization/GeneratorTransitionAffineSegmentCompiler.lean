import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouteBlockSourceFrames

/-!
# Generic raw-input compiler for fixed affine segment tables

Many transition operands are a fixed list of affine progressions evaluated at
every runtime transition seed.  This module packages the recurring pipeline:
evaluate the seven descriptor fields, execute each fixed-size progression
group, and project its first coordinate into one marked unary value row.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Runtime progressions denoted by an arbitrary verifier-fixed segment table.
-/
def transitionAffineSegmentProgressions
    (seed : TransitionRowSeed)
    (segments : List TransitionWidenedFallbackSegment) :
    List AffineUnaryTripleProgression :=
  segments.map (transitionWidenedFallbackSegmentProgression seed)

/-- First-coordinate value stream of an affine segment table. -/
def transitionAffineSegmentFirstValues
    (seed : TransitionRowSeed)
    (segments : List TransitionWidenedFallbackSegment) : List Nat :=
  transitionStackRouteFirstValues
    (transitionAffineSegmentProgressions seed segments)

/-- Fixed seven-form descriptors for an arbitrary segment table. -/
def transitionAffineSegmentDescriptorForms
    (segments : List TransitionWidenedFallbackSegment) :
    List AffineUnaryTripleForm :=
  segments.flatMap transitionWidenedFallbackSegmentDescriptorForms

/-- Evaluating the fixed form table gives exactly the runtime descriptors. -/
theorem transitionAffineSegmentDescriptorForms_value
    (seed : TransitionRowSeed)
    (segments : List TransitionWidenedFallbackSegment) :
    affineUnaryTripleMap (transitionAffineSegmentDescriptorForms segments)
        (transitionTailAffineSeed seed) =
      (transitionAffineSegmentProgressions seed segments).flatMap
        fun progression =>
          [ progression.base₁, progression.base₂, progression.base₃,
            progression.step₁, progression.step₂, progression.step₃,
            progression.count ] := by
  unfold transitionAffineSegmentDescriptorForms
    transitionAffineSegmentProgressions affineUnaryTripleMap
  rw [List.map_flatMap, List.flatMap_map]
  apply List.flatMap_congr
  intro segment hsegment
  exact transitionWidenedFallbackSegmentDescriptorForms_value seed segment

/-- Descriptor bytes agree with the generic progression-family input. -/
theorem encode_transitionAffineSegmentDescriptorForms
    (seed : TransitionRowSeed)
    (segments : List TransitionWidenedFallbackSegment) :
    encodeUnaryFrame
        (affineUnaryTripleMap
          (transitionAffineSegmentDescriptorForms segments)
          (transitionTailAffineSeed seed)) =
      encodeAffineUnaryTripleProgressionFamily
        (transitionAffineSegmentProgressions seed segments) := by
  rw [transitionAffineSegmentDescriptorForms_value]
  unfold encodeUnaryFrame
  induction transitionAffineSegmentProgressions seed segments with
  | nil => rfl
  | cons progression rest ih =>
      simp only [List.flatMap_cons,
        encodeAffineUnaryTripleProgressionFamily,
        encodeAffineUnaryTripleProgression, List.flatMap_append]
      rw [ih]
      simp [encodeUnaryFrame, List.append_assoc]

/-- Raw-input descriptors for every transition seed. -/
noncomputable def verifierTransitionAffineSegmentDescriptorFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (segments : List TransitionWidenedFallbackSegment)
    (input : List Γ) : List UnaryFrameSym :=
  verifierTransitionAffineMapFrames W
    (transitionAffineSegmentDescriptorForms segments) input

/-- Exact descriptor-family semantics of the generic raw source. -/
theorem verifierTransitionAffineSegmentDescriptorFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (segments : List TransitionWidenedFallbackSegment)
    (input : List Γ) :
    verifierTransitionAffineSegmentDescriptorFrames W segments input =
      encodeAffineUnaryTripleProgressionFamily
        ((verifierTransitionRowSeeds W input).flatMap fun seed =>
          transitionAffineSegmentProgressions seed segments) := by
  unfold verifierTransitionAffineSegmentDescriptorFrames
    verifierTransitionAffineMapFrames verifierTransitionTailAffineSeeds
    affineUnaryTripleMapFamily encodeUnaryFrame
  rw [List.flatMap_map]
  generalize verifierTransitionRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [List.flatMap_cons, List.flatMap_append]
      have hseed := encode_transitionAffineSegmentDescriptorForms
        seed segments
      unfold encodeUnaryFrame at hseed
      rw [hseed, ih]
      induction transitionAffineSegmentProgressions seed segments with
      | nil => rfl
      | cons progression progressions progressionIh =>
          simp [encodeAffineUnaryTripleProgressionFamily, progressionIh]

/-- Descriptor generation for any fixed segment table is polynomial-time. -/
noncomputable def
    verifierTransitionAffineSegmentDescriptorFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (segments : List TransitionWidenedFallbackSegment) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionAffineSegmentDescriptorFrames W segments) := by
  exact verifierTransitionAffineMapFrames_computableInPolyTime W
    (transitionAffineSegmentDescriptorForms segments)

/-- Execute every nonempty fixed segment group. -/
noncomputable def verifierTransitionAffineSegmentGroupedFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (segments : List TransitionWidenedFallbackSegment)
    (_hnonempty : 0 < segments.length)
    (input : List Γ) : List UnaryFrameSym :=
  affineUnaryTripleProgressionFixedGroupFrameStream (segments.length - 1)
    ((verifierTransitionRowSeeds W input).flatMap fun seed =>
      transitionAffineSegmentProgressions seed segments)

/-- The grouped descriptor execution is polynomial-time. -/
noncomputable def
    verifierTransitionAffineSegmentGroupedFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (segments : List TransitionWidenedFallbackSegment)
    (hnonempty : 0 < segments.length) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionAffineSegmentGroupedFrames
        W segments hnonempty) := by
  let descriptors :=
    verifierTransitionAffineSegmentDescriptorFrames_computableInPolyTime
      W segments
  let structured : _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineUnaryTripleProgressionFamily
      (fun input =>
        (verifierTransitionRowSeeds W input).flatMap fun seed =>
          transitionAffineSegmentProgressions seed segments) :=
    { tm := descriptors.tm
      inputAlphabet := descriptors.inputAlphabet
      outputAlphabet := descriptors.outputAlphabet
      time := descriptors.time
      outputsFun := fun input => by
        have run := descriptors.outputsFun input
        simpa only [id_eq,
          verifierTransitionAffineSegmentDescriptorFrames_eq
            W segments input] using run }
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch structured
      (affineUnaryTripleProgressionFixedGroupFrameStream_computableInPolyTime
        (segments.length - 1))
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => affineUnaryTripleProgressionFixedGroupFrameStream
      (segments.length - 1)
      ((verifierTransitionRowSeeds W input).flatMap fun seed =>
        transitionAffineSegmentProgressions seed segments))
  simpa [Function.comp_def] using Classical.choice composed

/-- Projected first-coordinate value row for every transition seed. -/
noncomputable def verifierTransitionAffineSegmentValueFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (segments : List TransitionWidenedFallbackSegment)
    (hnonempty : 0 < segments.length)
    (input : List Γ) : List UnaryFrameSym :=
  projectUnaryTripleGroupFirst
    (verifierTransitionAffineSegmentGroupedFrames
      W segments hnonempty input)

/-- Exact row-major semantics of the generic segment compiler. -/
theorem verifierTransitionAffineSegmentValueFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (segments : List TransitionWidenedFallbackSegment)
    (hnonempty : 0 < segments.length)
    (input : List Γ) :
    verifierTransitionAffineSegmentValueFrames W segments hnonempty input =
      encodeUnaryFrameFixedPrefixDropInput
        ((verifierTransitionRowSeeds W input).map fun seed =>
          transitionAffineSegmentFirstValues seed segments) := by
  unfold verifierTransitionAffineSegmentValueFrames
    verifierTransitionAffineSegmentGroupedFrames
    transitionAffineSegmentFirstValues
  rw [projectUnaryTripleGroupFirst_fixedGroupStream]
  apply affineUnaryTripleProgressionFixedGroupFirstFrameStream_flatMap
  intro seed hseed
  simp [transitionAffineSegmentProgressions]
  omega

/-- A concrete polynomial-time TM2 computes the value rows of every fixed
nonempty affine segment table directly from the verifier input. -/
noncomputable def
    verifierTransitionAffineSegmentValueFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (segments : List TransitionWidenedFallbackSegment)
    (hnonempty : 0 < segments.length) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionAffineSegmentValueFrames
        W segments hnonempty) := by
  let grouped :=
    verifierTransitionAffineSegmentGroupedFrames_computableInPolyTime
      W segments hnonempty
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch grouped
      projectUnaryTripleGroupFirst_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => projectUnaryTripleGroupFirst
      (verifierTransitionAffineSegmentGroupedFrames
        W segments hnonempty input))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.CookLevin

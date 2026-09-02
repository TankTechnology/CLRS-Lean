import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxTrueArmAffineSpanFrames
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxFalseArmFrames
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxCoordinates

/-!
# Unified raw-input descriptor source for dispatch mux invocations

The complete mux source must combine four previously verified views without
using an oracle-side zip.  This module instead evaluates one verifier-fixed
affine form table per transition seed.  Its four consecutive sections contain
the selectors, fresh-coordinate progression descriptors, true-arm affine-span
descriptors together with their fixed prefix drops, and false-arm progression
descriptors.

The result is already produced from the original verifier word by one concrete
polynomial-time TM2.  A later streaming controller only has to interpret this
single descriptor packet.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Encode a verifier-fixed prefix-drop amount as an affine form. -/
def transitionDispatchTrueArmDropForm (amount : Nat) :
    AffineUnaryTripleForm :=
  transitionHeightAffineForm (TransitionAffineNat.const amount)

@[simp] theorem transitionDispatchTrueArmDropForm_value
    (amount : Nat) (seed : TransitionRowSeed) :
    affineUnaryTripleFormValue
        (transitionDispatchTrueArmDropForm amount)
        (transitionTailAffineSeed seed) = amount := by
  simp [transitionDispatchTrueArmDropForm, transitionHeightAffineForm,
    TransitionAffineNat.const,
    transitionTailAffineSeed, affineUnaryTripleFormValue]

/-- Eight fixed forms for one true-arm affine span: the prefix drop followed
by the ordinary seven-field progression descriptor. -/
def transitionDispatchTrueArmSpanDescriptorBlock
    (amount : Nat) (segment : TransitionWidenedFallbackSegment) :
    List AffineUnaryTripleForm :=
  transitionDispatchTrueArmDropForm amount ::
    transitionWidenedFallbackSegmentDescriptorForms segment

/-- Runtime values of one true-arm span descriptor block. -/
def transitionDispatchTrueArmSpanDescriptorBlockValues
    (amount : Nat) (progression : AffineUnaryTripleProgression) : List Nat :=
  [ amount,
    progression.base₁, progression.base₂, progression.base₃,
    progression.step₁, progression.step₂, progression.step₃,
    progression.count ]

theorem transitionDispatchTrueArmSpanDescriptorBlock_value
    (amount : Nat) (segment : TransitionWidenedFallbackSegment)
    (seed : TransitionRowSeed) :
    affineUnaryTripleMap
        (transitionDispatchTrueArmSpanDescriptorBlock amount segment)
        (transitionTailAffineSeed seed) =
      transitionDispatchTrueArmSpanDescriptorBlockValues amount
        (transitionWidenedFallbackSegmentProgression seed segment) := by
  unfold transitionDispatchTrueArmSpanDescriptorBlock
    transitionDispatchTrueArmSpanDescriptorBlockValues
  rw [show affineUnaryTripleMap
      (transitionDispatchTrueArmDropForm amount ::
        transitionWidenedFallbackSegmentDescriptorForms segment)
      (transitionTailAffineSeed seed) =
    affineUnaryTripleFormValue (transitionDispatchTrueArmDropForm amount)
        (transitionTailAffineSeed seed) ::
      affineUnaryTripleMap
        (transitionWidenedFallbackSegmentDescriptorForms segment)
        (transitionTailAffineSeed seed) by rfl]
  rw [transitionWidenedFallbackSegmentDescriptorForms_value]
  simp

/-- Lock-step fixed tables of drops and true-arm affine segments.  The actual
layout tables have equal lengths; totality on malformed tables keeps the
definition executable without a proof argument. -/
def transitionDispatchTrueArmSpanDescriptorFormsFrom :
    List Nat → List TransitionWidenedFallbackSegment →
      List AffineUnaryTripleForm
  | amount :: amounts, segment :: segments =>
      transitionDispatchTrueArmSpanDescriptorBlock amount segment ++
        transitionDispatchTrueArmSpanDescriptorFormsFrom amounts segments
  | _, _ => []

/-- Runtime descriptor values in the same lock-step order. -/
def transitionDispatchTrueArmSpanDescriptorValuesFrom
    (seed : TransitionRowSeed) :
    List Nat → List TransitionWidenedFallbackSegment → List Nat
  | amount :: amounts, segment :: segments =>
      transitionDispatchTrueArmSpanDescriptorBlockValues amount
          (transitionWidenedFallbackSegmentProgression seed segment) ++
        transitionDispatchTrueArmSpanDescriptorValuesFrom seed amounts segments
  | _, _ => []

theorem transitionDispatchTrueArmSpanDescriptorFormsFrom_value
    (seed : TransitionRowSeed) :
    ∀ (amounts : List Nat)
      (segments : List TransitionWidenedFallbackSegment),
      affineUnaryTripleMap
          (transitionDispatchTrueArmSpanDescriptorFormsFrom amounts segments)
          (transitionTailAffineSeed seed) =
        transitionDispatchTrueArmSpanDescriptorValuesFrom seed amounts
          segments := by
  intro amounts
  induction amounts with
  | nil =>
      intro segments
      rfl
  | cons amount amounts ih =>
      intro segments
      cases segments with
      | nil => rfl
      | cons segment segments =>
          simp only [transitionDispatchTrueArmSpanDescriptorFormsFrom,
            transitionDispatchTrueArmSpanDescriptorValuesFrom]
          rw [show affineUnaryTripleMap
              (transitionDispatchTrueArmSpanDescriptorBlock amount segment ++
                transitionDispatchTrueArmSpanDescriptorFormsFrom amounts
                  segments)
              (transitionTailAffineSeed seed) =
            affineUnaryTripleMap
                (transitionDispatchTrueArmSpanDescriptorBlock amount segment)
                (transitionTailAffineSeed seed) ++
              affineUnaryTripleMap
                (transitionDispatchTrueArmSpanDescriptorFormsFrom amounts
                  segments)
                (transitionTailAffineSeed seed) by
              simp [affineUnaryTripleMap, List.map_append]]
          rw [transitionDispatchTrueArmSpanDescriptorBlock_value, ih]

/-- Fixed true-arm descriptor table of one normalized label layout. -/
noncomputable def
    TransitionDispatchTrueArmNormalizedLayout.affineSpanDescriptorForms
    (tm : _root_.Turing.FinTM2)
    (layout : TransitionDispatchTrueArmNormalizedLayout tm) :
    List AffineUnaryTripleForm :=
  transitionDispatchTrueArmSpanDescriptorFormsFrom
    (layout.affineSpanDropAmounts tm) (layout.affineSpanSegments tm)

/-- Runtime values of one normalized label's true-arm descriptor table. -/
noncomputable def
    TransitionDispatchTrueArmNormalizedLayout.affineSpanDescriptorValues
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (layout : TransitionDispatchTrueArmNormalizedLayout tm) : List Nat :=
  transitionDispatchTrueArmSpanDescriptorValuesFrom seed
    (layout.affineSpanDropAmounts tm) (layout.affineSpanSegments tm)

theorem
    TransitionDispatchTrueArmNormalizedLayout.affineSpanDescriptorForms_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (layout : TransitionDispatchTrueArmNormalizedLayout tm) :
    affineUnaryTripleMap (layout.affineSpanDescriptorForms tm)
        (transitionTailAffineSeed seed) =
      layout.affineSpanDescriptorValues tm seed := by
  exact transitionDispatchTrueArmSpanDescriptorFormsFrom_value seed
    (layout.affineSpanDropAmounts tm) (layout.affineSpanSegments tm)

/-- Complete fixed true-arm span descriptor section in label order. -/
noncomputable def transitionDispatchTrueArmSpanDescriptorForms
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  (transitionDispatchTrueArmNormalizedLayouts tm).flatMap
    (TransitionDispatchTrueArmNormalizedLayout.affineSpanDescriptorForms tm)

/-- Complete runtime true-arm span descriptor values in label order. -/
noncomputable def transitionDispatchTrueArmSpanDescriptorValues
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) : List Nat :=
  (transitionDispatchTrueArmNormalizedLayouts tm).flatMap
    (TransitionDispatchTrueArmNormalizedLayout.affineSpanDescriptorValues
      tm seed)

theorem transitionDispatchTrueArmSpanDescriptorForms_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    affineUnaryTripleMap (transitionDispatchTrueArmSpanDescriptorForms tm)
        (transitionTailAffineSeed seed) =
      transitionDispatchTrueArmSpanDescriptorValues tm seed := by
  unfold transitionDispatchTrueArmSpanDescriptorForms
    transitionDispatchTrueArmSpanDescriptorValues affineUnaryTripleMap
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro layout hlayout
  exact layout.affineSpanDescriptorForms_value tm seed

/-- Ordinary seven-field descriptor values of a progression family. -/
def transitionDispatchProgressionDescriptorValues
    (progressions : List AffineUnaryTripleProgression) : List Nat :=
  progressions.flatMap fun progression =>
    [ progression.base₁, progression.base₂, progression.base₃,
      progression.step₁, progression.step₂, progression.step₃,
      progression.count ]

/-- One unified verifier-fixed form table for all mux invocation operands. -/
noncomputable def transitionDispatchMuxInvocationDescriptorForms
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  transitionDispatchSelectorForms tm ++
    transitionDispatchMuxDescriptorForms tm ++
    transitionDispatchTrueArmSpanDescriptorForms tm ++
    transitionDispatchFalseArmDescriptorForms tm

/-- The four runtime descriptor sections emitted for one transition seed. -/
noncomputable def transitionDispatchMuxInvocationDescriptorValues
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) : List Nat :=
  transitionDispatchSelectors tm seed ++
    transitionDispatchProgressionDescriptorValues
      (transitionDispatchMuxAffineProgressions tm seed) ++
    transitionDispatchTrueArmSpanDescriptorValues tm seed ++
    transitionDispatchProgressionDescriptorValues
      (transitionDispatchFalseArmProgressions tm seed)

/-- Evaluating the single fixed table recovers all four descriptor sections
exactly and in their declared order. -/
theorem transitionDispatchMuxInvocationDescriptorForms_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    affineUnaryTripleMap (transitionDispatchMuxInvocationDescriptorForms tm)
        (transitionTailAffineSeed seed) =
      transitionDispatchMuxInvocationDescriptorValues tm seed := by
  unfold transitionDispatchMuxInvocationDescriptorForms
    transitionDispatchMuxInvocationDescriptorValues
    transitionDispatchProgressionDescriptorValues
  rw [show affineUnaryTripleMap
      (transitionDispatchSelectorForms tm ++
        transitionDispatchMuxDescriptorForms tm ++
        transitionDispatchTrueArmSpanDescriptorForms tm ++
        transitionDispatchFalseArmDescriptorForms tm)
      (transitionTailAffineSeed seed) =
    affineUnaryTripleMap (transitionDispatchSelectorForms tm)
        (transitionTailAffineSeed seed) ++
      affineUnaryTripleMap (transitionDispatchMuxDescriptorForms tm)
        (transitionTailAffineSeed seed) ++
      affineUnaryTripleMap (transitionDispatchTrueArmSpanDescriptorForms tm)
        (transitionTailAffineSeed seed) ++
      affineUnaryTripleMap (transitionDispatchFalseArmDescriptorForms tm)
        (transitionTailAffineSeed seed) by
      simp [affineUnaryTripleMap, List.map_append, List.append_assoc]]
  rw [transitionDispatchSelectorForms_value,
    transitionDispatchMuxDescriptorForms_value,
    transitionDispatchTrueArmSpanDescriptorForms_value,
    transitionDispatchFalseArmDescriptorForms_value]

/-- Raw verifier-input byte stream of the unified descriptor packets. -/
noncomputable def verifierTransitionDispatchMuxInvocationDescriptorFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  verifierTransitionAffineMapFrames W
    (transitionDispatchMuxInvocationDescriptorForms W.machine.tm) input

/-- Exact row-major semantics of the unified raw source. -/
theorem verifierTransitionDispatchMuxInvocationDescriptorFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorFrames W input =
      encodeUnaryFrame
        ((verifierTransitionRowSeeds W input).flatMap
          (transitionDispatchMuxInvocationDescriptorValues W.machine.tm)) := by
  unfold verifierTransitionDispatchMuxInvocationDescriptorFrames
    verifierTransitionAffineMapFrames verifierTransitionTailAffineSeeds
    affineUnaryTripleMapFamily
  congr 1
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro seed hseed
  exact transitionDispatchMuxInvocationDescriptorForms_value W.machine.tm seed

/-- A single concrete polynomial-time TM2 produces every mux invocation
descriptor section directly from the original verifier word. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationDescriptorFrames W) := by
  exact verifierTransitionAffineMapFrames_computableInPolyTime W
    (transitionDispatchMuxInvocationDescriptorForms W.machine.tm)

end CLRS.Chapter34.Turing.CookLevin

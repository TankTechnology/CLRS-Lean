import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouteDropSemantics

/-!
# Semantics of the dispatch-mux true-arm descriptor section

The unified raw source stores every true-arm affine span as an eight-field
block: a verifier-fixed prefix-drop amount followed by one ordinary affine
triple progression descriptor.  This file gives that packet format its exact
mathematical meaning.  It normalizes each span descriptor, proves that the
generated first-coordinate values implement the declared prefix drop, and
then identifies every normalized label group with the true arm of the actual
Cook--Levin dispatch mux.

Keeping this semantic bridge separate from the streaming controller makes the
machine proof small and gives it a precise, independently checked target.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Normalize corresponding prefix-drop amounts and affine span descriptors.
Malformed unequal tables denote the empty family; the verifier-fixed tables
used below are proved to have equal lengths. -/
def transitionDispatchTrueArmSpanProgressionsFrom
    (seed : TransitionRowSeed) :
    List Nat → List TransitionWidenedFallbackSegment →
      List AffineUnaryTripleProgression
  | amount :: amounts, segment :: segments =>
      transitionStackRouteDropPrefix amount
          (transitionWidenedFallbackSegmentProgression seed segment) ::
        transitionDispatchTrueArmSpanProgressionsFrom seed amounts segments
  | _, _ => []

/-- One normalized span emits exactly the first-coordinate values remaining
after its declared prefix drop. -/
theorem transitionDispatchTrueArmSpanProgression_firstValues
    (seed : TransitionRowSeed) (amount : Nat)
    (segment : TransitionWidenedFallbackSegment) :
    transitionProgressionFirstValues
        (transitionStackRouteDropPrefix amount
          (transitionWidenedFallbackSegmentProgression seed segment)) =
      (transitionWidenedFallbackSegmentValues seed segment).drop amount := by
  unfold transitionProgressionFirstValues
    transitionWidenedFallbackSegmentValues
  rw [transitionStackRouteDropPrefix_rows, List.map_drop]

/-- Lock-step normalization has exactly the row semantics of the fixed-group
prefix-drop operation used by the existing true-arm compiler. -/
theorem transitionDispatchTrueArmSpanProgressionsFrom_firstValues
    (seed : TransitionRowSeed) :
    ∀ (amounts : List Nat)
      (segments : List TransitionWidenedFallbackSegment),
      amounts.length = segments.length →
      (transitionDispatchTrueArmSpanProgressionsFrom seed amounts segments).flatMap
          transitionProgressionFirstValues =
        unaryFrameFixedGroupPrefixDropValues amounts
          (transitionAffineSegmentValueRows seed segments) := by
  intro amounts
  induction amounts with
  | nil =>
      intro segments hlength
      have hnil : segments = [] := List.eq_nil_of_length_eq_zero hlength.symm
      subst segments
      rfl
  | cons amount amounts ih =>
      intro segments hlength
      cases segments with
      | nil => simp at hlength
      | cons segment segments =>
          simp only [List.length_cons] at hlength
          simp only [transitionDispatchTrueArmSpanProgressionsFrom,
            List.flatMap_cons, unaryFrameFixedGroupPrefixDropValues,
            transitionAffineSegmentValueRows, List.map_cons]
          rw [transitionDispatchTrueArmSpanProgression_firstValues]
          rw [ih segments (by omega)]
          rfl

/-- Normalized affine progressions of one label's complete true arm. -/
noncomputable def
    TransitionDispatchTrueArmNormalizedLayout.affineSpanProgressions
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (layout : TransitionDispatchTrueArmNormalizedLayout tm) :
    List AffineUnaryTripleProgression :=
  transitionDispatchTrueArmSpanProgressionsFrom seed
    (layout.affineSpanDropAmounts tm) (layout.affineSpanSegments tm)

/-- The normalized progressions of one label generate its complete established
descriptor route, with no lost or duplicated coordinates. -/
theorem
    TransitionDispatchTrueArmNormalizedLayout.affineSpanProgressions_values
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed ∈ verifierTransitionRowSeeds W input)
    (layout : TransitionDispatchTrueArmNormalizedLayout W.machine.tm) :
    (layout.affineSpanProgressions W.machine.tm seed).flatMap
        transitionProgressionFirstValues =
      layout.descriptorValueRoute W.machine.tm seed := by
  unfold TransitionDispatchTrueArmNormalizedLayout.affineSpanProgressions
  rw [transitionDispatchTrueArmSpanProgressionsFrom_firstValues seed
    (layout.affineSpanDropAmounts W.machine.tm)
    (layout.affineSpanSegments W.machine.tm)
    (layout.affineSpanDropAmounts_length W.machine.tm)]
  exact layout.affineSpanSegments_values W input seed hseed

/-- One normalized progression group per program label, in dispatch order. -/
noncomputable def transitionDispatchTrueArmSpanProgressionGroups
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List (List AffineUnaryTripleProgression) :=
  (transitionDispatchTrueArmNormalizedLayouts tm).map fun layout =>
    layout.affineSpanProgressions tm seed

/-- Executing the grouped normalized descriptors recovers every descriptor
true-arm row in the original program-label order. -/
theorem transitionDispatchTrueArmSpanProgressionGroups_values
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed ∈ verifierTransitionRowSeeds W input) :
    (transitionDispatchTrueArmSpanProgressionGroups W.machine.tm seed).map
        (fun progressions =>
          progressions.flatMap transitionProgressionFirstValues) =
      transitionDispatchTrueArmDescriptorRoutes W.machine.tm seed := by
  unfold transitionDispatchTrueArmSpanProgressionGroups
    transitionDispatchTrueArmDescriptorRoutes
  rw [List.map_map]
  apply List.map_congr_left
  intro layout hlayout
  exact layout.affineSpanProgressions_values W input seed hseed

/-- For every verifier-produced transition seed, the normalized descriptor
groups are exactly the true-arm rows of the actual Cook--Levin dispatch muxes.
-/
theorem transitionDispatchTrueArmSpanProgressionGroups_eq_seed
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed ∈ verifierTransitionRowSeeds W input) :
    (transitionDispatchTrueArmSpanProgressionGroups W.machine.tm seed).map
        (fun progressions =>
          progressions.flatMap transitionProgressionFirstValues) =
      transitionDispatchTrueArmRowsFromSeed W.machine.tm seed := by
  rw [transitionDispatchTrueArmSpanProgressionGroups_values W input seed hseed]
  apply transitionDispatchTrueArmDescriptorRoutes_eq_seed
  have hheight := verifierTransitionRowSeeds_height_eq W input seed hseed
  rw [hheight]
  unfold workHeight
  exact Nat.add_pos_left (verifierHeight_eval_pos W input.length) _

end CLRS.Chapter34.Turing.CookLevin

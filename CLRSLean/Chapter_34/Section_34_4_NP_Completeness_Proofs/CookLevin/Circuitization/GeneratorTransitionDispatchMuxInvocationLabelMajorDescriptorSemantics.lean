import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelMajorDescriptorSource

/-!
# Semantics of label-major dispatch descriptors

This module identifies every fixed affine group of the label-major source
with its four runtime descriptor sections.  The result is the precise input
contract for a future single-pass label interpreter: one selector value, one
fresh-coordinate progression descriptor, all normalized true-arm span
descriptors, and the false-arm progression descriptors for the same label.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Value-level lock-step reassembly parallel to the fixed form-group zipper. -/
def transitionDispatchMuxInvocationLabelMajorDescriptorValueGroupsFrom :
    List Nat → List (List Nat) → List (List Nat) → List (List Nat) →
      List (List Nat)
  | selector :: selectors, coordinates :: coordinateGroups,
      whenTrue :: trueGroups, whenFalse :: falseGroups =>
      (selector :: coordinates ++ whenTrue ++ whenFalse) ::
        transitionDispatchMuxInvocationLabelMajorDescriptorValueGroupsFrom
          selectors coordinateGroups trueGroups falseGroups
  | _, _, _, _ => []

/-- The same label-major zipper with the four semantic sections kept as
separate rows.  This is the value-level shape materialized by the concrete
four-row delimiter source. -/
def transitionDispatchMuxInvocationLabelMajorFourRowDescriptorValueGroupsFrom :
    List Nat → List (List Nat) → List (List Nat) → List (List Nat) →
      List (List Nat)
  | selector :: selectors, coordinates :: coordinateGroups,
      whenTrue :: trueGroups, whenFalse :: falseGroups =>
      [[selector], coordinates, whenTrue, whenFalse] ++
        transitionDispatchMuxInvocationLabelMajorFourRowDescriptorValueGroupsFrom
          selectors coordinateGroups trueGroups falseGroups
  | _, _, _, _ => []

private theorem
    transitionDispatchMuxInvocationLabelMajorDescriptorFormGroupsFrom_values
    (seed : TransitionRowSeed)
    (selectors : List AffineUnaryTripleForm)
    (coordinateGroups trueGroups falseGroups :
      List (List AffineUnaryTripleForm)) :
    (transitionDispatchMuxInvocationLabelMajorDescriptorFormGroupsFrom
        selectors coordinateGroups trueGroups falseGroups).map
        (fun group =>
          affineUnaryTripleMap group (transitionTailAffineSeed seed)) =
      transitionDispatchMuxInvocationLabelMajorDescriptorValueGroupsFrom
        (affineUnaryTripleMap selectors (transitionTailAffineSeed seed))
        (coordinateGroups.map fun group =>
          affineUnaryTripleMap group (transitionTailAffineSeed seed))
        (trueGroups.map fun group =>
          affineUnaryTripleMap group (transitionTailAffineSeed seed))
        (falseGroups.map fun group =>
          affineUnaryTripleMap group (transitionTailAffineSeed seed)) := by
  induction selectors generalizing coordinateGroups trueGroups falseGroups with
  | nil => rfl
  | cons selector selectors ih =>
      cases coordinateGroups with
      | nil => rfl
      | cons coordinates coordinateGroups =>
          cases trueGroups with
          | nil => rfl
          | cons whenTrue trueGroups =>
              cases falseGroups with
              | nil => rfl
              | cons whenFalse falseGroups =>
                  simp only [
                    transitionDispatchMuxInvocationLabelMajorDescriptorFormGroupsFrom,
                    List.map_cons]
                  congr 1
                  · simp [affineUnaryTripleMap, List.map_append,
                      List.append_assoc]
                  · exact ih coordinateGroups trueGroups falseGroups

private theorem
    transitionDispatchMuxCoordinateDescriptorFormGroupsForLabels_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    ∀ (offset : TransitionAffineNat) (labels : List tm.Λ),
      (transitionDispatchMuxCoordinateDescriptorFormGroupsForLabels tm
          offset labels).map
          (fun group =>
            affineUnaryTripleMap group (transitionTailAffineSeed seed)) =
        (transitionDispatchMuxAffineProgressionsForLabels tm seed offset
          labels).map fun progression =>
            transitionDispatchProgressionDescriptorValues [progression] := by
  intro offset labels
  induction labels generalizing offset with
  | nil => rfl
  | cons label labels ih =>
      simp only [
        transitionDispatchMuxCoordinateDescriptorFormGroupsForLabels,
        transitionDispatchMuxAffineProgressionsForLabels, List.map_cons]
      rw [transitionDispatchMuxDescriptorBlock_value]
      congr 1
      exact ih _

private theorem
    transitionDispatchMuxCoordinateDescriptorFormGroups_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (transitionDispatchMuxCoordinateDescriptorFormGroups tm).map
        (fun group =>
          affineUnaryTripleMap group (transitionTailAffineSeed seed)) =
      (transitionDispatchMuxCoordinateProgressionGroups tm seed).map
        transitionDispatchProgressionDescriptorValues := by
  unfold transitionDispatchMuxCoordinateDescriptorFormGroups
    transitionDispatchMuxCoordinateProgressionGroups
    transitionDispatchMuxAffineProgressions
  simpa [Function.comp_def] using
    (transitionDispatchMuxCoordinateDescriptorFormGroupsForLabels_values
      tm seed (TransitionAffineNat.const 2) (programLabels tm))

private theorem transitionDispatchTrueArmDescriptorFormGroups_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (transitionDispatchTrueArmDescriptorFormGroups tm).map
        (fun group =>
          affineUnaryTripleMap group (transitionTailAffineSeed seed)) =
      (transitionDispatchTrueArmNormalizedLayouts tm).map fun layout =>
        layout.affineSpanDescriptorValues tm seed := by
  unfold transitionDispatchTrueArmDescriptorFormGroups
  rw [List.map_map]
  apply List.map_congr_left
  intro layout hlayout
  exact layout.affineSpanDescriptorForms_value tm seed

private theorem
    transitionDispatchPreviousOutputDescriptorFormGroupsForLabels_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    ∀ (offset : TransitionAffineNat) (labels : List tm.Λ),
      (transitionDispatchPreviousOutputDescriptorFormGroupsForLabels tm
          offset labels).map
          (fun group =>
            affineUnaryTripleMap group (transitionTailAffineSeed seed)) =
        (transitionDispatchPreviousOutputProgressionsForLabels tm seed offset
          labels).map fun progression =>
            transitionDispatchProgressionDescriptorValues [progression] := by
  intro offset labels
  induction labels generalizing offset with
  | nil => rfl
  | cons label labels ih =>
      cases labels with
      | nil => rfl
      | cons next labels =>
          simp only [
            transitionDispatchPreviousOutputDescriptorFormGroupsForLabels,
            transitionDispatchPreviousOutputProgressionsForLabels,
            List.map_cons]
          rw [transitionDispatchPreviousOutputDescriptorBlock_value]
          congr 1
          exact ih _

private theorem transitionDispatchFalseArmDescriptorFormGroups_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (transitionDispatchFalseArmDescriptorFormGroups tm).map
        (fun group =>
          affineUnaryTripleMap group (transitionTailAffineSeed seed)) =
      (transitionDispatchFalseArmProgressionGroups tm seed).map
        transitionDispatchProgressionDescriptorValues := by
  unfold transitionDispatchFalseArmDescriptorFormGroups
    transitionDispatchFalseArmProgressionGroups
    transitionDispatchPreviousOutputProgressions
  simp only [List.map_cons, List.map_map]
  congr 1
  · exact transitionWidenedFallbackDescriptorForms_value tm seed
  · simpa [Function.comp_def] using
      (transitionDispatchPreviousOutputDescriptorFormGroupsForLabels_values
        tm seed (TransitionAffineNat.const 2) (programLabels tm))

/-- Canonical descriptor packets by label.  Each row contains, in order, the
selector, coordinate progression descriptor, normalized true-span
descriptors, and false-arm progression descriptors of one dispatch label. -/
noncomputable def
    transitionDispatchMuxInvocationLabelMajorCanonicalDescriptorValueGroups
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List (List Nat) :=
  transitionDispatchMuxInvocationLabelMajorDescriptorValueGroupsFrom
    (transitionDispatchSelectors tm seed)
    ((transitionDispatchMuxCoordinateProgressionGroups tm seed).map
      transitionDispatchProgressionDescriptorValues)
    ((transitionDispatchTrueArmNormalizedLayouts tm).map fun layout =>
      layout.affineSpanDescriptorValues tm seed)
    ((transitionDispatchFalseArmProgressionGroups tm seed).map
      transitionDispatchProgressionDescriptorValues)

/-- Canonical physical descriptor rows by label: selector, fresh-coordinate
progressions, normalized true spans, and false-arm progressions. -/
noncomputable def
    transitionDispatchMuxInvocationLabelMajorCanonicalFourRowDescriptorValueGroups
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List (List Nat) :=
  transitionDispatchMuxInvocationLabelMajorFourRowDescriptorValueGroupsFrom
    (transitionDispatchSelectors tm seed)
    ((transitionDispatchMuxCoordinateProgressionGroups tm seed).map
      transitionDispatchProgressionDescriptorValues)
    ((transitionDispatchTrueArmNormalizedLayouts tm).map fun layout =>
      layout.affineSpanDescriptorValues tm seed)
    ((transitionDispatchFalseArmProgressionGroups tm seed).map
      transitionDispatchProgressionDescriptorValues)

/-- Evaluating the verifier-fixed form tables section by section gives the
canonical four physical descriptor rows for every label. -/
theorem
    transitionDispatchMuxInvocationLabelMajorCanonicalFourRowDescriptorValueGroups_eq_forms
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    transitionDispatchMuxInvocationLabelMajorCanonicalFourRowDescriptorValueGroups
        tm seed =
      transitionDispatchMuxInvocationLabelMajorFourRowDescriptorValueGroupsFrom
        (affineUnaryTripleMap (transitionDispatchSelectorForms tm)
          (transitionTailAffineSeed seed))
        ((transitionDispatchMuxCoordinateDescriptorFormGroups tm).map
          fun group =>
            affineUnaryTripleMap group (transitionTailAffineSeed seed))
        ((transitionDispatchTrueArmDescriptorFormGroups tm).map fun group =>
          affineUnaryTripleMap group (transitionTailAffineSeed seed))
        ((transitionDispatchFalseArmDescriptorFormGroups tm).map fun group =>
          affineUnaryTripleMap group (transitionTailAffineSeed seed)) := by
  unfold
    transitionDispatchMuxInvocationLabelMajorCanonicalFourRowDescriptorValueGroups
  rw [transitionDispatchSelectorForms_value]
  rw [transitionDispatchMuxCoordinateDescriptorFormGroups_values]
  rw [transitionDispatchTrueArmDescriptorFormGroups_values]
  rw [transitionDispatchFalseArmDescriptorFormGroups_values]

/-- The runtime values emitted by the fixed label-major affine table are
exactly the canonical per-label descriptor packets. -/
theorem
    transitionDispatchMuxInvocationLabelMajorDescriptorValueGroups_eq_canonical
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    transitionDispatchMuxInvocationLabelMajorDescriptorValueGroups tm seed =
      transitionDispatchMuxInvocationLabelMajorCanonicalDescriptorValueGroups
        tm seed := by
  unfold transitionDispatchMuxInvocationLabelMajorDescriptorValueGroups
    transitionDispatchMuxInvocationLabelMajorDescriptorFormGroups
    transitionDispatchMuxInvocationLabelMajorCanonicalDescriptorValueGroups
  rw [
    transitionDispatchMuxInvocationLabelMajorDescriptorFormGroupsFrom_values]
  rw [transitionDispatchSelectorForms_value]
  rw [transitionDispatchMuxCoordinateDescriptorFormGroups_values]
  rw [transitionDispatchTrueArmDescriptorFormGroups_values]
  rw [transitionDispatchFalseArmDescriptorFormGroups_values]

/-- Byte-exact raw-input semantics in terms of the canonical label-local
descriptor packets. -/
theorem
    verifierTransitionDispatchMuxInvocationLabelMajorDescriptorFrames_eq_canonical
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationLabelMajorDescriptorFrames W input =
      encodeUnaryFrame
        ((verifierTransitionRowSeeds W input).flatMap fun seed =>
          (transitionDispatchMuxInvocationLabelMajorCanonicalDescriptorValueGroups
            W.machine.tm seed).flatten) := by
  rw [verifierTransitionDispatchMuxInvocationLabelMajorDescriptorFrames_eq]
  congr 1
  apply List.flatMap_congr
  intro seed hseed
  rw [
    transitionDispatchMuxInvocationLabelMajorDescriptorValueGroups_eq_canonical]

end CLRS.Chapter34.Turing.CookLevin

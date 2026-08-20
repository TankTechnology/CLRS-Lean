import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorSemantics

/-!
# Label alignment of the dispatch-mux descriptor views

The unified descriptor packet contains four consecutive sections.  Before a
streaming interpreter may combine them, we must know that their semantic
views have the same label boundaries.  This module groups the fresh-coordinate
and false-arm progression families by label, proves exact row semantics for
both, and establishes a common group count with selectors and normalized true
arms on every verifier-produced transition seed.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- One fresh-coordinate progression group per dispatch label. -/
def transitionDispatchMuxCoordinateProgressionGroups
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List (List AffineUnaryTripleProgression) :=
  (transitionDispatchMuxAffineProgressions tm seed).map fun progression =>
    [progression]

/-- Executing the singleton coordinate groups recovers every semantic fresh
mux-coordinate row, without flattening away label boundaries. -/
theorem transitionDispatchMuxCoordinateProgressionGroups_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    (transitionDispatchMuxCoordinateProgressionGroups tm seed).map
        (fun progressions =>
          progressions.flatMap affineUnaryTripleProgressionRows) =
      (transitionDispatchMuxFreshLayoutsFromSeed tm seed).map
        TransitionDispatchMuxFreshLayout.coordinates := by
  unfold transitionDispatchMuxCoordinateProgressionGroups
  simp only [List.map_map]
  rw [transitionDispatchMuxAffineProgressions_eq_runtimes tm seed hwork]
  have hlayouts := transitionDispatchMuxRuntimes_layouts_eq tm seed
  have hcoordinates := congrArg
    (List.map TransitionDispatchMuxFreshLayout.coordinates) hlayouts
  simpa [TransitionDispatchMuxRuntime.layout, List.map_map,
    Function.comp_def] using hcoordinates

private theorem transitionWidenedFallbackProgressions_firstValues_eq
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (transitionWidenedFallbackProgressions tm seed).flatMap
        transitionProgressionFirstValues =
      transitionWidenedFallbackValues tm seed := by
  unfold transitionWidenedFallbackProgressions
  rw [List.flatMap_map]
  change (transitionWidenedFallbackSegments tm).flatMap
      (transitionWidenedFallbackSegmentValues seed) = _
  exact transitionWidenedFallbackSegments_values tm seed

/-- The preceding-output progression attached to each remaining label denotes
that label's complete semantic false arm. -/
theorem transitionDispatchPreviousOutputProgressionsForLabels_rows
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (source : CfgWires tm (workHeight tm seed.height))
    (hwork : 0 < workHeight tm seed.height) :
    ∀ (offset : TransitionAffineNat) (start : Nat)
      (label : tm.Λ) (labels : List tm.Λ),
      start = seed.start + offset.eval seed.height →
      (transitionDispatchPreviousOutputProgressionsForLabels tm seed
          offset (label :: labels)).map transitionProgressionFirstValues =
        transitionDispatchFalseArmRowsForLabels tm seed.height source
          (start + compileStmtGateCost tm (workHeight tm seed.height)
              (tm.m label) +
            (3 * cfgBitCount tm (workHeight tm seed.height) + 1))
          (arithmeticMuxCfgWires tm (workHeight tm seed.height)
            (start + compileStmtGateCost tm (workHeight tm seed.height)
              (tm.m label))) labels := by
  intro offset start label labels hstart
  induction labels generalizing offset start label with
  | nil => rfl
  | cons next labels ih =>
      simp only [transitionDispatchPreviousOutputProgressionsForLabels,
        List.map_cons, transitionDispatchFalseArmRowsForLabels]
      rw [transitionDispatchPreviousOutputProgression_values tm seed offset
        start label hstart hwork]
      congr 1
      apply ih
      rw [TransitionAffineNat.eval_add, TransitionAffineNat.eval_add,
        transitionDispatchStmtGateAffine_eval tm label seed.height hwork,
        transitionDispatchMuxGateAffine_eval tm seed.height, hstart]
      omega

/-- False-arm progression groups in label order: the widened source for the
first label, followed by one preceding-mux output progression per label. -/
def transitionDispatchFalseArmProgressionGroups
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List (List AffineUnaryTripleProgression) :=
  transitionWidenedFallbackProgressions tm seed ::
    (transitionDispatchPreviousOutputProgressions tm seed).map
      fun progression => [progression]

/-- The false-arm groups recover every semantic false-input row and preserve
its label boundary. -/
theorem transitionDispatchFalseArmProgressionGroups_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    (transitionDispatchFalseArmProgressionGroups tm seed).map
        (fun progressions =>
          progressions.flatMap transitionProgressionFirstValues) =
      transitionDispatchFalseArmRowsFromSeed tm seed := by
  unfold transitionDispatchFalseArmProgressionGroups
    transitionDispatchFalseArmRowsFromSeed
    transitionDispatchPreviousOutputProgressions
  cases hlabels : programLabels tm with
  | nil => exact False.elim (programLabels_nonempty tm hlabels)
  | cons label labels =>
      simp only [List.map_cons, List.map_map,
        transitionDispatchFalseArmRowsForLabels]
      rw [transitionWidenedFallbackProgressions_firstValues_eq]
      rw [show transitionCfgWireValues tm (workHeight tm seed.height)
          (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase) =
          transitionWidenedFallbackValues tm seed by
        unfold transitionCfgWireValues
        exact (transitionWidenedFallbackValues_eq_canonical tm seed).symm]
      congr 1
      simpa [Function.comp_def] using
        (transitionDispatchPreviousOutputProgressionsForLabels_rows
          tm seed
          (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
          hwork (TransitionAffineNat.const 2) (seed.start + 2) label labels
          (by simp))

private theorem transitionDispatchTrueArmNormalizedLayoutsForLabels_length
    (tm : _root_.Turing.FinTM2) :
    ∀ (offset : TransitionAffineNat) (labels : List tm.Λ),
      (transitionDispatchTrueArmNormalizedLayoutsForLabels tm offset
        labels).length = labels.length := by
  intro offset labels
  induction labels generalizing offset with
  | nil => rfl
  | cons label labels ih =>
      simp only [transitionDispatchTrueArmNormalizedLayoutsForLabels]
      split <;> simp [ih]

theorem transitionDispatchTrueArmSpanProgressionGroups_length
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (transitionDispatchTrueArmSpanProgressionGroups tm seed).length =
      (programLabels tm).length := by
  unfold transitionDispatchTrueArmSpanProgressionGroups
    transitionDispatchTrueArmNormalizedLayouts
  rw [List.length_map]
  exact transitionDispatchTrueArmNormalizedLayoutsForLabels_length tm
    (TransitionAffineNat.const 2) (programLabels tm)

private theorem transitionDispatchMuxAffineProgressionsForLabels_length
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    ∀ (offset : TransitionAffineNat) (labels : List tm.Λ),
      (transitionDispatchMuxAffineProgressionsForLabels tm seed offset
        labels).length = labels.length := by
  intro offset labels
  induction labels generalizing offset with
  | nil => rfl
  | cons label labels ih =>
      simp [transitionDispatchMuxAffineProgressionsForLabels, ih]

theorem transitionDispatchMuxCoordinateProgressionGroups_length
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (transitionDispatchMuxCoordinateProgressionGroups tm seed).length =
      (programLabels tm).length := by
  unfold transitionDispatchMuxCoordinateProgressionGroups
    transitionDispatchMuxAffineProgressions
  rw [List.length_map]
  exact transitionDispatchMuxAffineProgressionsForLabels_length tm seed
    (TransitionAffineNat.const 2) (programLabels tm)

private theorem transitionDispatchFalseArmRowsForLabels_length
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (source : CfgWires tm (workHeight tm height)) :
    ∀ (start : Nat) (fallback : CfgWires tm (workHeight tm height))
      (labels : List tm.Λ),
      (transitionDispatchFalseArmRowsForLabels tm height source start fallback
        labels).length = labels.length := by
  intro start fallback labels
  induction labels generalizing start fallback with
  | nil => rfl
  | cons label labels ih =>
      simp [transitionDispatchFalseArmRowsForLabels, ih]

theorem transitionDispatchFalseArmProgressionGroups_length
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed ∈ verifierTransitionRowSeeds W input) :
    (transitionDispatchFalseArmProgressionGroups W.machine.tm seed).length =
      (programLabels W.machine.tm).length := by
  have hwork : 0 < workHeight W.machine.tm seed.height := by
    have hheight := verifierTransitionRowSeeds_height_eq W input seed hseed
    rw [hheight]
    unfold workHeight
    exact Nat.add_pos_left (verifierHeight_eval_pos W input.length) _
  have hrows := transitionDispatchFalseArmProgressionGroups_values
    W.machine.tm seed hwork
  have hlength := congrArg List.length hrows
  rw [List.length_map] at hlength
  rw [hlength]
  unfold transitionDispatchFalseArmRowsFromSeed
  exact transitionDispatchFalseArmRowsForLabels_length W.machine.tm
    seed.height
    (arithmeticWidenedCfgWires W.machine.tm seed.height seed.start seed.rowBase)
    (seed.start + 2)
    (arithmeticWidenedCfgWires W.machine.tm seed.height seed.start seed.rowBase)
    (programLabels W.machine.tm)

@[simp] theorem transitionDispatchSelectors_length
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (transitionDispatchSelectors tm seed).length =
      (programLabels tm).length := by
  simp [transitionDispatchSelectors]

/-- All four independently encoded mux sections have exactly one semantic
group per fixed program label on every verifier transition row. -/
theorem transitionDispatchMuxDescriptorSections_length_aligned
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed ∈ verifierTransitionRowSeeds W input) :
    (transitionDispatchSelectors W.machine.tm seed).length =
        (transitionDispatchMuxCoordinateProgressionGroups W.machine.tm
          seed).length ∧
      (transitionDispatchMuxCoordinateProgressionGroups W.machine.tm
          seed).length =
        (transitionDispatchTrueArmSpanProgressionGroups W.machine.tm
          seed).length ∧
      (transitionDispatchTrueArmSpanProgressionGroups W.machine.tm
          seed).length =
        (transitionDispatchFalseArmProgressionGroups W.machine.tm
          seed).length := by
  rw [transitionDispatchSelectors_length,
    transitionDispatchMuxCoordinateProgressionGroups_length,
    transitionDispatchTrueArmSpanProgressionGroups_length,
    transitionDispatchFalseArmProgressionGroups_length W input seed hseed]
  exact ⟨rfl, rfl, rfl⟩

end CLRS.Chapter34.Turing.CookLevin

import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouteHeightActions

/-!
# Affine source family for widened stack cells

The cell portion of a widened stack consists of one public consecutive segment
followed by a verifier-fixed number of two-segment blank rows.  This module
identifies that descriptor family with both the closed fallback values and the
actual cell rows of the widened wire bundle.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- First-track values of segment progressions are exactly the concatenated
closed values of the original segment table. -/
theorem transitionStackRouteSegmentProgressions_values
    (seed : TransitionRowSeed)
    (segments : List TransitionWidenedFallbackSegment) :
    transitionStackRouteFirstValues
        (segments.map (transitionWidenedFallbackSegmentProgression seed)) =
      segments.flatMap (transitionWidenedFallbackSegmentValues seed) := by
  induction segments with
  | nil => rfl
  | cons segment rest ih =>
      simp only [List.map_cons, transitionStackRouteFirstValues,
        List.flatMap_cons, List.map_append]
      change transitionWidenedFallbackSegmentValues seed segment ++
          transitionStackRouteFirstValues
            (rest.map (transitionWidenedFallbackSegmentProgression seed)) = _
      rw [ih]

/-- Fixed descriptor segments for the cell portion of one widened stack. -/
noncomputable def transitionStackRouteCellSegments
    (tm : _root_.Turing.FinTM2) (k : tm.K) :
    List TransitionWidenedFallbackSegment :=
  transitionWidenedFallbackPublicCellSegment tm k ::
    (List.replicate (maxPushesPerStep tm)
      (transitionWidenedFallbackBlankCellSegments tm k)).flatten

/-- Runtime progression family for the flattened cell rows. -/
noncomputable def transitionStackRouteCellProgressions
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K) :
    List AffineUnaryTripleProgression :=
  (transitionStackRouteCellSegments tm k).map
    (transitionWidenedFallbackSegmentProgression seed)

/-- The cell descriptor family denotes exactly the canonical widened cell
value stream. -/
theorem transitionStackRouteCellProgressions_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K) :
    transitionStackRouteFirstValues
        (transitionStackRouteCellProgressions tm seed k) =
      transitionWidenedFallbackStackCellValues tm seed k := by
  unfold transitionStackRouteCellProgressions
  rw [transitionStackRouteSegmentProgressions_values]
  have hstack :=
    transitionWidenedFallbackStackSegments_values tm seed k
  unfold transitionWidenedFallbackStackSegments
    transitionWidenedFallbackStackValues at hstack
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil] at hstack
  rw [transitionWidenedFallbackPublicHeightSegment_values,
    transitionWidenedFallbackOverflowHeightSegment_values] at hstack
  rw [transitionWidenedFallbackStackHeightValues_eq_parts] at hstack
  simp only [List.append_assoc] at hstack
  unfold transitionStackRouteCellSegments
  exact List.append_cancel_left (List.append_cancel_left hstack)

/-- Flattening the actual widened source cell rows gives exactly the
first-track stream of the cell descriptor family. -/
theorem transitionWidenedStackCellValues_eq_routeSource
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K) :
    (TransitionStackValueBlock.ofWires
      ((arithmeticWidenedCfgWires tm seed.height seed.start
        seed.rowBase).stack k)).cellRows.flatten =
      transitionStackRouteFirstValues
        (transitionStackRouteCellProgressions tm seed k) := by
  rw [transitionStackRouteCellProgressions_values]
  unfold TransitionStackValueBlock.ofWires transitionStackCellWireRows
    transitionWidenedFallbackStackCellValues
  apply congrArg List.flatten
  apply List.ofFn_inj.mpr
  funext cell
  apply List.ofFn_inj.mpr
  funext symbol
  exact arithmeticWidenedCfgWires_stackCell tm seed k cell symbol

end CLRS.Chapter34.Turing.CookLevin

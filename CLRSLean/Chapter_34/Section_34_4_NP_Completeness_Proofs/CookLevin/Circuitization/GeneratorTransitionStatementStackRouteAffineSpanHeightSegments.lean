import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouteAffineSpanBounds
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionAffineSegmentRows
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouteStructuredSourceFrames

/-!
# Affine segment realization of compact stack-height spans

A normalized height route consists of inserted affine singletons, a prefix-
trimmed public-coordinate segment, a suffix-trimmed false-overflow segment,
and inserted affine singletons.  These are exactly the operations supported
by the existing fixed affine segment and fixed-position prefix-drop machines.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Singleton affine segments for a fixed list of inserted forms. -/
def transitionStackAffineSpanConstantSegments
    (forms : List AffineUnaryTripleForm) :
    List TransitionWidenedFallbackSegment :=
  forms.map transitionStackRouteSingletonSegment

/-- False-overflow height segment after removing a fixed suffix. -/
def transitionStackAffineSpanOverflowHeightSegment
    (tm : _root_.Turing.FinTM2) (sourceRdrop : Nat) :
    TransitionWidenedFallbackSegment :=
  { base := transitionAbsoluteStartForm (TransitionAffineNat.const 0)
    step := 0
    count := TransitionAffineNat.const
      (maxPushesPerStep tm - sourceRdrop) }

/-- Fixed segment table realizing one compact height span. -/
noncomputable def transitionStackAffineSpanHeightSegments
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (span : TransitionRouteSpan AffineUnaryTripleForm) :
    List TransitionWidenedFallbackSegment :=
  transitionStackAffineSpanConstantSegments span.headValues ++
    [transitionWidenedFallbackPublicHeightSegment tm k,
      transitionStackAffineSpanOverflowHeightSegment tm span.sourceRdrop] ++
    transitionStackAffineSpanConstantSegments span.tailValues

/-- Per-segment prefix deletions for a compact height span. -/
def transitionStackAffineSpanHeightDropAmounts
    (span : TransitionRouteSpan AffineUnaryTripleForm) : List Nat :=
  List.replicate span.headValues.length 0 ++
    [span.sourceDrop, 0] ++
    List.replicate span.tailValues.length 0

@[simp] theorem transitionStackAffineSpanConstantSegments_length
    (forms : List AffineUnaryTripleForm) :
    (transitionStackAffineSpanConstantSegments forms).length = forms.length := by
  simp [transitionStackAffineSpanConstantSegments]

theorem transitionStackAffineSpanHeightSegments_length
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (span : TransitionRouteSpan AffineUnaryTripleForm) :
    (transitionStackAffineSpanHeightSegments tm k span).length =
      span.headValues.length + 2 + span.tailValues.length := by
  simp [transitionStackAffineSpanHeightSegments]
  omega

theorem transitionStackAffineSpanHeightDropAmounts_length
    (span : TransitionRouteSpan AffineUnaryTripleForm) :
    (transitionStackAffineSpanHeightDropAmounts span).length =
      span.headValues.length + 2 + span.tailValues.length := by
  simp [transitionStackAffineSpanHeightDropAmounts]
  omega

theorem transitionStackAffineSpanHeightDropAmounts_nonempty
    (span : TransitionRouteSpan AffineUnaryTripleForm) :
    0 < (transitionStackAffineSpanHeightDropAmounts span).length := by
  rw [transitionStackAffineSpanHeightDropAmounts_length]
  omega

/-- Inserted singleton segments evaluate to their affine form list. -/
theorem transitionStackAffineSpanConstantSegments_values
    (seed : TransitionRowSeed) (forms : List AffineUnaryTripleForm) :
    (transitionStackAffineSpanConstantSegments forms).flatMap
        (transitionWidenedFallbackSegmentValues seed) =
      affineUnaryTripleMap forms (transitionTailAffineSeed seed) := by
  induction forms with
  | nil => rfl
  | cons form forms ih =>
      change (List.map transitionStackRouteSingletonSegment forms).flatMap
          (transitionWidenedFallbackSegmentValues seed) =
        forms.map (fun item => affineUnaryTripleFormValue item
          (transitionTailAffineSeed seed)) at ih
      simp only [transitionStackAffineSpanConstantSegments, List.map_cons,
        List.flatMap_cons, affineUnaryTripleMap, List.map_cons]
      rw [transitionStackRouteSingletonSegment_values]
      rw [ih]
      rfl

private theorem fixedGroupPrefixDropValues_replicate_zero
    (rows : List (List Nat)) :
    unaryFrameFixedGroupPrefixDropValues
        (List.replicate rows.length 0) rows = rows.flatten := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      rw [show (row :: rows).length = rows.length + 1 by simp]
      rw [show rows.length + 1 = Nat.succ rows.length by omega]
      simp only [List.replicate_succ,
        unaryFrameFixedGroupPrefixDropValues, List.drop_zero,
        List.flatten_cons]
      rw [ih]

private theorem fixedZeroConstantSegments_then
    (seed : TransitionRowSeed) (forms : List AffineUnaryTripleForm)
    (drops : List Nat) (rows : List (List Nat)) :
    unaryFrameFixedGroupPrefixDropValues
        (List.replicate forms.length 0 ++ drops)
        ((transitionStackAffineSpanConstantSegments forms).map
          (transitionWidenedFallbackSegmentValues seed) ++ rows) =
      affineUnaryTripleMap forms (transitionTailAffineSeed seed) ++
        unaryFrameFixedGroupPrefixDropValues drops rows := by
  induction forms with
  | nil => rfl
  | cons form forms ih =>
      change unaryFrameFixedGroupPrefixDropValues
          (List.replicate forms.length 0 ++ drops)
          ((List.map transitionStackRouteSingletonSegment forms).map
            (transitionWidenedFallbackSegmentValues seed) ++ rows) =
        forms.map (fun item => affineUnaryTripleFormValue item
            (transitionTailAffineSeed seed)) ++
          unaryFrameFixedGroupPrefixDropValues drops rows at ih
      simp only [List.length_cons, List.replicate_succ, List.cons_append,
        transitionStackAffineSpanConstantSegments, List.map_cons,
        unaryFrameFixedGroupPrefixDropValues, List.drop_zero,
        affineUnaryTripleMap]
      rw [transitionStackRouteSingletonSegment_values]
      rw [ih]
      simp

theorem transitionStackAffineSpanOverflowHeightSegment_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (sourceRdrop : Nat) :
    transitionWidenedFallbackSegmentValues seed
        (transitionStackAffineSpanOverflowHeightSegment tm sourceRdrop) =
      List.replicate (maxPushesPerStep tm - sourceRdrop) seed.start := by
  rw [transitionWidenedFallbackSegmentValues_eq_replicate]
  · simp [transitionStackAffineSpanOverflowHeightSegment,
      transitionAbsoluteStartForm_value]
  · rfl

private theorem transitionStackAffineSpanHeightSegments_expanded
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K)
    (span : TransitionRouteSpan AffineUnaryTripleForm) :
    unaryFrameFixedGroupPrefixDropValues
        (transitionStackAffineSpanHeightDropAmounts span)
        (transitionAffineSegmentValueRows seed
          (transitionStackAffineSpanHeightSegments tm k span)) =
      affineUnaryTripleMap span.headValues (transitionTailAffineSeed seed) ++
        (transitionWidenedFallbackSegmentValues seed
          (transitionWidenedFallbackPublicHeightSegment tm k)).drop
            span.sourceDrop ++
        transitionWidenedFallbackSegmentValues seed
          (transitionStackAffineSpanOverflowHeightSegment tm
            span.sourceRdrop) ++
        affineUnaryTripleMap span.tailValues
          (transitionTailAffineSeed seed) := by
  unfold transitionStackAffineSpanHeightDropAmounts
    transitionStackAffineSpanHeightSegments transitionAffineSegmentValueRows
  rw [List.map_append, List.map_append]
  simp only [List.append_assoc]
  rw [fixedZeroConstantSegments_then]
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    unaryFrameFixedGroupPrefixDropValues, List.drop_zero]
  have htail := fixedGroupPrefixDropValues_replicate_zero
    ((transitionStackAffineSpanConstantSegments span.tailValues).map
      (transitionWidenedFallbackSegmentValues seed))
  simp only [List.length_map,
    transitionStackAffineSpanConstantSegments_length] at htail
  rw [htail]
  rw [show
      ((transitionStackAffineSpanConstantSegments span.tailValues).map
        (transitionWidenedFallbackSegmentValues seed)).flatten =
        (transitionStackAffineSpanConstantSegments span.tailValues).flatMap
          (transitionWidenedFallbackSegmentValues seed) by rfl]
  rw [transitionStackAffineSpanConstantSegments_values]

private theorem rdrop_drop_append_parts
    (publicValues overflowValues : List α) (left right : Nat)
    (hleft : left ≤ publicValues.length)
    (hright : right ≤ overflowValues.length) :
    ((publicValues ++ overflowValues).drop left).rdrop right =
      publicValues.drop left ++ overflowValues.rdrop right := by
  rw [List.drop_append_of_le_length hleft]
  rw [List.rdrop_append_of_le_length right hright]

/-- The segment table and fixed prefix drops evaluate exactly to a compact
height span whenever both deletions stay in their designated source pieces. -/
theorem transitionStackAffineSpanHeightSegments_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K)
    (span : TransitionRouteSpan AffineUnaryTripleForm)
    (hleft : span.sourceDrop ≤ seed.height + 1)
    (hright : span.sourceRdrop ≤ maxPushesPerStep tm) :
    unaryFrameFixedGroupPrefixDropValues
        (transitionStackAffineSpanHeightDropAmounts span)
        (transitionAffineSegmentValueRows seed
          (transitionStackAffineSpanHeightSegments tm k span)) =
      ((span.map fun form => affineUnaryTripleFormValue form
        (transitionTailAffineSeed seed)).eval
          (transitionStackRouteSourceBlock tm seed k).heightValues) := by
  rw [transitionStackAffineSpanHeightSegments_expanded]
  rw [transitionWidenedFallbackPublicHeightSegment_values,
    transitionStackAffineSpanOverflowHeightSegment_values]
  unfold TransitionRouteSpan.eval TransitionRouteSpan.middle
    TransitionRouteSpan.map
  have hsource :
      (transitionStackRouteSourceBlock tm seed k).heightValues =
        transitionWidenedFallbackSegmentValues seed
            (transitionWidenedFallbackPublicHeightSegment tm k) ++
          transitionWidenedFallbackSegmentValues seed
            (transitionWidenedFallbackOverflowHeightSegment tm) := by
    rw [← transitionStackRouteFirstValues_eq_sourceBlock_height]
    unfold transitionStackRouteFirstValues
      transitionStackRouteHeightProgressions
      transitionStackRouteHeightSegments
    simp only [List.map_cons, List.map_nil, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.map_append]
    rfl
  rw [hsource]
  rw [rdrop_drop_append_parts _ _ span.sourceDrop span.sourceRdrop]
  · rw [transitionWidenedFallbackPublicHeightSegment_values,
      transitionWidenedFallbackOverflowHeightSegment_values]
    unfold affineUnaryTripleMap List.rdrop
    simp [List.append_assoc]
  · rw [transitionWidenedFallbackPublicHeightSegment_values]
    simp
    exact hleft
  · rw [transitionWidenedFallbackOverflowHeightSegment_values]
    simp
    exact hright

/-- Actual terminal routes satisfy the segment-table side conditions on every
verifier transition seed. -/
theorem TransitionStmtTerminalRowLayout.stackAffineSpanHeightSegments_values
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed ∈ verifierTransitionRowSeeds W input)
    (label : W.machine.tm.Λ) (labelOffset : TransitionAffineNat)
    (layout : TransitionStmtTerminalRowLayout W.machine.tm)
    (hlayout : transitionStmtTerminalRowLayout W.machine.tm
      (W.machine.tm.m label)
      (stmtPushSet_program_subset W.machine.tm label) = some layout)
    (k : W.machine.tm.K) :
    unaryFrameFixedGroupPrefixDropValues
        (transitionStackAffineSpanHeightDropAmounts
          (layout.stackAffineSpanRoute W.machine.tm k
            labelOffset).heightSpan)
        (transitionAffineSegmentValueRows seed
          (transitionStackAffineSpanHeightSegments W.machine.tm k
            (layout.stackAffineSpanRoute W.machine.tm k
              labelOffset).heightSpan)) =
      ((layout.stackAffineSpanRoute W.machine.tm k labelOffset).eval seed
        (transitionStackRouteSourceBlock W.machine.tm seed k)).heightValues := by
  apply transitionStackAffineSpanHeightSegments_values
  · have hbounds := layout.stackAffineSpanRoute_sourceDrop_le W.machine.tm
      label labelOffset hlayout k
    have hheight := verifierTransitionRowSeeds_height_eq W input seed hseed
    have hpadding := verifierHeight_actionPadding_le W input.length
    rw [hheight]
    omega
  · exact (layout.stackAffineSpanRoute_sourceRdrop_le W.machine.tm label
      labelOffset hlayout k).1

end CLRS.Chapter34.Turing.CookLevin

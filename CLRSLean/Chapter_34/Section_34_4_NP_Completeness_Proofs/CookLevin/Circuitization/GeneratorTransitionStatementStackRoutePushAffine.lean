import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionAffineSegmentCompiler
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRoutePrimitive

/-!
# Fixed affine segment table for one stack push

At positive workspace slack, a push row is itself a fixed affine progression
table: one false height value, the public height interval, the shortened false
overflow, the pushed symbol row, the public cell interval, and the shortened
blank-cell suffix.  This module proves that table byte-equal to the established
primitive push route.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- A singleton affine progression segment. -/
def transitionStackRouteSingletonSegment
    (base : AffineUnaryTripleForm) : TransitionWidenedFallbackSegment :=
  { base := base
    step := 0
    count := TransitionAffineNat.const 1 }

theorem transitionStackRouteSingletonSegment_values
    (seed : TransitionRowSeed) (base : AffineUnaryTripleForm) :
    transitionWidenedFallbackSegmentValues seed
        (transitionStackRouteSingletonSegment base) =
      [affineUnaryTripleFormValue base (transitionTailAffineSeed seed)] := by
  rw [transitionWidenedFallbackSegmentValues_eq_replicate]
  · simp [transitionStackRouteSingletonSegment]
  · rfl

/-- The false wire inserted at the head of a pushed height row. -/
def transitionStackRoutePushFalseSegment :
    TransitionWidenedFallbackSegment :=
  transitionStackRouteSingletonSegment
    (transitionAbsoluteStartForm (TransitionAffineNat.const 0))

@[simp] theorem transitionStackRoutePushFalseSegment_values
    (seed : TransitionRowSeed) :
    transitionWidenedFallbackSegmentValues seed
        transitionStackRoutePushFalseSegment = [seed.start] := by
  unfold transitionStackRoutePushFalseSegment
  rw [transitionStackRouteSingletonSegment_values]
  simp [transitionAbsoluteStartForm_value]

/-- The old false overflow suffix with its final coordinate removed. -/
def transitionStackRoutePushOverflowTailSegment
    (tm : _root_.Turing.FinTM2) : TransitionWidenedFallbackSegment :=
  { base := transitionAbsoluteStartForm (TransitionAffineNat.const 0)
    step := 0
    count := TransitionAffineNat.const (maxPushesPerStep tm - 1) }

theorem transitionStackRoutePushOverflowTailSegment_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    transitionWidenedFallbackSegmentValues seed
        (transitionStackRoutePushOverflowTailSegment tm) =
      List.replicate (maxPushesPerStep tm - 1) seed.start := by
  rw [transitionWidenedFallbackSegmentValues_eq_replicate]
  · simp [transitionStackRoutePushOverflowTailSegment,
      transitionAbsoluteStartForm_value]
  · rfl

/-- Affine form of one coordinate of the pushed symbol row. -/
def transitionStackRoutePushSymbolForm
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (labelOffset : TransitionAffineNat)
    (symbolOffsets : Fin (reachableAlphabet tm k).card → TransitionAffineNat)
    (code : Fin ((reachableAlphabet tm k).card + 1)) :
    AffineUnaryTripleForm :=
  if hcode : code.val < (reachableAlphabet tm k).card then
    transitionAbsoluteStartForm
      (labelOffset.add
        ((symbolOffsets ⟨code.val, hcode⟩).shiftInput
          (maxPushesPerStep tm)))
  else
    transitionAbsoluteStartForm (TransitionAffineNat.const 0)

/-- One singleton segment per pushed symbol coordinate. -/
def transitionStackRoutePushSymbolSegments
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (labelOffset : TransitionAffineNat)
    (symbolOffsets : Fin (reachableAlphabet tm k).card → TransitionAffineNat) :
    List TransitionWidenedFallbackSegment :=
  List.ofFn fun code => transitionStackRouteSingletonSegment
    (transitionStackRoutePushSymbolForm
      tm k labelOffset symbolOffsets code)

/-- The symbol singleton segments spell exactly the semantic pushed row. -/
theorem transitionStackRoutePushSymbolSegments_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K)
    (labelOffset : TransitionAffineNat)
    (symbolOffsets : Fin (reachableAlphabet tm k).card → TransitionAffineNat) :
    (transitionStackRoutePushSymbolSegments
        tm k labelOffset symbolOffsets).flatMap
        (transitionWidenedFallbackSegmentValues seed) =
      transitionPushedSymbolWireRow tm k seed.start
        (fun target =>
          (seed.start + labelOffset.eval seed.height) +
            (symbolOffsets target).eval (workHeight tm seed.height)) := by
  unfold transitionStackRoutePushSymbolSegments
    transitionPushedSymbolWireRow
  rw [List.ofFn_eq_map, List.ofFn_eq_map]
  generalize List.finRange ((reachableAlphabet tm k).card + 1) = codes
  induction codes with
  | nil => rfl
  | cons code rest ih =>
      simp only [List.flatMap_cons, List.map_cons]
      rw [transitionStackRouteSingletonSegment_values, ih]
      simp only [List.singleton_append]
      congr 1
      unfold transitionStackRoutePushSymbolForm
      split_ifs with hlt
      · rw [transitionAbsoluteStartForm_value,
          TransitionAffineNat.eval_add,
          TransitionAffineNat.eval_shiftInput]
        simp [workHeight]
        omega
      · rw [transitionAbsoluteStartForm_value]
        simp

/-- The cell segments remaining after removing one bottom blank row. -/
def transitionStackRoutePushCellTailSegments
    (tm : _root_.Turing.FinTM2) (k : tm.K) :
    List TransitionWidenedFallbackSegment :=
  transitionWidenedFallbackPublicCellSegment tm k ::
    (List.replicate (maxPushesPerStep tm - 1)
      (transitionWidenedFallbackBlankCellSegments tm k)).flatten

private theorem push_flatMap_replicate_blankSegments
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (k : tm.K) (count : Nat) :
    ((List.replicate count
        (transitionWidenedFallbackBlankCellSegments tm k)).flatten).flatMap
        (transitionWidenedFallbackSegmentValues seed) =
      (List.replicate count
        (transitionWidenedFallbackBlankCellValues tm seed k)).flatten := by
  unfold transitionWidenedFallbackBlankCellSegments
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.flatten_cons,
        List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]
      rw [transitionWidenedFallbackBlankFalseSegment_values,
        transitionWidenedFallbackBlankTrueSegment_values, ih]
      rw [← transitionWidenedFallbackBlankCellValues_eq_parts]

private theorem push_heightTail_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K)
    (hpush : 0 < maxPushesPerStep tm) :
    [transitionWidenedFallbackPublicHeightSegment tm k,
        transitionStackRoutePushOverflowTailSegment tm].flatMap
        (transitionWidenedFallbackSegmentValues seed) =
      transitionStackRouteFirstValues
        (transitionStackRouteTrimSuffix 1
          (transitionStackRouteHeightProgressions tm seed k)) := by
  rw [transitionStackRouteFirstValues_trimSuffix,
    transitionStackRouteHeightProgressions_values,
    transitionWidenedFallbackStackHeightValues_eq_parts]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [transitionWidenedFallbackPublicHeightSegment_values,
    transitionStackRoutePushOverflowTailSegment_values]
  rw [List.rdrop_append_of_le_length]
  · simp [List.rdrop]
  · simp
    omega

private theorem push_cellTail_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K)
    (hpush : 0 < maxPushesPerStep tm) :
    (transitionStackRoutePushCellTailSegments tm k).flatMap
        (transitionWidenedFallbackSegmentValues seed) =
      transitionStackRouteFirstValues
        (transitionStackRouteTrimSuffix
          ((reachableAlphabet tm k).card + 1)
          (transitionStackRouteCellProgressions tm seed k)) := by
  rw [transitionStackRouteFirstValues_trimSuffix,
    transitionStackRouteCellProgressions_values,
    transitionWidenedFallbackStackCellValues_eq_parts]
  unfold transitionStackRoutePushCellTailSegments
  simp only [List.flatMap_cons]
  rw [transitionWidenedFallbackPublicCellSegment_values,
    push_flatMap_replicate_blankSegments]
  let width := (reachableAlphabet tm k).card + 1
  let blank := transitionWidenedFallbackBlankCellValues tm seed k
  have hblank : blank.length = width := by
    simp [blank, width, transitionWidenedFallbackBlankCellValues]
  have hsuffixLength :
      (List.replicate (maxPushesPerStep tm) blank).flatten.length =
        maxPushesPerStep tm * width := by
    simpa using List.flatten_length_fixedWidth
      (List.replicate (maxPushesPerStep tm) blank) width (by
        intro row hrow
        rw [List.mem_replicate] at hrow
        exact hrow.2 ▸ hblank)
  have hwidth :
      width ≤ (List.replicate (maxPushesPerStep tm) blank).flatten.length := by
    rw [hsuffixLength]
    calc
      width = 1 * width := by simp
      _ ≤ maxPushesPerStep tm * width :=
        Nat.mul_le_mul_right width (by omega)
  rw [List.rdrop_append_of_le_length width hwidth]
  have hdrop := List.flatten_rdrop_one_fixedWidth
    (List.replicate (maxPushesPerStep tm) blank)
    (maxPushesPerStep tm - 1) width (by simp; omega) (by
      intro row hrow
      rw [List.mem_replicate] at hrow
      exact hrow.2 ▸ hblank)
  simp only [List.take_replicate] at hdrop
  rw [hdrop]
  simp [blank]

/-- Complete fixed segment table for one primitive stack push. -/
def transitionStackRoutePushSegments
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (labelOffset : TransitionAffineNat)
    (symbolOffsets : Fin (reachableAlphabet tm k).card → TransitionAffineNat) :
    List TransitionWidenedFallbackSegment :=
  [transitionStackRoutePushFalseSegment,
    transitionWidenedFallbackPublicHeightSegment tm k,
    transitionStackRoutePushOverflowTailSegment tm] ++
    transitionStackRoutePushSymbolSegments tm k labelOffset symbolOffsets ++
    transitionStackRoutePushCellTailSegments tm k

theorem transitionStackRoutePushSegments_nonempty
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (labelOffset : TransitionAffineNat)
    (symbolOffsets : Fin (reachableAlphabet tm k).card → TransitionAffineNat) :
    0 < (transitionStackRoutePushSegments
      tm k labelOffset symbolOffsets).length := by
  simp [transitionStackRoutePushSegments]

/-- At positive push slack, the affine table is byte-equal to the established
primitive push route. -/
theorem transitionStackRoutePushSegments_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K)
    (labelOffset : TransitionAffineNat)
    (symbolOffsets : Fin (reachableAlphabet tm k).card → TransitionAffineNat)
    (hpush : 0 < maxPushesPerStep tm) :
    transitionAffineSegmentFirstValues seed
        (transitionStackRoutePushSegments tm k labelOffset symbolOffsets) =
      transitionStackRoutePushBlockValues tm seed k
        (fun target =>
          (seed.start + labelOffset.eval seed.height) +
            (symbolOffsets target).eval (workHeight tm seed.height)) := by
  unfold transitionAffineSegmentFirstValues
    transitionAffineSegmentProgressions
  rw [transitionStackRouteSegmentProgressions_values]
  unfold transitionStackRoutePushSegments
  simp only [List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]
  rw [transitionStackRoutePushFalseSegment_values,
    transitionStackRoutePushSymbolSegments_values,
    push_cellTail_values tm seed k hpush]
  have hheight := push_heightTail_values tm seed k hpush
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hheight
  rw [hheight]
  unfold transitionStackRoutePushBlockValues
    transitionStackRoutePushHeightValues
    transitionStackRoutePushCellValues
  have hwork : 0 < workHeight tm seed.height := by
    unfold workHeight
    omega
  obtain ⟨height, hheightWork⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hwork)
  simp [hheightWork, List.append_assoc]

end CLRS.Chapter34.Turing.CookLevin

import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionAffineSegmentRows
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRoutePushAffine

/-!
# Fixed affine segment table for one stack pop

A pop keeps the existing affine source segments, inserts affine singleton
segments for the fresh height and final false height, and appends one fixed
blank symbol row.  Prefix deletion is delayed to the segment-group controller:
two values are removed from the positive public-height segment and one symbol
row from the positive public-cell segment.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Affine singleton carrying the fresh top-height wire. -/
def transitionStackRoutePopFreshSegment
    (tm : _root_.Turing.FinTM2)
    (labelOffset heightWireOffset : TransitionAffineNat) :
    TransitionWidenedFallbackSegment :=
  transitionStackRouteSingletonSegment
    (transitionAbsoluteStartForm
      (labelOffset.add
        (heightWireOffset.shiftInput (maxPushesPerStep tm))))

theorem transitionStackRoutePopFreshSegment_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset heightWireOffset : TransitionAffineNat) :
    transitionWidenedFallbackSegmentValues seed
        (transitionStackRoutePopFreshSegment
          tm labelOffset heightWireOffset) =
      [(seed.start + labelOffset.eval seed.height) +
        heightWireOffset.eval (workHeight tm seed.height)] := by
  unfold transitionStackRoutePopFreshSegment
  rw [transitionStackRouteSingletonSegment_values]
  rw [transitionAbsoluteStartForm_value,
    TransitionAffineNat.eval_add,
    TransitionAffineNat.eval_shiftInput]
  simp [workHeight, Nat.add_assoc]

/-- Original blank workspace rows followed by the new bottom blank row. -/
def transitionStackRoutePopBlankSuffixSegments
    (tm : _root_.Turing.FinTM2) (k : tm.K) :
    List TransitionWidenedFallbackSegment :=
  (List.replicate (maxPushesPerStep tm)
      (transitionWidenedFallbackBlankCellSegments tm k)).flatten ++
    transitionWidenedFallbackBlankCellSegments tm k

/-- Segment carrier for a positive-height primitive pop. -/
noncomputable def transitionStackRoutePopSegments
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (labelOffset heightWireOffset : TransitionAffineNat) :
    List TransitionWidenedFallbackSegment :=
  [transitionStackRoutePopFreshSegment tm labelOffset heightWireOffset,
    transitionWidenedFallbackPublicHeightSegment tm k,
    transitionWidenedFallbackOverflowHeightSegment tm,
    transitionStackRoutePushFalseSegment,
    transitionWidenedFallbackPublicCellSegment tm k] ++
      transitionStackRoutePopBlankSuffixSegments tm k

/-- Per-segment prefix deletion table. -/
def transitionStackRoutePopDropAmounts
    (tm : _root_.Turing.FinTM2) (k : tm.K) : List Nat :=
  [0, 2, 0, 0, (reachableAlphabet tm k).card + 1] ++
    List.replicate
      (transitionStackRoutePopBlankSuffixSegments tm k).length 0

theorem transitionStackRoutePopSegments_length
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (labelOffset heightWireOffset : TransitionAffineNat) :
    (transitionStackRoutePopSegments
      tm k labelOffset heightWireOffset).length =
      5 + (transitionStackRoutePopBlankSuffixSegments tm k).length := by
  simp [transitionStackRoutePopSegments]
  omega

theorem transitionStackRoutePopDropAmounts_length
    (tm : _root_.Turing.FinTM2) (k : tm.K) :
    (transitionStackRoutePopDropAmounts tm k).length =
      5 + (transitionStackRoutePopBlankSuffixSegments tm k).length := by
  simp [transitionStackRoutePopDropAmounts]
  omega

theorem transitionStackRoutePopDropAmounts_nonempty
    (tm : _root_.Turing.FinTM2) (k : tm.K) :
    0 < (transitionStackRoutePopDropAmounts tm k).length := by
  simp [transitionStackRoutePopDropAmounts]

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

private theorem pop_flatten_map_eq_flatMap
    {α β : Type} (items : List α) (values : α → List β) :
    (items.map values).flatten = items.flatMap values := by
  induction items with
  | nil => rfl
  | cons item items ih => simp [ih]

private theorem pop_replicate_blankSegments_values
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

private theorem pop_blankSuffix_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (k : tm.K) :
    (transitionStackRoutePopBlankSuffixSegments tm k).flatMap
        (transitionWidenedFallbackSegmentValues seed) =
      (List.replicate (maxPushesPerStep tm)
          (transitionWidenedFallbackBlankCellValues tm seed k)).flatten ++
        transitionWidenedFallbackBlankCellValues tm seed k := by
  unfold transitionStackRoutePopBlankSuffixSegments
  rw [List.flatMap_append, pop_replicate_blankSegments_values]
  unfold transitionWidenedFallbackBlankCellSegments
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [transitionWidenedFallbackBlankFalseSegment_values,
    transitionWidenedFallbackBlankTrueSegment_values,
    ← transitionWidenedFallbackBlankCellValues_eq_parts]

private theorem pop_blankCellValues_eq_wireRow
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (k : tm.K) :
    transitionWidenedFallbackBlankCellValues tm seed k =
      transitionBlankSymbolWireRow tm k seed.start (seed.start + 1) := by
  unfold transitionWidenedFallbackBlankCellValues
    transitionBlankSymbolWireRow arithmeticBlankHeadWires
  apply List.ofFn_inj.mpr
  funext code
  unfold encodeHeadCode
  by_cases hlast : code.val = (reachableAlphabet tm k).card
  · have hcode : code = Fin.last (reachableAlphabet tm k).card := by
      apply Fin.ext
      simpa using hlast
    subst code
    simp
  · have hcode : code ≠ Fin.last (reachableAlphabet tm k).card := by
      intro heq
      apply hlast
      simpa [heq]
    simp [hcode, hlast]

private theorem pop_segmentDrops_expanded
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (k : tm.K) (labelOffset heightWireOffset : TransitionAffineNat) :
    unaryFrameFixedGroupPrefixDropValues
        (transitionStackRoutePopDropAmounts tm k)
        (transitionAffineSegmentValueRows seed
          (transitionStackRoutePopSegments
            tm k labelOffset heightWireOffset)) =
      [(seed.start + labelOffset.eval seed.height) +
          heightWireOffset.eval (workHeight tm seed.height)] ++
        (transitionWidenedFallbackSegmentValues seed
          (transitionWidenedFallbackPublicHeightSegment tm k)).drop 2 ++
        transitionWidenedFallbackSegmentValues seed
          (transitionWidenedFallbackOverflowHeightSegment tm) ++
        [seed.start] ++
        (transitionWidenedFallbackSegmentValues seed
          (transitionWidenedFallbackPublicCellSegment tm k)).drop
            ((reachableAlphabet tm k).card + 1) ++
        (transitionStackRoutePopBlankSuffixSegments tm k).flatMap
          (transitionWidenedFallbackSegmentValues seed) := by
  unfold transitionStackRoutePopDropAmounts
    transitionStackRoutePopSegments transitionAffineSegmentValueRows
  rw [List.map_append]
  simp only [List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, unaryFrameFixedGroupPrefixDropValues,
    List.drop_zero]
  have hsuffix := fixedGroupPrefixDropValues_replicate_zero
    ((transitionStackRoutePopBlankSuffixSegments tm k).map
      (transitionWidenedFallbackSegmentValues seed))
  simp only [List.length_map] at hsuffix
  rw [hsuffix]
  rw [pop_flatten_map_eq_flatMap]
  rw [transitionStackRoutePopFreshSegment_values,
    transitionStackRoutePushFalseSegment_values]
  simp [List.append_assoc]

/-- At positive public tableau height, the carried affine segments and fixed
prefix deletions are byte-equal to the established primitive pop route. -/
theorem transitionStackRoutePopSegments_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K)
    (labelOffset heightWireOffset : TransitionAffineNat)
    (hheight : 0 < seed.height) :
    unaryFrameFixedGroupPrefixDropValues
        (transitionStackRoutePopDropAmounts tm k)
        (transitionAffineSegmentValueRows seed
          (transitionStackRoutePopSegments
            tm k labelOffset heightWireOffset)) =
      transitionStackRoutePopBlockValues tm seed k
        ((seed.start + labelOffset.eval seed.height) +
          heightWireOffset.eval (workHeight tm seed.height)) := by
  rw [pop_segmentDrops_expanded]
  rw [transitionWidenedFallbackPublicHeightSegment_values,
    transitionWidenedFallbackOverflowHeightSegment_values,
    transitionWidenedFallbackPublicCellSegment_values,
    pop_blankSuffix_values]
  unfold transitionStackRoutePopBlockValues
    transitionStackRoutePopHeightValues
    transitionStackRoutePopCellValues
  have hwork : 0 < workHeight tm seed.height := by
    unfold workHeight
    omega
  obtain ⟨height, hheightWork⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hwork)
  simp only [hheightWork]
  rw [transitionStackRouteHeightDrop_values,
    transitionStackRouteFirstValues_drop,
    transitionStackRouteCellProgressions_values,
    transitionWidenedFallbackStackHeightValues_eq_parts,
    transitionWidenedFallbackStackCellValues_eq_parts]
  rw [← pop_blankCellValues_eq_wireRow]
  rw [List.drop_append_of_le_length]
  · rw [List.drop_append_of_le_length]
    · simp [transitionWidenedFallbackBlankCellValues,
        List.append_assoc]
    · simp
      omega
  · simp
    omega

end CLRS.Chapter34.Turing.CookLevin

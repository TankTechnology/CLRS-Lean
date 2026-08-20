import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouteAffineSpanHeightFrames

/-!
# Affine segment realization of compact stack-cell spans

Cell routes use the same compact interval normal form as height routes, but
their semantic unit is a fixed-width symbol row.  The generated segment table
therefore drops `sourceDrop * alphabetWidth` public coordinates and shortens
the replicated blank-row suffix by `sourceRdrop` rows.  Fixed-width flattening
lemmas connect that bit stream back to the row-valued stack semantics.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Fixed blank-cell segment suffix after removing a fixed number of rows. -/
def transitionStackAffineSpanBlankCellSegments
    (tm : _root_.Turing.FinTM2) (k : tm.K) (sourceRdrop : Nat) :
    List TransitionWidenedFallbackSegment :=
  (List.replicate (maxPushesPerStep tm - sourceRdrop)
    (transitionWidenedFallbackBlankCellSegments tm k)).flatten

/-- Complete fixed segment table realizing a compact cell-row span. -/
noncomputable def transitionStackAffineSpanCellSegments
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (span : TransitionRouteSpan (List AffineUnaryTripleForm)) :
    List TransitionWidenedFallbackSegment :=
  let suffix :=
    transitionStackAffineSpanBlankCellSegments tm k span.sourceRdrop ++
      transitionStackAffineSpanConstantSegments span.tailValues.flatten
  transitionStackAffineSpanConstantSegments span.headValues.flatten ++
    transitionWidenedFallbackPublicCellSegment tm k :: suffix

/-- Per-segment prefix deletions for a compact cell-row span. -/
def transitionStackAffineSpanCellDropAmounts
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (span : TransitionRouteSpan (List AffineUnaryTripleForm)) : List Nat :=
  let suffix :=
    transitionStackAffineSpanBlankCellSegments tm k span.sourceRdrop ++
      transitionStackAffineSpanConstantSegments span.tailValues.flatten
  List.replicate span.headValues.flatten.length 0 ++
    [span.sourceDrop * ((reachableAlphabet tm k).card + 1)] ++
    List.replicate suffix.length 0

@[simp] theorem transitionStackAffineSpanBlankCellSegments_length
    (tm : _root_.Turing.FinTM2) (k : tm.K) (sourceRdrop : Nat) :
    (transitionStackAffineSpanBlankCellSegments tm k sourceRdrop).length =
      2 * (maxPushesPerStep tm - sourceRdrop) := by
  simp [transitionStackAffineSpanBlankCellSegments,
    transitionWidenedFallbackBlankCellSegments]
  omega

theorem transitionStackAffineSpanCellSegments_length
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (span : TransitionRouteSpan (List AffineUnaryTripleForm)) :
    (transitionStackAffineSpanCellSegments tm k span).length =
      span.headValues.flatten.length + 1 +
        (transitionStackAffineSpanBlankCellSegments tm k
          span.sourceRdrop).length + span.tailValues.flatten.length := by
  simp [transitionStackAffineSpanCellSegments]
  omega

theorem transitionStackAffineSpanCellDropAmounts_length
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (span : TransitionRouteSpan (List AffineUnaryTripleForm)) :
    (transitionStackAffineSpanCellDropAmounts tm k span).length =
      (transitionStackAffineSpanCellSegments tm k span).length := by
  rw [transitionStackAffineSpanCellSegments_length]
  simp [transitionStackAffineSpanCellDropAmounts]
  omega

theorem transitionStackAffineSpanCellDropAmounts_nonempty
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (span : TransitionRouteSpan (List AffineUnaryTripleForm)) :
    0 < (transitionStackAffineSpanCellDropAmounts tm k span).length := by
  rw [transitionStackAffineSpanCellDropAmounts_length,
    transitionStackAffineSpanCellSegments_length]
  omega

private theorem cell_fixedGroupPrefixDropValues_replicate_zero
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

private theorem cell_fixedZeroConstantSegments_then
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
      rw [transitionStackRouteSingletonSegment_values, ih]
      simp

/-- Shortened blank-cell segments denote the corresponding replicated blank
row suffix. -/
theorem transitionStackAffineSpanBlankCellSegments_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (k : tm.K) (sourceRdrop : Nat) :
    (transitionStackAffineSpanBlankCellSegments tm k sourceRdrop).flatMap
        (transitionWidenedFallbackSegmentValues seed) =
      (List.replicate (maxPushesPerStep tm - sourceRdrop)
        (transitionWidenedFallbackBlankCellValues tm seed k)).flatten := by
  unfold transitionStackAffineSpanBlankCellSegments
    transitionWidenedFallbackBlankCellSegments
  induction maxPushesPerStep tm - sourceRdrop with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.flatten_cons,
        List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]
      rw [transitionWidenedFallbackBlankFalseSegment_values,
        transitionWidenedFallbackBlankTrueSegment_values, ih]
      rw [← transitionWidenedFallbackBlankCellValues_eq_parts]

/-- Evaluating affine forms row-by-row and flattening equals evaluating their
flattened form list. -/
theorem affineUnaryTripleMap_rows_flatten
    (seed : AffineUnaryTripleSeed)
    (rows : List (List AffineUnaryTripleForm)) :
    (rows.map fun forms => affineUnaryTripleMap forms seed).flatten =
      affineUnaryTripleMap rows.flatten seed := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp [affineUnaryTripleMap]

private theorem flatten_rdrop_fixedWidth
    (rows : List (List Nat)) (count width : Nat)
    (hcount : count ≤ rows.length)
    (hrows : ∀ row ∈ rows, row.length = width) :
    rows.flatten.rdrop (count * width) = (rows.rdrop count).flatten := by
  unfold List.rdrop
  have hlength : rows.flatten.length = rows.length * width :=
    List.flatten_length_fixedWidth rows width hrows
  rw [hlength]
  rw [← Nat.sub_mul]
  rw [List.flatten_take_fixedWidth]
  omega
  exact hrows

private theorem cell_rdrop_drop_append_parts
    (publicValues overflowValues : List α) (left right : Nat)
    (hleft : left ≤ publicValues.length)
    (hright : right ≤ overflowValues.length) :
    ((publicValues ++ overflowValues).drop left).rdrop right =
      publicValues.drop left ++ overflowValues.rdrop right := by
  rw [List.drop_append_of_le_length hleft]
  rw [List.rdrop_append_of_le_length right hright]

private theorem transitionStackAffineSpanCellSegments_expanded
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K)
    (span : TransitionRouteSpan (List AffineUnaryTripleForm)) :
    unaryFrameFixedGroupPrefixDropValues
        (transitionStackAffineSpanCellDropAmounts tm k span)
        (transitionAffineSegmentValueRows seed
          (transitionStackAffineSpanCellSegments tm k span)) =
      affineUnaryTripleMap span.headValues.flatten
          (transitionTailAffineSeed seed) ++
        (transitionWidenedFallbackSegmentValues seed
          (transitionWidenedFallbackPublicCellSegment tm k)).drop
            (span.sourceDrop * ((reachableAlphabet tm k).card + 1)) ++
        (transitionStackAffineSpanBlankCellSegments tm k
          span.sourceRdrop).flatMap
            (transitionWidenedFallbackSegmentValues seed) ++
        affineUnaryTripleMap span.tailValues.flatten
          (transitionTailAffineSeed seed) := by
  unfold transitionStackAffineSpanCellDropAmounts
    transitionStackAffineSpanCellSegments transitionAffineSegmentValueRows
  dsimp only
  rw [List.map_append]
  simp only [List.append_assoc]
  rw [cell_fixedZeroConstantSegments_then]
  simp only [List.map_cons, List.singleton_append,
    unaryFrameFixedGroupPrefixDropValues]
  have hsuffix := cell_fixedGroupPrefixDropValues_replicate_zero
    (((transitionStackAffineSpanBlankCellSegments tm k span.sourceRdrop ++
      transitionStackAffineSpanConstantSegments
        span.tailValues.flatten).map
          (transitionWidenedFallbackSegmentValues seed)))
  simp only [List.length_map] at hsuffix
  rw [hsuffix]
  rw [show
      ((transitionStackAffineSpanBlankCellSegments tm k span.sourceRdrop ++
        transitionStackAffineSpanConstantSegments span.tailValues.flatten).map
          (transitionWidenedFallbackSegmentValues seed)).flatten =
        (transitionStackAffineSpanBlankCellSegments tm k span.sourceRdrop ++
          transitionStackAffineSpanConstantSegments span.tailValues.flatten
          ).flatMap (transitionWidenedFallbackSegmentValues seed) by rfl]
  rw [List.flatMap_append,
    transitionStackAffineSpanConstantSegments_values]

/-- The cell segment table evaluates exactly to the flattened compact row
span whenever its endpoint deletions remain in the public/overflow pieces. -/
theorem transitionStackAffineSpanCellSegments_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K)
    (span : TransitionRouteSpan (List AffineUnaryTripleForm))
    (hleft : span.sourceDrop ≤ seed.height)
    (hright : span.sourceRdrop ≤ maxPushesPerStep tm) :
    unaryFrameFixedGroupPrefixDropValues
        (transitionStackAffineSpanCellDropAmounts tm k span)
        (transitionAffineSegmentValueRows seed
          (transitionStackAffineSpanCellSegments tm k span)) =
      ((span.map fun forms => affineUnaryTripleMap forms
        (transitionTailAffineSeed seed)).eval
          (transitionStackRouteSourceBlock tm seed k).cellRows).flatten := by
  let width := (reachableAlphabet tm k).card + 1
  let source := (transitionStackRouteSourceBlock tm seed k).cellRows
  let blank := transitionWidenedFallbackBlankCellValues tm seed k
  have hshape :
      (transitionStackRouteSourceBlock tm seed k).HasShape tm k
        (workHeight tm seed.height) := by
    rw [transitionStackRouteSourceBlock_eq]
    exact TransitionStackValueBlock.hasShape_ofWires tm k
      (workHeight tm seed.height)
      ((arithmeticWidenedCfgWires tm seed.height seed.start
        seed.rowBase).stack k)
  have hsourceLength : source.length = workHeight tm seed.height := hshape.2.1
  have hsourceRows : ∀ row ∈ source, row.length = width := hshape.2.2
  have hleftSource : span.sourceDrop ≤ source.length := by
    rw [hsourceLength]
    unfold workHeight
    omega
  have hrightDrop : span.sourceRdrop ≤ (source.drop span.sourceDrop).length := by
    rw [List.length_drop, hsourceLength]
    unfold workHeight
    omega
  have hdropRows : ∀ row ∈ source.drop span.sourceDrop,
      row.length = width := by
    intro row hrow
    exact hsourceRows row (List.mem_of_mem_drop hrow)
  have hmiddleFlatten :
      ((source.drop span.sourceDrop).rdrop span.sourceRdrop).flatten =
        (source.flatten.drop (span.sourceDrop * width)).rdrop
          (span.sourceRdrop * width) := by
    rw [← flatten_rdrop_fixedWidth (source.drop span.sourceDrop)
      span.sourceRdrop width hrightDrop hdropRows]
    rw [List.flatten_drop_fixedWidth source span.sourceDrop width
      hleftSource hsourceRows]
  have hsourceParts :
      source.flatten =
        transitionWidenedFallbackSegmentValues seed
            (transitionWidenedFallbackPublicCellSegment tm k) ++
          (List.replicate (maxPushesPerStep tm) blank).flatten := by
    dsimp only [source]
    rw [transitionStackRouteSourceBlock_eq]
    rw [transitionWidenedStackCellValues_eq_routeSource]
    rw [transitionStackRouteCellProgressions_values]
    rw [transitionWidenedFallbackStackCellValues_eq_parts]
    rw [transitionWidenedFallbackPublicCellSegment_values]
  have hblankLength : blank.length = width := by
    simp [blank, width, transitionWidenedFallbackBlankCellValues]
  have hoverflowLength :
      (List.replicate (maxPushesPerStep tm) blank).flatten.length =
        maxPushesPerStep tm * width := by
    have h := List.flatten_length_fixedWidth
      (List.replicate (maxPushesPerStep tm) blank) width (by
        intro row hrow
        rw [List.eq_of_mem_replicate hrow]
        exact hblankLength)
    simpa using h
  have hpublicLength :
      (transitionWidenedFallbackSegmentValues seed
        (transitionWidenedFallbackPublicCellSegment tm k)).length =
          seed.height * width := by
    rw [transitionWidenedFallbackPublicCellSegment_values]
    simp [width]
  have hoverflowTrim :
      (List.replicate (maxPushesPerStep tm) blank).flatten.rdrop
          (span.sourceRdrop * width) =
        (List.replicate (maxPushesPerStep tm - span.sourceRdrop)
          blank).flatten := by
    rw [flatten_rdrop_fixedWidth]
    · unfold List.rdrop
      simp
    · simp
      exact hright
    · intro row hrow
      rw [List.eq_of_mem_replicate hrow]
      exact hblankLength
  rw [transitionStackAffineSpanCellSegments_expanded,
    transitionStackAffineSpanBlankCellSegments_values]
  unfold TransitionRouteSpan.eval TransitionRouteSpan.middle
    TransitionRouteSpan.map
  rw [List.flatten_append, List.flatten_append]
  rw [affineUnaryTripleMap_rows_flatten,
    affineUnaryTripleMap_rows_flatten]
  rw [hmiddleFlatten, hsourceParts]
  rw [cell_rdrop_drop_append_parts]
  · rw [hoverflowTrim]
    dsimp only [width, blank]
    simp only [List.append_assoc]
  · rw [hpublicLength]
    exact Nat.mul_le_mul_right width hleft
  · rw [hoverflowLength]
    exact Nat.mul_le_mul_right width hright

/-- Actual terminal routes satisfy the cell segment-table side conditions on
every verifier transition seed. -/
theorem TransitionStmtTerminalRowLayout.stackAffineSpanCellSegments_values
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
        (transitionStackAffineSpanCellDropAmounts W.machine.tm k
          (layout.stackAffineSpanRoute W.machine.tm k labelOffset).cellSpan)
        (transitionAffineSegmentValueRows seed
          (transitionStackAffineSpanCellSegments W.machine.tm k
            (layout.stackAffineSpanRoute W.machine.tm k
              labelOffset).cellSpan)) =
      ((layout.stackAffineSpanRoute W.machine.tm k labelOffset).eval seed
        (transitionStackRouteSourceBlock W.machine.tm seed k)).cellRows.flatten := by
  apply transitionStackAffineSpanCellSegments_values
  · have hbounds := layout.stackAffineSpanRoute_sourceDrop_le W.machine.tm
      label labelOffset hlayout k
    have hheight := verifierTransitionRowSeeds_height_eq W input seed hseed
    have hpadding := verifierHeight_actionPadding_le W input.length
    rw [hheight]
    omega
  · exact (layout.stackAffineSpanRoute_sourceRdrop_le W.machine.tm label
      labelOffset hlayout k).2

end CLRS.Chapter34.Turing.CookLevin

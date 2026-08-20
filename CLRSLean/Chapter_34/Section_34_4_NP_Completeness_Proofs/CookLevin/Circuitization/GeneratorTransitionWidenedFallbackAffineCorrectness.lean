import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionWidenedFallbackAffine

/-!
# Correctness of the widened fallback segment table

This module identifies the first track of the generated progression family
with the canonical widened workspace row.  It contains only list and affine
arithmetic; execution by a fixed TM2 is isolated in the following module.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Source values carried by the first track of one runtime segment. -/
def transitionWidenedFallbackSegmentValues
    (seed : TransitionRowSeed)
    (segment : TransitionWidenedFallbackSegment) : List Nat :=
  (affineUnaryTripleProgressionRows
    (transitionWidenedFallbackSegmentProgression seed segment)).map
      fun row => row.1

/-- Closed positional formula for one segment's emitted values. -/
theorem transitionWidenedFallbackSegmentValues_eq_ofFn
    (seed : TransitionRowSeed)
    (segment : TransitionWidenedFallbackSegment) :
    transitionWidenedFallbackSegmentValues seed segment =
      List.ofFn fun index : Fin (segment.count.eval seed.height) =>
        affineUnaryTripleFormValue segment.base
            (transitionTailAffineSeed seed) + index.val * segment.step := by
  unfold transitionWidenedFallbackSegmentValues
  rw [affineUnaryTripleProgressionRows_eq_ofFn, List.map_ofFn]
  rfl

/-- A unit-stride segment is the corresponding consecutive interval. -/
theorem transitionWidenedFallbackSegmentValues_eq_range
    (seed : TransitionRowSeed)
    (segment : TransitionWidenedFallbackSegment)
    (hstep : segment.step = 1) :
    transitionWidenedFallbackSegmentValues seed segment =
      List.range'
        (affineUnaryTripleFormValue segment.base
          (transitionTailAffineSeed seed))
        (segment.count.eval seed.height) := by
  rw [transitionWidenedFallbackSegmentValues_eq_ofFn,
    ← transitionEqOfFnAdd_eq_range]
  apply List.ofFn_inj.mpr
  funext index
  simp [hstep]

/-- A zero-stride segment is a constant replicated block. -/
theorem transitionWidenedFallbackSegmentValues_eq_replicate
    (seed : TransitionRowSeed)
    (segment : TransitionWidenedFallbackSegment)
    (hstep : segment.step = 0) :
    transitionWidenedFallbackSegmentValues seed segment =
      List.replicate (segment.count.eval seed.height)
        (affineUnaryTripleFormValue segment.base
          (transitionTailAffineSeed seed)) := by
  rw [transitionWidenedFallbackSegmentValues_eq_ofFn,
    ← List.ofFn_const]
  apply List.ofFn_inj.mpr
  funext index
  simp [hstep]

theorem transitionWidenedFallbackPrefixSegment_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    transitionWidenedFallbackSegmentValues seed
        (transitionWidenedFallbackPrefixSegment tm) =
      transitionWidenedFallbackPrefixValues tm seed := by
  rw [transitionWidenedFallbackSegmentValues_eq_range]
  · simp [transitionWidenedFallbackPrefixSegment,
      transitionWidenedFallbackPrefixValues]
  · rfl

theorem transitionWidenedFallbackPublicHeightSegment_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (k : tm.K) :
    transitionWidenedFallbackSegmentValues seed
        (transitionWidenedFallbackPublicHeightSegment tm k) =
      List.range'
        (seed.rowBase + transitionEqPrefixWidth tm +
          cfgStackBitOffset tm seed.height k)
        (seed.height + 1) := by
  rw [transitionWidenedFallbackSegmentValues_eq_range]
  · simp only [transitionWidenedFallbackPublicHeightSegment,
      transitionAbsoluteRowBaseForm_value]
    rw [TransitionAffineNat.eval_add, TransitionAffineNat.eval_const,
      transitionStackBitOffsetAffine_eval]
    simp [TransitionAffineNat.eval]
    omega
  · rfl

theorem transitionWidenedFallbackOverflowHeightSegment_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    transitionWidenedFallbackSegmentValues seed
        (transitionWidenedFallbackOverflowHeightSegment tm) =
      List.replicate (maxPushesPerStep tm) seed.start := by
  rw [transitionWidenedFallbackSegmentValues_eq_replicate]
  · simp only [transitionWidenedFallbackOverflowHeightSegment,
      TransitionAffineNat.eval_const]
    rw [transitionAbsoluteStartForm_value]
    simp
  · rfl

theorem transitionWidenedFallbackPublicCellSegment_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (k : tm.K) :
    transitionWidenedFallbackSegmentValues seed
        (transitionWidenedFallbackPublicCellSegment tm k) =
      List.range'
        (seed.rowBase + transitionEqPrefixWidth tm +
          cfgStackBitOffset tm seed.height k + (seed.height + 1))
        (seed.height * ((reachableAlphabet tm k).card + 1)) := by
  rw [transitionWidenedFallbackSegmentValues_eq_range]
  · simp only [transitionWidenedFallbackPublicCellSegment,
      transitionAbsoluteRowBaseForm_value]
    rw [TransitionAffineNat.eval_add, TransitionAffineNat.eval_add,
      TransitionAffineNat.eval_const, transitionStackBitOffsetAffine_eval]
    simp [TransitionAffineNat.eval]
    constructor
    · ring
    · omega
  · rfl

theorem transitionWidenedFallbackBlankFalseSegment_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (k : tm.K) :
    transitionWidenedFallbackSegmentValues seed
        (transitionWidenedFallbackBlankFalseSegment tm k) =
      List.replicate (reachableAlphabet tm k).card seed.start := by
  rw [transitionWidenedFallbackSegmentValues_eq_replicate]
  · simp only [transitionWidenedFallbackBlankFalseSegment,
      TransitionAffineNat.eval_const]
    rw [transitionAbsoluteStartForm_value]
    simp
  · rfl

theorem transitionWidenedFallbackBlankTrueSegment_values
    (seed : TransitionRowSeed) :
    transitionWidenedFallbackSegmentValues seed
        transitionWidenedFallbackBlankTrueSegment =
      [seed.start + 1] := by
  rw [transitionWidenedFallbackSegmentValues_eq_replicate]
  · simp only [transitionWidenedFallbackBlankTrueSegment,
      TransitionAffineNat.eval_const]
    rw [transitionAbsoluteStartForm_value]
    simp
  · rfl

/-- Flattening a replicated two-segment cell table commutes with collecting
the values of both segments. -/
private theorem transitionWidenedFallback_replicate_blankSegments
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
        List.flatMap_append]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [transitionWidenedFallbackBlankFalseSegment_values,
        transitionWidenedFallbackBlankTrueSegment_values, ih]
      rw [← transitionWidenedFallbackBlankCellValues_eq_parts]

/-- The generated segment values of one stack are its canonical widened
height and cell values. -/
theorem transitionWidenedFallbackStackSegments_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (k : tm.K) :
    (transitionWidenedFallbackStackSegments tm k).flatMap
        (transitionWidenedFallbackSegmentValues seed) =
      transitionWidenedFallbackStackValues tm seed k := by
  unfold transitionWidenedFallbackStackSegments
    transitionWidenedFallbackStackValues
  rw [List.flatMap_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [transitionWidenedFallbackPublicHeightSegment_values,
    transitionWidenedFallbackOverflowHeightSegment_values,
    transitionWidenedFallbackPublicCellSegment_values,
    transitionWidenedFallback_replicate_blankSegments,
    transitionWidenedFallbackStackHeightValues_eq_parts,
    transitionWidenedFallbackStackCellValues_eq_parts]
  simp [List.append_assoc]

private theorem transitionWidenedFallback_flatMap_flatten
    {alpha beta gamma : Type}
    (items : List alpha) (blocks : alpha → List beta)
    (values : beta → List gamma) :
    ((items.map blocks).flatten).flatMap values =
      items.flatMap fun item => (blocks item).flatMap values := by
  induction items with
  | nil => rfl
  | cons item items ih => simp [ih]

private theorem transitionWidenedFallback_flatMap_eq_map_flatten
    {alpha beta : Type} (items : List alpha) (values : alpha → List beta) :
    items.flatMap values = (items.map values).flatten := by
  induction items with
  | nil => rfl
  | cons item items ih => simp [ih]

/-- Collecting the first progression track of the complete fixed table gives
the byte-value-exact canonical widened fallback row. -/
theorem transitionWidenedFallbackSegments_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (transitionWidenedFallbackSegments tm).flatMap
        (transitionWidenedFallbackSegmentValues seed) =
      transitionWidenedFallbackValues tm seed := by
  unfold transitionWidenedFallbackSegments transitionWidenedFallbackValues
  simp only [List.flatMap_cons]
  rw [transitionWidenedFallbackPrefixSegment_values]
  rw [transitionWidenedFallback_flatMap_flatten]
  rw [transitionWidenedFallback_flatMap_eq_map_flatten]
  congr 1
  apply congrArg List.flatten
  apply List.map_congr_left
  intro position hposition
  exact transitionWidenedFallbackStackSegments_values tm seed
    ((arithmeticStackEquiv tm).symm position)

end CLRS.Chapter34.Turing.CookLevin

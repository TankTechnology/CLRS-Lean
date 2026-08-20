import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineMuxInvocationProgressionControllerRun
import Mathlib.Tactic

/-!
# Polynomial bounds for affine mux invocation expansion

Selectors occur once in a compact segment source but are replayed in every
coordinate frame.  The output and runtime are therefore quadratic, rather
than linear, in the compact source length.  This file isolates that arithmetic
from the controller execution proof.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

theorem affineMuxInvocationProgressionControllerRowSteps_le_frame
    (selector selectorNot : Nat) (row : Nat × Nat × Nat) :
    affineMuxInvocationProgressionControllerRowSteps selector selectorNot row ≤
      5 * (encodeAffineMuxFinPairFrame
        (affineMuxInvocationFrameOfRow selector selectorNot row)).length := by
  simp [affineMuxInvocationProgressionControllerRowSteps,
    affineMuxInvocationFrameOfRow, encodeAffineMuxFinPairFrame_length]
  omega

theorem affineMuxInvocationProgressionControllerRowsSteps_le_frames
    (selector selectorNot : Nat) (rows : List (Nat × Nat × Nat)) :
    affineMuxInvocationProgressionControllerRowsSteps selector selectorNot rows ≤
      5 * (affineMuxInvocationRowsFrames selector selectorNot rows).length := by
  induction rows with
  | nil => simp [affineMuxInvocationProgressionControllerRowsSteps,
      affineMuxInvocationRowsFrames]
  | cons row rest ih =>
      have hrow :=
        affineMuxInvocationProgressionControllerRowSteps_le_frame
          selector selectorNot row
      simp only [affineMuxInvocationRowsFrames] at ih
      simp only [affineMuxInvocationProgressionControllerRowsSteps,
        affineMuxInvocationRowsFrames, List.flatMap_cons, List.length_append]
      omega

theorem affineMuxInvocationFrameOfRow_length_le_source
    (selector selectorNot : Nat) (row : Nat × Nat × Nat) :
    (encodeAffineMuxFinPairFrame
        (affineMuxInvocationFrameOfRow selector selectorNot row)).length ≤
      (selector + selectorNot + 5) *
        (encodeUnaryFrame (affineUnaryTripleRowValues row)).length := by
  simp [affineMuxInvocationFrameOfRow, affineUnaryTripleRowValues,
    encodeAffineMuxFinPairFrame_length, encodeUnaryFrame_length]
  nlinarith

theorem affineMuxInvocationRowsFrames_length_le_source
    (selector selectorNot : Nat) (rows : List (Nat × Nat × Nat)) :
    (affineMuxInvocationRowsFrames selector selectorNot rows).length ≤
      (selector + selectorNot + 5) *
        (affineMuxInvocationRowsSource rows).length := by
  induction rows with
  | nil => simp [affineMuxInvocationRowsFrames,
      affineMuxInvocationRowsSource]
  | cons row rest ih =>
      have hrow := affineMuxInvocationFrameOfRow_length_le_source
        selector selectorNot row
      simp only [affineMuxInvocationRowsFrames,
        affineMuxInvocationRowsSource] at ih
      simp only [affineMuxInvocationRowsFrames,
        affineMuxInvocationRowsSource, List.flatMap_cons, List.length_append]
      rw [Nat.mul_add]
      exact Nat.add_le_add hrow ih

theorem AffineMuxInvocationProgression.sourceFrames_length_eq
    (segment : AffineMuxInvocationProgression) :
    segment.sourceFrames.length =
      segment.selector + segment.selectorNot +
        (if segment.emitsHeader then 1 else 0) + 3 +
        (affineMuxInvocationRowsSource segment.dataRows).length + 1 := by
  simp [AffineMuxInvocationProgression.sourceFrames,
    AffineMuxInvocationProgression.headerProgression_frameStream,
    affineMuxInvocationProgression_dataSource_eq, encodeUnaryFrame_length]
  omega

theorem AffineMuxInvocationProgression.sourceFrames_length_pos
    (segment : AffineMuxInvocationProgression) :
    0 < segment.sourceFrames.length := by
  rw [segment.sourceFrames_length_eq]
  omega

theorem AffineMuxInvocationProgression.selector_le_sourceFrames_length
    (segment : AffineMuxInvocationProgression) :
    segment.selector ≤ segment.sourceFrames.length := by
  rw [segment.sourceFrames_length_eq]
  omega

theorem AffineMuxInvocationProgression.selectorNot_le_sourceFrames_length
    (segment : AffineMuxInvocationProgression) :
    segment.selectorNot ≤ segment.sourceFrames.length := by
  rw [segment.sourceFrames_length_eq]
  omega

theorem AffineMuxInvocationProgression.selectors_le_sourceFrames_length
    (segment : AffineMuxInvocationProgression) :
    segment.selector + segment.selectorNot ≤ segment.sourceFrames.length := by
  rw [segment.sourceFrames_length_eq]
  omega

theorem AffineMuxInvocationProgression.dataSource_length_le_sourceFrames
    (segment : AffineMuxInvocationProgression) :
    (affineMuxInvocationRowsSource segment.dataRows).length ≤
      segment.sourceFrames.length := by
  rw [segment.sourceFrames_length_eq]
  omega

theorem AffineMuxInvocationProgression.headerFrames_length_le_sourceFrames
    (segment : AffineMuxInvocationProgression) :
    segment.headerFrames.length ≤ segment.sourceFrames.length := by
  cases h : segment.emitsHeader with
  | false => simp [AffineMuxInvocationProgression.headerFrames, h]
  | true =>
      simp [AffineMuxInvocationProgression.headerFrames, h,
        encodeAffineMuxFinHeader_length]
      rw [segment.sourceFrames_length_eq]
      simp [h]
      omega

theorem AffineMuxInvocationProgression.invocationFrames_length_le
    (segment : AffineMuxInvocationProgression) :
    segment.invocationFrames.length ≤
      7 * segment.sourceFrames.length ^ 2 := by
  let sourceLength := segment.sourceFrames.length
  let dataLength :=
    (affineMuxInvocationRowsSource segment.dataRows).length
  have hpositive : 1 ≤ sourceLength := by
    exact segment.sourceFrames_length_pos
  have hselector : segment.selector ≤ sourceLength :=
    segment.selector_le_sourceFrames_length
  have hselectorNot : segment.selectorNot ≤ sourceLength :=
    segment.selectorNot_le_sourceFrames_length
  have hselectors : segment.selector + segment.selectorNot ≤ sourceLength :=
    segment.selectors_le_sourceFrames_length
  have hdata : dataLength ≤ sourceLength :=
    segment.dataSource_length_le_sourceFrames
  have hrows := affineMuxInvocationRowsFrames_length_le_source
    segment.selector segment.selectorNot segment.dataRows
  have hheader := segment.headerFrames_length_le_sourceFrames
  have hframes := affineMuxInvocationProgression_rowsFrames_eq segment
  rw [hframes] at hrows
  have hcoefficient :
      segment.selector + segment.selectorNot + 5 ≤ sourceLength + 5 := by
    omega
  have hproduct := Nat.mul_le_mul hcoefficient hdata
  have hrowBound :
      (segment.frames.flatMap encodeAffineMuxFinPairFrame).length ≤
        (sourceLength + 5) * sourceLength :=
    hrows.trans hproduct
  simp only [AffineMuxInvocationProgression.invocationFrames,
    List.length_append]
  dsimp only [sourceLength, dataLength] at *
  nlinarith

theorem affineMuxInvocationProgressionControllerSegmentSteps_le
    (segment : AffineMuxInvocationProgression) :
    affineMuxInvocationProgressionControllerSegmentSteps segment ≤
      100 * segment.sourceFrames.length ^ 2 := by
  let sourceLength := segment.sourceFrames.length
  have hpositive : 1 ≤ sourceLength := by
    exact segment.sourceFrames_length_pos
  have hselector : segment.selector ≤ sourceLength :=
    segment.selector_le_sourceFrames_length
  have hselectorNot : segment.selectorNot ≤ sourceLength :=
    segment.selectorNot_le_sourceFrames_length
  have hrows :=
    affineMuxInvocationProgressionControllerRowsSteps_le_frames
      segment.selector segment.selectorNot segment.dataRows
  have hrowFrames :
      (affineMuxInvocationRowsFrames segment.selector segment.selectorNot
        segment.dataRows).length ≤ segment.invocationFrames.length := by
    simp [AffineMuxInvocationProgression.invocationFrames,
      affineMuxInvocationProgression_rowsFrames_eq]
  have hinvocation := segment.invocationFrames_length_le
  have hheader :
      affineMuxInvocationProgressionControllerHeaderSteps
          segment.selector segment.emitsHeader ≤ 5 * segment.selector + 8 := by
    cases segment.emitsHeader <;>
      simp [affineMuxInvocationProgressionControllerHeaderSteps] <;> omega
  unfold affineMuxInvocationProgressionControllerSegmentSteps
  dsimp only [sourceLength] at *
  nlinarith

theorem affineMuxInvocationProgressionControllerFamilySteps_le_flatMap
    (segments : List AffineMuxInvocationProgression) :
    affineMuxInvocationProgressionControllerFamilySteps segments ≤
      100 *
        (segments.flatMap AffineMuxInvocationProgression.sourceFrames).length ^
          2 := by
  induction segments with
  | nil => simp [affineMuxInvocationProgressionControllerFamilySteps]
  | cons segment rest ih =>
      have hsegment :=
        affineMuxInvocationProgressionControllerSegmentSteps_le segment
      simp only [affineMuxInvocationProgressionControllerFamilySteps,
        List.flatMap_cons, List.length_append]
      nlinarith [Nat.zero_le segment.sourceFrames.length,
        Nat.zero_le
          (rest.flatMap AffineMuxInvocationProgression.sourceFrames).length]

/-- Uniform quadratic bound in the actual compact source length. -/
theorem affineMuxInvocationProgressionControllerFamilySteps_le
    (segments : List AffineMuxInvocationProgression) :
    affineMuxInvocationProgressionControllerFamilySteps segments ≤
      100 *
        (affineMuxInvocationProgressionFamilySourceFrames segments).length ^ 2 := by
  rw [affineMuxInvocationProgressionFamilySourceFrames_eq]
  exact affineMuxInvocationProgressionControllerFamilySteps_le_flatMap segments

end CLRS.Chapter34.Turing.PolyBuilder

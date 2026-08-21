import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorAlignment
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameDelimiterMap

/-!
# Label-major source for dispatch-mux descriptors

The earlier unified affine source is section-major: all selectors, then all
coordinate descriptors, then all true-arm descriptors, then all false-arm
descriptors.  Four independent interpreters can consume that layout, but
recombining their outputs would require a machine-level same-input fan-out.

This module removes that obstacle at the source.  It groups the same fixed
affine forms by program label, evaluates the resulting fixed table with the
existing raw-input affine-map machine, and replaces the final ordinary unary
separator of every group by a physical `frameEnd`.  Thus one fixed
polynomial-time TM2 emits a label-major descriptor packet stream directly
from the verifier input.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- One seven-form fresh-coordinate descriptor group per program label. -/
def transitionDispatchMuxCoordinateDescriptorFormGroupsForLabels
    (tm : _root_.Turing.FinTM2) :
    TransitionAffineNat → List tm.Λ → List (List AffineUnaryTripleForm)
  | _, [] => []
  | offset, label :: labels =>
      let muxOffset := offset.add (transitionDispatchStmtGateAffine tm label)
      transitionDispatchMuxDescriptorBlock tm muxOffset ::
        transitionDispatchMuxCoordinateDescriptorFormGroupsForLabels tm
          (muxOffset.add (transitionDispatchMuxGateAffine tm)) labels

/-- Complete coordinate descriptor groups in fixed program-label order. -/
def transitionDispatchMuxCoordinateDescriptorFormGroups
    (tm : _root_.Turing.FinTM2) : List (List AffineUnaryTripleForm) :=
  transitionDispatchMuxCoordinateDescriptorFormGroupsForLabels tm
    (TransitionAffineNat.const 2) (programLabels tm)

theorem transitionDispatchMuxCoordinateDescriptorFormGroups_length
    (tm : _root_.Turing.FinTM2) :
    (transitionDispatchMuxCoordinateDescriptorFormGroups tm).length =
      (programLabels tm).length := by
  unfold transitionDispatchMuxCoordinateDescriptorFormGroups
  generalize TransitionAffineNat.const 2 = offset
  generalize programLabels tm = labels
  induction labels generalizing offset with
  | nil => rfl
  | cons label labels ih =>
      simp [transitionDispatchMuxCoordinateDescriptorFormGroupsForLabels, ih]

/-- Group the preceding-mux descriptor blocks by the label that consumes
them.  The first label has no preceding mux and is handled separately by the
widened-fallback group. -/
def transitionDispatchPreviousOutputDescriptorFormGroupsForLabels
    (tm : _root_.Turing.FinTM2) :
    TransitionAffineNat → List tm.Λ → List (List AffineUnaryTripleForm)
  | _, [] => []
  | _, [_] => []
  | offset, label :: next :: labels =>
      let muxOffset := offset.add (transitionDispatchStmtGateAffine tm label)
      transitionDispatchPreviousOutputDescriptorBlock tm offset label ::
        transitionDispatchPreviousOutputDescriptorFormGroupsForLabels tm
          (muxOffset.add (transitionDispatchMuxGateAffine tm))
          (next :: labels)

private theorem
    transitionDispatchPreviousOutputDescriptorFormGroupsForLabels_length
    (tm : _root_.Turing.FinTM2) :
    ∀ (offset : TransitionAffineNat) (labels : List tm.Λ),
      (transitionDispatchPreviousOutputDescriptorFormGroupsForLabels tm
        offset labels).length = labels.length - 1 := by
  intro offset labels
  induction labels generalizing offset with
  | nil => rfl
  | cons label labels ih =>
      cases labels with
      | nil => rfl
      | cons next labels =>
          simp only [
            transitionDispatchPreviousOutputDescriptorFormGroupsForLabels,
            List.length_cons]
          rw [ih]
          simp

/-- One false-arm descriptor group per label: the complete widened fallback
for the first label, followed by one preceding-mux progression per remaining
label. -/
noncomputable def transitionDispatchFalseArmDescriptorFormGroups
    (tm : _root_.Turing.FinTM2) : List (List AffineUnaryTripleForm) :=
  transitionWidenedFallbackDescriptorForms tm ::
    transitionDispatchPreviousOutputDescriptorFormGroupsForLabels tm
      (TransitionAffineNat.const 2) (programLabels tm)

theorem transitionDispatchFalseArmDescriptorFormGroups_length
    (tm : _root_.Turing.FinTM2) :
    (transitionDispatchFalseArmDescriptorFormGroups tm).length =
      (programLabels tm).length := by
  have hlabels : 0 < (programLabels tm).length :=
    List.length_pos_of_ne_nil (programLabels_nonempty tm)
  unfold transitionDispatchFalseArmDescriptorFormGroups
  rw [List.length_cons,
    transitionDispatchPreviousOutputDescriptorFormGroupsForLabels_length]
  omega

/-- Fixed true-arm descriptor blocks, one normalized block per label. -/
noncomputable def transitionDispatchTrueArmDescriptorFormGroups
    (tm : _root_.Turing.FinTM2) : List (List AffineUnaryTripleForm) :=
  (transitionDispatchTrueArmNormalizedLayouts tm).map
    (TransitionDispatchTrueArmNormalizedLayout.affineSpanDescriptorForms tm)

theorem transitionDispatchTrueArmDescriptorFormGroups_length
    (tm : _root_.Turing.FinTM2) :
    (transitionDispatchTrueArmDescriptorFormGroups tm).length =
      (programLabels tm).length := by
  let seed : TransitionRowSeed :=
    { height := 0, start := 0, rowBase := 0 }
  have h := transitionDispatchTrueArmSpanProgressionGroups_length tm seed
  simpa [transitionDispatchTrueArmDescriptorFormGroups,
    transitionDispatchTrueArmSpanProgressionGroups] using h

/-- Lock-step label-major reassembly of the four fixed descriptor sections.
Malformed unequal tables stop at the shortest section; the canonical tables
below are proved aligned. -/
def transitionDispatchMuxInvocationLabelMajorDescriptorFormGroupsFrom :
    List AffineUnaryTripleForm →
      List (List AffineUnaryTripleForm) →
      List (List AffineUnaryTripleForm) →
      List (List AffineUnaryTripleForm) →
      List (List AffineUnaryTripleForm)
  | selector :: selectors, coordinates :: coordinateGroups,
      whenTrue :: trueGroups, whenFalse :: falseGroups =>
      (selector :: coordinates ++ whenTrue ++ whenFalse) ::
        transitionDispatchMuxInvocationLabelMajorDescriptorFormGroupsFrom
          selectors coordinateGroups trueGroups falseGroups
  | _, _, _, _ => []

private theorem
    transitionDispatchMuxInvocationLabelMajorDescriptorFormGroupsFrom_length
    (selectors : List AffineUnaryTripleForm)
    (coordinateGroups trueGroups falseGroups :
      List (List AffineUnaryTripleForm))
    (hcoordinate : selectors.length = coordinateGroups.length)
    (htrue : selectors.length = trueGroups.length)
    (hfalse : selectors.length = falseGroups.length) :
    (transitionDispatchMuxInvocationLabelMajorDescriptorFormGroupsFrom
      selectors coordinateGroups trueGroups falseGroups).length =
      selectors.length := by
  induction selectors generalizing coordinateGroups trueGroups falseGroups with
  | nil =>
      have hcoordinateNil : coordinateGroups = [] :=
        List.eq_nil_of_length_eq_zero hcoordinate.symm
      have htrueNil : trueGroups = [] :=
        List.eq_nil_of_length_eq_zero htrue.symm
      have hfalseNil : falseGroups = [] :=
        List.eq_nil_of_length_eq_zero hfalse.symm
      subst coordinateGroups
      subst trueGroups
      subst falseGroups
      rfl
  | cons selector selectors ih =>
      cases coordinateGroups with
      | nil => simp at hcoordinate
      | cons coordinates coordinateGroups =>
          cases trueGroups with
          | nil => simp at htrue
          | cons whenTrue trueGroups =>
              cases falseGroups with
              | nil => simp at hfalse
              | cons whenFalse falseGroups =>
                  simp only [List.length_cons] at hcoordinate htrue hfalse
                  simp only [
                    transitionDispatchMuxInvocationLabelMajorDescriptorFormGroupsFrom,
                    List.length_cons]
                  rw [ih coordinateGroups trueGroups falseGroups
                    (by omega) (by omega) (by omega)]

/-- The verifier-fixed descriptor form table, now physically organized one
complete label packet at a time. -/
noncomputable def
    transitionDispatchMuxInvocationLabelMajorDescriptorFormGroups
    (tm : _root_.Turing.FinTM2) : List (List AffineUnaryTripleForm) :=
  transitionDispatchMuxInvocationLabelMajorDescriptorFormGroupsFrom
    (transitionDispatchSelectorForms tm)
    (transitionDispatchMuxCoordinateDescriptorFormGroups tm)
    (transitionDispatchTrueArmDescriptorFormGroups tm)
    (transitionDispatchFalseArmDescriptorFormGroups tm)

theorem transitionDispatchMuxInvocationLabelMajorDescriptorFormGroups_length
    (tm : _root_.Turing.FinTM2) :
    (transitionDispatchMuxInvocationLabelMajorDescriptorFormGroups tm).length =
      (programLabels tm).length := by
  unfold transitionDispatchMuxInvocationLabelMajorDescriptorFormGroups
  rw [transitionDispatchMuxInvocationLabelMajorDescriptorFormGroupsFrom_length]
  · simp [transitionDispatchSelectorForms]
  · simp [transitionDispatchSelectorForms,
      transitionDispatchMuxCoordinateDescriptorFormGroups_length]
  · simp [transitionDispatchSelectorForms,
      transitionDispatchTrueArmDescriptorFormGroups_length]
  · simp [transitionDispatchSelectorForms,
      transitionDispatchFalseArmDescriptorFormGroups_length]

/-- Flattened fixed table consumed by the generic affine-map source. -/
noncomputable def transitionDispatchMuxInvocationLabelMajorDescriptorForms
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  (transitionDispatchMuxInvocationLabelMajorDescriptorFormGroups tm).flatten

private theorem
    transitionDispatchMuxInvocationLabelMajorDescriptorFormGroupsFrom_nonempty
    (selectors : List AffineUnaryTripleForm)
    (coordinateGroups trueGroups falseGroups :
      List (List AffineUnaryTripleForm)) :
    ∀ group ∈
        transitionDispatchMuxInvocationLabelMajorDescriptorFormGroupsFrom
          selectors coordinateGroups trueGroups falseGroups,
      0 < group.length := by
  intro group hgroup
  induction selectors generalizing coordinateGroups trueGroups falseGroups with
  | nil =>
      simp [transitionDispatchMuxInvocationLabelMajorDescriptorFormGroupsFrom]
        at hgroup
  | cons selector selectors ih =>
      cases coordinateGroups with
      | nil =>
          simp [transitionDispatchMuxInvocationLabelMajorDescriptorFormGroupsFrom]
            at hgroup
      | cons coordinates coordinateGroups =>
          cases trueGroups with
          | nil =>
              simp [transitionDispatchMuxInvocationLabelMajorDescriptorFormGroupsFrom]
                at hgroup
          | cons whenTrue trueGroups =>
              cases falseGroups with
              | nil =>
                  simp [transitionDispatchMuxInvocationLabelMajorDescriptorFormGroupsFrom]
                    at hgroup
              | cons whenFalse falseGroups =>
                  simp only [
                    transitionDispatchMuxInvocationLabelMajorDescriptorFormGroupsFrom,
                    List.mem_cons] at hgroup
                  rcases hgroup with rfl | hgroup
                  · simp
                  · exact ih coordinateGroups trueGroups falseGroups hgroup

/-- Every canonical label group contains at least its selector form. -/
theorem
    transitionDispatchMuxInvocationLabelMajorDescriptorFormGroups_nonempty
    (tm : _root_.Turing.FinTM2) :
    ∀ group ∈
        transitionDispatchMuxInvocationLabelMajorDescriptorFormGroups tm,
      0 < group.length := by
  exact
    transitionDispatchMuxInvocationLabelMajorDescriptorFormGroupsFrom_nonempty
      (transitionDispatchSelectorForms tm)
      (transitionDispatchMuxCoordinateDescriptorFormGroups tm)
      (transitionDispatchTrueArmDescriptorFormGroups tm)
      (transitionDispatchFalseArmDescriptorFormGroups tm)

/-- Runtime descriptor values, retaining the fixed label boundaries of the
form table. -/
noncomputable def transitionDispatchMuxInvocationLabelMajorDescriptorValueGroups
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List (List Nat) :=
  (transitionDispatchMuxInvocationLabelMajorDescriptorFormGroups tm).map
    fun group => affineUnaryTripleMap group (transitionTailAffineSeed seed)

/-- Evaluating the flattened fixed table is exactly the flattened family of
label-local descriptor values. -/
theorem transitionDispatchMuxInvocationLabelMajorDescriptorForms_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    affineUnaryTripleMap
        (transitionDispatchMuxInvocationLabelMajorDescriptorForms tm)
        (transitionTailAffineSeed seed) =
      (transitionDispatchMuxInvocationLabelMajorDescriptorValueGroups
        tm seed).flatten := by
  unfold transitionDispatchMuxInvocationLabelMajorDescriptorForms
    transitionDispatchMuxInvocationLabelMajorDescriptorValueGroups
    affineUnaryTripleMap
  rw [List.map_flatten]

/-- Delimiter row for a nonempty fixed form group: ordinary separators for
all internal fields and one physical marker after its last field. -/
def transitionDispatchMuxInvocationLabelMajorDescriptorGroupDelimiters
    (group : List AffineUnaryTripleForm) : List UnaryFrameSym :=
  List.replicate (group.length - 1) .separator ++ [.frameEnd]

/-- One verifier-fixed delimiter cycle for all label groups in a transition
seed. -/
noncomputable def
    transitionDispatchMuxInvocationLabelMajorDescriptorDelimiterTable
    (tm : _root_.Turing.FinTM2) : List UnaryFrameSym :=
  (transitionDispatchMuxInvocationLabelMajorDescriptorFormGroups tm).flatMap
    transitionDispatchMuxInvocationLabelMajorDescriptorGroupDelimiters

/-- The delimiter cycle has one entry for every affine value field in one
transition seed. -/
private theorem
    transitionDispatchMuxInvocationLabelMajorDescriptorDelimiterTable_length_of_nonempty
    (groups : List (List AffineUnaryTripleForm))
    (hnonempty : ∀ group ∈ groups, 0 < group.length) :
    (groups.flatMap
      transitionDispatchMuxInvocationLabelMajorDescriptorGroupDelimiters).length =
      groups.flatten.length := by
  induction groups with
  | nil => rfl
  | cons group groups ih =>
      have hgroup : 0 < group.length := hnonempty group (by simp)
      have hgroups : ∀ row ∈ groups, 0 < row.length := by
        intro row hrow
        exact hnonempty row (by simp [hrow])
      simp only [List.flatMap_cons, List.flatten_cons, List.length_append]
      rw [ih hgroups]
      simp [transitionDispatchMuxInvocationLabelMajorDescriptorGroupDelimiters]
      omega

theorem transitionDispatchMuxInvocationLabelMajorDescriptorDelimiterTable_length
    (tm : _root_.Turing.FinTM2) :
    (transitionDispatchMuxInvocationLabelMajorDescriptorDelimiterTable
        tm).length =
      (transitionDispatchMuxInvocationLabelMajorDescriptorForms tm).length := by
  unfold transitionDispatchMuxInvocationLabelMajorDescriptorDelimiterTable
    transitionDispatchMuxInvocationLabelMajorDescriptorForms
  exact
    transitionDispatchMuxInvocationLabelMajorDescriptorDelimiterTable_length_of_nonempty
      (transitionDispatchMuxInvocationLabelMajorDescriptorFormGroups tm)
      (transitionDispatchMuxInvocationLabelMajorDescriptorFormGroups_nonempty
        tm)

theorem
    transitionDispatchMuxInvocationLabelMajorDescriptorDelimiterTable_nonempty
    (tm : _root_.Turing.FinTM2) :
    0 <
      (transitionDispatchMuxInvocationLabelMajorDescriptorDelimiterTable tm).length := by
  have hgroups :
      0 <
        (transitionDispatchMuxInvocationLabelMajorDescriptorFormGroups tm).length := by
    rw [transitionDispatchMuxInvocationLabelMajorDescriptorFormGroups_length]
    exact List.length_pos_of_ne_nil (programLabels_nonempty tm)
  unfold transitionDispatchMuxInvocationLabelMajorDescriptorDelimiterTable
  cases hgroup : transitionDispatchMuxInvocationLabelMajorDescriptorFormGroups
      tm with
  | nil => simp [hgroup] at hgroups
  | cons group groups =>
      simp [transitionDispatchMuxInvocationLabelMajorDescriptorGroupDelimiters]

/-- Ordinary unary encoding of the label-major affine descriptor values. -/
noncomputable def verifierTransitionDispatchMuxInvocationLabelMajorDescriptorFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  verifierTransitionAffineMapFrames W
    (transitionDispatchMuxInvocationLabelMajorDescriptorForms W.machine.tm)
    input

/-- Exact seed-major semantics of the single label-major affine source. -/
theorem verifierTransitionDispatchMuxInvocationLabelMajorDescriptorFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationLabelMajorDescriptorFrames W input =
      encodeUnaryFrame
        ((verifierTransitionRowSeeds W input).flatMap fun seed =>
          (transitionDispatchMuxInvocationLabelMajorDescriptorValueGroups
            W.machine.tm seed).flatten) := by
  unfold verifierTransitionDispatchMuxInvocationLabelMajorDescriptorFrames
    verifierTransitionAffineMapFrames verifierTransitionTailAffineSeeds
    affineUnaryTripleMapFamily
  rw [List.flatMap_map]
  congr 1
  apply List.flatMap_congr
  intro seed hseed
  exact transitionDispatchMuxInvocationLabelMajorDescriptorForms_value
    W.machine.tm seed

/-- Concrete marked label-major descriptor stream generated from the original
verifier word. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorMarkedDescriptorFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFrameDelimiters
    (transitionDispatchMuxInvocationLabelMajorDescriptorDelimiterTable
      W.machine.tm)
    (transitionDispatchMuxInvocationLabelMajorDescriptorDelimiterTable_nonempty
      W.machine.tm)
    (verifierTransitionDispatchMuxInvocationLabelMajorDescriptorFrames W input)

/-- The complete raw-input affine source and label-boundary pass are one fixed
polynomial-time TM2. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorMarkedDescriptorFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationLabelMajorMarkedDescriptorFrames
        W) := by
  let source := verifierTransitionAffineMapFrames_computableInPolyTime W
    (transitionDispatchMuxInvocationLabelMajorDescriptorForms W.machine.tm)
  let marker := unaryFrameDelimiterMap_computableInPolyTime
    (transitionDispatchMuxInvocationLabelMajorDescriptorDelimiterTable
      W.machine.tm)
    (transitionDispatchMuxInvocationLabelMajorDescriptorDelimiterTable_nonempty
      W.machine.tm)
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch source marker
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => rewriteUnaryFrameDelimiters
      (transitionDispatchMuxInvocationLabelMajorDescriptorDelimiterTable
        W.machine.tm)
      (transitionDispatchMuxInvocationLabelMajorDescriptorDelimiterTable_nonempty
        W.machine.tm)
      (verifierTransitionDispatchMuxInvocationLabelMajorDescriptorFrames
        W input))
  simpa only [Function.comp_def,
    verifierTransitionDispatchMuxInvocationLabelMajorDescriptorFrames]
    using Classical.choice composed

end CLRS.Chapter34.Turing.CookLevin

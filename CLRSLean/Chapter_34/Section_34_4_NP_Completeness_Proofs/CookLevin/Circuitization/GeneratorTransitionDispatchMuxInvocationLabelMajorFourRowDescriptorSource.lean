import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelMajorPacketEncoding

/-!
# Four physical descriptor rows per label-major dispatch packet

The typed label-major packet still stores its four semantic sections inside
one marked row.  This module supplies a second verifier-fixed delimiter pass
over the ordinary affine source.  It replaces the final field separator of
the selector, coordinate, true-arm, and false-arm sections by `frameEnd`.
Thus one concrete polynomial-time TM2 emits four physical descriptor rows per
label directly from the original verifier input.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- One delimiter per field of a section, with a physical boundary after its
last field.  Empty malformed sections contribute no delimiter. -/
def transitionDispatchMuxInvocationLabelMajorSectionDelimiters
    (forms : List AffineUnaryTripleForm) : List UnaryFrameSym :=
  List.ofFn fun position : Fin forms.length =>
    if position.val + 1 = forms.length then .frameEnd else .separator

@[simp] theorem
    transitionDispatchMuxInvocationLabelMajorSectionDelimiters_length
    (forms : List AffineUnaryTripleForm) :
    (transitionDispatchMuxInvocationLabelMajorSectionDelimiters
      forms).length = forms.length := by
  simp [transitionDispatchMuxInvocationLabelMajorSectionDelimiters]

/-- Lock-step delimiter groups matching the label-major form-group zipper.
The selector is a singleton field; each of the remaining three sections gets
its own final physical boundary. -/
def transitionDispatchMuxInvocationLabelMajorFourRowDescriptorDelimiterGroupsFrom :
    List AffineUnaryTripleForm →
      List (List AffineUnaryTripleForm) →
      List (List AffineUnaryTripleForm) →
      List (List AffineUnaryTripleForm) →
      List (List UnaryFrameSym)
  | _ :: selectors, coordinates :: coordinateGroups,
      whenTrue :: trueGroups, whenFalse :: falseGroups =>
      ([.frameEnd] ++
        transitionDispatchMuxInvocationLabelMajorSectionDelimiters
          coordinates ++
        transitionDispatchMuxInvocationLabelMajorSectionDelimiters
          whenTrue ++
        transitionDispatchMuxInvocationLabelMajorSectionDelimiters
          whenFalse) ::
        transitionDispatchMuxInvocationLabelMajorFourRowDescriptorDelimiterGroupsFrom
          selectors coordinateGroups trueGroups falseGroups
  | _, _, _, _ => []

/-- Four-row delimiter groups in fixed program-label order. -/
noncomputable def
    transitionDispatchMuxInvocationLabelMajorFourRowDescriptorDelimiterGroups
    (tm : _root_.Turing.FinTM2) : List (List UnaryFrameSym) :=
  transitionDispatchMuxInvocationLabelMajorFourRowDescriptorDelimiterGroupsFrom
    (transitionDispatchSelectorForms tm)
    (transitionDispatchMuxCoordinateDescriptorFormGroups tm)
    (transitionDispatchTrueArmDescriptorFormGroups tm)
    (transitionDispatchFalseArmDescriptorFormGroups tm)

private theorem
    transitionDispatchMuxInvocationLabelMajorFourRowDescriptorDelimiterGroupsFrom_lengths
    (selectors : List AffineUnaryTripleForm)
    (coordinateGroups trueGroups falseGroups :
      List (List AffineUnaryTripleForm)) :
    (transitionDispatchMuxInvocationLabelMajorFourRowDescriptorDelimiterGroupsFrom
        selectors coordinateGroups trueGroups falseGroups).map List.length =
      (transitionDispatchMuxInvocationLabelMajorDescriptorFormGroupsFrom
        selectors coordinateGroups trueGroups falseGroups).map List.length := by
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
                    transitionDispatchMuxInvocationLabelMajorFourRowDescriptorDelimiterGroupsFrom,
                    transitionDispatchMuxInvocationLabelMajorDescriptorFormGroupsFrom,
                    List.map_cons, List.length_append, List.length_cons,
                    List.length_nil,
                    transitionDispatchMuxInvocationLabelMajorSectionDelimiters_length]
                  congr 1
                  · omega
                  · exact ih coordinateGroups trueGroups falseGroups

/-- Complete four-row delimiter cycle, repeated once per transition seed. -/
noncomputable def
    transitionDispatchMuxInvocationLabelMajorFourRowDescriptorDelimiterTable
    (tm : _root_.Turing.FinTM2) : List UnaryFrameSym :=
  (transitionDispatchMuxInvocationLabelMajorFourRowDescriptorDelimiterGroups
    tm).flatten

/-- The four-row table still has exactly one delimiter per affine field. -/
theorem
    transitionDispatchMuxInvocationLabelMajorFourRowDescriptorDelimiterTable_length
    (tm : _root_.Turing.FinTM2) :
    (transitionDispatchMuxInvocationLabelMajorFourRowDescriptorDelimiterTable
      tm).length =
      (transitionDispatchMuxInvocationLabelMajorDescriptorForms tm).length := by
  unfold
    transitionDispatchMuxInvocationLabelMajorFourRowDescriptorDelimiterTable
    transitionDispatchMuxInvocationLabelMajorFourRowDescriptorDelimiterGroups
    transitionDispatchMuxInvocationLabelMajorDescriptorForms
    transitionDispatchMuxInvocationLabelMajorDescriptorFormGroups
  simp only [List.length_flatten]
  exact congrArg List.sum
    (transitionDispatchMuxInvocationLabelMajorFourRowDescriptorDelimiterGroupsFrom_lengths
      (transitionDispatchSelectorForms tm)
      (transitionDispatchMuxCoordinateDescriptorFormGroups tm)
      (transitionDispatchTrueArmDescriptorFormGroups tm)
      (transitionDispatchFalseArmDescriptorFormGroups tm))

/-- The table is nonempty because every verifier has at least one program
label and every label-major packet contains its selector. -/
theorem
    transitionDispatchMuxInvocationLabelMajorFourRowDescriptorDelimiterTable_nonempty
    (tm : _root_.Turing.FinTM2) :
    0 <
      (transitionDispatchMuxInvocationLabelMajorFourRowDescriptorDelimiterTable
        tm).length := by
  rw [
    transitionDispatchMuxInvocationLabelMajorFourRowDescriptorDelimiterTable_length]
  have hold :=
    transitionDispatchMuxInvocationLabelMajorDescriptorDelimiterTable_nonempty
      tm
  rw [transitionDispatchMuxInvocationLabelMajorDescriptorDelimiterTable_length]
    at hold
  exact hold

/-- Concrete four-row descriptor stream produced from the original verifier
word. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorFourRowDescriptorFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFrameDelimiters
    (transitionDispatchMuxInvocationLabelMajorFourRowDescriptorDelimiterTable
      W.machine.tm)
    (transitionDispatchMuxInvocationLabelMajorFourRowDescriptorDelimiterTable_nonempty
      W.machine.tm)
    (verifierTransitionDispatchMuxInvocationLabelMajorDescriptorFrames W input)

private theorem
    transitionDispatchMuxInvocationLabelMajorCanonicalDescriptorValueGroups_fourRow_length
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (transitionDispatchMuxInvocationLabelMajorCanonicalDescriptorValueGroups
        tm seed).flatten.length =
      (transitionDispatchMuxInvocationLabelMajorFourRowDescriptorDelimiterTable
        tm).length := by
  rw [
    transitionDispatchMuxInvocationLabelMajorFourRowDescriptorDelimiterTable_length]
  rw [←
    transitionDispatchMuxInvocationLabelMajorDescriptorValueGroups_eq_canonical]
  unfold transitionDispatchMuxInvocationLabelMajorDescriptorValueGroups
    transitionDispatchMuxInvocationLabelMajorDescriptorForms
  simp only [List.length_flatten, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro group hgroup
  simp [affineUnaryTripleMap]

/-- Exact seed-major semantics of the delimiter pass.  Each seed is encoded
against the verifier-fixed four-row delimiter table. -/
theorem
    verifierTransitionDispatchMuxInvocationLabelMajorFourRowDescriptorFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationLabelMajorFourRowDescriptorFrames
        W input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        encodeUnaryFrameWithFixedDelimiters
          (transitionDispatchMuxInvocationLabelMajorCanonicalDescriptorValueGroups
            W.machine.tm seed).flatten
          (transitionDispatchMuxInvocationLabelMajorFourRowDescriptorDelimiterTable
            W.machine.tm) := by
  unfold
    verifierTransitionDispatchMuxInvocationLabelMajorFourRowDescriptorFrames
  rw [verifierTransitionDispatchMuxInvocationLabelMajorDescriptorFrames_eq_canonical]
  rw [rewriteUnaryFrameDelimiters_encodeUnaryFrame]
  rw [show
      (verifierTransitionRowSeeds W input).flatMap
          (fun seed =>
            (transitionDispatchMuxInvocationLabelMajorCanonicalDescriptorValueGroups
              W.machine.tm seed).flatten) =
        ((verifierTransitionRowSeeds W input).map fun seed =>
          (transitionDispatchMuxInvocationLabelMajorCanonicalDescriptorValueGroups
            W.machine.tm seed).flatten).flatten by
      induction verifierTransitionRowSeeds W input with
      | nil => rfl
      | cons seed seeds ih =>
          simp only [List.flatMap_cons, List.map_cons, List.flatten_cons]
          rw [ih]]
  rw [encodeUnaryFrameWithDelimiterCycle_eq_fixedRows]
  · simp [List.flatMap_map]
  · intro row hrow
    rw [List.mem_map] at hrow
    rcases hrow with ⟨seed, hseed, rfl⟩
    exact
      transitionDispatchMuxInvocationLabelMajorCanonicalDescriptorValueGroups_fourRow_length
        W.machine.tm seed

/-- The affine source followed by four-row delimiter materialization is one
fixed polynomial-time TM2. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorFourRowDescriptorFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationLabelMajorFourRowDescriptorFrames
        W) := by
  let source := verifierTransitionAffineMapFrames_computableInPolyTime W
    (transitionDispatchMuxInvocationLabelMajorDescriptorForms W.machine.tm)
  let marker := unaryFrameDelimiterMap_computableInPolyTime
    (transitionDispatchMuxInvocationLabelMajorFourRowDescriptorDelimiterTable
      W.machine.tm)
    (transitionDispatchMuxInvocationLabelMajorFourRowDescriptorDelimiterTable_nonempty
      W.machine.tm)
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch source marker
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => rewriteUnaryFrameDelimiters
      (transitionDispatchMuxInvocationLabelMajorFourRowDescriptorDelimiterTable
        W.machine.tm)
      (transitionDispatchMuxInvocationLabelMajorFourRowDescriptorDelimiterTable_nonempty
        W.machine.tm)
      (verifierTransitionDispatchMuxInvocationLabelMajorDescriptorFrames
        W input))
  simpa only [Function.comp_def,
    verifierTransitionDispatchMuxInvocationLabelMajorDescriptorFrames]
    using Classical.choice composed

end CLRS.Chapter34.Turing.CookLevin

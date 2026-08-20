import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorTrueExecute
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFramePeriodicBoundaryFilter

/-!
# Label boundaries for the routed dispatch true arm

The true-arm interpreter currently retains one marker after every normalized
affine span.  A fixed verifier-dependent Boolean period is enough to merge
those spans back into label rows: inside each normalized label all boundaries
are erased except the last one.  This module constructs that period, proves it
has exactly the physical span width, and runs the concrete boundary filter.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Boundary pattern for one nonempty span family: erase all internal
boundaries and retain the final one. -/
def transitionDispatchTrueArmKeepLastBoundary
    (amounts : List Nat) : List Bool :=
  List.replicate (amounts.length - 1) false ++ [true]

private theorem transitionDispatchTrueArmKeepLastBoundary_length
    (amounts : List Nat) (hnonempty : 0 < amounts.length) :
    (transitionDispatchTrueArmKeepLastBoundary amounts).length =
      amounts.length := by
  simp [transitionDispatchTrueArmKeepLastBoundary]
  omega

private theorem
    transitionDispatchTrueArmNormalizedLayout_dropAmounts_nonempty
    (tm : _root_.Turing.FinTM2)
    (layout : TransitionDispatchTrueArmNormalizedLayout tm) :
    0 < (layout.affineSpanDropAmounts tm).length := by
  cases layout with
  | branch =>
      simp [TransitionDispatchTrueArmNormalizedLayout.affineSpanDropAmounts]
  | terminal labelOffset label rowLayout hlayout =>
      exact rowLayout.terminalAffineSpanDropAmounts_nonempty tm labelOffset

/-- One fixed boundary-selection period for a complete transition seed, in
normalized program-label order. -/
noncomputable def transitionDispatchTrueArmSpanLabelBoundarySelection
    (tm : _root_.Turing.FinTM2) : List Bool :=
  (transitionDispatchTrueArmNormalizedLayouts tm).flatMap fun layout =>
    transitionDispatchTrueArmKeepLastBoundary
      (layout.affineSpanDropAmounts tm)

/-- The boundary period consumes exactly one entry per physically executed
true-arm span. -/
theorem transitionDispatchTrueArmSpanLabelBoundarySelection_length
    (tm : _root_.Turing.FinTM2) :
    (transitionDispatchTrueArmSpanLabelBoundarySelection tm).length =
      (transitionDispatchTrueArmSpanDropAmounts tm).length := by
  unfold transitionDispatchTrueArmSpanLabelBoundarySelection
    transitionDispatchTrueArmSpanDropAmounts
  induction transitionDispatchTrueArmNormalizedLayouts tm with
  | nil => rfl
  | cons layout layouts ih =>
      simp only [List.flatMap_cons, List.length_append]
      rw [transitionDispatchTrueArmKeepLastBoundary_length
        (layout.affineSpanDropAmounts tm)
        (transitionDispatchTrueArmNormalizedLayout_dropAmounts_nonempty
          tm layout), ih]

/-- The fixed selection period is nonempty. -/
theorem transitionDispatchTrueArmSpanLabelBoundarySelection_nonempty
    (tm : _root_.Turing.FinTM2) :
    0 < (transitionDispatchTrueArmSpanLabelBoundarySelection tm).length := by
  rw [transitionDispatchTrueArmSpanLabelBoundarySelection_length]
  exact transitionDispatchTrueArmSpanDropAmounts_nonempty tm

/-- Prefix-normalized true-arm span rows, grouped by transition seed. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorTrueDroppedSpanValueRowGroups
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List (List (List Nat)) :=
  (verifierTransitionRowSeeds W input).map
    (transitionDispatchTrueArmSpanDroppedValueRows W.machine.tm)

/-- The preceding physical prefix-drop output is literally the standard
marked-row encoding of the normalized span rows. -/
theorem
    verifierTransitionDispatchMuxInvocationDescriptorTrueDroppedSpanMarkedFrames_eq_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorTrueDroppedSpanMarkedFrames
        W input =
      encodeUnaryFramePeriodicMarkedRowInput
        (verifierTransitionDispatchMuxInvocationDescriptorTrueDroppedSpanValueRowGroups
          W input).flatten := by
  rw [verifierTransitionDispatchMuxInvocationDescriptorTrueDroppedSpanMarkedFrames_eq]
  unfold
    verifierTransitionDispatchMuxInvocationDescriptorTrueDroppedSpanValueRowGroups
    verifierTransitionDispatchMuxInvocationDescriptorTrueRawValueRowGroups
    encodeUnaryFramePeriodicPrefixDropOutput
    encodeUnaryFramePeriodicMarkedRowInput
    transitionDispatchTrueArmSpanDroppedValueRows
  rw [List.flatten_eq_flatMap, List.flatMap_map, List.flatMap_assoc]
  simp [List.flatMap_map]

/-- Merge span rows into label rows by retaining only the verifier-fixed last
span boundaries. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorTrueLabelFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFramePeriodicBoundaries
    (transitionDispatchTrueArmSpanLabelBoundarySelection W.machine.tm)
    (transitionDispatchTrueArmSpanLabelBoundarySelection_nonempty W.machine.tm)
    (verifierTransitionDispatchMuxInvocationDescriptorTrueDroppedSpanMarkedFrames
      W input)

/-- Exact physical semantics of the label-boundary pass. -/
theorem verifierTransitionDispatchMuxInvocationDescriptorTrueLabelFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorTrueLabelFrames W input =
      encodeUnaryFramePeriodicBoundaryOutput
        (transitionDispatchTrueArmSpanLabelBoundarySelection W.machine.tm)
        (transitionDispatchTrueArmSpanLabelBoundarySelection_nonempty
          W.machine.tm)
        (verifierTransitionDispatchMuxInvocationDescriptorTrueDroppedSpanValueRowGroups
          W input).flatten := by
  unfold verifierTransitionDispatchMuxInvocationDescriptorTrueLabelFrames
  rw [verifierTransitionDispatchMuxInvocationDescriptorTrueDroppedSpanMarkedFrames_eq_rows]
  exact rewriteUnaryFramePeriodicBoundaries_encode _ _ _

/-- The routed true-arm execution followed by label-boundary restoration is a
single concrete polynomial-time TM2 from the original verifier word. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorTrueLabelFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationDescriptorTrueLabelFrames W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionDispatchMuxInvocationDescriptorTrueDroppedSpanMarkedFrames_computableInPolyTime
        W)
      (unaryFramePeriodicBoundaryFilter_computableInPolyTime
        (transitionDispatchTrueArmSpanLabelBoundarySelection W.machine.tm)
        (transitionDispatchTrueArmSpanLabelBoundarySelection_nonempty
          W.machine.tm))
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => rewriteUnaryFramePeriodicBoundaries
      (transitionDispatchTrueArmSpanLabelBoundarySelection W.machine.tm)
      (transitionDispatchTrueArmSpanLabelBoundarySelection_nonempty
        W.machine.tm)
      (verifierTransitionDispatchMuxInvocationDescriptorTrueDroppedSpanMarkedFrames
        W input))
  simpa [Function.comp_def,
    verifierTransitionDispatchMuxInvocationDescriptorTrueLabelFrames]
    using Classical.choice composed

end CLRS.Chapter34.Turing.CookLevin

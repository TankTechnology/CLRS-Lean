import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelMajorTrueProgressionFrames
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorTrueLabelFrames

/-!
# Final true-arm label rows from the label-major source

This module continues the concrete label-major true-arm machine.  Each
recovered affine progression is executed as a singleton group, projected to
its first coordinate, normalized by the fixed drop period, and merged back
into one row per dispatch label.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Execute the progression family and retain one temporary marker per affine
span. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorTrueRawMarkedFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  projectUnaryTripleGroupFirst
    (affineUnaryTripleProgressionFixedGroupFrameStream 0
      (verifierTransitionDispatchMuxInvocationDescriptorTrueRawProgressions
        W input))

/-- Singleton execution and first-coordinate projection are polynomial-time
from the label-major source. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorTrueRawMarkedFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationLabelMajorTrueRawMarkedFrames
        W) := by
  let descriptors :=
    verifierTransitionDispatchMuxInvocationLabelMajorTrueProgressionFrames_computableInPolyTime
      W
  let structured : _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineUnaryTripleProgressionFamily
      (verifierTransitionDispatchMuxInvocationDescriptorTrueRawProgressions W) :=
    { tm := descriptors.tm
      inputAlphabet := descriptors.inputAlphabet
      outputAlphabet := descriptors.outputAlphabet
      time := descriptors.time
      outputsFun := fun input => by
        have run := descriptors.outputsFun input
        simpa only [id_eq,
          verifierTransitionDispatchMuxInvocationLabelMajorTrueProgressionFrames_eq
            W input] using run }
  let executed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch structured
      (affineUnaryTripleProgressionFixedGroupFrameStream_computableInPolyTime 0)
  let projected :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (Classical.choice executed)
      projectUnaryTripleGroupFirst_computableInPolyTime
  let result := Classical.choice projected
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [Function.comp_apply, id_eq,
          verifierTransitionDispatchMuxInvocationLabelMajorTrueRawMarkedFrames]
          using run }

/-- Apply the verifier-fixed prefix-drop period while retaining span markers.
-/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorTrueDroppedSpanMarkedFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFramePeriodicPrefixDrop
    (transitionDispatchTrueArmSpanDropAmounts W.machine.tm)
    (transitionDispatchTrueArmSpanDropAmounts_nonempty W.machine.tm)
    (verifierTransitionDispatchMuxInvocationLabelMajorTrueRawMarkedFrames
      W input)

/-- The periodic prefix normalization remains polynomial-time. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorTrueDroppedSpanMarkedFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationLabelMajorTrueDroppedSpanMarkedFrames
        W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionDispatchMuxInvocationLabelMajorTrueRawMarkedFrames_computableInPolyTime
        W)
      (unaryFramePeriodicPrefixDrop_computableInPolyTime
        (transitionDispatchTrueArmSpanDropAmounts W.machine.tm)
        (transitionDispatchTrueArmSpanDropAmounts_nonempty W.machine.tm))
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => rewriteUnaryFramePeriodicPrefixDrop
      (transitionDispatchTrueArmSpanDropAmounts W.machine.tm)
      (transitionDispatchTrueArmSpanDropAmounts_nonempty W.machine.tm)
      (verifierTransitionDispatchMuxInvocationLabelMajorTrueRawMarkedFrames
        W input))
  simpa [Function.comp_def,
    verifierTransitionDispatchMuxInvocationLabelMajorTrueDroppedSpanMarkedFrames]
    using Classical.choice composed

/-- Merge normalized spans into the final true input row of each label. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorTrueLabelFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFramePeriodicBoundaries
    (transitionDispatchTrueArmSpanLabelBoundarySelection W.machine.tm)
    (transitionDispatchTrueArmSpanLabelBoundarySelection_nonempty W.machine.tm)
    (verifierTransitionDispatchMuxInvocationLabelMajorTrueDroppedSpanMarkedFrames
      W input)

/-- The new physical route is byte-for-byte the established final true label
channel. -/
theorem verifierTransitionDispatchMuxInvocationLabelMajorTrueLabelFrames_eq_existing
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationLabelMajorTrueLabelFrames W input =
      verifierTransitionDispatchMuxInvocationDescriptorTrueLabelFrames
        W input := by
  rfl

/-- The complete label-major true-arm route is one concrete polynomial-time
TM2 from the original verifier word. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorTrueLabelFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationLabelMajorTrueLabelFrames W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionDispatchMuxInvocationLabelMajorTrueDroppedSpanMarkedFrames_computableInPolyTime
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
      (verifierTransitionDispatchMuxInvocationLabelMajorTrueDroppedSpanMarkedFrames
        W input))
  simpa [Function.comp_def,
    verifierTransitionDispatchMuxInvocationLabelMajorTrueLabelFrames]
    using Classical.choice composed

end CLRS.Chapter34.Turing.CookLevin

import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelMajorFalseFrames
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorFalseLabelFrames

/-!
# Final false-arm label rows from the label-major source

The fourth row of every label-major packet has already been recovered as the
canonical false-arm progression descriptor stream.  Here those descriptors
are executed as singleton groups, projected to their first coordinates, and
merged according to the fixed false-arm label boundary period.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Execute every label-major false descriptor and retain one temporary
marker per affine span. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorFalseRawMarkedFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  projectUnaryTripleGroupFirst
    (affineUnaryTripleProgressionFixedGroupFrameStream 0
      ((verifierTransitionRowSeeds W input).flatMap
        (transitionDispatchFalseArmProgressions W.machine.tm)))

/-- Progression execution and first-coordinate projection form a concrete
polynomial-time continuation of the label-major false source. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorFalseRawMarkedFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationLabelMajorFalseRawMarkedFrames
        W) := by
  let descriptors :=
    verifierTransitionDispatchMuxInvocationLabelMajorFalseFrames_computableInPolyTime
      W
  let structured : _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineUnaryTripleProgressionFamily
      (fun input =>
        (verifierTransitionRowSeeds W input).flatMap
          (transitionDispatchFalseArmProgressions W.machine.tm)) :=
    { tm := descriptors.tm
      inputAlphabet := descriptors.inputAlphabet
      outputAlphabet := descriptors.outputAlphabet
      time := descriptors.time
      outputsFun := fun input => by
        have run := descriptors.outputsFun input
        simpa only [id_eq,
          verifierTransitionDispatchMuxInvocationLabelMajorFalseFrames_eq_existing,
          verifierTransitionDispatchMuxInvocationDescriptorFalseFrames_eq]
          using run }
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
          verifierTransitionDispatchMuxInvocationLabelMajorFalseRawMarkedFrames]
          using run }

/-- Merge widened-fallback span markers and retain one marker per final
dispatch label. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorFalseLabelFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFramePeriodicBoundaries
    (transitionDispatchFalseArmLabelBoundarySelection W.machine.tm)
    (transitionDispatchFalseArmLabelBoundarySelection_nonempty W.machine.tm)
    (verifierTransitionDispatchMuxInvocationLabelMajorFalseRawMarkedFrames
      W input)

/-- The label-major route recovers exactly the established final false label
channel. -/
theorem verifierTransitionDispatchMuxInvocationLabelMajorFalseLabelFrames_eq_existing
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationLabelMajorFalseLabelFrames W input =
      verifierTransitionDispatchMuxInvocationDescriptorFalseLabelFrames
        W input := by
  rfl

/-- The complete label-major false-arm route is one concrete polynomial-time
TM2 from the original verifier word. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorFalseLabelFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationLabelMajorFalseLabelFrames W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionDispatchMuxInvocationLabelMajorFalseRawMarkedFrames_computableInPolyTime
        W)
      (unaryFramePeriodicBoundaryFilter_computableInPolyTime
        (transitionDispatchFalseArmLabelBoundarySelection W.machine.tm)
        (transitionDispatchFalseArmLabelBoundarySelection_nonempty
          W.machine.tm))
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => rewriteUnaryFramePeriodicBoundaries
      (transitionDispatchFalseArmLabelBoundarySelection W.machine.tm)
      (transitionDispatchFalseArmLabelBoundarySelection_nonempty
        W.machine.tm)
      (verifierTransitionDispatchMuxInvocationLabelMajorFalseRawMarkedFrames
        W input))
  simpa [Function.comp_def,
    verifierTransitionDispatchMuxInvocationLabelMajorFalseLabelFrames]
    using Classical.choice composed

end CLRS.Chapter34.Turing.CookLevin

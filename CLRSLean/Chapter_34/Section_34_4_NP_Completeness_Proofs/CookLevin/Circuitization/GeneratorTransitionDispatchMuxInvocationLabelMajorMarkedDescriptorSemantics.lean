import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelMajorDescriptorSemantics

/-!
# Physical semantics of marked label-major dispatch descriptors

The source module supplies the concrete delimiter-rewriting TM2, while the
semantics module identifies its ordinary unary values with canonical
label-local descriptor packets.  This file joins those two interfaces: the
actual machine output is exactly the cyclic unary encoding of the canonical
descriptor values under the verifier-fixed label-boundary table.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Canonical physical target of the label-major delimiter pass. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorCanonicalMarkedDescriptorFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  encodeUnaryFrameWithDelimiterCycle
    (transitionDispatchMuxInvocationLabelMajorDescriptorDelimiterTable
      W.machine.tm)
    (transitionDispatchMuxInvocationLabelMajorDescriptorDelimiterTable_nonempty
      W.machine.tm)
    ((verifierTransitionRowSeeds W input).flatMap fun seed =>
      (transitionDispatchMuxInvocationLabelMajorCanonicalDescriptorValueGroups
        W.machine.tm seed).flatten)

/-- The concrete raw-input delimiter machine emits the canonical marked
descriptor value stream byte for byte. -/
theorem
    verifierTransitionDispatchMuxInvocationLabelMajorMarkedDescriptorFrames_eq_canonical
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationLabelMajorMarkedDescriptorFrames
        W input =
      verifierTransitionDispatchMuxInvocationLabelMajorCanonicalMarkedDescriptorFrames
        W input := by
  unfold
    verifierTransitionDispatchMuxInvocationLabelMajorMarkedDescriptorFrames
    verifierTransitionDispatchMuxInvocationLabelMajorCanonicalMarkedDescriptorFrames
  rw [
    verifierTransitionDispatchMuxInvocationLabelMajorDescriptorFrames_eq_canonical]
  exact rewriteUnaryFrameDelimiters_encodeUnaryFrame _ _ _

end CLRS.Chapter34.Turing.CookLevin

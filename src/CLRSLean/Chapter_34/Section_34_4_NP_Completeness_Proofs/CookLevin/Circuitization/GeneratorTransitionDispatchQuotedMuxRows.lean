import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelMajorLabelPacketCompiler
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionMuxQuotedRowParserRuntime

/-!
# Quoted rows for every outer dispatch mux

The already closed label-major packet compiler and mux expander are retargeted
to their typed invocation views, then composed with the delimiter-safe parser.
The output order is seed-major and label-minor, matching the canonical
dispatch artifact order.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Canonical global mux bytes are exactly the encoding of the reconstructed
seed-major typed views. -/
theorem verifierTransitionDispatchMuxInvocationFrames_eq_viewFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationFrames W input =
      transitionMuxInvocationViewFamilyFrames
        (verifierTransitionDispatchMuxInvocationViews W input) := by
  unfold verifierTransitionDispatchMuxInvocationFrames
    transitionMuxInvocationViewFamilyFrames
    verifierTransitionDispatchMuxInvocationViews
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro seed hseed
  rw [transitionDispatchMuxDescriptorInvocationViews_eq_artifacts W input
    seed hseed]
  rw [List.flatMap_map]
  exact
    (transitionDispatchArtifactsFromSeed_muxInvocationViews_encode
      W.machine.tm seed).symm

/-- The physical global mux machine exposed through its typed view family. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationViews_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id
      transitionMuxInvocationViewFamilyFrames
      (verifierTransitionDispatchMuxInvocationViews W) := by
  let raw :=
    verifierTransitionDispatchMuxInvocationFrames_computableInPolyTime_of_labelPacketCompiler
      W
      (verifierTransitionDispatchMuxInvocationLabelMajorPacketFamily_computableInPolyTime
        W)
  exact
    { tm := raw.tm
      inputAlphabet := raw.inputAlphabet
      outputAlphabet := raw.outputAlphabet
      time := raw.time
      outputsFun := fun input => by
        have run := raw.outputsFun input
        rw [verifierTransitionDispatchMuxInvocationFrames_eq_viewFamily W
          input] at run
        simpa only [id_eq] using run }

/-- Marked quoted rows for every outer dispatch mux invocation. -/
noncomputable def verifierTransitionDispatchQuotedMuxFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFrameMarkedRowFamily :=
  transitionMuxInvocationQuotedRowFamily
    (verifierTransitionDispatchMuxInvocationViews W input)

@[simp] theorem verifierTransitionDispatchQuotedMuxFamily_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierTransitionDispatchQuotedMuxFamily W input).rows =
      (verifierTransitionDispatchMuxInvocationViews W input).map fun view =>
        quoteUnaryFrameStream view.encode := rfl

/-- Concrete raw-input compiler for all quoted outer mux rows. -/
noncomputable def
    verifierTransitionDispatchQuotedMuxFamily_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (verifierTransitionDispatchQuotedMuxFamily W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionDispatchMuxInvocationViews_computableInPolyTime W)
      transitionMuxQuotedRowParser_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id
    encodeUnaryFrameMarkedRowFamily
    (fun input => transitionMuxInvocationQuotedRowFamily
      (verifierTransitionDispatchMuxInvocationViews W input))
  simpa only [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.CookLevin

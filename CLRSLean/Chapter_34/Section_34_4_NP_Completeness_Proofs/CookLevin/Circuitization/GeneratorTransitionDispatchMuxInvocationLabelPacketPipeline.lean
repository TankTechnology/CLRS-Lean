import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelPacketAssemblerVerifierRuntime

/-!
# Complete dispatch-mux pipeline above the label-packet source

All downstream stages are composed here: periodic stack preparation, exact
packet assembly, output reversal, and affine mux expansion.  The only premise
left at this boundary is a polynomial-time machine producing the typed
unprepared label-packet family from the original verifier input.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Literal unprepared four-row packet encoding of an aligned view family. -/
def AlignedTransitionDispatchMuxInvocationViewFamily.labelPacketFrames
    (family : AlignedTransitionDispatchMuxInvocationViewFamily) :
    List UnaryFrameSym :=
  encodeUnaryFrameMarkedRowFamily
    (transitionDispatchMuxInvocationLabelPacketFamily family.views)

/-- Periodic coordinate/true-row reversal is a typed polynomial-time identity
from unprepared aligned families to their stack-ready encoding. -/
noncomputable def
    transitionDispatchMuxInvocationLabelPacketPrepareAligned_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      AlignedTransitionDispatchMuxInvocationViewFamily.labelPacketFrames
      AlignedTransitionDispatchMuxInvocationViewFamily.preparedFrames id := by
  let generic :=
    transitionDispatchMuxInvocationLabelPacketPrepare_computableInPolyTime
  exact
    { tm := generic.tm
      inputAlphabet := generic.inputAlphabet
      outputAlphabet := generic.outputAlphabet
      time := generic.time
      outputsFun := fun family => by
        have run := generic.outputsFun
          (transitionDispatchMuxInvocationLabelPacketFamily family.views)
        simpa only [id_eq,
          AlignedTransitionDispatchMuxInvocationViewFamily.labelPacketFrames,
          AlignedTransitionDispatchMuxInvocationViewFamily.preparedFrames,
          encode_transitionDispatchMuxInvocationLabelPacketFamily_prepare]
          using run }

/-- Any raw-input compiler whose typed output is the actual prepared aligned
family composes directly with the closed assembler and mux expander. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationFrames_computableInPolyTime_of_preparedLabelPacketCompiler
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (compiler : _root_.Turing.TM2ComputableInPolyTime id
      AlignedTransitionDispatchMuxInvocationViewFamily.preparedFrames
      (verifierTransitionDispatchMuxInvocationAlignedViewFamily W)) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationFrames W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch compiler
      transitionDispatchMuxInvocationFrames_fromAlignedViews_computableInPolyTime
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [Function.comp_apply, id_eq,
          verifierTransitionDispatchMuxInvocationAlignedViewFamily_segments,
          verifierTransitionDispatchMuxInvocationSegments_frames W input]
          using run }

/-- A compiler for the typed unprepared label family automatically yields the
literal prepared byte stream via the verified periodic row transform. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationPreparedLabelPacketFrames_computableInPolyTime_of_labelPacketCompiler
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (compiler : _root_.Turing.TM2ComputableInPolyTime id
      AlignedTransitionDispatchMuxInvocationViewFamily.labelPacketFrames
      (verifierTransitionDispatchMuxInvocationAlignedViewFamily W)) :
    _root_.Turing.TM2ComputableInPolyTime id
      AlignedTransitionDispatchMuxInvocationViewFamily.preparedFrames
      (verifierTransitionDispatchMuxInvocationAlignedViewFamily W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch compiler
      transitionDispatchMuxInvocationLabelPacketPrepareAligned_computableInPolyTime
  simpa only [Function.comp_def, id_eq] using Classical.choice composed

/-- Complete raw-input-to-mux closure from the single remaining typed
label-family compiler premise. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationFrames_computableInPolyTime_of_labelPacketCompiler
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (compiler : _root_.Turing.TM2ComputableInPolyTime id
      AlignedTransitionDispatchMuxInvocationViewFamily.labelPacketFrames
      (verifierTransitionDispatchMuxInvocationAlignedViewFamily W)) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationFrames W) :=
  verifierTransitionDispatchMuxInvocationFrames_computableInPolyTime_of_preparedLabelPacketCompiler
    W
    (verifierTransitionDispatchMuxInvocationPreparedLabelPacketFrames_computableInPolyTime_of_labelPacketCompiler
      W compiler)

end CLRS.Chapter34.Turing.CookLevin

import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelPacketAssemblerBounds
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineMuxInvocationProgressionControllerRuntime

/-!
# Polynomial-time dispatch-mux assembly on aligned label families

The packet assembler is total on the typed input domain used by Cook--Levin:
a list of mux views together with the row-alignment invariant proved for the
verifier.  This module compiles the exact builder execution, reverses its
prepend-only output, and composes it with the existing affine mux controller.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- A label family carrying precisely the invariant required by the concrete
packet assembler.  The proof field has no tape representation. -/
structure AlignedTransitionDispatchMuxInvocationViewFamily where
  views : List TransitionDispatchMuxInvocationView
  rowAligned : ∀ view ∈ views, view.RowAligned

/-- Literal stack-ready packet encoding of an aligned label family. -/
def AlignedTransitionDispatchMuxInvocationViewFamily.preparedFrames
    (family : AlignedTransitionDispatchMuxInvocationViewFamily) :
    List UnaryFrameSym :=
  family.views.flatMap
    TransitionDispatchMuxInvocationView.preparedLabelPacketFrames

/-- Arithmetic mux segments reconstructed from an aligned label family. -/
def AlignedTransitionDispatchMuxInvocationViewFamily.segments
    (family : AlignedTransitionDispatchMuxInvocationViewFamily) :
    List AffineMuxInvocationProgression :=
  family.views.flatMap
    TransitionDispatchMuxInvocationView.invocationSegments

/-- The physical source emitted label by label is exactly the generic affine
mux source encoding of the reconstructed segment family. -/
theorem AlignedTransitionDispatchMuxInvocationViewFamily.sourceFrames_eq
    (family : AlignedTransitionDispatchMuxInvocationViewFamily) :
    affineMuxInvocationProgressionFamilySourceFrames family.segments =
      family.views.flatMap
        TransitionDispatchMuxInvocationView.sourceFrames := by
  rw [affineMuxInvocationProgressionFamilySourceFrames_eq]
  unfold AlignedTransitionDispatchMuxInvocationViewFamily.segments
    TransitionDispatchMuxInvocationView.sourceFrames
  exact List.flatMap_assoc

/-- Exact complete assembler run, including the two final halt transitions. -/
def transitionDispatchMuxInvocationLabelPacketAssemblerAligned_haltRun
    (family : AlignedTransitionDispatchMuxInvocationViewFamily) :
    EvalsToInTime
      (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
      (initialCfg transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram
        family.preparedFrames)
      (some (haltCfg
        transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram
        (affineMuxInvocationProgressionFamilySourceFrames
          family.segments).reverse))
      (transitionDispatchMuxInvocationLabelPacketAssemblerFamilySteps
        family.views + 2) := by
  have hfamily :=
    transitionDispatchMuxInvocationLabelPacketAssembler_views_sourceFrames
      family.views [] [] family.rowAligned
  have hsource := family.sourceFrames_eq
  have hfamily' : EvalsToInTime
      (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
      (initialCfg transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram
        family.preparedFrames)
      (some (transitionDispatchMuxInvocationLabelPacketAssemblerLoopCfg []
        (affineMuxInvocationProgressionFamilySourceFrames
          family.segments).reverse))
      (transitionDispatchMuxInvocationLabelPacketAssemblerFamilySteps
        family.views) := by
    simpa [AlignedTransitionDispatchMuxInvocationViewFamily.preparedFrames,
      hsource,
      transitionDispatchMuxInvocationLabelPacketAssemblerLoopCfg,
      transitionDispatchMuxInvocationLabelPacketAssemblerCfg, initialCfg,
      transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram] using
      hfamily
  have hhalt := transitionDispatchMuxInvocationLabelPacketAssembler_halt
    (affineMuxInvocationProgressionFamilySourceFrames family.segments).reverse
  let full := EvalsToInTime.trans
    (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
    (transitionDispatchMuxInvocationLabelPacketAssemblerFamilySteps
      family.views) 2 _ _ _ hfamily' hhalt
  simpa [Nat.add_comm] using full

/-- The exact run is quadratic in the literal prepared input encoding. -/
theorem transitionDispatchMuxInvocationLabelPacketAssemblerAligned_steps_le
    (family : AlignedTransitionDispatchMuxInvocationViewFamily) :
    transitionDispatchMuxInvocationLabelPacketAssemblerFamilySteps
          family.views + 2 ≤
      110 * family.preparedFrames.length ^ 2 + 2 := by
  have hbound :=
    transitionDispatchMuxInvocationLabelPacketAssemblerFamilySteps_le
      family.views family.rowAligned
  simpa [AlignedTransitionDispatchMuxInvocationViewFamily.preparedFrames]
    using Nat.add_le_add_right hbound 2

/-- Compiled fixed TM2 for the prepend-oriented (reversed) affine source. -/
noncomputable def
    transitionDispatchMuxInvocationLabelPacketAssemblerAligned_rev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      AlignedTransitionDispatchMuxInvocationViewFamily.preparedFrames id
      (fun family =>
        (affineMuxInvocationProgressionFamilySourceFrames
          family.segments).reverse) where
  tm := compile transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 110 * Polynomial.X ^ 2 + 2
  outputsFun := fun family => by
    have builderRun :=
      transitionDispatchMuxInvocationLabelPacketAssemblerAligned_haltRun family
    have compiledRun := compile_evalsToInTime
      transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram builderRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile
          transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram).step
        (_root_.Turing.initList
          (compile
            transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
          family.preparedFrames)
        (some (_root_.Turing.haltList
          (compile
            transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
          (affineMuxInvocationProgressionFamilySourceFrames
            family.segments).reverse))
        (transitionDispatchMuxInvocationLabelPacketAssemblerFamilySteps
          family.views + 2) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
    have htime :
        transitionDispatchMuxInvocationLabelPacketAssemblerFamilySteps
              family.views + 2 ≤
          (110 * Polynomial.X ^ 2 + 2).eval
            family.preparedFrames.length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat] using
        transitionDispatchMuxInvocationLabelPacketAssemblerAligned_steps_le
          family
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile
          transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram).step
        (_root_.Turing.initList
          (compile
            transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
          family.preparedFrames)
        (some (_root_.Turing.haltList
          (compile
            transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
          (affineMuxInvocationProgressionFamilySourceFrames
            family.segments).reverse))
        ((110 * Polynomial.X ^ 2 + 2).eval
          family.preparedFrames.length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Forward affine source obtained by composing the assembler with the
standard verified list reverser. -/
noncomputable def
    transitionDispatchMuxInvocationLabelPacketAssemblerAlignedSource_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      AlignedTransitionDispatchMuxInvocationViewFamily.preparedFrames id
      (fun family =>
        affineMuxInvocationProgressionFamilySourceFrames family.segments) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      transitionDispatchMuxInvocationLabelPacketAssemblerAligned_rev_computableInPolyTime
      (reverse_computableInPolyTime (Γ := UnaryFrameSym))
  simpa [Function.comp_def] using Classical.choice composed

/-- Typed form of the forward assembler.  Its output encoding is exactly the
input encoding required by the generic affine mux controller. -/
noncomputable def
    transitionDispatchMuxInvocationLabelPacketAssemblerAligned_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      AlignedTransitionDispatchMuxInvocationViewFamily.preparedFrames
      affineMuxInvocationProgressionFamilySourceFrames
      AlignedTransitionDispatchMuxInvocationViewFamily.segments := by
  let source :=
    transitionDispatchMuxInvocationLabelPacketAssemblerAlignedSource_computableInPolyTime
  exact
    { tm := source.tm
      inputAlphabet := source.inputAlphabet
      outputAlphabet := source.outputAlphabet
      time := source.time
      outputsFun := fun family => by
        simpa only [id_eq] using source.outputsFun family }

/-- End-to-end fixed polynomial-time TM2 from prepared aligned label packets
to the exact mux invocation frames used in the transition circuit. -/
noncomputable def
    transitionDispatchMuxInvocationFrames_fromAlignedViews_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      AlignedTransitionDispatchMuxInvocationViewFamily.preparedFrames id
      (fun family =>
        affineMuxInvocationProgressionFamilyFrames family.segments) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      transitionDispatchMuxInvocationLabelPacketAssemblerAligned_computableInPolyTime
      affineMuxInvocationProgressionFamilyFrames_computableInPolyTime
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.CookLevin

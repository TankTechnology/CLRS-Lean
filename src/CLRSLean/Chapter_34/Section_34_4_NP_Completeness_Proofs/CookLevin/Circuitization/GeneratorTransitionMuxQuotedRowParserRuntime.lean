import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionMuxQuotedRowParserSimulation
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition

/-!
# Polynomial runtime of the transition-mux quoted-row parser

This module turns the exact builder simulation into the public fixed-TM2
contract.  The only structural bound needed is that every mux invocation has
a nonempty header, so the number of produced rows is bounded by the literal
input length.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Every typed mux view contributes at least its mandatory header to the
literal parser input. -/
theorem transitionMuxInvocation_views_length_le_frames
    (views : List TransitionDispatchMuxInvocationView) :
    views.length ≤ (transitionMuxInvocationViewFamilyFrames views).length := by
  induction views with
  | nil => simp [transitionMuxInvocationViewFamilyFrames]
  | cons view rest ih =>
      have hview : 1 ≤ view.encode.length := by
        simp [TransitionDispatchMuxInvocationView.encode,
          encodeAffineMuxFinFrames, encodeAffineMuxFinHeader]
        omega
      simp only [transitionMuxInvocationViewFamilyFrames] at ih
      simp only [transitionMuxInvocationViewFamilyFrames,
        List.length_cons, List.flatMap_cons, List.length_append]
      omega

/-- Uniform linear envelope for the exact closed-parser run. -/
theorem transitionMuxQuotedRowParserSteps_le
    (views : List TransitionDispatchMuxInvocationView) :
    transitionMuxQuotedRowParserSteps views ≤
      4 * (transitionMuxInvocationViewFamilyFrames views).length + 3 := by
  cases views with
  | nil => simp [transitionMuxQuotedRowParserSteps,
      transitionMuxInvocationViewFamilyFrames]
  | cons view rest =>
      have hcount := transitionMuxInvocation_views_length_le_frames
        (view :: rest)
      simp only [transitionMuxQuotedRowParserSteps]
      omega

/-- Compiled fixed TM2 for the prepend-oriented parser output. -/
noncomputable def transitionMuxQuotedRowParserRev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      transitionMuxInvocationViewFamilyFrames id
      (fun views =>
        (encodeUnaryFrameMarkedRowFamily
          (transitionMuxInvocationQuotedRowFamily views)).reverse) where
  tm := compile transitionMuxQuotedRowParserRevProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 4 * Polynomial.X + 3
  outputsFun := fun views => by
    have builderRun := transitionMuxQuotedRowParserRev_run views
    have compiledRun := compile_evalsToInTime
      transitionMuxQuotedRowParserRevProgram builderRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile transitionMuxQuotedRowParserRevProgram).step
        (_root_.Turing.initList
          (compile transitionMuxQuotedRowParserRevProgram)
          (transitionMuxInvocationViewFamilyFrames views))
        (some (_root_.Turing.haltList
          (compile transitionMuxQuotedRowParserRevProgram)
          (encodeUnaryFrameMarkedRowFamily
            (transitionMuxInvocationQuotedRowFamily views)).reverse))
        (transitionMuxQuotedRowParserSteps views) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
    have htime : transitionMuxQuotedRowParserSteps views ≤
        (4 * Polynomial.X + 3).eval
          (transitionMuxInvocationViewFamilyFrames views).length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_ofNat] using
        transitionMuxQuotedRowParserSteps_le views
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile transitionMuxQuotedRowParserRevProgram).step
        (_root_.Turing.initList
          (compile transitionMuxQuotedRowParserRevProgram)
          (transitionMuxInvocationViewFamilyFrames views))
        (some (_root_.Turing.haltList
          (compile transitionMuxQuotedRowParserRevProgram)
          (encodeUnaryFrameMarkedRowFamily
            (transitionMuxInvocationQuotedRowFamily views)).reverse))
        ((4 * Polynomial.X + 3).eval
          (transitionMuxInvocationViewFamilyFrames views).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Forward delimiter-safe quoted rows, obtained by restoring output order
with the already verified fixed list reverser. -/
noncomputable def transitionMuxQuotedRowParser_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      transitionMuxInvocationViewFamilyFrames
      encodeUnaryFrameMarkedRowFamily
      transitionMuxInvocationQuotedRowFamily := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      transitionMuxQuotedRowParserRev_computableInPolyTime
      (reverse_computableInPolyTime (Γ := UnaryFrameSym))
  let raw := Classical.choice composed
  exact
    { tm := raw.tm
      inputAlphabet := raw.inputAlphabet
      outputAlphabet := raw.outputAlphabet
      time := raw.time
      outputsFun := fun views => by
        have run := raw.outputsFun views
        simpa [Function.comp_def] using run }

end CLRS.Chapter34.Turing.CookLevin

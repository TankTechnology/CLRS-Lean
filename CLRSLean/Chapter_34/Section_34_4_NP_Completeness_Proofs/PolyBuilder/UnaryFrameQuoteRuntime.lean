import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameQuoteSimulation
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition

/-!
# Polynomial runtime of unary-frame quoting
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- The concrete quoting controller, before forward-order restoration. -/
noncomputable def unaryFrameQuoteMarkedRev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List UnaryFrameSym =>
        (encodeUnaryFrameMarkedRowFamily
          (quotedUnaryFrameSingleton input)).reverse) where
  tm := compile unaryFrameQuoteMarkedRevProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 3 * Polynomial.X + 3
  outputsFun := fun input => by
    have builderRun := unaryFrameQuoteMarkedRev_run input
    have compiledRun := compile_evalsToInTime
      unaryFrameQuoteMarkedRevProgram builderRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile unaryFrameQuoteMarkedRevProgram).step
        (_root_.Turing.initList
          (compile unaryFrameQuoteMarkedRevProgram) input)
        (some (_root_.Turing.haltList
          (compile unaryFrameQuoteMarkedRevProgram)
          (encodeUnaryFrameMarkedRowFamily
            (quotedUnaryFrameSingleton input)).reverse))
        (unaryFrameQuoteMarkedSteps input) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
    have htime : unaryFrameQuoteMarkedSteps input ≤
        (3 * Polynomial.X + 3).eval input.length := by
      simp [unaryFrameQuoteMarkedSteps]
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile unaryFrameQuoteMarkedRevProgram).step
        (_root_.Turing.initList
          (compile unaryFrameQuoteMarkedRevProgram) input)
        (some (_root_.Turing.haltList
          (compile unaryFrameQuoteMarkedRevProgram)
          (encodeUnaryFrameMarkedRowFamily
            (quotedUnaryFrameSingleton input)).reverse))
        ((3 * Polynomial.X + 3).eval input.length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Forward marked singleton quoting in polynomial time. -/
noncomputable def unaryFrameQuoteMarked_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily quotedUnaryFrameSingleton := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      unaryFrameQuoteMarkedRev_computableInPolyTime
      (reverse_computableInPolyTime (Γ := UnaryFrameSym))
  let raw := Classical.choice composed
  exact
    { tm := raw.tm
      inputAlphabet := raw.inputAlphabet
      outputAlphabet := raw.outputAlphabet
      time := raw.time
      outputsFun := fun input => by
        have run := raw.outputsFun input
        simpa [Function.comp_def] using run }

/-- Quote the output of any concrete unary-frame transducer as one safe outer
row, while preserving the original raw input. -/
noncomputable def unaryFrameQuoteAfter_computableInPolyTime
    {Γ : Type} [Fintype Γ] {f : List Γ → List UnaryFrameSym}
    (M : _root_.Turing.TM2ComputableInPolyTime id id f) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (fun input => quotedUnaryFrameSingleton (f input)) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch M
      unaryFrameQuoteMarked_computableInPolyTime
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder

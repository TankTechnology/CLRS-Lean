import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedOrPairFormatSimulation
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition

/-!
# Formatting marked operand pairs as finite-OR frames: polynomial runtime
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

theorem unaryFrameMarkedOrPairFormatRevSteps_le
    (frames : List AffineOrFinPairFrame) :
    unaryFrameMarkedOrPairFormatRevSteps frames ≤
      3 * (encodeAffineOrFinMarkedPairFrames frames).length + 2 := by
  unfold unaryFrameMarkedOrPairFormatRevSteps
    encodeAffineOrFinMarkedPairFrames
  induction frames with
  | nil => simp
  | cons frame rest ih =>
      simp only [List.map_cons, List.sum_cons, List.flatMap_cons,
        List.length_append]
      have hframeLength :
          (encodeAffineOrFinMarkedPairFrame frame).length =
            frame.left + frame.right + 3 := by
        simp [encodeAffineOrFinMarkedPairFrame]
        omega
      rw [hframeLength]
      have ih' :
          (rest.map fun item =>
            2 * (item.left + item.right) + 9).sum + 2 ≤
          3 * (rest.flatMap encodeAffineOrFinMarkedPairFrame).length + 2 := by
        simpa only using ih
      omega

/-- The prepend-order formatter is a concrete linear-time TM2. -/
noncomputable def unaryFrameMarkedOrPairFormatRev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineOrFinMarkedPairFrames id
      (fun frames : List AffineOrFinPairFrame =>
        (encodeAffineOrFinFrames frames).reverse) where
  tm := compile unaryFrameMarkedOrPairFormatRevProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 3 * Polynomial.X + 2
  outputsFun := fun frames => by
    have builderRun := unaryFrameMarkedOrPairFormatRev_run frames
    have compiledRun := compile_evalsToInTime
      unaryFrameMarkedOrPairFormatRevProgram builderRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile unaryFrameMarkedOrPairFormatRevProgram).step
        (_root_.Turing.initList
          (compile unaryFrameMarkedOrPairFormatRevProgram)
          (encodeAffineOrFinMarkedPairFrames frames))
        (some (_root_.Turing.haltList
          (compile unaryFrameMarkedOrPairFormatRevProgram)
          (encodeAffineOrFinFrames frames).reverse))
        (unaryFrameMarkedOrPairFormatRevSteps frames) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
    have htime : unaryFrameMarkedOrPairFormatRevSteps frames ≤
        (3 * Polynomial.X + 2).eval
          (encodeAffineOrFinMarkedPairFrames frames).length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_ofNat] using
        unaryFrameMarkedOrPairFormatRevSteps_le frames
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile unaryFrameMarkedOrPairFormatRevProgram).step
        (_root_.Turing.initList
          (compile unaryFrameMarkedOrPairFormatRevProgram)
          (encodeAffineOrFinMarkedPairFrames frames))
        (some (_root_.Turing.haltList
          (compile unaryFrameMarkedOrPairFormatRevProgram)
          (encodeAffineOrFinFrames frames).reverse))
        ((3 * Polynomial.X + 2).eval
          (encodeAffineOrFinMarkedPairFrames frames).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Forward canonical finite-OR frame formatting in polynomial time. -/
noncomputable def unaryFrameMarkedOrPairFormat_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineOrFinMarkedPairFrames id encodeAffineOrFinFrames := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      unaryFrameMarkedOrPairFormatRev_computableInPolyTime
      (reverse_computableInPolyTime (Γ := UnaryFrameSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder

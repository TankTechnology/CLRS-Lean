import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowPresentSimulation
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition

/-!
# Marking every delimited row as present: polynomial runtime
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

theorem unaryFrameMarkedRowPresentRevSteps_le
    (family : UnaryFrameMarkedRowFamily) :
    unaryFrameMarkedRowPresentRevSteps family ≤
      3 * (encodeUnaryFrameMarkedRowFamily family).length + 3 := by
  unfold unaryFrameMarkedRowPresentRevSteps
    encodeUnaryFrameMarkedRowFamily
  induction family.rows with
  | nil => simp
  | cons row rest ih =>
      simp only [List.map_cons, List.sum_cons, List.flatMap_cons,
        List.length_append, List.length_cons, List.length_nil]
      have ih' : (rest.map fun item => 2 * item.length + 3).sum + 3 ≤
          3 * (rest.flatMap fun item => item ++ [.frameEnd]).length + 3 := by
        simpa only using ih
      omega

/-- The prepend-order formatter is a concrete linear-time TM2. -/
noncomputable def unaryFrameMarkedRowPresentRev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeUnaryFrameMarkedRowFamily id
      (fun family : UnaryFrameMarkedRowFamily =>
        (encodeUnaryFramePresentMarkedRowFamily family).reverse) where
  tm := compile unaryFrameMarkedRowPresentRevProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 3 * Polynomial.X + 3
  outputsFun := fun family => by
    have builderRun := unaryFrameMarkedRowPresentRev_run family
    have compiledRun := compile_evalsToInTime
      unaryFrameMarkedRowPresentRevProgram builderRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile unaryFrameMarkedRowPresentRevProgram).step
        (_root_.Turing.initList
          (compile unaryFrameMarkedRowPresentRevProgram)
          (encodeUnaryFrameMarkedRowFamily family))
        (some (_root_.Turing.haltList
          (compile unaryFrameMarkedRowPresentRevProgram)
          (encodeUnaryFramePresentMarkedRowFamily family).reverse))
        (unaryFrameMarkedRowPresentRevSteps family) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
    have htime : unaryFrameMarkedRowPresentRevSteps family ≤
        (3 * Polynomial.X + 3).eval
          (encodeUnaryFrameMarkedRowFamily family).length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_ofNat] using
        unaryFrameMarkedRowPresentRevSteps_le family
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile unaryFrameMarkedRowPresentRevProgram).step
        (_root_.Turing.initList
          (compile unaryFrameMarkedRowPresentRevProgram)
          (encodeUnaryFrameMarkedRowFamily family))
        (some (_root_.Turing.haltList
          (compile unaryFrameMarkedRowPresentRevProgram)
          (encodeUnaryFramePresentMarkedRowFamily family).reverse))
        ((3 * Polynomial.X + 3).eval
          (encodeUnaryFrameMarkedRowFamily family).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Forward all-present marked-row formatting in polynomial time. -/
noncomputable def unaryFrameMarkedRowPresent_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeUnaryFrameMarkedRowFamily id
      encodeUnaryFramePresentMarkedRowFamily := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      unaryFrameMarkedRowPresentRev_computableInPolyTime
      (reverse_computableInPolyTime (Γ := UnaryFrameSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder

import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.InputShapeController
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition

/-!
# Polynomial-time packaging of the continuous input-shape controller

The underlying controller already executes separator NOTs, optional
conjunction arms, and the final disjunction without intermediate halts.  This
module exposes its exact simulation and quadratic input-size envelope through
the fixed-TM2 polynomial-time interface.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Native prepend-order execution of the complete input-shape script. -/
noncomputable def affineInputShapeRev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineInputShapeScript id
      (fun script : AffineInputShapeScript =>
        (affineInputShapeGateStream script).reverse) where
  tm := compile affineInputShapeRevProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 1200 * Polynomial.X ^ 2 + 20
  outputsFun := fun script => by
    have builderRun := affineInputShape_run script []
    have compiledRun := compile_evalsToInTime
      affineInputShapeRevProgram builderRun
    rw [show affineInputShapeLoopCfg
        (encodeAffineInputShapeScript script) [] =
          initialCfg affineInputShapeRevProgram
            (encodeAffineInputShapeScript script) by rfl] at compiledRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile affineInputShapeRevProgram).step
        (_root_.Turing.initList (compile affineInputShapeRevProgram)
          (encodeAffineInputShapeScript script))
        (some (_root_.Turing.haltList (compile affineInputShapeRevProgram)
          (affineInputShapeGateStream script).reverse))
        (affineInputShapeRevSteps script) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg,
        List.append_nil] using compiledRun
    have htime : affineInputShapeRevSteps script ≤
        (1200 * Polynomial.X ^ 2 + 20).eval
          (encodeAffineInputShapeScript script).length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_ofNat] using affineInputShapeRev_steps_le script
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile affineInputShapeRevProgram).step
        (_root_.Turing.initList (compile affineInputShapeRevProgram)
          (encodeAffineInputShapeScript script))
        (some (_root_.Turing.haltList (compile affineInputShapeRevProgram)
          (affineInputShapeGateStream script).reverse))
        ((1200 * Polynomial.X ^ 2 + 20).eval
          (encodeAffineInputShapeScript script).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Forward complete input-shape circuit serialization. -/
noncomputable def affineInputShapeGateStream_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineInputShapeScript id affineInputShapeGateStream := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      affineInputShapeRev_computableInPolyTime
      (reverse_computableInPolyTime (Γ := CircuitSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder

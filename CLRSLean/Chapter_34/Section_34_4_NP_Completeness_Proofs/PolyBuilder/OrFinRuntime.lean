import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OrFin
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition

/-!
# Polynomial-time packaging of the finite OR-family controller

The controller in `OrFin` has an exact simulation and a linear runtime bound.
This module exposes those facts through the fixed-TM2 polynomial-time
interface, both for its native reverse output and for the forward circuit
stream used by Cook--Levin circuit generation.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- The fixed controller compiles arbitrary runtime OR frames to the reverse
gate stream in linear time in the explicit unary encoding. -/
noncomputable def affineOrFinRev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineOrFinFrames id
      (fun frames : List AffineOrFinPairFrame =>
        (affineOrFinGateStream frames).reverse) where
  tm := compile affineOrFinRevProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 100 * Polynomial.X + 3
  outputsFun := fun frames => by
    have builderRun := affineOrFin_run frames []
    have compiledRun := compile_evalsToInTime
      affineOrFinRevProgram builderRun
    rw [show affineOrFinLoopCfg (encodeAffineOrFinFrames frames) [] =
        initialCfg affineOrFinRevProgram
          (encodeAffineOrFinFrames frames) by rfl] at compiledRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile affineOrFinRevProgram).step
        (_root_.Turing.initList (compile affineOrFinRevProgram)
          (encodeAffineOrFinFrames frames))
        (some (_root_.Turing.haltList (compile affineOrFinRevProgram)
          (affineOrFinGateStream frames).reverse))
        (affineOrFinRevSteps frames) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg,
        List.append_nil] using compiledRun
    have htime : affineOrFinRevSteps frames ≤
        (100 * Polynomial.X + 3).eval
          (encodeAffineOrFinFrames frames).length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_ofNat] using
        affineOrFinRev_steps_le frames
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile affineOrFinRevProgram).step
        (_root_.Turing.initList (compile affineOrFinRevProgram)
          (encodeAffineOrFinFrames frames))
        (some (_root_.Turing.haltList (compile affineOrFinRevProgram)
          (affineOrFinGateStream frames).reverse))
        ((100 * Polynomial.X + 3).eval
          (encodeAffineOrFinFrames frames).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Forward finite OR-family gate serialization in polynomial time. -/
noncomputable def affineOrFinGateStream_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineOrFinFrames id affineOrFinGateStream := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      affineOrFinRev_computableInPolyTime
      (reverse_computableInPolyTime (Γ := CircuitSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder

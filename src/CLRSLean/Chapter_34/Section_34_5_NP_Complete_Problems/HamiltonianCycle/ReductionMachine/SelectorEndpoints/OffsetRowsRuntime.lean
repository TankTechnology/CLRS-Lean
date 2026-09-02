import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.SelectorEndpoints.OffsetRowsBounds
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse

/-!
# HAM-CYCLE selector endpoints: reusable offset-row formatter
-/

noncomputable section

open Computability StateTransition

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.SelectorEndpoints

open PolyBuilder
open SelectorClique
open _root_.Turing

noncomputable def offsetRowsFormatRevComputableInPolyTime :
    TM2ComputableInPolyTime encodeOffsetRowsFamily id
      (fun family => (offsetRowsEdgeStream family).reverse) where
  tm := compile offsetPairRowsFormatRevProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 20 * Polynomial.X ^ 2 + 20
  outputsFun := fun family => by
    have builderRun := offsetRowsFormatRev_run family
    have compiledRun := compile_evalsToInTime
      offsetPairRowsFormatRevProgram builderRun
    have machineRun : EvalsToInTime
        (compile offsetPairRowsFormatRevProgram).step
        (_root_.Turing.initList (compile offsetPairRowsFormatRevProgram)
          (encodeOffsetRowsFamily family))
        (some (_root_.Turing.haltList
          (compile offsetPairRowsFormatRevProgram)
          (offsetRowsEdgeStream family).reverse))
        (offsetRowsFormatRevSteps family) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
    have htime : offsetRowsFormatRevSteps family ≤
        (20 * Polynomial.X ^ 2 + 20).eval
          (encodeOffsetRowsFamily family).length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat] using
        offsetRowsFormatRevSteps_le_input family
    have boundedRun : EvalsToInTime
        (compile offsetPairRowsFormatRevProgram).step
        (_root_.Turing.initList (compile offsetPairRowsFormatRevProgram)
          (encodeOffsetRowsFamily family))
        (some (_root_.Turing.haltList
          (compile offsetPairRowsFormatRevProgram)
          (offsetRowsEdgeStream family).reverse))
        ((20 * Polynomial.X ^ 2 + 20).eval
          (encodeOffsetRowsFamily family).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- A fixed polynomial-time TM2 formats any unary base followed by arbitrary
marked lower-endpoint rows. -/
noncomputable def offsetRowsFormatComputableInPolyTime :
    TM2ComputableInPolyTime encodeOffsetRowsFamily id
      offsetRowsEdgeStream := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    offsetRowsFormatRevComputableInPolyTime
    (reverse_computableInPolyTime (Γ := CliqueSym))
  simpa only [Function.comp_def, List.reverse_reverse] using
    Classical.choice composed

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.SelectorEndpoints

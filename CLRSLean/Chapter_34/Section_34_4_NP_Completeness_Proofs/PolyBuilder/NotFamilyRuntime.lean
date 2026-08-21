import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.NotFamily
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition

/-!
# Polynomial-time packaging of the affine NOT-family controller

The controller in `NotFamily` already has an exact simulation and a linear
runtime bound.  This file exposes those facts through the public fixed-TM2
polynomial-time interface, first for reverse output and then for the forward
circuit stream.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- The compiled controller emits the reverse NOT-family gate stream in
linear time in its explicit unary-frame input. -/
noncomputable def affineNotFamilyRev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineNotFamilySources id
      (fun sources : List Nat => (affineNotFamilyGateStream sources).reverse) where
  tm := compile affineNotFamilyRevProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 20 * Polynomial.X + 2
  outputsFun := fun sources => by
    have builderRun := affineNotFamily_run sources []
    have compiledRun := compile_evalsToInTime
      affineNotFamilyRevProgram builderRun
    rw [show affineNotFamilyLoopCfg
        (encodeAffineNotFamilySources sources) [] =
          initialCfg affineNotFamilyRevProgram
            (encodeAffineNotFamilySources sources) by rfl] at compiledRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile affineNotFamilyRevProgram).step
        (_root_.Turing.initList (compile affineNotFamilyRevProgram)
          (encodeAffineNotFamilySources sources))
        (some (_root_.Turing.haltList (compile affineNotFamilyRevProgram)
          (affineNotFamilyGateStream sources).reverse))
        (affineNotFamilyRevSteps sources) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg,
        List.append_nil] using compiledRun
    have htime : affineNotFamilyRevSteps sources ≤
        (20 * Polynomial.X + 2).eval
          (encodeAffineNotFamilySources sources).length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_ofNat] using
        affineNotFamilyRev_steps_le sources
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile affineNotFamilyRevProgram).step
        (_root_.Turing.initList (compile affineNotFamilyRevProgram)
          (encodeAffineNotFamilySources sources))
        (some (_root_.Turing.haltList (compile affineNotFamilyRevProgram)
          (affineNotFamilyGateStream sources).reverse))
        ((20 * Polynomial.X + 2).eval
          (encodeAffineNotFamilySources sources).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Forward affine NOT-family gate serialization in polynomial time. -/
noncomputable def affineNotFamilyGateStream_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineNotFamilySources id affineNotFamilyGateStream := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      affineNotFamilyRev_computableInPolyTime
      (reverse_computableInPolyTime (Γ := CircuitSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder

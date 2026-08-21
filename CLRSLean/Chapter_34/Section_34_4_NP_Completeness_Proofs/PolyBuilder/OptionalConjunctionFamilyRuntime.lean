import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OptionalConjunctionFamily
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition

/-!
# Polynomial-time packaging of the optional conjunction-family controller
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- The compiled controller computes the reversed optional-family gate stream
within its established quadratic bound. -/
noncomputable def affineOptionalConjunctionFamilyRev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineOptionalConjunctionFamily id
      (fun frames : List (Option AffineConjunctionFrame) =>
        (affineOptionalConjunctionFamilyGateStream frames).reverse) where
  tm := compile affineOptionalConjunctionFamilyRevProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 1005 * Polynomial.X ^ 2 + 2
  outputsFun := fun frames => by
    have builderRun := affineOptionalConjunctionFamily_run frames []
    have compiledRun := compile_evalsToInTime
      affineOptionalConjunctionFamilyRevProgram builderRun
    rw [show affineOptionalConjunctionFamilyLoopCfg
        (encodeAffineOptionalConjunctionFamily frames) [] =
          initialCfg affineOptionalConjunctionFamilyRevProgram
            (encodeAffineOptionalConjunctionFamily frames) by rfl] at compiledRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile affineOptionalConjunctionFamilyRevProgram).step
        (_root_.Turing.initList
          (compile affineOptionalConjunctionFamilyRevProgram)
          (encodeAffineOptionalConjunctionFamily frames))
        (some (_root_.Turing.haltList
          (compile affineOptionalConjunctionFamilyRevProgram)
          (affineOptionalConjunctionFamilyGateStream frames).reverse))
        (affineOptionalConjunctionFamilyRevSteps frames) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg,
        List.append_nil] using compiledRun
    have htime : affineOptionalConjunctionFamilyRevSteps frames ≤
        (1005 * Polynomial.X ^ 2 + 2).eval
          (encodeAffineOptionalConjunctionFamily frames).length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat] using
        affineOptionalConjunctionFamilyRev_steps_le frames
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile affineOptionalConjunctionFamilyRevProgram).step
        (_root_.Turing.initList
          (compile affineOptionalConjunctionFamilyRevProgram)
          (encodeAffineOptionalConjunctionFamily frames))
        (some (_root_.Turing.haltList
          (compile affineOptionalConjunctionFamilyRevProgram)
          (affineOptionalConjunctionFamilyGateStream frames).reverse))
        ((1005 * Polynomial.X ^ 2 + 2).eval
          (encodeAffineOptionalConjunctionFamily frames).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Forward optional conjunction-family gate generation in polynomial time. -/
noncomputable def
    affineOptionalConjunctionFamilyGateStream_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineOptionalConjunctionFamily id
      affineOptionalConjunctionFamilyGateStream := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      affineOptionalConjunctionFamilyRev_computableInPolyTime
      (reverse_computableInPolyTime (Γ := CircuitSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder

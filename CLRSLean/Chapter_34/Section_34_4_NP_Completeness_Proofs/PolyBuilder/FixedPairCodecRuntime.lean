import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.FixedPairCodecSimulation
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition

/-!
# Polynomial runtime of fixed two-symbol codecs
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Fixed two-symbol expansion is a concrete linear-time TM2 transduction. -/
noncomputable def fixedPairEncode_computableInPolyTime
    {Γ Δ : Type} [Fintype Γ]
    (encode : Γ → Δ × Δ) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fixedPairEncode encode) := by
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List Γ =>
      input.flatMap (fixedPairEncodeBody encode).emit)
  exact boundedLoop_computableInPolyTime (fixedPairEncodeBody encode)

/-- Direct reverse-output decoding is a concrete linear-time TM2. -/
noncomputable def fixedPairDecodeRev_computableInPolyTime
    {Γ Δ : Type} [Fintype Γ] [Fintype Δ]
    (decode : Δ → Δ → Γ) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List Δ => (fixedPairDecode decode input).reverse) where
  tm := compile (fixedPairDecodeRevProgram decode)
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 2 * Polynomial.X + 2
  outputsFun := fun input => by
    have builderRun := fixedPairDecodeRev_run decode input
    have compiledRun := compile_evalsToInTime
      (fixedPairDecodeRevProgram decode) builderRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile (fixedPairDecodeRevProgram decode)).step
        (_root_.Turing.initList
          (compile (fixedPairDecodeRevProgram decode)) input)
        (some (_root_.Turing.haltList
          (compile (fixedPairDecodeRevProgram decode))
          (fixedPairDecode decode input).reverse))
        (fixedPairDecodeSteps input) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
    have htime : fixedPairDecodeSteps input ≤
        (2 * Polynomial.X + 2).eval input.length := by
      simpa using fixedPairDecodeSteps_le input
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile (fixedPairDecodeRevProgram decode)).step
        (_root_.Turing.initList
          (compile (fixedPairDecodeRevProgram decode)) input)
        (some (_root_.Turing.haltList
          (compile (fixedPairDecodeRevProgram decode))
          (fixedPairDecode decode input).reverse))
        ((2 * Polynomial.X + 2).eval input.length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Total forward-order fixed-pair decoding is polynomial-time computable. -/
noncomputable def fixedPairDecode_computableInPolyTime
    {Γ Δ : Type} [Fintype Γ] [Fintype Δ]
    (decode : Δ → Δ → Γ) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fixedPairDecode decode) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (fixedPairDecodeRev_computableInPolyTime decode)
      (reverse_computableInPolyTime (Γ := Γ))
  let raw := Classical.choice composed
  exact
    { tm := raw.tm
      inputAlphabet := raw.inputAlphabet
      outputAlphabet := raw.outputAlphabet
      time := raw.time
      outputsFun := fun input => by
        have run := raw.outputsFun input
        simpa [Function.comp_def] using run }

end CLRS.Chapter34.Turing.PolyBuilder

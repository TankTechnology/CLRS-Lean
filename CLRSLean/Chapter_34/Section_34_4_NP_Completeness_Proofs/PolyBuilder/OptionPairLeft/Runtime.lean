import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OptionPairLeft.Run
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition

/-!
# Left pair formatter: polynomial runtime
-/

noncomputable section

open Computability StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder.OptionPairLeft

open _root_.Turing

noncomputable def revComputableInPolyTime
    (Γ : Type) [Fintype Γ] :
    TM2ComputableInPolyTime id id
      (fun input : List Γ => (format input).reverse) where
  tm := compile (program Γ)
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 2 * Polynomial.X + 3
  outputsFun := fun input => by
    have builderRun := run input
    have compiledRun := compile_evalsToInTime (program Γ) builderRun
    have bounded : EvalsToInTime (compile (program Γ)).step
        (initList (compile (program Γ)) input)
        (some (haltList (compile (program Γ)) (format input).reverse))
        ((2 * Polynomial.X + 3).eval input.length) := by
      convert compiledRun using 1 <;>
        simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
          encodeCfg_initialCfg, encodeCfg_haltCfg]
    simp only [TM2OutputsInTime]
    convert bounded using 1
    · congr 1
      change List.map id _ = _
      exact List.map_id _
    · simp only [Option.map_some]
      congr 2
      change List.map id _ = _
      exact List.map_id _
    · rfl

/-- A fixed linear-time machine produces `input.map some ++ [none]`. -/
noncomputable def computableInPolyTime (Γ : Type) [Fintype Γ] :
    TM2ComputableInPolyTime id id (@format Γ) := by
  let composed := _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
    (revComputableInPolyTime Γ)
    (reverse_computableInPolyTime (Γ := Option Γ))
  have machine := Classical.choice composed
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have output := machine.outputsFun input
        simpa [Function.comp_def] using output }

end CLRS.Chapter34.Turing.PolyBuilder.OptionPairLeft

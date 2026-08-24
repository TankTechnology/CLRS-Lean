import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.GuardSelector.Simulation
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition

/-!
# VERTEX-COVER guarded selector: polynomial runtime
-/

noncomputable section

open Computability StateTransition

namespace CLRS.Chapter34.Turing.VertexCover.ComplementMachine.GuardSelector

open PolyBuilder
open _root_.Turing

theorem steps_le (input : Bool × List CliqueSym) :
    steps input ≤ 3 * (inputEncoding input).length + 13 := by
  rcases input with ⟨accept, candidate⟩
  cases accept <;> simp [steps, inputEncoding, pairEncoding] <;> omega

def outputs_in_time (input : Bool × List CliqueSym) :
    TM2OutputsInTime (compile program) (inputEncoding input)
      (some (selectedOutput input))
      (3 * (inputEncoding input).length + 13) := by
  have builderRun := run input
  have compiledRun := compile_evalsToInTime program builderRun
  change EvalsToInTime (compile program).step
      (initList (compile program) (inputEncoding input))
      (some (haltList (compile program) (selectedOutput input)))
      (3 * (inputEncoding input).length + 13)
  refine ⟨⟨compiledRun.steps, ?_⟩, compiledRun.steps_le_m.trans
    (steps_le input)⟩
  convert compiledRun.evals_in_steps using 1 <;>
    simp only [encodeCfg_initialCfg, encodeCfg_haltCfg]

/-- Fixed polynomial-time selection of the candidate or canonical fallback. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime inputEncoding id selectedOutput where
  tm := compile program
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 3 * Polynomial.X + 13
  outputsFun := fun input => by
    have output := outputs_in_time input
    convert output using 1 <;>
      simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_ofNat]
    all_goals
      change List.map id _ = _
      exact List.map_id _

end CLRS.Chapter34.Turing.VertexCover.ComplementMachine.GuardSelector

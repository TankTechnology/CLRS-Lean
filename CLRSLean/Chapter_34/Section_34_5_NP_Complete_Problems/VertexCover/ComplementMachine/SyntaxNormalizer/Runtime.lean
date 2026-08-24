import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.SyntaxNormalizer.Semantics
import Mathlib.Tactic

/-!
# Raw graph syntax normalizer: polynomial runtime
-/

noncomputable section

open Computability StateTransition

namespace CLRS.Chapter34.Turing.VertexCover.ComplementMachine.SyntaxNormalizer

open PolyBuilder
open _root_.Turing

/-- Both parser branches satisfy one linear step bound. -/
theorem steps_le (input : List CliqueSym) :
    steps input ≤ 4 * input.length + 7 := by
  unfold steps
  split <;> omega

/-- The compiled controller emits the exact normalized stream within the
advertised linear polynomial. -/
def outputs_in_time (input : List CliqueSym) :
    TM2OutputsInTime (compile program) input
      (some (normalizedStream input))
      ((4 * Polynomial.X + 7).eval input.length) := by
  have builderRun := run input
  have compiledRun := compile_evalsToInTime program builderRun
  have htime : steps input ≤
      (4 * Polynomial.X + 7).eval input.length := by
    simpa [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] using
      steps_le input
  change EvalsToInTime (compile program).step
    (initList (compile program) input)
    (some (haltList (compile program) (normalizedStream input)))
    ((4 * Polynomial.X + 7).eval input.length)
  refine ⟨⟨compiledRun.steps, ?_⟩,
    compiledRun.steps_le_m.trans htime⟩
  convert compiledRun.evals_in_steps using 1
  all_goals simp only [encodeCfg_initialCfg, encodeCfg_haltCfg]

/-- A fixed linear-time TM2 computes the total typed syntax normalization. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id encodeCliqueInstance normalizedInstanceValue where
  tm := compile program
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 4 * Polynomial.X + 7
  outputsFun := fun input => by
    have output := outputs_in_time input
    rw [normalizedStream_eq] at output
    convert output using 1 <;> simp
    all_goals
      change List.map id _ = _
      exact List.map_id _

end CLRS.Chapter34.Turing.VertexCover.ComplementMachine.SyntaxNormalizer

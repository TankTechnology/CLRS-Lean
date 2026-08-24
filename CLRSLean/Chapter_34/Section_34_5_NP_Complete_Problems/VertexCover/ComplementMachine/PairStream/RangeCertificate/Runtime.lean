import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.PairStream.RangeCertificate.Run
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition
import Mathlib.Tactic

/-!
# Range-certificate controller: polynomial runtime
-/

noncomputable section

open Computability StateTransition

namespace CLRS.Chapter34.Turing.VertexCover.ComplementMachine.PairStream.RangeCertificate

open PolyBuilder
open _root_.Turing

/-- Quadratic bound for a consecutive range of unary vertex records. -/
theorem phaseSteps_le (start count : Nat) :
    phaseSteps start count ≤
      5 * count * (start + count) + 6 * count := by
  induction count generalizing start with
  | zero => simp [phaseSteps]
  | succ count ih =>
      simp only [phaseSteps]
      have htail := ih (start + 1)
      nlinarith

/-- The reverse-output controller is quadratic in the original canonical
graph-string length. -/
theorem steps_le_encoding (I : CliqueInstance) :
    steps I ≤ 10 * ((encodeCliqueInstance I).length + 1) ^ 2 := by
  let n := I.vertexCount
  let suffix := graphSuffix I
  let inputLength := (encodeCliqueInstance I).length
  have hphase := phaseSteps_le 0 n
  have hlength : inputLength = n + suffix.length + 2 := by
    simp [inputLength, n, suffix, graphSuffix, encodeCliqueInstance]
    omega
  have hn : n ≤ inputLength := by omega
  have hsuffix : suffix.length ≤ inputLength := by omega
  change phaseSteps 0 n + 3 * n + suffix.length + 7 ≤ _
  nlinarith [sq_nonneg (inputLength + 1)]

/-- The compiled controller emits the exact reversed range certificate within
the advertised quadratic polynomial. -/
def outputs_in_time (I : CliqueInstance) :
    TM2OutputsInTime (compile program) (encodeCliqueInstance I)
      (some (rangeCertificate I).reverse)
      ((10 * (Polynomial.X + 1) ^ 2).eval
        (encodeCliqueInstance I).length) := by
  have builderRun := run I
  have compiledRun := compile_evalsToInTime program builderRun
  have htime : steps I ≤
      (10 * (Polynomial.X + 1) ^ 2).eval
        (encodeCliqueInstance I).length := by
    simpa [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X] using steps_le_encoding I
  change EvalsToInTime (compile program).step
    (initList (compile program) (encodeCliqueInstance I))
    (some (haltList (compile program) (rangeCertificate I).reverse))
    ((10 * (Polynomial.X + 1) ^ 2).eval
      (encodeCliqueInstance I).length)
  refine ⟨⟨compiledRun.steps, ?_⟩, compiledRun.steps_le_m.trans htime⟩
  convert compiledRun.evals_in_steps using 1
  all_goals simp only [encodeCfg_initialCfg, encodeCfg_haltCfg]

/-- Fixed quadratic-time machine for the reversed physical certificate. -/
noncomputable def revComputableInPolyTime :
    TM2ComputableInPolyTime encodeCliqueInstance id
      (fun I : CliqueInstance => (rangeCertificate I).reverse) where
  tm := compile program
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 10 * (Polynomial.X + 1) ^ 2
  outputsFun := fun I => by
    have output := outputs_in_time I
    convert output using 1
    · change List.map id _ = _
      exact List.map_id _
    · congr 1
      change List.map id _ = _
      exact List.map_id _

/-- Fixed polynomial-time machine mapping a canonical graph directly to the
typed range certificate `[0, ..., |V| - 1]`. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime encodeCliqueInstance encodeCliqueCertificate
      (fun I : CliqueInstance => List.range I.vertexCount) := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    revComputableInPolyTime
    (reverse_computableInPolyTime (Γ := CliqueSym))
  let raw := Classical.choice composed
  exact
    { tm := raw.tm
      inputAlphabet := raw.inputAlphabet
      outputAlphabet := raw.outputAlphabet
      time := raw.time
      outputsFun := fun I => by
        have output := raw.outputsFun I
        simpa [Function.comp_def, rangeCertificate] using output }

end CLRS.Chapter34.Turing.VertexCover.ComplementMachine.PairStream.RangeCertificate

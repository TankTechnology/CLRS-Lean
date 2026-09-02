import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.TargetBound.Semantics

/-!
# General CLIQUE verifier: polynomial runtime of the target bound
-/

noncomputable section

open Computability StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.TargetBound

open PolyBuilder
open _root_.Turing

private theorem targetSteps_le (count : Nat) (input : List CliqueSym) :
    targetSteps count input ≤ 2 * input.length + count + 4 := by
  induction input generalizing count with
  | nil => simp [targetSteps]
  | cons symbol input ih =>
      have hsame := ih count
      cases symbol <;> try simp [targetSteps] <;> try omega
      case tick =>
        cases count with
        | zero => simp [targetSteps]; omega
        | succ count =>
            have h := ih count
            simp [targetSteps]
            omega

private theorem vertexSteps_le (count : Nat) (input : List CliqueSym) :
    vertexSteps count input ≤ 3 * input.length + count + 4 := by
  induction input generalizing count with
  | nil => simp [vertexSteps]
  | cons symbol input ih =>
      have hsame := ih count
      cases symbol <;> try simp [vertexSteps] <;> try omega
      case tick =>
        have h := ih (count + 1)
        simp [vertexSteps]
        omega
      case fieldSep =>
        have h := targetSteps_le count input
        simp [vertexSteps]
        omega

private theorem instanceSteps_le (input : List CliqueSym) :
    instanceSteps input ≤ 3 * input.length + 4 := by
  cases input with
  | nil => simp [instanceSteps]
  | cons symbol input =>
      have h := vertexSteps_le 0 input
      simp [instanceSteps]
      omega

/-- Total step budget of the exact target-bound run. -/
def targetBoundSteps (certificate input : List CliqueSym) : Nat :=
  certificate.length + 1 + instanceSteps input

/-- The controller is linear in the separator-based pair encoding. -/
theorem targetBoundSteps_le (certificate input : List CliqueSym) :
    targetBoundSteps certificate input ≤
      3 * (pairEncoding certificate input).length + 4 := by
  have h := instanceSteps_le input
  simp only [targetBoundSteps, pairEncoding, List.length_append,
    List.length_map, List.length_cons, List.length_nil]
  omega

/-- The compiled controller emits its singleton Boolean result inside the
displayed linear budget. -/
def targetBound_outputs_in_time (certificate input : List CliqueSym) :
    TM2OutputsInTime (compile program) (pairEncoding certificate input)
      (some (boolEncoding (targetBoundPass certificate input)))
      (3 * (pairEncoding certificate input).length + 4) := by
  have builderRun := targetBound_run certificate input
  have compiledRun := compile_evalsToInTime program builderRun
  change EvalsToInTime (compile program).step
      (initList (compile program) (pairEncoding certificate input))
      (some (haltList (compile program)
        [targetBoundPass certificate input]))
      (3 * (pairEncoding certificate input).length + 4)
  refine ⟨⟨compiledRun.steps, ?_⟩, compiledRun.steps_le_m.trans
    (targetBoundSteps_le certificate input)⟩
  convert compiledRun.evals_in_steps using 1 <;>
    simp only [encodeCfg_initialCfg, encodeCfg_haltCfg] <;> rfl

/-- Polynomial-time computability of the concrete target-bound component on
raw certificate/instance pairs. -/
noncomputable def targetBoundPassComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun pr : List CliqueSym × List CliqueSym => pairEncoding pr.1 pr.2)
      boolEncoding (fun pr => targetBoundPass pr.1 pr.2) where
  tm := compile program
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 3 * Polynomial.X + 4
  outputsFun := fun pr => by
    rcases pr with ⟨certificate, input⟩
    have run := targetBound_outputs_in_time certificate input
    convert run using 1 <;>
      simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_ofNat]
    all_goals
      change List.map id _ = _
      exact List.map_id _

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.TargetBound

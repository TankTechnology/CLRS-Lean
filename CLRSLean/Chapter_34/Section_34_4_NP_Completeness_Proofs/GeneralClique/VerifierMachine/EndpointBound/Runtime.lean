import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.EndpointBound.Run

/-!
# General CLIQUE verifier: polynomial runtime of endpoint-bound checking
-/

noncomputable section

open Computability StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.EndpointBound

open PolyBuilder
open _root_.Turing

private theorem phaseSteps_le (phase : Phase) (input : List CliqueSym) :
    phaseSteps phase input ≤
      4 * (input.length + phaseSpent phase) +
        2 * phaseRemaining phase + 6 := by
  induction input generalizing phase with
  | nil =>
      cases phase <;>
        simp [phaseSteps, phaseRemaining, phaseSpent] <;> omega
  | cons symbol input ih =>
      cases phase with
      | edges vertexCount =>
          have hedges := ih (Phase.edges vertexCount)
          have hleft := ih (Phase.left vertexCount)
          cases symbol <;>
            simp [phaseSteps, phaseRemaining, phaseSpent] at hedges hleft ⊢ <;>
            omega
      | left vertexCount =>
          have hleft := ih (Phase.left vertexCount)
          have hright := ih (Phase.right vertexCount 0)
          cases symbol <;>
            simp [phaseSteps, phaseRemaining, phaseSpent] at hleft hright ⊢ <;>
            omega
      | right remaining spent =>
          have hsame := ih (Phase.right remaining spent)
          cases symbol <;>
            try (simp [phaseSteps, phaseRemaining, phaseSpent] at hsame ⊢ <;>
              omega)
          · cases remaining with
            | zero => simp [phaseSteps, phaseRemaining, phaseSpent]; omega
            | succ remaining =>
                have h := ih (Phase.right remaining (spent + 1))
                simp [phaseSteps, phaseRemaining, phaseSpent] at h ⊢
                omega
          · cases remaining with
            | zero => simp [phaseSteps, phaseRemaining, phaseSpent]; omega
            | succ remaining =>
                have h := ih (Phase.edges (remaining + (spent + 1)))
                simp [phaseSteps, phaseRemaining, phaseSpent] at h ⊢
                omega

private theorem targetFieldSteps_le (vertexCount : Nat)
    (input : List CliqueSym) :
    targetFieldSteps vertexCount input ≤
      4 * input.length + 2 * vertexCount + 6 := by
  induction input with
  | nil => simp [targetFieldSteps]; omega
  | cons symbol input ih =>
      have hedges := phaseSteps_le (Phase.edges vertexCount) input
      simp only [phaseSpent, phaseRemaining, Nat.add_zero] at hedges
      cases symbol <;> simp [targetFieldSteps] <;> omega

private theorem vertexFieldSteps_le (loaded : Nat)
    (input : List CliqueSym) :
    vertexFieldSteps loaded input ≤
      4 * input.length + 2 * loaded + 6 := by
  induction input generalizing loaded with
  | nil => simp [vertexFieldSteps]; omega
  | cons symbol input ih =>
      have hsame := ih loaded
      have htick := ih (loaded + 1)
      have htarget := targetFieldSteps_le loaded input
      cases symbol <;> simp [vertexFieldSteps] <;> omega

private theorem instanceSteps_le (input : List CliqueSym) :
    instanceSteps input ≤ 4 * input.length + 6 := by
  cases input with
  | nil => simp [instanceSteps]
  | cons symbol input =>
      have h := vertexFieldSteps_le 0 input
      simp [instanceSteps] at h ⊢
      omega

/-- Total exact builder-step count of the endpoint-bound checker. -/
def endpointBoundSteps (certificate input : List CliqueSym) : Nat :=
  certificate.length + 1 + instanceSteps input

/-- Uniform linear bound in the paired raw input length. -/
theorem endpointBoundSteps_le (certificate input : List CliqueSym) :
    endpointBoundSteps certificate input ≤
      4 * (pairEncoding certificate input).length + 6 := by
  have h := instanceSteps_le input
  simp only [endpointBoundSteps, pairEncoding, List.length_append,
    List.length_map, List.length_cons, List.length_nil]
  omega

/-- The compiled fixed controller emits the endpoint-bound Boolean within the
displayed linear budget. -/
def endpointBound_outputs_in_time (certificate input : List CliqueSym) :
    TM2OutputsInTime (compile program) (pairEncoding certificate input)
      (some (boolEncoding (endpointBoundPass certificate input)))
      (4 * (pairEncoding certificate input).length + 6) := by
  have builderRun := endpointBound_run certificate input
  have compiledRun := compile_evalsToInTime program builderRun
  change EvalsToInTime (compile program).step
      (initList (compile program) (pairEncoding certificate input))
      (some (haltList (compile program)
        [endpointBoundPass certificate input]))
      (4 * (pairEncoding certificate input).length + 6)
  refine ⟨⟨compiledRun.steps, ?_⟩, compiledRun.steps_le_m.trans
    (endpointBoundSteps_le certificate input)⟩
  convert compiledRun.evals_in_steps using 1 <;>
    simp only [encodeCfg_initialCfg, encodeCfg_haltCfg] <;> rfl

/-- Polynomial-time computability of the concrete endpoint-bound component. -/
noncomputable def endpointBoundPassComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun pr : List CliqueSym × List CliqueSym => pairEncoding pr.1 pr.2)
      boolEncoding (fun pr => endpointBoundPass pr.1 pr.2) where
  tm := compile program
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 4 * Polynomial.X + 6
  outputsFun := fun pr => by
    rcases pr with ⟨certificate, input⟩
    have run := endpointBound_outputs_in_time certificate input
    convert run using 1 <;>
      simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_ofNat]
    all_goals
      change List.map id _ = _
      exact List.map_id _

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.EndpointBound

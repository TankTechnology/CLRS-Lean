import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.CertificateRange.Run

/-!
# General CLIQUE verifier: polynomial runtime of certificate range checking
-/

noncomputable section

open Computability StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.CertificateRange

open PolyBuilder
open _root_.Turing

private theorem phaseSteps_le (phase : Phase) (input : List CliqueSym) :
    phaseSteps phase input ≤
      6 * (input.length + phaseSpent phase) +
        3 * phaseRemaining phase + 7 := by
  induction input generalizing phase with
  | nil =>
      cases phase <;>
        simp [phaseSteps, phaseRemaining, phaseSpent] <;> omega
  | cons symbol input ih =>
      cases phase with
      | vertices vertexCount =>
          have hvertices := ih (Phase.vertices vertexCount)
          have hvertex := ih (Phase.vertex vertexCount 0)
          cases symbol <;>
            simp [phaseSteps, phaseRemaining, phaseSpent] at hvertices hvertex ⊢ <;>
            omega
      | vertex remaining spent =>
          have hsame := ih (Phase.vertex remaining spent)
          cases symbol <;>
            try (simp [phaseSteps, phaseRemaining, phaseSpent] at hsame ⊢ <;>
              omega)
          · cases remaining with
            | zero => simp [phaseSteps, phaseRemaining, phaseSpent]; omega
            | succ remaining =>
                have h := ih (Phase.vertex remaining (spent + 1))
                simp [phaseSteps, phaseRemaining, phaseSpent] at h ⊢
                omega
          · cases remaining with
            | zero => simp [phaseSteps, phaseRemaining, phaseSpent]; omega
            | succ remaining =>
                have h := ih (Phase.vertices (remaining + (spent + 1)))
                simp [phaseSteps, phaseRemaining, phaseSpent] at h ⊢
                omega

private theorem certificatePhaseSteps_le (vertexCount : Nat)
    (certificate : List CliqueSym) :
    certificatePhaseSteps vertexCount certificate ≤
      6 * certificate.length + 3 * vertexCount + 7 := by
  cases certificate with
  | nil => simp [certificatePhaseSteps]; omega
  | cons marker payload =>
      have h := phaseSteps_le (Phase.vertices vertexCount) payload
      simp [certificatePhaseSteps, phaseSpent, phaseRemaining] at h ⊢
      omega

private theorem finishCertificateSteps_le (vertexCount : Nat)
    (certificate input : List CliqueSym) :
    finishCertificateSteps vertexCount certificate input ≤
      7 * (input.length + certificate.length) + 3 * vertexCount + 9 := by
  have h := certificatePhaseSteps_le vertexCount certificate
  simp [finishCertificateSteps] at h ⊢
  omega

private theorem vertexFieldSteps_le (certificate : List CliqueSym)
    (loaded : Nat) (input : List CliqueSym) :
    vertexFieldSteps certificate loaded input ≤
      7 * (input.length + certificate.length) + 3 * loaded + 10 := by
  induction input generalizing loaded with
  | nil => simp [vertexFieldSteps]; omega
  | cons symbol input ih =>
      have hsame := ih loaded
      have htick := ih (loaded + 1)
      have hfinish := finishCertificateSteps_le loaded certificate input
      cases symbol <;> simp [vertexFieldSteps] <;> omega

private theorem instanceSteps_le (certificate input : List CliqueSym) :
    instanceSteps certificate input ≤
      7 * (input.length + certificate.length) + 10 := by
  cases input with
  | nil => simp [instanceSteps]; omega
  | cons marker input =>
      have h := vertexFieldSteps_le certificate 0 input
      simp [instanceSteps] at h ⊢
      omega

/-- Total exact builder-step count of the certificate-range checker. -/
def certificateRangeSteps (certificate input : List CliqueSym) : Nat :=
  2 * certificate.length + 1 + instanceSteps certificate input

/-- Uniform linear bound in the paired raw input length. -/
theorem certificateRangeSteps_le (certificate input : List CliqueSym) :
    certificateRangeSteps certificate input ≤
      9 * (pairEncoding certificate input).length + 2 := by
  have h := instanceSteps_le certificate input
  simp only [certificateRangeSteps, pairEncoding, List.length_append,
    List.length_map, List.length_cons, List.length_nil]
  omega

/-- The compiled fixed controller emits the range Boolean within the displayed
linear budget. -/
def certificateRange_outputs_in_time (certificate input : List CliqueSym) :
    TM2OutputsInTime (compile program) (pairEncoding certificate input)
      (some (boolEncoding (certificateRangePass certificate input)))
      (9 * (pairEncoding certificate input).length + 2) := by
  have builderRun := certificateRange_run certificate input
  have compiledRun := compile_evalsToInTime program builderRun
  change EvalsToInTime (compile program).step
      (initList (compile program) (pairEncoding certificate input))
      (some (haltList (compile program)
        [certificateRangePass certificate input]))
      (9 * (pairEncoding certificate input).length + 2)
  refine ⟨⟨compiledRun.steps, ?_⟩, compiledRun.steps_le_m.trans
    (certificateRangeSteps_le certificate input)⟩
  convert compiledRun.evals_in_steps using 1 <;>
    simp only [encodeCfg_initialCfg, encodeCfg_haltCfg] <;> rfl

/-- Polynomial-time computability of the concrete certificate-range component. -/
noncomputable def certificateRangePassComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun pr : List CliqueSym × List CliqueSym => pairEncoding pr.1 pr.2)
      boolEncoding (fun pr => certificateRangePass pr.1 pr.2) where
  tm := compile program
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 9 * Polynomial.X + 2
  outputsFun := fun pr => by
    rcases pr with ⟨certificate, input⟩
    have run := certificateRange_outputs_in_time certificate input
    convert run using 1 <;>
      simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_ofNat]
    all_goals
      change List.map id _ = _
      exact List.map_id _

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.CertificateRange

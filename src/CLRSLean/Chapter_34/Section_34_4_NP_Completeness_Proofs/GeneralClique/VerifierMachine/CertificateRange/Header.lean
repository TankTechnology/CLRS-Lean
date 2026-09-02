import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.CertificateRange.Phases

/-!
# General CLIQUE verifier: restored-certificate header

This file connects instance cleanup and certificate restoration to the record
scanner.  It is kept separate from the outer input scanner so each proof has a
small compilation unit.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.CertificateRange

open PolyBuilder

/-- Steps from the restored certificate marker to the final answer. -/
def certificatePhaseSteps (vertexCount : Nat) : List CliqueSym → Nat
  | [] => vertexCount + 7
  | _ :: payload => phaseSteps (.vertices vertexCount) payload + 1

/-- Execute the restored certificate marker and all vertex records. -/
def certificatePhase_run (vertexCount : Nat) (certificate : List CliqueSym)
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .certificateMark buffer₁ buffer₂ test (certificate.map some) [] []
        (List.replicate vertexCount (some .tick)) [])
      (some (haltCfg program
        [certificatePayloadResult vertexCount certificate]))
      (certificatePhaseSteps vertexCount certificate) := by
  cases certificate with
  | nil =>
      let after := cfg (.clearInput false) none buffer₂ test [] [] []
        (List.replicate vertexCount (some .tick)) []
      have first : EvalsToInTime (step program)
          (cfg .certificateMark buffer₁ buffer₂ test [] [] []
            (List.replicate vertexCount (some .tick)) [])
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := clearInput_run false [] []
        (List.replicate vertexCount (some .tick)) 0 none buffer₂ test
      have rest' : EvalsToInTime (step program) after
          (some (haltCfg program [false])) (vertexCount + 6) := by
        simpa using rest
      let full := EvalsToInTime.trans (step program)
        1 (vertexCount + 6) _ after _ first rest'
      simpa [certificatePayloadResult, certificatePhaseSteps] using full
  | cons marker payload =>
      let after := cfg .vertices (some (some marker)) buffer₂ test
        (payload.map some) [] []
        (List.replicate vertexCount (some .tick)) []
      have first : EvalsToInTime (step program)
          (cfg .certificateMark buffer₁ buffer₂ test
            ((marker :: payload).map some) [] []
            (List.replicate vertexCount (some .tick)) [])
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := phase_run (Phase.vertices vertexCount) payload
        (some (some marker)) buffer₂ test
      let full := EvalsToInTime.trans (step program)
        1 (phaseSteps (.vertices vertexCount) payload)
        _ after _ first rest
      simpa [certificatePayloadResult, certificatePhaseSteps, phaseLabel,
        phaseRemaining, phaseSpent, phaseResult, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using full

/-- Steps for discarding the unused instance suffix, restoring the saved
certificate, and checking its records. -/
def finishCertificateSteps (vertexCount : Nat) (certificate input : List CliqueSym) :
    Nat :=
  input.length + 1 + (certificate.length + 1) +
    certificatePhaseSteps vertexCount certificate

/-- Connect instance cleanup, exact certificate restoration, and record scan. -/
def finishCertificate_run (vertexCount : Nat)
    (certificate input : List CliqueSym)
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .discardInstance buffer₁ buffer₂ test (input.map some) []
        (certificate.map some).reverse
        (List.replicate vertexCount (some .tick)) [])
      (some (haltCfg program
        [certificatePayloadResult vertexCount certificate]))
      (finishCertificateSteps vertexCount certificate input) := by
  have discard := discardInstance_run (input.map some)
    (certificate.map some).reverse
    (List.replicate vertexCount (some .tick)) buffer₁ buffer₂ test
  let restoredStart := cfg .restoreCertificate none buffer₂ test [] []
    (certificate.map some).reverse
    (List.replicate vertexCount (some .tick)) []
  have discard' : EvalsToInTime (step program)
      (cfg .discardInstance buffer₁ buffer₂ test (input.map some) []
        (certificate.map some).reverse
        (List.replicate vertexCount (some .tick)) [])
      (some restoredStart) (input.length + 1) := by
    simpa [restoredStart] using discard
  have restore := restoreCertificate_run (certificate.map some).reverse []
    (List.replicate vertexCount (some .tick)) none buffer₂ test
  let certificateStart := cfg .certificateMark none buffer₂ test
    (certificate.map some) [] []
    (List.replicate vertexCount (some .tick)) []
  have restore' : EvalsToInTime (step program) restoredStart
      (some certificateStart) (certificate.length + 1) := by
    simpa [restoredStart, certificateStart] using restore
  have scan := certificatePhase_run vertexCount certificate none buffer₂ test
  have throughRestore := EvalsToInTime.trans (step program)
    (input.length + 1) (certificate.length + 1)
    _ restoredStart _ discard' restore'
  have throughRestore' : EvalsToInTime (step program)
      (cfg .discardInstance buffer₁ buffer₂ test (input.map some) []
        (certificate.map some).reverse
        (List.replicate vertexCount (some .tick)) [])
      (some certificateStart)
      (input.length + 1 + (certificate.length + 1)) := by
    simpa [Nat.add_comm] using throughRestore
  let full := EvalsToInTime.trans (step program)
    (input.length + 1 + (certificate.length + 1))
    (certificatePhaseSteps vertexCount certificate)
    _ certificateStart _ throughRestore' scan
  simpa [finishCertificateSteps, certificateStart, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using full

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.CertificateRange

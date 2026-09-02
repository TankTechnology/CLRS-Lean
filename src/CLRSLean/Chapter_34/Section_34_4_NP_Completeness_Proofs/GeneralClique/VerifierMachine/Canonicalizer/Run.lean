import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.Canonicalizer.Simulation
import Mathlib.Tactic

/-!
# Raw-input canonicalizer: complete run
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.Canonicalizer

open PolyBuilder

/-- Exact branch-sensitive cost of one complete canonicalization. -/
def steps (kind : Kind) (input : List CliqueSym) : Nat :=
  if accepts kind (scanSymbols (initialMode kind) input) then
    4 * input.length + 3
  else
    match kind with
    | .certificate => 3 * input.length + 4
    | .instance => 3 * input.length + 6

/-- The fixed controller halts on every raw string with its total canonical
representative. -/
def run (kind : Kind) (input : List CliqueSym) :
    EvalsToInTime (step (program kind))
      (initialCfg (program kind) input)
      (some (haltCfg (program kind) (canonicalStream kind input)))
      (steps kind input) := by
  rcases scan_run kind (initialMode kind) input [] [] none none false with
    ⟨finalBuffer, scanned⟩
  have scanned' : EvalsToInTime (step (program kind))
      (initialCfg (program kind) input)
      (some (cfg kind
        (.scan (scanSymbols (initialMode kind) input)) finalBuffer none false
        [] [] input.reverse []))
      (2 * input.length) := by
    simpa [initialCfg, cfg, program] using scanned
  by_cases haccepts :
      accepts kind (scanSymbols (initialMode kind) input) = true
  · have finish : EvalsToInTime (step (program kind))
        (cfg kind (.scan (scanSymbols (initialMode kind) input))
          finalBuffer none false [] [] input.reverse [])
        (some (cfg kind .restore none none false [] [] input.reverse [])) 1 :=
      ⟨⟨1, by simp [flip, step, program, cfg, stepOp, haccepts]⟩, le_rfl⟩
    have restored := restore_run kind input.reverse [] none none false
    have restored' : EvalsToInTime (step (program kind))
        (cfg kind .restore none none false [] [] input.reverse [])
        (some (haltCfg (program kind) input))
        (2 * input.length + 2) := by
      simpa using restored
    let first := EvalsToInTime.trans (step (program kind))
      (2 * input.length) 1 _ _ _ scanned' finish
    let full := EvalsToInTime.trans (step (program kind))
      _ (2 * input.length + 2) _ _ _ first restored'
    convert full using 1
    all_goals simp [steps, canonicalStream, haccepts, Nat.add_comm,
      Nat.add_left_comm]
    omega
  · have hacceptsFalse :
        accepts kind (scanSymbols (initialMode kind) input) = false := by
      exact Bool.eq_false_of_not_eq_true haccepts
    have finish : EvalsToInTime (step (program kind))
        (cfg kind (.scan (scanSymbols (initialMode kind) input))
          finalBuffer none false [] [] input.reverse [])
        (some (cfg kind .clear none none false [] [] input.reverse [])) 1 :=
      ⟨⟨1, by simp [flip, step, program, cfg, stepOp,
        hacceptsFalse]⟩, le_rfl⟩
    have cleared := clear_run kind input.reverse [] none none false
    let first := EvalsToInTime.trans (step (program kind))
      (2 * input.length) 1 _ _ _ scanned' finish
    let second := EvalsToInTime.trans (step (program kind))
      _ (input.length + 1) _ _ _ first (by simpa using cleared)
    rcases kind with _ | _
    ·
        have fallbackRun := certificate_fallback_run [] none none false
        let full := EvalsToInTime.trans (step (program .certificate))
          _ 2 _ _ _ second fallbackRun
        convert full using 1
        all_goals simp [steps, canonicalStream, hacceptsFalse, fallback,
          Nat.add_assoc, Nat.add_left_comm]
        omega
    ·
        have fallbackRun := instance_fallback_run [] none none false
        let full := EvalsToInTime.trans (step (program .instance))
          _ 4 _ _ _ second fallbackRun
        convert full using 1
        all_goals simp [steps, canonicalStream, hacceptsFalse, fallback,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        omega

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.Canonicalizer

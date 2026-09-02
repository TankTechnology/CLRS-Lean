import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine.LookupPhases

/-!
# Concrete verifier: total cleanup and canonical halting output
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitVerifier

open Computability StateTransition
open _root_.Turing

private abbrev transition := flip Option.bind step

theorem clear_input_phase (state : State) (answer : Bool)
    (input : List (Option CircuitSym)) (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    ∃ finalState,
      transition^[input.length + 1]
        (some (cfg (some (.clearInput answer)) state input output certificate values
          scratch gateCount index saved)) =
        some (cfg (some (.clearCertificate answer)) finalState [] output certificate values
          scratch gateCount index saved) := by
  induction input generalizing state with
  | nil =>
      refine ⟨{ state with inputBuffer := none }, ?_⟩
      change step (cfg (some (.clearInput answer)) state [] output certificate values
        scratch gateCount index saved) = _
      exact clear_input_done_step state answer output certificate values scratch
        gateCount index saved
  | cons head rest ih =>
      rcases ih { state with inputBuffer := some head } with ⟨finalState, hrun⟩
      refine ⟨finalState, ?_⟩
      have hfirst := clear_input_step state answer head rest output certificate values
        scratch gateCount index saved
      simpa using step_then (rest.length + 1) hfirst hrun

theorem clear_certificate_phase (state : State) (answer : Bool)
    (input : List (Option CircuitSym)) (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    ∃ finalState,
      transition^[certificate.length + 1]
        (some (cfg (some (.clearCertificate answer)) state input output certificate values
          scratch gateCount index saved)) =
        some (cfg (some (.clearValues answer)) finalState input output [] values scratch
          gateCount index saved) := by
  induction certificate generalizing state with
  | nil =>
      refine ⟨{ state with boolBuffer := none }, ?_⟩
      change step (cfg (some (.clearCertificate answer)) state input output [] values
        scratch gateCount index saved) = _
      exact clear_certificate_done_step state answer input output values scratch
        gateCount index saved
  | cons bit rest ih =>
      rcases ih { state with boolBuffer := some bit } with ⟨finalState, hrun⟩
      refine ⟨finalState, ?_⟩
      have hfirst := clear_certificate_step state answer bit input output rest values
        scratch gateCount index saved
      simpa using step_then (rest.length + 1) hfirst hrun

theorem clear_values_phase (state : State) (answer : Bool)
    (input : List (Option CircuitSym)) (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    ∃ finalState,
      transition^[values.length + 1]
        (some (cfg (some (.clearValues answer)) state input output certificate values
          scratch gateCount index saved)) =
        some (cfg (some (.clearScratch answer)) finalState input output certificate [] scratch
          gateCount index saved) := by
  induction values generalizing state with
  | nil =>
      refine ⟨{ state with boolBuffer := none }, ?_⟩
      change step (cfg (some (.clearValues answer)) state input output certificate []
        scratch gateCount index saved) = _
      exact clear_values_done_step state answer input output certificate scratch
        gateCount index saved
  | cons bit rest ih =>
      rcases ih { state with boolBuffer := some bit } with ⟨finalState, hrun⟩
      refine ⟨finalState, ?_⟩
      have hfirst := clear_values_step state answer bit input output certificate rest
        scratch gateCount index saved
      simpa using step_then (rest.length + 1) hfirst hrun

theorem clear_scratch_phase (state : State) (answer : Bool)
    (input : List (Option CircuitSym)) (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    ∃ finalState,
      transition^[scratch.length + 1]
        (some (cfg (some (.clearScratch answer)) state input output certificate values
          scratch gateCount index saved)) =
        some (cfg (some (.clearGateCount answer)) finalState input output certificate values []
          gateCount index saved) := by
  induction scratch generalizing state with
  | nil =>
      refine ⟨{ state with boolBuffer := none }, ?_⟩
      change step (cfg (some (.clearScratch answer)) state input output certificate values []
        gateCount index saved) = _
      exact clear_scratch_done_step state answer input output certificate values
        gateCount index saved
  | cons bit rest ih =>
      rcases ih { state with boolBuffer := some bit } with ⟨finalState, hrun⟩
      refine ⟨finalState, ?_⟩
      have hfirst := clear_scratch_step state answer bit input output certificate values rest
        gateCount index saved
      simpa using step_then (rest.length + 1) hfirst hrun

theorem clear_gate_count_phase (state : State) (answer : Bool)
    (input : List (Option CircuitSym)) (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    ∃ finalState,
      transition^[gateCount + 1]
        (some (cfg (some (.clearGateCount answer)) state input output certificate values
          scratch gateCount index saved)) =
        some (cfg (some (.clearIndex answer)) finalState input output certificate values scratch
          0 index saved) := by
  induction gateCount generalizing state with
  | zero =>
      refine ⟨{ state with counterPresent := false }, ?_⟩
      change step (cfg (some (.clearGateCount answer)) state input output certificate
        values scratch 0 index saved) = _
      exact clear_gate_count_done_step state answer input output certificate values
        scratch index saved
  | succ gateCount ih =>
      rcases ih { state with counterPresent := true } with ⟨finalState, hrun⟩
      refine ⟨finalState, ?_⟩
      have hfirst := clear_gate_count_step state answer input output certificate values
        scratch gateCount index saved
      simpa using step_then (gateCount + 1) hfirst hrun

theorem clear_index_phase (state : State) (answer : Bool)
    (input : List (Option CircuitSym)) (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    ∃ finalState,
      transition^[index + 1]
        (some (cfg (some (.clearIndex answer)) state input output certificate values
          scratch gateCount index saved)) =
        some (cfg (some (.clearSaved answer)) finalState input output certificate values scratch
          gateCount 0 saved) := by
  induction index generalizing state with
  | zero =>
      refine ⟨{ state with counterPresent := false }, ?_⟩
      change step (cfg (some (.clearIndex answer)) state input output certificate
        values scratch gateCount 0 saved) = _
      exact clear_index_done_step state answer input output certificate values scratch
        gateCount saved
  | succ index ih =>
      rcases ih { state with counterPresent := true } with ⟨finalState, hrun⟩
      refine ⟨finalState, ?_⟩
      have hfirst := clear_index_step state answer input output certificate values
        scratch gateCount index saved
      simpa using step_then (index + 1) hfirst hrun

theorem clear_saved_phase (state : State) (answer : Bool)
    (input : List (Option CircuitSym)) (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    ∃ finalState,
      transition^[saved + 1]
        (some (cfg (some (.clearSaved answer)) state input output certificate values
          scratch gateCount index saved)) =
        some (cfg (some (.emit answer)) finalState input output certificate values scratch
          gateCount index 0) := by
  induction saved generalizing state with
  | zero =>
      refine ⟨{ state with counterPresent := false }, ?_⟩
      change step (cfg (some (.clearSaved answer)) state input output certificate
        values scratch gateCount index 0) = _
      exact clear_saved_done_step state answer input output certificate values scratch
        gateCount index
  | succ saved ih =>
      rcases ih { state with counterPresent := true } with ⟨finalState, hrun⟩
      refine ⟨finalState, ?_⟩
      have hfirst := clear_saved_step state answer input output certificate values scratch
        gateCount index saved
      simpa using step_then (saved + 1) hfirst hrun

/-- Exact total cleanup cost from the common decision label. -/
def cleanupSteps (input : List (Option CircuitSym))
    (certificate values scratch : List Bool) (gateCount index saved : Nat) : Nat :=
  input.length + certificate.length + values.length + scratch.length +
    gateCount + index + saved + 9

/-- Cleanup empties every non-output stack, emits one Boolean, resets finite
state, and halts in Mathlib's canonical `haltList` configuration. -/
theorem cleanup_phase (state : State) (answer : Bool)
    (input : List (Option CircuitSym)) (certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    transition^[cleanupSteps input certificate values scratch gateCount index saved]
      (some (cfg (some (.clearInput answer)) state input [] certificate values scratch
        gateCount index saved)) =
      some (haltList machine [answer]) := by
  rcases clear_input_phase state answer input [] certificate values scratch
      gateCount index saved with ⟨s₁, h₁⟩
  rcases clear_certificate_phase s₁ answer [] [] certificate values scratch
      gateCount index saved with ⟨s₂, h₂⟩
  rcases clear_values_phase s₂ answer [] [] [] values scratch
      gateCount index saved with ⟨s₃, h₃⟩
  rcases clear_scratch_phase s₃ answer [] [] [] [] scratch
      gateCount index saved with ⟨s₄, h₄⟩
  rcases clear_gate_count_phase s₄ answer [] [] [] [] [] gateCount index saved with
    ⟨s₅, h₅⟩
  rcases clear_index_phase s₅ answer [] [] [] [] [] 0 index saved with ⟨s₆, h₆⟩
  rcases clear_saved_phase s₆ answer [] [] [] [] [] 0 0 saved with ⟨s₇, h₇⟩
  have h₈ : transition^[1]
      (some (cfg (some (.emit answer)) s₇ [] [] [] [] [] 0 0 0)) =
      some (cfg (some .done) s₇ [] [answer] [] [] [] 0 0 0) := by
    change step (cfg (some (.emit answer)) s₇ [] [] [] [] [] 0 0 0) = _
    exact emit_step s₇ answer
  have h₉ : transition^[1]
      (some (cfg (some .done) s₇ [] [answer] [] [] [] 0 0 0)) =
      some (haltList machine [answer]) := by
    change step (cfg (some .done) s₇ [] [answer] [] [] [] 0 0 0) = _
    calc
      step (cfg (some .done) s₇ [] [answer] [] [] [] 0 0 0) =
          some (cfg none initialState [] [answer] [] [] [] 0 0 0) :=
        done_step s₇ answer
      _ = some (haltList machine [answer]) := by
        apply congrArg some
        apply _root_.Turing.TM2Comp.Cfg_ext
        · rfl
        · rfl
        · funext stack
          cases stack <;> simp [cfg, machine, stackContents, haltList, Function.update]
  have h₁₂ := step_comp (input.length + 1) (certificate.length + 1) h₁ h₂
  have h₁₂₃ := step_comp ((certificate.length + 1) + (input.length + 1))
    (values.length + 1) h₁₂ h₃
  have h₁₄ := step_comp ((values.length + 1) +
    ((certificate.length + 1) + (input.length + 1)))
    (scratch.length + 1) h₁₂₃ h₄
  have h₁₅ := step_comp ((scratch.length + 1) + ((values.length + 1) +
    ((certificate.length + 1) + (input.length + 1))))
    (gateCount + 1) h₁₄ h₅
  have h₁₆ := step_comp ((gateCount + 1) + ((scratch.length + 1) +
    ((values.length + 1) + ((certificate.length + 1) + (input.length + 1)))))
    (index + 1) h₁₅ h₆
  have h₁₇ := step_comp ((index + 1) + ((gateCount + 1) +
    ((scratch.length + 1) + ((values.length + 1) +
      ((certificate.length + 1) + (input.length + 1))))))
    (saved + 1) h₁₆ h₇
  have h₁₈ := step_comp ((saved + 1) + ((index + 1) + ((gateCount + 1) +
    ((scratch.length + 1) + ((values.length + 1) +
      ((certificate.length + 1) + (input.length + 1))))))) 1 h₁₇ h₈
  have hfull := step_comp (1 + ((saved + 1) + ((index + 1) + ((gateCount + 1) +
    ((scratch.length + 1) + ((values.length + 1) +
      ((certificate.length + 1) + (input.length + 1)))))))) 1 h₁₈ h₉
  have hsteps : cleanupSteps input certificate values scratch gateCount index saved =
      1 + (1 + ((saved + 1) + ((index + 1) + ((gateCount + 1) +
        ((scratch.length + 1) + ((values.length + 1) +
          ((certificate.length + 1) + (input.length + 1)))))))) := by
    simp [cleanupSteps]
    omega
  rw [hsteps]
  exact hfull

end CLRS.Chapter34.Turing.GeneralCircuitVerifier

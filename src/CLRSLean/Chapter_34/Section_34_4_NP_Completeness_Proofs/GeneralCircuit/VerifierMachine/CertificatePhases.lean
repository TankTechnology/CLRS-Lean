import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine.Steps

/-!
# Concrete verifier: certificate and unary-parser phases
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitVerifier

open Computability StateTransition

private abbrev transition := flip Option.bind step

/-- Compose two exact verifier-machine segments. -/
theorem step_comp {A B C : Option machine.Cfg} (n₁ n₂ : Nat)
    (h₁ : transition^[n₁] A = B) (h₂ : transition^[n₂] B = C) :
    transition^[n₂ + n₁] A = C := by
  rw [Function.iterate_add_apply, h₁, h₂]

/-- Compose one concrete step with a following exact phase. -/
theorem step_then {A : Option machine.Cfg} {B C : machine.Cfg} (n : Nat)
    (h₁ : step B = some C) (h₂ : transition^[n] (some C) = A) :
    transition^[n + 1] (some B) = A := by
  rw [Function.iterate_add_apply]
  change transition^[n] (step B) = A
  rw [h₁]
  exact h₂

/-- Scanning a certificate reverses its Boolean interpretation onto scratch,
counts every symbol, and accumulates exactly the public legality check. -/
theorem scan_phase (state : State) (certificate : List CircuitSym)
    (input : List (Option CircuitSym)) (output stored values scratch : List Bool)
    (gateCount index saved : Nat) :
    ∃ finalState,
      finalState.validAssignment =
        (state.validAssignment && certificate.all isAssignmentSymbol) ∧
      transition^[certificate.length + 1]
        (some (cfg (some .scanCertificate) state
          (List.map some certificate ++ none :: input)
          output stored values scratch gateCount index saved)) =
        some (cfg (some .reverseCertificate) finalState input output stored values
          ((certificate.map assignmentSymbolValue).reverse ++ scratch)
          (gateCount + certificate.length) index saved) := by
  induction certificate generalizing state scratch gateCount with
  | nil =>
      refine ⟨{ state with inputBuffer := some none }, ?_, ?_⟩
      · simp
      · change step (cfg (some .scanCertificate) state (none :: input)
          output stored values scratch gateCount index saved) = _
        exact scan_separator_step state input output stored values scratch
          gateCount index saved
  | cons symbol rest ih =>
      let nextState : State :=
        { state with inputBuffer := some (some symbol), validAssignment :=
            state.validAssignment && isAssignmentSymbol symbol }
      rcases ih nextState (assignmentSymbolValue symbol :: scratch) (gateCount + 1) with
        ⟨finalState, hvalid, hrun⟩
      refine ⟨finalState, ?_, ?_⟩
      · simpa [nextState, Bool.and_assoc] using hvalid
      · have hfirst := scan_symbol_step state symbol
          (List.map some rest ++ none :: input) output stored values scratch
          gateCount index saved
        have hcomposed := step_then (rest.length + 1) hfirst hrun
        simpa [nextState, List.reverse_cons, List.append_assoc, Nat.add_assoc,
          Nat.add_left_comm, Nat.add_comm] using hcomposed

/-- Reversing the scratch stack restores the certificate in source order. -/
theorem reverse_phase (state : State) (bits : List Bool)
    (input : List (Option CircuitSym)) (output certificate values : List Bool)
    (gateCount index saved : Nat) :
    ∃ finalState,
      finalState.validAssignment = state.validAssignment ∧
      transition^[bits.length + 1]
        (some (cfg (some .reverseCertificate) state input output certificate values bits
          gateCount index saved)) =
        some (cfg (some .inputCount) finalState input output
          (bits.reverse ++ certificate) values [] gateCount index saved) := by
  induction bits generalizing state certificate with
  | nil =>
      refine ⟨{ state with boolBuffer := none }, rfl, ?_⟩
      change step (cfg (some .reverseCertificate) state input output certificate values []
        gateCount index saved) = _
      exact reverse_empty_step state input output certificate values gateCount index saved
  | cons bit rest ih =>
      rcases ih { state with boolBuffer := some bit } (bit :: certificate) with
        ⟨finalState, hvalid, hrun⟩
      refine ⟨finalState, by simpa using hvalid, ?_⟩
      have hfirst := reverse_symbol_step state bit input output certificate values rest
        gateCount index saved
      have hcomposed := step_then (rest.length + 1) hfirst hrun
      simpa [List.reverse_cons, List.append_assoc] using hcomposed

/-- Label reached after a terminated unary index. -/
def parsedLabel : Return → Label
  | .inputGate => .certificateLookup
  | .outputGate => .checkTrailing
  | ret => .gateSubtract ret

theorem parse_nat_end_step (state : State) (ret : Return)
    (input : List (Option CircuitSym)) (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some (.parseNat ret)) state (some .endMark :: input)
      output certificate values scratch gateCount index saved) =
      some (cfg (some (parsedLabel ret))
        { state with inputBuffer := some (some .endMark) }
        input output certificate values scratch gateCount index saved) := by
  cases ret
  · simpa [parsedLabel] using parse_nat_end_input_step state input output certificate
      values scratch gateCount index saved
  · exact parse_nat_end_gate_step state .notGate (by decide) (by decide)
      input output certificate values scratch gateCount index saved
  · exact parse_nat_end_gate_step state .andLeft (by decide) (by decide)
      input output certificate values scratch gateCount index saved
  · rename_i left
    exact parse_nat_end_gate_step state (.andRight left) (by simp) (by simp)
      input output certificate values scratch gateCount index saved
  · exact parse_nat_end_gate_step state .orLeft (by decide) (by decide)
      input output certificate values scratch gateCount index saved
  · rename_i left
    exact parse_nat_end_gate_step state (.orRight left) (by simp) (by simp)
      input output certificate values scratch gateCount index saved
  · simpa [parsedLabel] using parse_nat_end_output_step state input output certificate
      values scratch gateCount index saved

/-- The unary parser consumes `encNat n`, adds `n` to the index counter, and
reaches the continuation determined only by its finite return tag. -/
theorem parse_nat_phase (state : State) (ret : Return) (n offset : Nat)
    (input : List (Option CircuitSym)) (output certificate values scratch : List Bool)
    (gateCount saved : Nat) :
    ∃ finalState,
      transition^[n + 1]
        (some (cfg (some (.parseNat ret)) state
          (List.map some (encNat n) ++ input)
          output certificate values scratch gateCount offset saved)) =
        some (cfg (some (parsedLabel ret)) finalState input output certificate values
          scratch gateCount (offset + n) saved) := by
  induction n generalizing state offset with
  | zero =>
      refine ⟨{ state with inputBuffer := some (some .endMark) }, ?_⟩
      change step (cfg (some (.parseNat ret)) state (some .endMark :: input)
        output certificate values scratch gateCount offset saved) = _
      exact parse_nat_end_step state ret input output certificate values scratch
        gateCount offset saved
  | succ n ih =>
      rcases ih { state with inputBuffer := some (some .argMark) } (offset + 1) with
        ⟨finalState, hrun⟩
      refine ⟨finalState, ?_⟩
      have hfirst := parse_nat_arg_step state ret
        (List.map some (encNat n) ++ input) output certificate values scratch
        gateCount offset saved
      have hcomposed := step_then (n + 1) hfirst hrun
      simpa [encNat, List.replicate_succ, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm] using hcomposed

end CLRS.Chapter34.Turing.GeneralCircuitVerifier

import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine.Cleanup

/-!
# Concrete verifier: rejecting one-step contracts
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitVerifier

attribute [local simp] setInput setBool setCounter inputIs hasInput hasBool
  hasCounter bufferedBool hasEncodedSymbol bufferedAssignmentValue
  noteAssignmentSymbol go reject finishGate finishLookup popBool pushBool
  moveBufferedBool

macro "verify_reject_step" : tactic => `(tactic|
  (apply congrArg some
   apply _root_.Turing.TM2Comp.Cfg_ext
   · simp [step, cfg, machine, program, stackContents, List.replicate_succ,
       Function.update]
   · simp [step, cfg, machine, program, stackContents, List.replicate_succ,
       Function.update]
   · funext stack
     cases stack <;>
       simp [step, cfg, machine, program, stackContents, List.replicate_succ,
         Function.update]))

theorem scan_eof_reject_step (state : State)
    (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some .scanCertificate) state [] output certificate values scratch
      gateCount index saved) =
      some (cfg (some (.clearInput false))
        { state with inputBuffer := none }
        [] output certificate values scratch gateCount index saved) := by
  verify_reject_step

theorem input_count_arg_underflow_step (state : State)
    (input : List (Option CircuitSym))
    (output certificate values scratch : List Bool) (index saved : Nat) :
    step (cfg (some .inputCount) state (some .argMark :: input)
      output certificate values scratch 0 index saved) =
      some (cfg (some (.clearInput false))
        { state with inputBuffer := some (some .argMark), counterPresent := false }
        input output certificate values scratch 0 index saved) := by
  verify_reject_step

theorem input_count_end_nonempty_step (state : State)
    (input : List (Option CircuitSym))
    (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some .inputCount) state (some .endMark :: input)
      output certificate values scratch (gateCount + 1) index saved) =
      some (cfg (some (.clearInput false))
        { state with inputBuffer := some (some .endMark), counterPresent := true }
        input output certificate values scratch gateCount index saved) := by
  verify_reject_step

theorem input_count_end_invalid_step (state : State)
    (input : List (Option CircuitSym))
    (output certificate values scratch : List Bool) (index saved : Nat)
    (hinvalid : state.validAssignment = false) :
    step (cfg (some .inputCount) state (some .endMark :: input)
      output certificate values scratch 0 index saved) =
      some (cfg (some (.clearInput false))
        { state with inputBuffer := some (some .endMark), counterPresent := false }
        input output certificate values scratch 0 index saved) := by
  rcases state with ⟨inputBuffer, boolBuffer, counterPresent, validAssignment⟩
  simp only [State.validAssignment] at hinvalid
  subst validAssignment
  verify_reject_step

theorem input_count_eof_reject_step (state : State)
    (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some .inputCount) state [] output certificate values scratch
      gateCount index saved) =
      some (cfg (some (.clearInput false)) { state with inputBuffer := none }
        [] output certificate values scratch gateCount index saved) := by
  verify_reject_step

theorem input_count_bad_symbol_reject_step (state : State) (symbol : CircuitSym)
    (harg : symbol ≠ .argMark) (hend : symbol ≠ .endMark)
    (input : List (Option CircuitSym))
    (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some .inputCount) state (some symbol :: input)
      output certificate values scratch gateCount index saved) =
      some (cfg (some (.clearInput false))
        { state with inputBuffer := some (some symbol) }
        input output certificate values scratch gateCount index saved) := by
  cases symbol <;> simp_all <;> verify_reject_step

theorem parse_nat_eof_reject_step (state : State) (ret : Return)
    (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some (.parseNat ret)) state [] output certificate values scratch
      gateCount index saved) =
      some (cfg (some (.clearInput false)) { state with inputBuffer := none }
        [] output certificate values scratch gateCount index saved) := by
  cases ret <;> verify_reject_step

theorem parse_nat_bad_symbol_reject_step (state : State) (ret : Return)
    (symbol : CircuitSym) (harg : symbol ≠ .argMark) (hend : symbol ≠ .endMark)
    (input : List (Option CircuitSym))
    (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some (.parseNat ret)) state (some symbol :: input)
      output certificate values scratch gateCount index saved) =
      some (cfg (some (.clearInput false))
        { state with inputBuffer := some (some symbol) }
        input output certificate values scratch gateCount index saved) := by
  cases ret <;> cases symbol <;> simp_all <;> verify_reject_step

theorem gates_eof_reject_step (state : State)
    (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some .gates) state [] output certificate values scratch
      gateCount index saved) =
      some (cfg (some (.clearInput false)) { state with inputBuffer := none }
        [] output certificate values scratch gateCount index saved) := by
  verify_reject_step

theorem gates_bad_marker_reject_step (state : State) (symbol : CircuitSym)
    (harg : symbol = .argMark ∨ symbol = .endMark)
    (input : List (Option CircuitSym))
    (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some .gates) state (some symbol :: input)
      output certificate values scratch gateCount index saved) =
      some (cfg (some (.clearInput false))
        { state with inputBuffer := some (some symbol) }
        input output certificate values scratch gateCount index saved) := by
  rcases harg with rfl | rfl <;> verify_reject_step

theorem certificate_lookup_prefix_underflow_step (state : State)
    (input : List (Option CircuitSym)) (output values scratch : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some .certificateLookup) state input output [] values scratch
      gateCount (index + 1) saved) =
      some (cfg (some (.clearInput false))
        { state with boolBuffer := none, counterPresent := true }
        input output [] values scratch gateCount index saved) := by
  verify_reject_step

theorem certificate_lookup_target_underflow_step (state : State)
    (input : List (Option CircuitSym)) (output values scratch : List Bool)
    (gateCount saved : Nat) :
    step (cfg (some .certificateLookup) state input output [] values scratch
      gateCount 0 saved) =
      some (cfg (some (.clearInput false))
        { state with boolBuffer := none, counterPresent := false }
        input output [] values scratch gateCount 0 saved) := by
  verify_reject_step

theorem gate_subtract_underflow_step (state : State) (ret : Return)
    (input : List (Option CircuitSym))
    (output certificate values scratch : List Bool)
    (index saved : Nat) :
    step (cfg (some (.gateSubtract ret)) state input output certificate values scratch
      0 (index + 1) saved) =
      some (cfg (some (.clearInput false))
        { state with counterPresent := false }
        input output certificate values scratch 0 index saved) := by
  cases ret <;> verify_reject_step

theorem gate_transfer_first_underflow_step (state : State) (ret : Return)
    (input : List (Option CircuitSym))
    (output certificate values scratch : List Bool) (saved : Nat) :
    step (cfg (some (.gateTransferFirst ret)) state input output certificate values scratch
      0 0 saved) =
      some (cfg (some (.clearInput false))
        { state with counterPresent := false }
        input output certificate values scratch 0 0 saved) := by
  cases ret <;> verify_reject_step

theorem check_trailing_nonempty_step (state : State)
    (head : Option CircuitSym) (input : List (Option CircuitSym))
    (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some .checkTrailing) state (head :: input)
      output certificate values scratch gateCount index saved) =
      some (cfg (some (.clearInput false))
        { state with inputBuffer := some head }
        input output certificate values scratch gateCount index saved) := by
  cases head with
  | none => verify_reject_step
  | some sym => cases sym <;> verify_reject_step

end CLRS.Chapter34.Turing.GeneralCircuitVerifier

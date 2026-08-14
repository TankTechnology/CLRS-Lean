import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine.Basic

/-!
# Concrete TM2 for the general-circuit verifier: one-step contracts

These lemmas expose the finite program as ordinary list transformations.  The
later phase proofs use only these contracts, not the nested `TM2.Stmt` syntax.
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitVerifier

attribute [local simp] setInput setBool setCounter inputIs hasInput hasBool
  hasCounter bufferedBool hasEncodedSymbol bufferedAssignmentValue
  noteAssignmentSymbol go reject finishGate finishLookup popBool pushBool
  moveBufferedBool

macro "verify_step" : tactic => `(tactic|
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

private abbrev blankState (valid : Bool) : State :=
  { inputBuffer := none, boolBuffer := none, counterPresent := false,
    validAssignment := valid }

theorem scan_symbol_step (state : State) (symbol : CircuitSym)
    (input : List (Option CircuitSym)) (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some .scanCertificate) state (some symbol :: input)
      output certificate values scratch gateCount index saved) =
      some (cfg (some .scanCertificate)
        { state with inputBuffer := some (some symbol), validAssignment :=
            state.validAssignment && isAssignmentSymbol symbol }
        input output certificate values
        (assignmentSymbolValue symbol :: scratch) (gateCount + 1) index saved) := by
  cases symbol <;> verify_step

theorem scan_separator_step (state : State) (input : List (Option CircuitSym))
    (output certificate values scratch : List Bool) (gateCount index saved : Nat) :
    step (cfg (some .scanCertificate) state (none :: input)
      output certificate values scratch gateCount index saved) =
      some (cfg (some .reverseCertificate)
        { state with inputBuffer := some none }
        input output certificate values scratch gateCount index saved) := by
  verify_step

theorem reverse_symbol_step (state : State) (value : Bool)
    (input : List (Option CircuitSym)) (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some .reverseCertificate) state input output certificate values
      (value :: scratch) gateCount index saved) =
      some (cfg (some .reverseCertificate)
        { state with boolBuffer := some value }
        input output (value :: certificate) values scratch gateCount index saved) := by
  cases value <;> verify_step

theorem reverse_empty_step (state : State) (input : List (Option CircuitSym))
    (output certificate values : List Bool) (gateCount index saved : Nat) :
    step (cfg (some .reverseCertificate) state input output certificate values []
      gateCount index saved) =
      some (cfg (some .inputCount) { state with boolBuffer := none }
        input output certificate values [] gateCount index saved) := by
  verify_step

theorem input_count_arg_step (state : State) (input : List (Option CircuitSym))
    (output certificate values scratch : List Bool) (gateCount index saved : Nat) :
    step (cfg (some .inputCount) state (some .argMark :: input)
      output certificate values scratch (gateCount + 1) index saved) =
      some (cfg (some .inputCount)
        { state with inputBuffer := some (some .argMark), counterPresent := true }
        input output certificate values scratch gateCount index saved) := by
  verify_step

theorem input_count_end_step (state : State) (input : List (Option CircuitSym))
    (output certificate values scratch : List Bool) (index saved : Nat)
    (hvalid : state.validAssignment = true) :
    step (cfg (some .inputCount) state (some .endMark :: input)
      output certificate values scratch 0 index saved) =
      some (cfg (some .gates)
        { state with inputBuffer := some (some .endMark), counterPresent := false }
        input output certificate values scratch 0 index saved) := by
  rcases state with ⟨inputBuffer, boolBuffer, counterPresent, validAssignment⟩
  simp only [State.validAssignment] at hvalid
  subst validAssignment
  verify_step

theorem parse_nat_arg_step (state : State) (ret : Return)
    (input : List (Option CircuitSym)) (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some (.parseNat ret)) state (some .argMark :: input)
      output certificate values scratch gateCount index saved) =
      some (cfg (some (.parseNat ret)) { state with inputBuffer := some (some .argMark) }
        input output certificate values scratch gateCount (index + 1) saved) := by
  cases ret <;> verify_step

theorem parse_nat_end_input_step (state : State) (input : List (Option CircuitSym))
    (output certificate values scratch : List Bool) (gateCount index saved : Nat) :
    step (cfg (some (.parseNat .inputGate)) state (some .endMark :: input)
      output certificate values scratch gateCount index saved) =
      some (cfg (some .certificateLookup)
        { state with inputBuffer := some (some .endMark) }
        input output certificate values scratch gateCount index saved) := by
  verify_step

theorem parse_nat_end_gate_step (state : State) (ret : Return)
    (hinput : ret ≠ .inputGate) (houtput : ret ≠ .outputGate)
    (input : List (Option CircuitSym)) (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some (.parseNat ret)) state (some .endMark :: input)
      output certificate values scratch gateCount index saved) =
      some (cfg (some (.gateSubtract ret))
        { state with inputBuffer := some (some .endMark) }
        input output certificate values scratch gateCount index saved) := by
  cases ret <;> simp_all <;> verify_step

theorem gates_input_step (state : State) (input : List (Option CircuitSym))
    (output certificate values scratch : List Bool) (gateCount index saved : Nat) :
    step (cfg (some .gates) state (some .inputMark :: input)
      output certificate values scratch gateCount index saved) =
      some (cfg (some (.parseNat .inputGate))
        { state with inputBuffer := some (some .inputMark) }
        input output certificate values scratch gateCount index saved) := by
  verify_step

theorem gates_const_step (state : State) (value : Bool)
    (input : List (Option CircuitSym)) (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some .gates) state
      (some (if value then .constTrueMark else .constFalseMark) :: input)
      output certificate values scratch gateCount index saved) =
      some (cfg (some .gates)
        { state with inputBuffer := some (some
            (if value then .constTrueMark else .constFalseMark)) }
        input output certificate (value :: values) scratch (gateCount + 1) index saved) := by
  cases value <;> verify_step

theorem gates_not_step (state : State) (input : List (Option CircuitSym))
    (output certificate values scratch : List Bool) (gateCount index saved : Nat) :
    step (cfg (some .gates) state (some .notMark :: input)
      output certificate values scratch gateCount index saved) =
      some (cfg (some (.parseNat .notGate))
        { state with inputBuffer := some (some .notMark) }
        input output certificate values scratch gateCount index saved) := by
  verify_step

theorem gates_and_step (state : State) (input : List (Option CircuitSym))
    (output certificate values scratch : List Bool) (gateCount index saved : Nat) :
    step (cfg (some .gates) state (some .andMark :: input)
      output certificate values scratch gateCount index saved) =
      some (cfg (some (.parseNat .andLeft))
        { state with inputBuffer := some (some .andMark) }
        input output certificate values scratch gateCount index saved) := by
  verify_step

theorem gates_or_step (state : State) (input : List (Option CircuitSym))
    (output certificate values scratch : List Bool) (gateCount index saved : Nat) :
    step (cfg (some .gates) state (some .orMark :: input)
      output certificate values scratch gateCount index saved) =
      some (cfg (some (.parseNat .orLeft))
        { state with inputBuffer := some (some .orMark) }
        input output certificate values scratch gateCount index saved) := by
  verify_step

theorem gates_output_step (state : State) (input : List (Option CircuitSym))
    (output certificate values scratch : List Bool) (gateCount index saved : Nat) :
    step (cfg (some .gates) state (some .outputMark :: input)
      output certificate values scratch gateCount index saved) =
      some (cfg (some (.parseNat .outputGate))
        { state with inputBuffer := some (some .outputMark) }
        input output certificate values scratch gateCount index saved) := by
  verify_step

theorem parse_nat_end_output_step (state : State) (input : List (Option CircuitSym))
    (output certificate values scratch : List Bool) (gateCount index saved : Nat) :
    step (cfg (some (.parseNat .outputGate)) state (some .endMark :: input)
      output certificate values scratch gateCount index saved) =
      some (cfg (some .checkTrailing)
        { state with inputBuffer := some (some .endMark) }
        input output certificate values scratch gateCount index saved) := by
  verify_step

theorem check_trailing_empty_step (state : State)
    (output certificate values scratch : List Bool) (gateCount index saved : Nat) :
    step (cfg (some .checkTrailing) state [] output certificate values scratch
      gateCount index saved) =
      some (cfg (some (.gateSubtract .outputGate))
        { state with inputBuffer := none }
        [] output certificate values scratch gateCount index saved) := by
  verify_step

theorem certificate_lookup_prefix_step (state : State) (bit : Bool)
    (input : List (Option CircuitSym)) (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some .certificateLookup) state input output (bit :: certificate)
      values scratch gateCount (index + 1) saved) =
      some (cfg (some .certificateLookup)
        { state with boolBuffer := some bit, counterPresent := true }
        input output certificate values (bit :: scratch) gateCount index (saved + 1)) := by
  cases bit <;> verify_step

theorem certificate_lookup_target_step (state : State) (bit : Bool)
    (input : List (Option CircuitSym)) (output certificate values scratch : List Bool)
    (gateCount saved : Nat) :
    step (cfg (some .certificateLookup) state input output (bit :: certificate)
      values scratch gateCount 0 saved) =
      some (cfg (some (.certificateRestore bit))
        { state with boolBuffer := some bit, counterPresent := false }
        input output certificate values (bit :: scratch) gateCount 0 (saved + 1)) := by
  cases bit <;> verify_step

theorem certificate_restore_step (state : State) (value bit : Bool)
    (input : List (Option CircuitSym)) (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some (.certificateRestore value)) state input output certificate values
      (bit :: scratch) gateCount index (saved + 1)) =
      some (cfg (some (.certificateRestore value))
        { state with boolBuffer := some bit, counterPresent := true }
        input output (bit :: certificate) values scratch gateCount index saved) := by
  cases value <;> cases bit <;> verify_step

theorem certificate_restore_done_step (state : State) (value : Bool)
    (input : List (Option CircuitSym)) (output certificate values scratch : List Bool)
    (gateCount index : Nat) :
    step (cfg (some (.certificateRestore value)) state input output certificate values
      scratch gateCount index 0) =
      some (cfg (some .gates) { state with counterPresent := false }
        input output certificate (value :: values) scratch (gateCount + 1) index 0) := by
  cases value <;> verify_step

theorem gate_subtract_step (state : State) (ret : Return)
    (input : List (Option CircuitSym)) (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some (.gateSubtract ret)) state input output certificate values scratch
      (gateCount + 1) (index + 1) saved) =
      some (cfg (some (.gateSubtract ret)) { state with counterPresent := true }
        input output certificate values scratch gateCount index (saved + 1)) := by
  cases ret <;> verify_step

theorem gate_subtract_done_step (state : State) (ret : Return)
    (input : List (Option CircuitSym)) (output certificate values scratch : List Bool)
    (gateCount saved : Nat) :
    step (cfg (some (.gateSubtract ret)) state input output certificate values scratch
      gateCount 0 saved) =
      some (cfg (some (.gateTransferFirst ret)) { state with counterPresent := false }
        input output certificate values scratch gateCount 0 saved) := by
  cases ret <;> verify_step

theorem gate_transfer_first_step (state : State) (ret : Return) (bit : Bool)
    (input : List (Option CircuitSym)) (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some (.gateTransferFirst ret)) state input output certificate (bit :: values)
      scratch (gateCount + 1) index saved) =
      some (cfg (some (.gateTransfer ret bit))
        { state with boolBuffer := some bit, counterPresent := true }
        input output certificate values (bit :: scratch) gateCount (index + 1) saved) := by
  cases ret <;> cases bit <;> verify_step

theorem gate_transfer_step (state : State) (ret : Return) (candidate bit : Bool)
    (input : List (Option CircuitSym)) (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some (.gateTransfer ret candidate)) state input output certificate (bit :: values)
      scratch (gateCount + 1) index saved) =
      some (cfg (some (.gateTransfer ret bit))
        { state with boolBuffer := some bit, counterPresent := true }
        input output certificate values (bit :: scratch) gateCount (index + 1) saved) := by
  cases ret <;> cases candidate <;> cases bit <;> verify_step

theorem gate_transfer_done_step (state : State) (ret : Return) (candidate : Bool)
    (input : List (Option CircuitSym)) (output certificate values scratch : List Bool)
    (index saved : Nat) :
    step (cfg (some (.gateTransfer ret candidate)) state input output certificate values
      scratch 0 index saved) =
      some (cfg (some (.gateRestore ret candidate)) { state with counterPresent := false }
        input output certificate values scratch 0 index saved) := by
  cases ret <;> cases candidate <;> verify_step

theorem gate_restore_step (state : State) (ret : Return) (value bit : Bool)
    (input : List (Option CircuitSym)) (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some (.gateRestore ret value)) state input output certificate values
      (bit :: scratch) gateCount (index + 1) saved) =
      some (cfg (some (.gateRestore ret value))
        { state with boolBuffer := some bit, counterPresent := true }
        input output certificate (bit :: values) scratch (gateCount + 1) index saved) := by
  cases ret <;> cases value <;> cases bit <;> verify_step

theorem gate_restore_done_step (state : State) (ret : Return) (value : Bool)
    (input : List (Option CircuitSym)) (output certificate values scratch : List Bool)
    (gateCount saved : Nat) :
    step (cfg (some (.gateRestore ret value)) state input output certificate values scratch
      gateCount 0 saved) =
      some (cfg (some (.gateRestoreSaved ret value)) { state with counterPresent := false }
        input output certificate values scratch gateCount 0 saved) := by
  cases ret <;> cases value <;> verify_step

theorem gate_restore_saved_step (state : State) (ret : Return) (value : Bool)
    (input : List (Option CircuitSym)) (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some (.gateRestoreSaved ret value)) state input output certificate values scratch
      gateCount index (saved + 1)) =
      some (cfg (some (.gateRestoreSaved ret value)) { state with counterPresent := true }
        input output certificate values scratch (gateCount + 1) index saved) := by
  cases ret <;> cases value <;> verify_step

theorem gate_restore_saved_not_done_step (state : State) (value : Bool)
    (input : List (Option CircuitSym)) (output certificate values scratch : List Bool)
    (gateCount index : Nat) :
    step (cfg (some (.gateRestoreSaved .notGate value)) state input output certificate values
      scratch gateCount index 0) =
      some (cfg (some .gates) { state with counterPresent := false }
        input output certificate ((!value) :: values) scratch (gateCount + 1) index 0) := by
  cases value <;> verify_step

theorem gate_restore_saved_and_left_done_step (state : State) (value : Bool)
    (input : List (Option CircuitSym)) (output certificate values scratch : List Bool)
    (gateCount index : Nat) :
    step (cfg (some (.gateRestoreSaved .andLeft value)) state input output certificate values
      scratch gateCount index 0) =
      some (cfg (some (.parseNat (.andRight value))) { state with counterPresent := false }
        input output certificate values scratch gateCount index 0) := by
  cases value <;> verify_step

theorem gate_restore_saved_and_right_done_step (state : State) (left value : Bool)
    (input : List (Option CircuitSym)) (output certificate values scratch : List Bool)
    (gateCount index : Nat) :
    step (cfg (some (.gateRestoreSaved (.andRight left) value)) state input output certificate values
      scratch gateCount index 0) =
      some (cfg (some .gates) { state with counterPresent := false }
        input output certificate ((left && value) :: values) scratch (gateCount + 1) index 0) := by
  cases left <;> cases value <;> verify_step

theorem gate_restore_saved_or_left_done_step (state : State) (value : Bool)
    (input : List (Option CircuitSym)) (output certificate values scratch : List Bool)
    (gateCount index : Nat) :
    step (cfg (some (.gateRestoreSaved .orLeft value)) state input output certificate values
      scratch gateCount index 0) =
      some (cfg (some (.parseNat (.orRight value))) { state with counterPresent := false }
        input output certificate values scratch gateCount index 0) := by
  cases value <;> verify_step

theorem gate_restore_saved_or_right_done_step (state : State) (left value : Bool)
    (input : List (Option CircuitSym)) (output certificate values scratch : List Bool)
    (gateCount index : Nat) :
    step (cfg (some (.gateRestoreSaved (.orRight left) value)) state input output certificate values
      scratch gateCount index 0) =
      some (cfg (some .gates) { state with counterPresent := false }
        input output certificate ((left || value) :: values) scratch (gateCount + 1) index 0) := by
  cases left <;> cases value <;> verify_step

theorem gate_restore_saved_output_done_step (state : State) (value : Bool)
    (certificate values scratch : List Bool) (gateCount index : Nat) :
    step (cfg (some (.gateRestoreSaved .outputGate value)) state [] [] certificate values
      scratch gateCount index 0) =
      some (cfg (some (.clearInput value)) { state with counterPresent := false }
        [] [] certificate values scratch gateCount index 0) := by
  cases value <;> verify_step

theorem clear_input_step (state : State) (answer : Bool) (head : Option CircuitSym)
    (input : List (Option CircuitSym)) (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some (.clearInput answer)) state (head :: input)
      output certificate values scratch gateCount index saved) =
      some (cfg (some (.clearInput answer)) { state with inputBuffer := some head }
        input output certificate values scratch gateCount index saved) := by
  cases answer <;> cases head <;> try { rename_i symbol; cases symbol } <;> verify_step

theorem clear_input_done_step (state : State) (answer : Bool)
    (output certificate values scratch : List Bool) (gateCount index saved : Nat) :
    step (cfg (some (.clearInput answer)) state []
      output certificate values scratch gateCount index saved) =
      some (cfg (some (.clearCertificate answer)) { state with inputBuffer := none }
        [] output certificate values scratch gateCount index saved) := by
  cases answer <;> verify_step

theorem clear_certificate_step (state : State) (answer bit : Bool)
    (input : List (Option CircuitSym)) (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some (.clearCertificate answer)) state input output (bit :: certificate)
      values scratch gateCount index saved) =
      some (cfg (some (.clearCertificate answer)) { state with boolBuffer := some bit }
        input output certificate values scratch gateCount index saved) := by
  cases answer <;> cases bit <;> verify_step

theorem clear_certificate_done_step (state : State) (answer : Bool)
    (input : List (Option CircuitSym)) (output values scratch : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some (.clearCertificate answer)) state input output [] values scratch
      gateCount index saved) =
      some (cfg (some (.clearValues answer)) { state with boolBuffer := none }
        input output [] values scratch gateCount index saved) := by
  cases answer <;> verify_step

theorem clear_values_step (state : State) (answer bit : Bool)
    (input : List (Option CircuitSym)) (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some (.clearValues answer)) state input output certificate (bit :: values)
      scratch gateCount index saved) =
      some (cfg (some (.clearValues answer)) { state with boolBuffer := some bit }
        input output certificate values scratch gateCount index saved) := by
  cases answer <;> cases bit <;> verify_step

theorem clear_values_done_step (state : State) (answer : Bool)
    (input : List (Option CircuitSym)) (output certificate scratch : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some (.clearValues answer)) state input output certificate [] scratch
      gateCount index saved) =
      some (cfg (some (.clearScratch answer)) { state with boolBuffer := none }
        input output certificate [] scratch gateCount index saved) := by
  cases answer <;> verify_step

theorem clear_scratch_step (state : State) (answer bit : Bool)
    (input : List (Option CircuitSym)) (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some (.clearScratch answer)) state input output certificate values
      (bit :: scratch) gateCount index saved) =
      some (cfg (some (.clearScratch answer)) { state with boolBuffer := some bit }
        input output certificate values scratch gateCount index saved) := by
  cases answer <;> cases bit <;> verify_step

theorem clear_scratch_done_step (state : State) (answer : Bool)
    (input : List (Option CircuitSym)) (output certificate values : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some (.clearScratch answer)) state input output certificate values []
      gateCount index saved) =
      some (cfg (some (.clearGateCount answer)) { state with boolBuffer := none }
        input output certificate values [] gateCount index saved) := by
  cases answer <;> verify_step

theorem clear_gate_count_step (state : State) (answer : Bool)
    (input : List (Option CircuitSym)) (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some (.clearGateCount answer)) state input output certificate values scratch
      (gateCount + 1) index saved) =
      some (cfg (some (.clearGateCount answer)) { state with counterPresent := true }
        input output certificate values scratch gateCount index saved) := by
  cases answer <;> verify_step

theorem clear_gate_count_done_step (state : State) (answer : Bool)
    (input : List (Option CircuitSym)) (output certificate values scratch : List Bool)
    (index saved : Nat) :
    step (cfg (some (.clearGateCount answer)) state input output certificate values scratch
      0 index saved) =
      some (cfg (some (.clearIndex answer)) { state with counterPresent := false }
        input output certificate values scratch 0 index saved) := by
  cases answer <;> verify_step

theorem clear_index_step (state : State) (answer : Bool)
    (input : List (Option CircuitSym)) (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some (.clearIndex answer)) state input output certificate values scratch
      gateCount (index + 1) saved) =
      some (cfg (some (.clearIndex answer)) { state with counterPresent := true }
        input output certificate values scratch gateCount index saved) := by
  cases answer <;> verify_step

theorem clear_index_done_step (state : State) (answer : Bool)
    (input : List (Option CircuitSym)) (output certificate values scratch : List Bool)
    (gateCount saved : Nat) :
    step (cfg (some (.clearIndex answer)) state input output certificate values scratch
      gateCount 0 saved) =
      some (cfg (some (.clearSaved answer)) { state with counterPresent := false }
        input output certificate values scratch gateCount 0 saved) := by
  cases answer <;> verify_step

theorem clear_saved_step (state : State) (answer : Bool)
    (input : List (Option CircuitSym)) (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some (.clearSaved answer)) state input output certificate values scratch
      gateCount index (saved + 1)) =
      some (cfg (some (.clearSaved answer)) { state with counterPresent := true }
        input output certificate values scratch gateCount index saved) := by
  cases answer <;> verify_step

theorem clear_saved_done_step (state : State) (answer : Bool)
    (input : List (Option CircuitSym)) (output certificate values scratch : List Bool)
    (gateCount index : Nat) :
    step (cfg (some (.clearSaved answer)) state input output certificate values scratch
      gateCount index 0) =
      some (cfg (some (.emit answer)) { state with counterPresent := false }
        input output certificate values scratch gateCount index 0) := by
  cases answer <;> verify_step

theorem emit_step (state : State) (answer : Bool) :
    step (cfg (some (.emit answer)) state [] [] [] [] [] 0 0 0) =
      some (cfg (some .done) state [] [answer] [] [] [] 0 0 0) := by
  cases answer <;> verify_step

theorem done_step (state : State) (answer : Bool) :
    step (cfg (some .done) state [] [answer] [] [] [] 0 0 0) =
      some (cfg none initialState [] [answer] [] [] [] 0 0 0) := by
  cases answer <;> verify_step

end CLRS.Chapter34.Turing.GeneralCircuitVerifier

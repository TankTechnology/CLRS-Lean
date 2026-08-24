import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Normalizer.Config

/-!
# Guarded circuit normalizer: one-step contracts

These lemmas expose the nested TM2 statements as ordinary transformations of
the named stacks.  Later proofs do not unfold `program` directly.
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer

attribute [local simp] setInput setNormalized setCounter inputIs hasInput
  hasNormalized hasCounter bufferedNormalized popCounter pushCounter boundStack
  go reject normalizedGateTag gateReturn startGate finishRowPrefix finishOperand
  retainOperandTick finishOperandField

/-- Install one selected bound while leaving the unselected counter explicit. -/
def withBound : Return → Nat → Nat → Nat → Nat × Nat
  | .inputGate, bound, _, gateCount => (bound, gateCount)
  | _, bound, inputCount, _ => (inputCount, bound)

@[simp] theorem withBound_input (bound inputCount gateCount : Nat) :
    withBound .inputGate bound inputCount gateCount = (bound, gateCount) := rfl

def afterRowPrefixLabel : GateKind → Label
  | .input => .parseOperand .inputGate
  | .constFalse | .constTrue => .gates
  | .not => .parseOperand .notGate
  | .and => .parseOperand .andLeft
  | .or => .parseOperand .orLeft

def afterRowPrefixRows (kind : GateKind)
    (rows : List NormalizedCircuitSym) : List NormalizedCircuitSym :=
  match kind with
  | .constFalse | .constTrue => .rowEnd :: normalizedGateTag kind :: rows
  | _ => normalizedGateTag kind :: rows

def afterRowPrefixGateCount (kind : GateKind) (gateCount : Nat) : Nat :=
  match kind with
  | .constFalse | .constTrue => gateCount + 1
  | _ => gateCount

macro "normalize_step" : tactic => `(tactic|
  (apply congrArg some
   apply _root_.Turing.TM2Comp.Cfg_ext
   · simp [step, cfg, machine, program, stackContents, withBound,
       afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
       List.replicate_succ,
       Function.update]
   · simp [step, cfg, machine, program, stackContents, withBound,
       afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
       List.replicate_succ,
       Function.update]
   · funext stack
     cases stack <;>
       simp [step, cfg, machine, program, stackContents, withBound,
         afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
         List.replicate_succ,
         Function.update]))

theorem input_count_arg_step (state : State) (input : List CircuitSym)
    (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some .inputCount) state (.argMark :: input) output rows
      inputCount gateCount operand saved outputIndex) =
      some (cfg (some .inputCount)
        { state with inputBuffer := some .argMark }
        input output rows (inputCount + 1) gateCount operand saved outputIndex) := by
  normalize_step

theorem input_count_end_step (state : State) (input : List CircuitSym)
    (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some .inputCount) state (.endMark :: input) output rows
      inputCount gateCount operand saved outputIndex) =
      some (cfg (some .gates)
        { state with inputBuffer := some .endMark }
        input output rows inputCount gateCount operand saved outputIndex) := by
  normalize_step

theorem row_index_copy_tick_step (state : State) (kind : GateKind)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some (.rowIndexCopy kind)) state input output rows
      inputCount (gateCount + 1) operand saved outputIndex) =
      some (cfg (some (.rowIndexCopy kind))
        { state with counterPresent := true }
        input output (.tick :: rows) inputCount gateCount operand (saved + 1)
        outputIndex) := by
  cases kind <;> normalize_step

theorem row_index_copy_done_step (state : State) (kind : GateKind)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (inputCount operand saved outputIndex : Nat) :
    step (cfg (some (.rowIndexCopy kind)) state input output rows
      inputCount 0 operand saved outputIndex) =
      some (cfg (some (.rowIndexRestore kind))
        { state with counterPresent := false }
        input output (.fieldEnd :: rows) inputCount 0 operand saved outputIndex) := by
  cases kind <;> normalize_step

theorem row_index_restore_tick_step (state : State) (kind : GateKind)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some (.rowIndexRestore kind)) state input output rows
      inputCount gateCount operand (saved + 1) outputIndex) =
      some (cfg (some (.rowIndexRestore kind))
        { state with counterPresent := true }
        input output rows inputCount (gateCount + 1) operand saved outputIndex) := by
  cases kind <;> normalize_step

theorem row_index_restore_done_step (state : State) (kind : GateKind)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand outputIndex : Nat) :
    step (cfg (some (.rowIndexRestore kind)) state input output rows
      inputCount gateCount operand 0 outputIndex) =
      some (cfg (some (afterRowPrefixLabel kind))
        { state with counterPresent := false }
        input output (afterRowPrefixRows kind rows) inputCount
        (afterRowPrefixGateCount kind gateCount) operand 0 outputIndex) := by
  cases kind <;> normalize_step

theorem operand_arg_step (state : State) (ret : Return)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some (.parseOperand ret)) state (.argMark :: input) output rows
      inputCount gateCount operand saved outputIndex) =
      some (cfg (some (.parseOperand ret))
        { state with inputBuffer := some .argMark }
        input output
        (match ret with | .outputGate => rows | _ => .tick :: rows)
        inputCount gateCount (operand + 1) saved
        (match ret with | .outputGate => outputIndex + 1 | _ => outputIndex)) := by
  cases ret <;> normalize_step

theorem operand_end_step (state : State) (ret : Return)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some (.parseOperand ret)) state (.endMark :: input) output rows
      inputCount gateCount operand saved outputIndex) =
      some (cfg
        (some (match ret with
          | .outputGate => .checkTrailing
          | _ => .compareOperand ret))
        { state with inputBuffer := some .endMark }
        input output
        (match ret with | .outputGate => rows | _ => .fieldEnd :: rows)
        inputCount gateCount operand saved outputIndex) := by
  cases ret <;> normalize_step

/-- One comparison tick consumes one operand unit and one selected bound unit. -/
theorem compare_operand_tick_step (state : State) (ret : Return)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (bound inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some (.compareOperand ret)) state input output rows
      (withBound ret (bound + 1) inputCount gateCount).1
      (withBound ret (bound + 1) inputCount gateCount).2
      (operand + 1) saved outputIndex) =
      some (cfg (some (.compareOperand ret))
        { state with counterPresent := true }
        input output rows
        (withBound ret bound inputCount gateCount).1
        (withBound ret bound inputCount gateCount).2
        operand (saved + 1) outputIndex) := by
  cases ret <;> normalize_step

/-- An empty operand plus one remaining bound unit establishes strictness. -/
theorem compare_operand_done_step (state : State) (ret : Return)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (bound inputCount gateCount saved outputIndex : Nat) :
    step (cfg (some (.compareOperand ret)) state input output rows
      (withBound ret (bound + 1) inputCount gateCount).1
      (withBound ret (bound + 1) inputCount gateCount).2
      0 saved outputIndex) =
      some (cfg (some (.restoreBound ret))
        { state with counterPresent := true }
        input output rows
        (withBound ret bound inputCount gateCount).1
        (withBound ret bound inputCount gateCount).2
        0 (saved + 1) outputIndex) := by
  cases ret <;> normalize_step

theorem restore_bound_tick_step (state : State) (ret : Return)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (bound inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some (.restoreBound ret)) state input output rows
      (withBound ret bound inputCount gateCount).1
      (withBound ret bound inputCount gateCount).2
      operand (saved + 1) outputIndex) =
      some (cfg (some (.restoreBound ret))
        { state with counterPresent := true }
        input output rows
        (withBound ret (bound + 1) inputCount gateCount).1
        (withBound ret (bound + 1) inputCount gateCount).2
        operand saved outputIndex) := by
  cases ret <;> normalize_step

theorem clear_input_step (state : State) (head : CircuitSym)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some .clearInput) state (head :: input) output rows
      inputCount gateCount operand saved outputIndex) =
      some (cfg (some .clearInput) { state with inputBuffer := some head }
        input output rows inputCount gateCount operand saved outputIndex) := by
  cases head <;> normalize_step

theorem clear_input_done_step (state : State)
    (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some .clearInput) state [] output rows
      inputCount gateCount operand saved outputIndex) =
      some (cfg (some .clearOutput) { state with inputBuffer := none }
        [] output rows inputCount gateCount operand saved outputIndex) := by
  normalize_step

theorem clear_output_step (state : State) (head : NormalizedCircuitSym)
    (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some .clearOutput) state [] (head :: output) rows
      inputCount gateCount operand saved outputIndex) =
      some (cfg (some .clearOutput) { state with normalizedBuffer := some head }
        [] output rows inputCount gateCount operand saved outputIndex) := by
  cases head <;> normalize_step

theorem clear_output_done_step (state : State) (rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some .clearOutput) state [] [] rows
      inputCount gateCount operand saved outputIndex) =
      some (cfg (some .clearRows) { state with normalizedBuffer := none }
        [] [] rows inputCount gateCount operand saved outputIndex) := by
  normalize_step

theorem clear_rows_step (state : State) (head : NormalizedCircuitSym)
    (rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some .clearRows) state [] [] (head :: rows)
      inputCount gateCount operand saved outputIndex) =
      some (cfg (some .clearRows) { state with normalizedBuffer := some head }
        [] [] rows inputCount gateCount operand saved outputIndex) := by
  cases head <;> normalize_step

theorem clear_rows_done_step (state : State)
    (inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some .clearRows) state [] [] []
      inputCount gateCount operand saved outputIndex) =
      some (cfg (some .clearInputCount) { state with normalizedBuffer := none }
        [] [] [] inputCount gateCount operand saved outputIndex) := by
  normalize_step

theorem clear_input_count_tick_step (state : State)
    (inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some .clearInputCount) state [] [] []
      (inputCount + 1) gateCount operand saved outputIndex) =
      some (cfg (some .clearInputCount) { state with counterPresent := true }
        [] [] [] inputCount gateCount operand saved outputIndex) := by
  normalize_step

theorem clear_input_count_done_step (state : State)
    (gateCount operand saved outputIndex : Nat) :
    step (cfg (some .clearInputCount) state [] [] []
      0 gateCount operand saved outputIndex) =
      some (cfg (some .clearGateCount) { state with counterPresent := false }
        [] [] [] 0 gateCount operand saved outputIndex) := by
  normalize_step

theorem clear_gate_count_tick_step (state : State)
    (gateCount operand saved outputIndex : Nat) :
    step (cfg (some .clearGateCount) state [] [] []
      0 (gateCount + 1) operand saved outputIndex) =
      some (cfg (some .clearGateCount) { state with counterPresent := true }
        [] [] [] 0 gateCount operand saved outputIndex) := by
  normalize_step

theorem clear_gate_count_done_step (state : State)
    (operand saved outputIndex : Nat) :
    step (cfg (some .clearGateCount) state [] [] []
      0 0 operand saved outputIndex) =
      some (cfg (some .clearOperand) { state with counterPresent := false }
        [] [] [] 0 0 operand saved outputIndex) := by
  normalize_step

theorem clear_operand_tick_step (state : State)
    (operand saved outputIndex : Nat) :
    step (cfg (some .clearOperand) state [] [] []
      0 0 (operand + 1) saved outputIndex) =
      some (cfg (some .clearOperand) { state with counterPresent := true }
        [] [] [] 0 0 operand saved outputIndex) := by
  normalize_step

theorem clear_operand_done_step (state : State) (saved outputIndex : Nat) :
    step (cfg (some .clearOperand) state [] [] [] 0 0 0 saved outputIndex) =
      some (cfg (some .clearSaved) { state with counterPresent := false }
        [] [] [] 0 0 0 saved outputIndex) := by
  normalize_step

theorem clear_saved_tick_step (state : State) (saved outputIndex : Nat) :
    step (cfg (some .clearSaved) state [] [] [] 0 0 0 (saved + 1) outputIndex) =
      some (cfg (some .clearSaved) { state with counterPresent := true }
        [] [] [] 0 0 0 saved outputIndex) := by
  normalize_step

theorem clear_saved_done_step (state : State) (outputIndex : Nat) :
    step (cfg (some .clearSaved) state [] [] [] 0 0 0 0 outputIndex) =
      some (cfg (some .clearOutputIndex) { state with counterPresent := false }
        [] [] [] 0 0 0 0 outputIndex) := by
  normalize_step

theorem clear_output_index_tick_step (state : State) (outputIndex : Nat) :
    step (cfg (some .clearOutputIndex) state [] [] [] 0 0 0 0 (outputIndex + 1)) =
      some (cfg (some .clearOutputIndex) { state with counterPresent := true }
        [] [] [] 0 0 0 0 outputIndex) := by
  normalize_step

theorem clear_output_index_done_step (state : State) :
    step (cfg (some .clearOutputIndex) state [] [] [] 0 0 0 0 0) =
      some (cfg (some .emitInvalid) { state with counterPresent := false }
        [] [] [] 0 0 0 0 0) := by
  normalize_step

theorem emit_invalid_step (state : State) :
    step (cfg (some .emitInvalid) state [] [] [] 0 0 0 0 0) =
      some (cfg (some .done) state [] [.invalidMark] [] 0 0 0 0 0) := by
  normalize_step

theorem done_invalid_step (state : State) :
    step (cfg (some .done) state [] [.invalidMark] [] 0 0 0 0 0) =
      some (_root_.Turing.haltList machine [.invalidMark]) := by
  change step (cfg (some .done) state [] [.invalidMark] [] 0 0 0 0 0) = _
  apply congrArg some
  apply _root_.Turing.TM2Comp.Cfg_ext
  · simp [step, cfg, machine, program, stackContents, initialState,
      _root_.Turing.haltList, Function.update]
  · simp [step, cfg, machine, program, stackContents, initialState,
      _root_.Turing.haltList, Function.update]
  · funext stack
    cases stack <;>
      simp [step, cfg, machine, program, stackContents, initialState,
        _root_.Turing.haltList, Function.update]

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer

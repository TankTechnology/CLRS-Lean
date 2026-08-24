import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Emitter.Config

/-! # General-circuit formula emitter: one-step contracts -/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter

attribute [local simp] setInput setCounter inputIs hasInput hasCounter go
  emitFalse afterOffset

macro "emitter_step" : tactic => `(tactic|
  (apply congrArg some
   apply _root_.Turing.TM2Comp.Cfg_ext
   · simp [step, cfg, reverseMachine, program, stackContents,
       List.replicate_succ, Function.update]
   · simp [step, cfg, reverseMachine, program, stackContents,
       List.replicate_succ, Function.update]
   · funext stack
     cases stack <;>
       simp [step, cfg, reverseMachine, program, stackContents,
         List.replicate_succ, Function.update]))

theorem start_invalid_step (state : State) :
    step (cfg (some .start) state [.invalidMark] [] 0 0) =
      some (cfg (some .done) { state with inputBuffer := some .invalidMark }
        [] [.lit false] 0 0) := by
  emitter_step

theorem start_valid_step (state : State) (input : List NormalizedCircuitSym)
    (output : List FormulaSym) (inputCount saved : Nat) :
    step (cfg (some .start) state (.validMark :: input) output inputCount saved) =
      some (cfg (some .expectInputCount)
        { state with inputBuffer := some .validMark }
        input output inputCount saved) := by
  emitter_step

theorem expect_input_count_step (state : State)
    (input : List NormalizedCircuitSym) (output : List FormulaSym)
    (inputCount saved : Nat) :
    step (cfg (some .expectInputCount) state (.inputCountMark :: input) output
      inputCount saved) =
      some (cfg (some .inputCount)
        { state with inputBuffer := some .inputCountMark }
        input output inputCount saved) := by
  emitter_step

theorem input_count_tick_step (state : State)
    (input : List NormalizedCircuitSym) (output : List FormulaSym)
    (inputCount saved : Nat) :
    step (cfg (some .inputCount) state (.tick :: input) output
      inputCount saved) =
      some (cfg (some .inputCount) { state with inputBuffer := some .tick }
        input output (inputCount + 1) saved) := by
  emitter_step

theorem input_count_end_step (state : State)
    (input : List NormalizedCircuitSym) (output : List FormulaSym)
    (inputCount saved : Nat) :
    step (cfg (some .inputCount) state (.fieldEnd :: input) output
      inputCount saved) =
      some (cfg (some .expectOutput)
        { state with inputBuffer := some .fieldEnd }
        input (.varMark :: .andMark :: output) inputCount saved) := by
  emitter_step

theorem expect_output_step (state : State)
    (input : List NormalizedCircuitSym) (output : List FormulaSym)
    (inputCount saved : Nat) :
    step (cfg (some .expectOutput) state (.outputIndexMark :: input) output
      inputCount saved) =
      some (cfg (some (.copyPrefix .output))
        { state with inputBuffer := some .outputIndexMark }
        input output inputCount saved) := by
  emitter_step

theorem copy_prefix_tick_step (state : State) (ret : OffsetReturn)
    (input : List NormalizedCircuitSym) (output : List FormulaSym)
    (inputCount saved : Nat) :
    step (cfg (some (.copyPrefix ret)) state input output
      (inputCount + 1) saved) =
      some (cfg (some (.copyPrefix ret))
        { state with counterPresent := true }
        input (.endMark :: output) inputCount (saved + 1)) := by
  emitter_step

theorem copy_prefix_empty_step (state : State) (ret : OffsetReturn)
    (input : List NormalizedCircuitSym) (output : List FormulaSym)
    (saved : Nat) :
    step (cfg (some (.copyPrefix ret)) state input output 0 saved) =
      some (cfg (some (.restorePrefix ret))
        { state with counterPresent := false }
        input output 0 saved) := by
  emitter_step

theorem restore_prefix_tick_step (state : State) (ret : OffsetReturn)
    (input : List NormalizedCircuitSym) (output : List FormulaSym)
    (inputCount saved : Nat) :
    step (cfg (some (.restorePrefix ret)) state input output
      inputCount (saved + 1)) =
      some (cfg (some (.restorePrefix ret))
        { state with counterPresent := true }
        input output (inputCount + 1) saved) := by
  emitter_step

theorem restore_prefix_empty_step (state : State) (ret : OffsetReturn)
    (input : List NormalizedCircuitSym) (output : List FormulaSym)
    (inputCount : Nat) :
    step (cfg (some (.restorePrefix ret)) state input output inputCount 0) =
      some (cfg (some (.parseOffset ret))
        { state with counterPresent := false }
        input output inputCount 0) := by
  emitter_step

theorem parse_offset_tick_step (state : State) (ret : OffsetReturn)
    (input : List NormalizedCircuitSym) (output : List FormulaSym)
    (inputCount saved : Nat) :
    step (cfg (some (.parseOffset ret)) state (.tick :: input) output
      inputCount saved) =
      some (cfg (some (.parseOffset ret))
        { state with inputBuffer := some .tick }
        input (.endMark :: output) inputCount saved) := by
  emitter_step

def afterOffsetLabel : OffsetReturn → Label
  | .output => .expectGateCount
  | .row => .gateTag
  | .notSource | .andRight | .orRight => .expectRowEnd
  | .andLeft => .copyPrefix .andRight
  | .orLeft => .copyPrefix .orRight

def afterOffsetOutput (ret : OffsetReturn) (output : List FormulaSym) :
    List FormulaSym :=
  match ret with
  | .andLeft | .orLeft => .varMark :: .endMark :: output
  | _ => .endMark :: output

theorem parse_offset_end_step (state : State) (ret : OffsetReturn)
    (input : List NormalizedCircuitSym) (output : List FormulaSym)
    (inputCount saved : Nat) :
    step (cfg (some (.parseOffset ret)) state (.fieldEnd :: input) output
      inputCount saved) =
      some (cfg (some (afterOffsetLabel ret))
        { state with inputBuffer := some .fieldEnd }
        input (afterOffsetOutput ret output) inputCount saved) := by
  cases ret <;> simp [afterOffsetLabel, afterOffsetOutput] <;> emitter_step

theorem expect_gate_count_step (state : State)
    (input : List NormalizedCircuitSym) (output : List FormulaSym)
    (inputCount saved : Nat) :
    step (cfg (some .expectGateCount) state (.gateCountMark :: input) output
      inputCount saved) =
      some (cfg (some .gateCount)
        { state with inputBuffer := some .gateCountMark }
        input output inputCount saved) := by
  emitter_step

theorem gate_count_tick_step (state : State)
    (input : List NormalizedCircuitSym) (output : List FormulaSym)
    (inputCount saved : Nat) :
    step (cfg (some .gateCount) state (.tick :: input) output
      inputCount saved) =
      some (cfg (some .gateCount) { state with inputBuffer := some .tick }
        input output inputCount saved) := by
  emitter_step

theorem gate_count_end_step (state : State)
    (input : List NormalizedCircuitSym) (output : List FormulaSym)
    (inputCount saved : Nat) :
    step (cfg (some .gateCount) state (.fieldEnd :: input) output
      inputCount saved) =
      some (cfg (some .rows) { state with inputBuffer := some .fieldEnd }
        input output inputCount saved) := by
  emitter_step

theorem rows_gate_step (state : State)
    (input : List NormalizedCircuitSym) (output : List FormulaSym)
    (inputCount saved : Nat) :
    step (cfg (some .rows) state (.gateRowMark :: input) output
      inputCount saved) =
      some (cfg (some (.copyPrefix .row))
        { state with inputBuffer := some .gateRowMark }
        input (.varMark :: .iffMark :: .andMark :: output) inputCount saved) := by
  emitter_step

theorem rows_empty_step (state : State) (output : List FormulaSym)
    (inputCount saved : Nat) :
    step (cfg (some .rows) state [] output inputCount saved) =
      some (cfg (some .clearInputCount) { state with inputBuffer := none }
        [] (.lit true :: output) inputCount saved) := by
  emitter_step

theorem gate_tag_input_step (state : State)
    (input : List NormalizedCircuitSym) (output : List FormulaSym)
    (inputCount saved : Nat) :
    step (cfg (some .gateTag) state (.inputGateMark :: input) output
      inputCount saved) =
      some (cfg (some .parseInputOperand)
        { state with inputBuffer := some .inputGateMark }
        input (.varMark :: output) inputCount saved) := by
  emitter_step

theorem gate_tag_const_false_step (state : State)
    (input : List NormalizedCircuitSym) (output : List FormulaSym)
    (inputCount saved : Nat) :
    step (cfg (some .gateTag) state (.constFalseMark :: input) output
      inputCount saved) =
      some (cfg (some .expectRowEnd)
        { state with inputBuffer := some .constFalseMark }
        input (.lit false :: output) inputCount saved) := by
  emitter_step

theorem gate_tag_const_true_step (state : State)
    (input : List NormalizedCircuitSym) (output : List FormulaSym)
    (inputCount saved : Nat) :
    step (cfg (some .gateTag) state (.constTrueMark :: input) output
      inputCount saved) =
      some (cfg (some .expectRowEnd)
        { state with inputBuffer := some .constTrueMark }
        input (.lit true :: output) inputCount saved) := by
  emitter_step

theorem gate_tag_not_step (state : State)
    (input : List NormalizedCircuitSym) (output : List FormulaSym)
    (inputCount saved : Nat) :
    step (cfg (some .gateTag) state (.notGateMark :: input) output
      inputCount saved) =
      some (cfg (some (.copyPrefix .notSource))
        { state with inputBuffer := some .notGateMark }
        input (.varMark :: .notMark :: output) inputCount saved) := by
  emitter_step

theorem gate_tag_and_step (state : State)
    (input : List NormalizedCircuitSym) (output : List FormulaSym)
    (inputCount saved : Nat) :
    step (cfg (some .gateTag) state (.andGateMark :: input) output
      inputCount saved) =
      some (cfg (some (.copyPrefix .andLeft))
        { state with inputBuffer := some .andGateMark }
        input (.varMark :: .andMark :: output) inputCount saved) := by
  emitter_step

theorem gate_tag_or_step (state : State)
    (input : List NormalizedCircuitSym) (output : List FormulaSym)
    (inputCount saved : Nat) :
    step (cfg (some .gateTag) state (.orGateMark :: input) output
      inputCount saved) =
      some (cfg (some (.copyPrefix .orLeft))
        { state with inputBuffer := some .orGateMark }
        input (.varMark :: .orMark :: output) inputCount saved) := by
  emitter_step

theorem input_operand_tick_step (state : State)
    (input : List NormalizedCircuitSym) (output : List FormulaSym)
    (inputCount saved : Nat) :
    step (cfg (some .parseInputOperand) state (.tick :: input) output
      inputCount saved) =
      some (cfg (some .parseInputOperand)
        { state with inputBuffer := some .tick }
        input (.endMark :: output) inputCount saved) := by
  emitter_step

theorem input_operand_end_step (state : State)
    (input : List NormalizedCircuitSym) (output : List FormulaSym)
    (inputCount saved : Nat) :
    step (cfg (some .parseInputOperand) state (.fieldEnd :: input) output
      inputCount saved) =
      some (cfg (some .expectRowEnd)
        { state with inputBuffer := some .fieldEnd }
        input (.endMark :: output) inputCount saved) := by
  emitter_step

theorem row_end_step (state : State) (input : List NormalizedCircuitSym)
    (output : List FormulaSym) (inputCount saved : Nat) :
    step (cfg (some .expectRowEnd) state (.rowEnd :: input) output
      inputCount saved) =
      some (cfg (some .rows) { state with inputBuffer := some .rowEnd }
        input output inputCount saved) := by
  emitter_step

theorem clear_input_count_tick_step (state : State) (output : List FormulaSym)
    (inputCount saved : Nat) :
    step (cfg (some .clearInputCount) state [] output (inputCount + 1) saved) =
      some (cfg (some .clearInputCount)
        { state with counterPresent := true }
        [] output inputCount saved) := by
  emitter_step

theorem clear_input_count_empty_step (state : State)
    (output : List FormulaSym) :
    step (cfg (some .clearInputCount) state [] output 0 0) =
      some (cfg (some .done) { state with counterPresent := false }
        [] output 0 0) := by
  emitter_step

theorem done_step (state : State) (output : List FormulaSym) :
    step (cfg (some .done) state [] output 0 0) =
      some (_root_.Turing.haltList reverseMachine output) := by
  apply congrArg some
  apply _root_.Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext stack
    cases stack <;>
      simp [step, cfg, reverseMachine, program, stackContents, initialState,
        _root_.Turing.haltList, Function.update]

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter

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

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter

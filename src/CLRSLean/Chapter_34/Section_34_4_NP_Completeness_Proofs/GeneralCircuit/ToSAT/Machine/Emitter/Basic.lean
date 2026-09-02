import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Emitter.Semantics
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Tactic.DeriveFintype

/-!
# General-circuit formula emitter: concrete machine

The machine consumes the two canonical record shapes produced by the guarded
normalizer.  It emits the desired prefix stream in reverse; the public machine
later composes it with the verified generic reversal controller.
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter

open Computability
open _root_.Turing

inductive Stack
  | input | output | inputCount | saved
deriving DecidableEq, Fintype, Inhabited

abbrev Alphabet : Stack → Type
  | .input => NormalizedCircuitSym
  | .output => FormulaSym
  | .inputCount | .saved => Unit

/-- Continuations of the shared `inputCount + offset` variable emitter. -/
inductive OffsetReturn
  | output | row | notSource | andLeft | andRight | orLeft | orRight
deriving DecidableEq, Fintype, Inhabited

inductive Label
  | start | expectInputCount | inputCount | expectOutput
  | copyPrefix (ret : OffsetReturn)
  | restorePrefix (ret : OffsetReturn)
  | parseOffset (ret : OffsetReturn)
  | expectGateCount | gateCount | rows | gateTag
  | parseInputOperand | expectRowEnd | clearInputCount | done
deriving DecidableEq, Fintype, Inhabited

structure State where
  inputBuffer : Option NormalizedCircuitSym
  counterPresent : Bool
deriving DecidableEq, Fintype, Inhabited

def initialState : State :=
  { inputBuffer := none, counterPresent := false }

def setInput (state : State) (symbol : Option NormalizedCircuitSym) : State :=
  { state with inputBuffer := symbol }

def setCounter (state : State) (symbol : Option Unit) : State :=
  { state with counterPresent := symbol.isSome }

def inputIs (symbol : NormalizedCircuitSym) (state : State) : Bool :=
  decide (state.inputBuffer = some symbol)

def hasInput (state : State) : Bool := state.inputBuffer.isSome
def hasCounter (state : State) : Bool := state.counterPresent

abbrev Stmt := TM2.Stmt Alphabet Label State

def go (label : Label) : Stmt := .goto fun _ => label

def emitFalse : Stmt :=
  .push .output (fun _ => .lit false) <| go .done

/-- Continue after the unary offset terminator emitted the mandatory final
`endMark` of a variable encoding. -/
def afterOffset : OffsetReturn → Stmt
  | .output => go .expectGateCount
  | .row => go .gateTag
  | .notSource | .andRight | .orRight => go .expectRowEnd
  | .andLeft =>
      .push .output (fun _ => .varMark) <| go (.copyPrefix .andRight)
  | .orLeft =>
      .push .output (fun _ => .varMark) <| go (.copyPrefix .orRight)

def program : Label → Stmt
  | .start =>
      .pop .input setInput <|
        .branch (inputIs .invalidMark) emitFalse <|
          .branch (inputIs .validMark) (go .expectInputCount) emitFalse
  | .expectInputCount =>
      .pop .input setInput <|
        .branch (inputIs .inputCountMark) (go .inputCount) emitFalse
  | .inputCount =>
      .pop .input setInput <|
        .branch (inputIs .tick)
          (.push .inputCount (fun _ => ()) <| go .inputCount) <|
        .branch (inputIs .fieldEnd)
          (.push .output (fun _ => .andMark) <|
            .push .output (fun _ => .varMark) <| go .expectOutput)
          emitFalse
  | .expectOutput =>
      .pop .input setInput <|
        .branch (inputIs .outputIndexMark) (go (.copyPrefix .output)) emitFalse
  | .copyPrefix ret =>
      .pop .inputCount setCounter <|
        .branch hasCounter
          (.push .output (fun _ => .endMark) <|
            .push .saved (fun _ => ()) <| go (.copyPrefix ret))
          (go (.restorePrefix ret))
  | .restorePrefix ret =>
      .pop .saved setCounter <|
        .branch hasCounter
          (.push .inputCount (fun _ => ()) <| go (.restorePrefix ret))
          (go (.parseOffset ret))
  | .parseOffset ret =>
      .pop .input setInput <|
        .branch (inputIs .tick)
          (.push .output (fun _ => .endMark) <| go (.parseOffset ret)) <|
        .branch (inputIs .fieldEnd)
          (.push .output (fun _ => .endMark) <| afterOffset ret)
          emitFalse
  | .expectGateCount =>
      .pop .input setInput <|
        .branch (inputIs .gateCountMark) (go .gateCount) emitFalse
  | .gateCount =>
      .pop .input setInput <|
        .branch (inputIs .tick) (go .gateCount) <|
          .branch (inputIs .fieldEnd) (go .rows) emitFalse
  | .rows =>
      .pop .input setInput <|
        .branch hasInput
          (.branch (inputIs .gateRowMark)
            (.push .output (fun _ => .andMark) <|
              .push .output (fun _ => .iffMark) <|
                .push .output (fun _ => .varMark) <|
                  go (.copyPrefix .row))
            emitFalse)
          (.push .output (fun _ => .lit true) <| go .clearInputCount)
  | .gateTag =>
      .pop .input setInput <|
        .branch (inputIs .inputGateMark)
          (.push .output (fun _ => .varMark) <| go .parseInputOperand) <|
        .branch (inputIs .constFalseMark)
          (.push .output (fun _ => .lit false) <| go .expectRowEnd) <|
        .branch (inputIs .constTrueMark)
          (.push .output (fun _ => .lit true) <| go .expectRowEnd) <|
        .branch (inputIs .notGateMark)
          (.push .output (fun _ => .notMark) <|
            .push .output (fun _ => .varMark) <|
              go (.copyPrefix .notSource)) <|
        .branch (inputIs .andGateMark)
          (.push .output (fun _ => .andMark) <|
            .push .output (fun _ => .varMark) <|
              go (.copyPrefix .andLeft)) <|
        .branch (inputIs .orGateMark)
          (.push .output (fun _ => .orMark) <|
            .push .output (fun _ => .varMark) <|
              go (.copyPrefix .orLeft))
          emitFalse
  | .parseInputOperand =>
      .pop .input setInput <|
        .branch (inputIs .tick)
          (.push .output (fun _ => .endMark) <| go .parseInputOperand) <|
        .branch (inputIs .fieldEnd)
          (.push .output (fun _ => .endMark) <| go .expectRowEnd)
          emitFalse
  | .expectRowEnd =>
      .pop .input setInput <|
        .branch (inputIs .rowEnd) (go .rows) emitFalse
  | .clearInputCount =>
      .pop .inputCount setCounter <|
        .branch hasCounter (go .clearInputCount) (go .done)
  | .done => .load (fun _ => initialState) .halt

abbrev reverseMachine : FinTM2 :=
  @FinTM2.mk Stack (by infer_instance) (by infer_instance)
    .input .output Alphabet Label .start
    (by infer_instance) State initialState (by infer_instance) (by infer_instance)
    program

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter

import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.InternalEncoding
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Tactic.DeriveFintype

/-!
# Guarded circuit normalizer: concrete machine

This fixed TM2 reads the raw unary circuit syntax.  Successful gate rows are
staged in reverse on `rows`; unbounded counts and operands live only on unary
`Unit` stacks.  Finite control stores tags and pop buffers, never a natural
number.  Every failed parse or strict-bound check enters one cleanup path.
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer

open Computability
open _root_.Turing

/-- Typed stacks of the guarded normalizer. -/
inductive Stack
  | input | output | rows
  | inputCount | gateCount | operand | saved | outputIndex
deriving DecidableEq, Fintype, Inhabited

/-- Each unbounded numeric work area is genuinely unary. -/
abbrev Alphabet : Stack → Type
  | .input => CircuitSym
  | .output | .rows => NormalizedCircuitSym
  | .inputCount | .gateCount | .operand | .saved | .outputIndex => Unit

/-- Finite gate tags retained while the chronological index is copied. -/
inductive GateKind
  | input | constFalse | constTrue | not | and | or
deriving DecidableEq, Fintype, Inhabited

/-- Continuations of the shared unary operand and bound-check pipeline. -/
inductive Return
  | inputGate | notGate | andLeft | andRight | orLeft | orRight | outputGate
deriving DecidableEq, Fintype, Inhabited

/-- The counter against which an operand must be strictly bounded. -/
inductive Bound
  | inputCount | gateCount
deriving DecidableEq, Fintype, Inhabited

/-- Finite-control labels. -/
inductive Label
  | inputCount | gates
  | rowIndexCopy (kind : GateKind) | rowIndexRestore (kind : GateKind)
  | parseOperand (ret : Return) | checkTrailing
  | compareOperand (ret : Return) | restoreBound (ret : Return)
  | rowsToOutput | emitGateCount | emitOutputIndex | emitInputCount
  | clearInput | clearOutput | clearRows | clearInputCount | clearGateCount
  | clearOperand | clearSaved | clearOutputIndex | emitInvalid
  | done
deriving DecidableEq, Fintype, Inhabited

/-- The three typed pop buffers used by the program. -/
structure State where
  inputBuffer : Option CircuitSym
  normalizedBuffer : Option NormalizedCircuitSym
  counterPresent : Bool
deriving DecidableEq, Fintype, Inhabited

/-- Reset state used initially and at the unique halt instruction. -/
def initialState : State :=
  { inputBuffer := none, normalizedBuffer := none, counterPresent := false }

def setInput (state : State) (symbol : Option CircuitSym) : State :=
  { state with inputBuffer := symbol }

def setNormalized (state : State) (symbol : Option NormalizedCircuitSym) : State :=
  { state with normalizedBuffer := symbol }

def setCounter (state : State) (symbol : Option Unit) : State :=
  { state with counterPresent := symbol.isSome }

def inputIs (symbol : CircuitSym) (state : State) : Bool :=
  decide (state.inputBuffer = some symbol)

def hasInput (state : State) : Bool := state.inputBuffer.isSome
def hasNormalized (state : State) : Bool := state.normalizedBuffer.isSome
def hasCounter (state : State) : Bool := state.counterPresent

def bufferedNormalized (state : State) : NormalizedCircuitSym :=
  state.normalizedBuffer.getD .invalidMark

abbrev Stmt := TM2.Stmt Alphabet Label State

/-- Statically selected unary counters. -/
inductive CounterStack
  | inputCount | gateCount | operand | saved | outputIndex

def popCounter (source : CounterStack) (next : Stmt) : Stmt :=
  match source with
  | .inputCount => .pop .inputCount setCounter next
  | .gateCount => .pop .gateCount setCounter next
  | .operand => .pop .operand setCounter next
  | .saved => .pop .saved setCounter next
  | .outputIndex => .pop .outputIndex setCounter next

def pushCounter (target : CounterStack) (next : Stmt) : Stmt :=
  match target with
  | .inputCount => .push .inputCount (fun _ => ()) next
  | .gateCount => .push .gateCount (fun _ => ()) next
  | .operand => .push .operand (fun _ => ()) next
  | .saved => .push .saved (fun _ => ()) next
  | .outputIndex => .push .outputIndex (fun _ => ()) next

def boundStack : Return → CounterStack
  | .inputGate => .inputCount
  | .notGate | .andLeft | .andRight | .orLeft | .orRight | .outputGate =>
      .gateCount

def go (label : Label) : Stmt := .goto fun _ => label
def reject : Stmt := go .clearInput

def normalizedGateTag : GateKind → NormalizedCircuitSym
  | .input => .inputGateMark
  | .constFalse => .constFalseMark
  | .constTrue => .constTrueMark
  | .not => .notGateMark
  | .and => .andGateMark
  | .or => .orGateMark

def gateReturn : GateKind → Option Return
  | .input => some .inputGate
  | .constFalse | .constTrue => none
  | .not => some .notGate
  | .and => some .andLeft
  | .or => some .orLeft

/-- Begin one indexed row after its raw tag has been consumed. -/
def startGate (kind : GateKind) : Stmt :=
  .push .rows (fun _ => .gateRowMark) <| go (.rowIndexCopy kind)

/-- Append the tag after the chronological unary index has been restored. -/
def finishRowPrefix (kind : GateKind) : Stmt :=
  .push .rows (fun _ => normalizedGateTag kind) <|
    match gateReturn kind with
    | some ret => go (.parseOperand ret)
    | none =>
        .push .rows (fun _ => .rowEnd) <|
          .push .gateCount (fun _ => ()) <| go .gates

/-- Continue after a successful strict operand bound check. -/
def finishOperand : Return → Stmt
  | .andLeft => go (.parseOperand .andRight)
  | .orLeft => go (.parseOperand .orRight)
  | .outputGate => go .rowsToOutput
  | .inputGate | .notGate | .andRight | .orRight =>
      .push .rows (fun _ => .rowEnd) <|
        .push .gateCount (fun _ => ()) <| go .gates

/-- Parse one raw unary tick, retaining it wherever the continuation needs it. -/
def retainOperandTick : Return → Stmt
  | .outputGate =>
      .push .operand (fun _ => ()) <|
        .push .outputIndex (fun _ => ()) <| go (.parseOperand .outputGate)
  | ret =>
      .push .operand (fun _ => ()) <|
        .push .rows (fun _ => .tick) <| go (.parseOperand ret)

/-- Finish one raw unary operand field. -/
def finishOperandField : Return → Stmt
  | .outputGate => go .checkTrailing
  | ret =>
      .push .rows (fun _ => .fieldEnd) <| go (.compareOperand ret)

/-- Concrete normalizer program. -/
def program : Label → Stmt
  | .inputCount =>
      .pop .input setInput <|
        .branch (inputIs .argMark)
          (.push .inputCount (fun _ => ()) <| go .inputCount)
          (.branch (inputIs .endMark) (go .gates) reject)
  | .gates =>
      .pop .input setInput <|
        .branch (inputIs .inputMark) (startGate .input) <|
        .branch (inputIs .constFalseMark) (startGate .constFalse) <|
        .branch (inputIs .constTrueMark) (startGate .constTrue) <|
        .branch (inputIs .notMark) (startGate .not) <|
        .branch (inputIs .andMark) (startGate .and) <|
        .branch (inputIs .orMark) (startGate .or) <|
        .branch (inputIs .outputMark) (go (.parseOperand .outputGate)) reject
  | .rowIndexCopy kind =>
      .pop .gateCount setCounter <|
        .branch hasCounter
          (.push .rows (fun _ => .tick) <|
            .push .saved (fun _ => ()) <| go (.rowIndexCopy kind))
          (.push .rows (fun _ => .fieldEnd) <| go (.rowIndexRestore kind))
  | .rowIndexRestore kind =>
      .pop .saved setCounter <|
        .branch hasCounter
          (.push .gateCount (fun _ => ()) <| go (.rowIndexRestore kind))
          (finishRowPrefix kind)
  | .parseOperand ret =>
      .pop .input setInput <|
        .branch (inputIs .argMark) (retainOperandTick ret)
          (.branch (inputIs .endMark) (finishOperandField ret) reject)
  | .checkTrailing =>
      .pop .input setInput <|
        .branch hasInput reject (go (.compareOperand .outputGate))
  | .compareOperand ret =>
      .pop .operand setCounter <|
        .branch hasCounter
          (popCounter (boundStack ret) <|
            .branch hasCounter
              (.push .saved (fun _ => ()) <| go (.compareOperand ret))
              reject)
          (popCounter (boundStack ret) <|
            .branch hasCounter
              (.push .saved (fun _ => ()) <| go (.restoreBound ret))
              reject)
  | .restoreBound ret =>
      .pop .saved setCounter <|
        .branch hasCounter
          (pushCounter (boundStack ret) <| go (.restoreBound ret))
          (finishOperand ret)
  | .rowsToOutput =>
      .pop .rows setNormalized <|
        .branch hasNormalized
          (.push .output bufferedNormalized <| go .rowsToOutput)
          (.push .output (fun _ => .fieldEnd) <| go .emitGateCount)
  | .emitGateCount =>
      .pop .gateCount setCounter <|
        .branch hasCounter
          (.push .output (fun _ => .tick) <| go .emitGateCount)
          (.push .output (fun _ => .gateCountMark) <|
            .push .output (fun _ => .fieldEnd) <| go .emitOutputIndex)
  | .emitOutputIndex =>
      .pop .outputIndex setCounter <|
        .branch hasCounter
          (.push .output (fun _ => .tick) <| go .emitOutputIndex)
          (.push .output (fun _ => .outputIndexMark) <|
            .push .output (fun _ => .fieldEnd) <| go .emitInputCount)
  | .emitInputCount =>
      .pop .inputCount setCounter <|
        .branch hasCounter
          (.push .output (fun _ => .tick) <| go .emitInputCount)
          (.push .output (fun _ => .inputCountMark) <|
            .push .output (fun _ => .validMark) <| go .done)
  | .clearInput =>
      .pop .input setInput <|
        .branch hasInput (go .clearInput) (go .clearOutput)
  | .clearOutput =>
      .pop .output setNormalized <|
        .branch hasNormalized (go .clearOutput) (go .clearRows)
  | .clearRows =>
      .pop .rows setNormalized <|
        .branch hasNormalized (go .clearRows) (go .clearInputCount)
  | .clearInputCount =>
      .pop .inputCount setCounter <|
        .branch hasCounter (go .clearInputCount) (go .clearGateCount)
  | .clearGateCount =>
      .pop .gateCount setCounter <|
        .branch hasCounter (go .clearGateCount) (go .clearOperand)
  | .clearOperand =>
      .pop .operand setCounter <|
        .branch hasCounter (go .clearOperand) (go .clearSaved)
  | .clearSaved =>
      .pop .saved setCounter <|
        .branch hasCounter (go .clearSaved) (go .clearOutputIndex)
  | .clearOutputIndex =>
      .pop .outputIndex setCounter <|
        .branch hasCounter (go .clearOutputIndex) (go .emitInvalid)
  | .emitInvalid =>
      .push .output (fun _ => .invalidMark) <| go .done
  | .done => .load (fun _ => initialState) .halt

/-- The concrete finite TM2. -/
abbrev machine : FinTM2 :=
  @FinTM2.mk Stack (by infer_instance) (by infer_instance)
    .input .output Alphabet Label .inputCount
    (by infer_instance) State initialState (by infer_instance) (by infer_instance) program

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer

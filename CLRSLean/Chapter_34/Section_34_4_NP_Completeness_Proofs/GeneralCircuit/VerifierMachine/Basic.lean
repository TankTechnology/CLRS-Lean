import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.Verification
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Tactic.DeriveFintype

/-!
# Concrete TM2 for the general-circuit verifier: machine definition

The machine reads `pairEncoding certificate input`.  It keeps the canonical
certificate, the reverse list of already-computed gate values, and a lookup
scratch stack separate.  Gate and certificate indices are unary counters.
Every rejecting branch enters the same total cleanup path and emits `[false]`.
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitVerifier

open Computability
open _root_.Turing

/-- Typed stacks used by the concrete verifier. -/
inductive Stack
  | input | output | certificate | values | scratch
  | gateCount | index | saved
deriving DecidableEq, Fintype, Inhabited

/-- Each work area carries only the data it represents. -/
abbrev Alphabet : Stack → Type
  | .input => Option CircuitSym
  | .output | .certificate | .values | .scratch => Bool
  | .gateCount | .index | .saved => Unit

/-- What to do after a unary index has been parsed and looked up. -/
inductive Return
  | inputGate | notGate | andLeft | andRight (left : Bool)
  | orLeft | orRight (left : Bool) | outputGate
deriving DecidableEq, Fintype, Inhabited

/-- Finite-control labels for parsing, lookup/restore, and total cleanup. -/
inductive Label
  | scanCertificate | reverseCertificate | inputCount | gates
  | parseNat (ret : Return)
  | checkTrailing
  | certificateLookup
  | certificateRestore (value : Bool)
  | gateSubtract (ret : Return)
  | gateTransferFirst (ret : Return)
  | gateTransfer (ret : Return) (candidate : Bool)
  | gateRestore (ret : Return) (value : Bool)
  | gateRestoreSaved (ret : Return) (value : Bool)
  | clearInput (answer : Bool)
  | clearCertificate (answer : Bool)
  | clearValues (answer : Bool)
  | clearScratch (answer : Bool)
  | clearGateCount (answer : Bool)
  | clearIndex (answer : Bool)
  | clearSaved (answer : Bool)
  | emit (answer : Bool) | done
deriving DecidableEq, Fintype, Inhabited

/-- The two typed pop buffers and the unary-counter emptiness flag. -/
structure State where
  inputBuffer : Option (Option CircuitSym)
  boolBuffer : Option Bool
  counterPresent : Bool
  validAssignment : Bool
deriving DecidableEq, Fintype, Inhabited

/-- Reset state used both initially and by the final halting statement. -/
def initialState : State :=
  { inputBuffer := none, boolBuffer := none, counterPresent := false,
    validAssignment := true }

def setInput (state : State) (symbol : Option (Option CircuitSym)) : State :=
  { state with inputBuffer := symbol }

def setBool (state : State) (value : Option Bool) : State :=
  { state with boolBuffer := value }

def setCounter (state : State) (value : Option Unit) : State :=
  { state with counterPresent := value.isSome }

def inputIs (symbol : Option CircuitSym) (state : State) : Bool :=
  match symbol, state.inputBuffer with
  | none, some none => true
  | some .inputMark, some (some .inputMark)
  | some .constFalseMark, some (some .constFalseMark)
  | some .constTrueMark, some (some .constTrueMark)
  | some .notMark, some (some .notMark)
  | some .andMark, some (some .andMark)
  | some .orMark, some (some .orMark)
  | some .outputMark, some (some .outputMark)
  | some .argMark, some (some .argMark)
  | some .endMark, some (some .endMark) => true
  | _, _ => false

def hasInput (state : State) : Bool := state.inputBuffer.isSome
def hasBool (state : State) : Bool := state.boolBuffer.isSome
def hasCounter (state : State) : Bool := state.counterPresent
def bufferedBool (state : State) : Bool := state.boolBuffer.getD false
def hasEncodedSymbol (state : State) : Bool :=
  match state.inputBuffer with
  | some (some _) => true
  | _ => false

def bufferedAssignmentValue (state : State) : Bool :=
  match state.inputBuffer with
  | some (some symbol) => assignmentSymbolValue symbol
  | _ => false

def noteAssignmentSymbol (state : State) : State :=
  match state.inputBuffer with
  | some (some symbol) =>
      { state with validAssignment := state.validAssignment && isAssignmentSymbol symbol }
  | _ => state

abbrev Stmt := TM2.Stmt Alphabet Label State

inductive BoolStack
  | certificate | values | scratch

def popBool (source : BoolStack) (next : Stmt) : Stmt :=
  match source with
  | .certificate => .pop .certificate setBool next
  | .values => .pop .values setBool next
  | .scratch => .pop .scratch setBool next

def pushBool (target : BoolStack) (next : Stmt) : Stmt :=
  match target with
  | .certificate => .push .certificate bufferedBool next
  | .values => .push .values bufferedBool next
  | .scratch => .push .scratch bufferedBool next

def go (label : Label) : Stmt := .goto fun _ => label
def reject : Stmt := go (.clearInput false)

/-- Push a newly computed gate value and advance the gate-count counter. -/
def finishGate (value : Bool) : Stmt :=
  .push .values (fun _ => value) <|
    .push .gateCount (fun _ => ()) <|
      go .gates

/-- Dispatch the result of an exact predecessor lookup. -/
def finishLookup (ret : Return) (value : Bool) : Stmt :=
  match ret with
  | .inputGate => finishGate value
  | .notGate => finishGate (!value)
  | .andLeft => go (.parseNat (.andRight value))
  | .andRight left => finishGate (left && value)
  | .orLeft => go (.parseNat (.orRight value))
  | .orRight left => finishGate (left || value)
  | .outputGate => go (.clearInput value)

/-- Pop a Boolean stack into the buffer, rejecting an impossible underflow. -/
def moveBufferedBool (source target : BoolStack) (next : State → Label) : Stmt :=
  popBool source <|
    .branch hasBool
      (pushBool target <| .goto next)
      reject

/-- The concrete verifier program. -/
def program : Label → Stmt
  | .scanCertificate =>
      .pop .input setInput <|
        .branch hasEncodedSymbol
          (.load noteAssignmentSymbol <|
            .push .scratch bufferedAssignmentValue <|
              .push .gateCount (fun _ => ()) <| go .scanCertificate)
          (.branch (inputIs none) (go .reverseCertificate) reject)
  | .reverseCertificate =>
      .pop .scratch setBool <|
        .branch hasBool
          (.push .certificate bufferedBool <| go .reverseCertificate)
          (go .inputCount)
  | .inputCount =>
      .pop .input setInput <|
        .branch (inputIs (some .argMark))
          (.pop .gateCount setCounter <|
            .branch hasCounter (go .inputCount) reject)
          (.branch (inputIs (some .endMark))
            (.pop .gateCount setCounter <|
              .branch hasCounter reject <|
                .branch (fun state => state.validAssignment) (go .gates) reject)
            reject)
  | .gates =>
      .pop .input setInput <|
        .branch (inputIs (some .inputMark)) (go (.parseNat .inputGate)) <|
        .branch (inputIs (some .constFalseMark)) (finishGate false) <|
        .branch (inputIs (some .constTrueMark)) (finishGate true) <|
        .branch (inputIs (some .notMark)) (go (.parseNat .notGate)) <|
        .branch (inputIs (some .andMark)) (go (.parseNat .andLeft)) <|
        .branch (inputIs (some .orMark)) (go (.parseNat .orLeft)) <|
        .branch (inputIs (some .outputMark)) (go (.parseNat .outputGate)) reject
  | .parseNat ret =>
      .pop .input setInput <|
        .branch (inputIs (some .argMark))
          (.push .index (fun _ => ()) <| go (.parseNat ret))
          (.branch (inputIs (some .endMark))
            (match ret with
             | .inputGate => go .certificateLookup
             | .outputGate => go .checkTrailing
             | _ => go (.gateSubtract ret))
            reject)
  | .checkTrailing =>
      .pop .input setInput <|
        .branch hasInput reject (go (.gateSubtract .outputGate))
  | .certificateLookup =>
      .pop .index setCounter <|
        .branch hasCounter
          (.pop .certificate setBool <|
            .branch hasBool
              (.push .scratch bufferedBool <|
                .push .saved (fun _ => ()) <| go .certificateLookup)
              reject)
          (.pop .certificate setBool <|
            .branch hasBool
              (.push .scratch bufferedBool <|
                .push .saved (fun _ => ()) <|
                  .goto fun state => .certificateRestore (bufferedBool state))
              reject)
  | .certificateRestore value =>
      .pop .saved setCounter <|
        .branch hasCounter
          (moveBufferedBool .scratch .certificate fun _ => .certificateRestore value)
          (finishLookup .inputGate value)
  | .gateSubtract ret =>
      .pop .index setCounter <|
        .branch hasCounter
          (.pop .gateCount setCounter <|
            .branch hasCounter
              (.push .saved (fun _ => ()) <| go (.gateSubtract ret))
              reject)
          (go (.gateTransferFirst ret))
  | .gateTransferFirst ret =>
      .pop .gateCount setCounter <|
        .branch hasCounter
          (.pop .values setBool <|
            .branch hasBool
              (.push .scratch bufferedBool <|
                .push .index (fun _ => ()) <|
                  .goto fun state => .gateTransfer ret (bufferedBool state))
              reject)
          reject
  | .gateTransfer ret candidate =>
      .pop .gateCount setCounter <|
        .branch hasCounter
          (.pop .values setBool <|
            .branch hasBool
              (.push .scratch bufferedBool <|
                .push .index (fun _ => ()) <|
                  .goto fun state => .gateTransfer ret (bufferedBool state))
              reject)
          (go (.gateRestore ret candidate))
  | .gateRestore ret value =>
      .pop .index setCounter <|
        .branch hasCounter
          (.pop .scratch setBool <|
            .branch hasBool
              (.push .values bufferedBool <|
                .push .gateCount (fun _ => ()) <| go (.gateRestore ret value))
              reject)
          (go (.gateRestoreSaved ret value))
  | .gateRestoreSaved ret value =>
      .pop .saved setCounter <|
        .branch hasCounter
          (.push .gateCount (fun _ => ()) <| go (.gateRestoreSaved ret value))
          (finishLookup ret value)
  | .clearInput answer =>
      .pop .input setInput <|
        .branch hasInput (go (.clearInput answer)) (go (.clearCertificate answer))
  | .clearCertificate answer =>
      .pop .certificate setBool <|
        .branch hasBool (go (.clearCertificate answer)) (go (.clearValues answer))
  | .clearValues answer =>
      .pop .values setBool <|
        .branch hasBool (go (.clearValues answer)) (go (.clearScratch answer))
  | .clearScratch answer =>
      .pop .scratch setBool <|
        .branch hasBool (go (.clearScratch answer)) (go (.clearGateCount answer))
  | .clearGateCount answer =>
      .pop .gateCount setCounter <|
        .branch hasCounter (go (.clearGateCount answer)) (go (.clearIndex answer))
  | .clearIndex answer =>
      .pop .index setCounter <|
        .branch hasCounter (go (.clearIndex answer)) (go (.clearSaved answer))
  | .clearSaved answer =>
      .pop .saved setCounter <|
        .branch hasCounter (go (.clearSaved answer)) (go (.emit answer))
  | .emit answer => .push .output (fun _ => answer) <| go .done
  | .done => .load (fun _ => initialState) .halt

/-- The concrete finite TM2. -/
abbrev machine : FinTM2 :=
  @FinTM2.mk Stack (by infer_instance) (by infer_instance)
    .input .output Alphabet Label .scanCertificate
    (by infer_instance) State initialState (by infer_instance) (by infer_instance) program

/-- Concrete stack family used by the phase specifications. -/
abbrev stackContents (input : List (Option CircuitSym))
    (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) : ∀ stack : Stack, List (Alphabet stack)
  | .input => input
  | .output => output
  | .certificate => certificate
  | .values => values
  | .scratch => scratch
  | .gateCount => List.replicate gateCount ()
  | .index => List.replicate index ()
  | .saved => List.replicate saved ()

/-- Named constructor for configurations appearing in phase lemmas. -/
def cfg (label : Option Label) (state : State)
    (input : List (Option CircuitSym))
    (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) : machine.Cfg :=
  ⟨label, state, stackContents input output certificate values scratch gateCount index saved⟩

/-- Short name for the verifier transition function. -/
def step : machine.Cfg → Option machine.Cfg := machine.step

end CLRS.Chapter34.Turing.GeneralCircuitVerifier

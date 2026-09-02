import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.Incidence.Scanner.Runtime
import Mathlib.Tactic.DeriveFintype

/-!
# HAM-CYCLE incidence-chain formatter: core controller

The scanner emits one row of `(occurrence, side)` pairs per source vertex.
This controller retains the preceding pair in finite control plus a unary
counter and emits the normalized gadget edge joining it to the next pair.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Chain

open PolyBuilder
open HamiltonianCycleReduction

/-- Canonical incidence-chain edge stream for one source instance. -/
def chainEdgeStream (I : VertexCoverInstance) : List CliqueSym :=
  (allIncidenceChainEdges I).flatMap encodeCliqueEdge

/-- Exact local offset of an incident gadget vertex. -/
def incidentOffset (side : Bool) (position : Nat) : Nat :=
  (if side then 6 else 0) + position

@[simp] theorem incidentVertex_eq (ref : IncidentOccurrence) (position : Nat) :
    incidentVertex ref position =
      12 * ref.occurrence + incidentOffset ref.rightSide position := by
  simp [incidentVertex, globalWidgetVertex, widgetVertex, widgetVertexCount,
    incidentOffset]

/-- Fixed phases of the streaming chain-edge formatter. -/
inductive Label
  | beginRow | firstOccurrence | incPrevious | firstSide | firstSideEnd
  | nextOccurrence (previousSide : Bool)
  | incCurrent (previousSide : Bool)
  | currentSide (previousSide : Bool)
  | currentSideEnd (previousSide : Bool)
  | emitMark (previousSide currentSide : Bool)
  | emitLeft (previousSide currentSide : Bool)
  | leftTicks (previousSide currentSide : Bool) (remaining : Fin 12)
  | leftOffset (currentSide : Bool) (remaining : Fin 11)
  | emitPairSeparator (currentSide : Bool)
  | emitRight (currentSide : Bool)
  | restoreCurrent (currentSide : Bool)
  | rightTicks (currentSide : Bool) (remaining : Fin 12)
  | rightOffset (remaining : Fin 6)
  | emitRecordEnd (currentSide : Bool)
  | clearPrevious | finish | invalid
deriving DecidableEq, Fintype

def predFin {n : Nat} (value : Fin (n + 1))
    (_hpositive : value.val ≠ 0) : Fin (n + 1) :=
  ⟨value.val - 1, by omega⟩

def leftTicksStart (previousSide currentSide : Bool) : Label :=
  .leftTicks previousSide currentSide ⟨11, by omega⟩

def leftOffsetStart (previousSide currentSide : Bool) : Label :=
  if previousSide then
    .leftOffset currentSide ⟨10, by omega⟩
  else
    .leftOffset currentSide ⟨4, by omega⟩

def rightTicksStart (currentSide : Bool) : Label :=
  .rightTicks currentSide ⟨11, by omega⟩

def rightOffsetStart : Label :=
  .rightOffset ⟨5, by omega⟩

/-- The fixed prepend-order formatter.  Counter one holds the previous
occurrence and counter two the current occurrence. -/
def program : Program UnaryFrameSym CliqueSym where
  Label := Label
  main := .beginRow
  op
    | .beginRow => .popInput .finish fun
        | .frameEnd => .beginRow
        | .tick => .incPrevious
        | .separator => .firstSide
    | .firstOccurrence => .popInput .invalid fun
        | .tick => .incPrevious
        | .separator => .firstSide
        | .frameEnd => .invalid
    | .incPrevious => .inc₁ .firstOccurrence
    | .firstSide => .popInput .invalid fun
        | .tick => .firstSideEnd
        | .separator => .nextOccurrence false
        | .frameEnd => .invalid
    | .firstSideEnd => .popInput .invalid fun
        | .separator => .nextOccurrence true
        | _ => .invalid
    | .nextOccurrence previousSide => .popInput .invalid fun
        | .frameEnd => .clearPrevious
        | .tick => .incCurrent previousSide
        | .separator => .currentSide previousSide
    | .incCurrent previousSide => .inc₂ (.nextOccurrence previousSide)
    | .currentSide previousSide => .popInput .invalid fun
        | .tick => .currentSideEnd previousSide
        | .separator => .emitMark previousSide false
        | .frameEnd => .invalid
    | .currentSideEnd previousSide => .popInput .invalid fun
        | .separator => .emitMark previousSide true
        | _ => .invalid
    | .emitMark previousSide currentSide =>
        .pushOutput .edgeMark (.emitLeft previousSide currentSide)
    | .emitLeft previousSide currentSide =>
        .dec₁ (leftOffsetStart previousSide currentSide)
          (leftTicksStart previousSide currentSide)
    | .leftTicks previousSide currentSide remaining =>
        .pushOutput .tick
          (if hzero : remaining.val = 0 then
            .emitLeft previousSide currentSide
          else
            .leftTicks previousSide currentSide (predFin remaining hzero))
    | .leftOffset currentSide remaining =>
        .pushOutput .tick
          (if hzero : remaining.val = 0 then
            .emitPairSeparator currentSide
          else
            .leftOffset currentSide (predFin remaining hzero))
    | .emitPairSeparator currentSide =>
        .pushOutput .pairSep (.emitRight currentSide)
    | .emitRight currentSide =>
        .dec₂
          (if currentSide then rightOffsetStart else .emitRecordEnd false)
          (.restoreCurrent currentSide)
    | .restoreCurrent currentSide =>
        .inc₁ (rightTicksStart currentSide)
    | .rightTicks currentSide remaining =>
        .pushOutput .tick
          (if hzero : remaining.val = 0 then
            .emitRight currentSide
          else
            .rightTicks currentSide (predFin remaining hzero))
    | .rightOffset remaining =>
        .pushOutput .tick
          (if hzero : remaining.val = 0 then
            .emitRecordEnd true
          else
            .rightOffset (predFin remaining hzero))
    | .emitRecordEnd currentSide =>
        .pushOutput .recordEnd (.nextOccurrence currentSide)
    | .clearPrevious => .dec₁ .beginRow .clearPrevious
    | .finish => .halt
    | .invalid => .halt

/-- Proof-facing formatter configuration. -/
def cfg (label : Label) (buffer : Option UnaryFrameSym) (test : Bool)
    (input : List UnaryFrameSym) (output : List CliqueSym)
    (previous current : List Unit) : BuilderCfg program where
  label := some label
  buffer₁ := buffer
  buffer₂ := none
  test := test
  input := input
  output := output
  work₁ := []
  work₂ := []
  counter₁ := previous
  counter₂ := current
  counter₃ := []

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Chain

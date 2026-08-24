import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.Incidence.Scanner.Runtime
import Mathlib.Tactic.DeriveFintype

/-!
# HAM-CYCLE selector endpoints: incidence-row endpoint extractor

This fixed controller retains the first and latest occurrence of each
nonempty incidence row.  At the row boundary it emits the two gadget ports
used by the selector-edge formatter.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Endpoints

open PolyBuilder
open HamiltonianCycleReduction

/-- The first and last gadget ports of one nonempty incidence row. -/
def endpointValues : List IncidentOccurrence → List Nat
  | [] => []
  | first :: rest =>
      [incidentVertex first 0,
        incidentVertex ((first :: rest).getLast (by simp)) 5]

/-- Cell-marked endpoint stream consumed by the affine row copier. -/
def endpointCellStream (I : VertexCoverInstance) : List UnaryFrameSym :=
  (List.range I.vertexCount).flatMap fun u =>
    (endpointValues (incidentOccurrences I u)).flatMap fun endpoint =>
      encodeUnaryFrame [endpoint] ++ [.frameEnd]

/-- Fixed phases of the first/last endpoint extractor. -/
inductive Label
  | beginRow
  | incFirstOne | incFirstTwo | firstOccurrence
  | firstSide | firstSideEnd
  | nextOccurrence (firstSide lastSide : Bool)
  | clearLast (firstSide : Bool) (beganWithTick : Bool)
  | incLast (firstSide : Bool)
  | currentOccurrence (firstSide : Bool)
  | currentSide (firstSide : Bool)
  | currentSideEnd (firstSide : Bool)
  | emitFirst (firstSide lastSide : Bool)
  | firstTicks (firstSide lastSide : Bool) (remaining : Fin 12)
  | firstOffset (lastSide : Bool) (remaining : Fin 6)
  | firstSeparator (lastSide : Bool)
  | firstBoundary (lastSide : Bool)
  | emitLast (lastSide : Bool)
  | lastTicks (lastSide : Bool) (remaining : Fin 12)
  | lastOffset (remaining : Fin 11)
  | lastSeparator | lastBoundary
  | finish | invalid
deriving DecidableEq, Fintype

def predFin {n : Nat} (value : Fin (n + 1))
    (_hpositive : value.val ≠ 0) : Fin (n + 1) :=
  ⟨value.val - 1, by omega⟩

def firstTicksStart (firstSide lastSide : Bool) : Label :=
  .firstTicks firstSide lastSide ⟨11, by omega⟩

def firstOffsetStart (lastSide : Bool) : Label :=
  .firstOffset lastSide ⟨5, by omega⟩

def lastTicksStart (lastSide : Bool) : Label :=
  .lastTicks lastSide ⟨11, by omega⟩

def lastOffsetStart : Label :=
  .lastOffset ⟨10, by omega⟩

/-- Prepend-order fixed endpoint extractor. -/
def program : Program UnaryFrameSym UnaryFrameSym where
  Label := Label
  main := .beginRow
  op
    | .beginRow => .popInput .finish fun
        | .frameEnd => .beginRow
        | .tick => .incFirstOne
        | .separator => .firstSide
    | .incFirstOne => .inc₁ .incFirstTwo
    | .incFirstTwo => .inc₂ .firstOccurrence
    | .firstOccurrence => .popInput .invalid fun
        | .tick => .incFirstOne
        | .separator => .firstSide
        | .frameEnd => .invalid
    | .firstSide => .popInput .invalid fun
        | .tick => .firstSideEnd
        | .separator => .nextOccurrence false false
        | .frameEnd => .invalid
    | .firstSideEnd => .popInput .invalid fun
        | .separator => .nextOccurrence true true
        | _ => .invalid
    | .nextOccurrence firstSide lastSide => .popInput .invalid fun
        | .frameEnd => .emitFirst firstSide lastSide
        | .tick => .clearLast firstSide true
        | .separator => .clearLast firstSide false
    | .clearLast firstSide beganWithTick =>
        .dec₂
          (if beganWithTick then .incLast firstSide else .currentSide firstSide)
          (.clearLast firstSide beganWithTick)
    | .incLast firstSide => .inc₂ (.currentOccurrence firstSide)
    | .currentOccurrence firstSide => .popInput .invalid fun
        | .tick => .incLast firstSide
        | .separator => .currentSide firstSide
        | .frameEnd => .invalid
    | .currentSide firstSide => .popInput .invalid fun
        | .tick => .currentSideEnd firstSide
        | .separator => .nextOccurrence firstSide false
        | .frameEnd => .invalid
    | .currentSideEnd firstSide => .popInput .invalid fun
        | .separator => .nextOccurrence firstSide true
        | _ => .invalid
    | .emitFirst firstSide lastSide =>
        .dec₁
          (if firstSide then firstOffsetStart lastSide
            else .firstSeparator lastSide)
          (firstTicksStart firstSide lastSide)
    | .firstTicks firstSide lastSide remaining =>
        .pushOutput .tick
          (if hzero : remaining.val = 0 then .emitFirst firstSide lastSide
            else .firstTicks firstSide lastSide (predFin remaining hzero))
    | .firstOffset lastSide remaining =>
        .pushOutput .tick
          (if hzero : remaining.val = 0 then .firstSeparator lastSide
            else .firstOffset lastSide (predFin remaining hzero))
    | .firstSeparator lastSide => .pushOutput .separator (.firstBoundary lastSide)
    | .firstBoundary lastSide => .pushOutput .frameEnd (.emitLast lastSide)
    | .emitLast lastSide =>
        .dec₂
          (if lastSide then lastOffsetStart else .lastOffset ⟨4, by omega⟩)
          (lastTicksStart lastSide)
    | .lastTicks lastSide remaining =>
        .pushOutput .tick
          (if hzero : remaining.val = 0 then .emitLast lastSide
            else .lastTicks lastSide (predFin remaining hzero))
    | .lastOffset remaining =>
        .pushOutput .tick
          (if hzero : remaining.val = 0 then .lastSeparator
            else .lastOffset (predFin remaining hzero))
    | .lastSeparator => .pushOutput .separator .lastBoundary
    | .lastBoundary => .pushOutput .frameEnd .beginRow
    | .finish => .halt
    | .invalid => .halt

/-- Proof-facing endpoint-extractor configuration. -/
def cfg (label : Label) (buffer : Option UnaryFrameSym) (test : Bool)
    (input output : List UnaryFrameSym) (first last : List Unit) :
    BuilderCfg program where
  label := some label
  buffer₁ := buffer
  buffer₂ := none
  test := test
  input := input
  output := output
  work₁ := []
  work₂ := []
  counter₁ := first
  counter₂ := last
  counter₃ := []

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Endpoints

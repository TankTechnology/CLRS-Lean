import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Certificate.Basic
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import Mathlib.Tactic.DeriveFintype

/-!
# HAM-CYCLE consecutive-pair generator

The controller stores the first, previous, and current certificate vertices in
three unary counters.  It emits every path edge and finally the closing edge,
in reverse physical order; the standard verified reversal machine restores
the public canonical stream.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.HamiltonianCycle.VerifierMachine.CyclePairs

open PolyBuilder

/-- Ordered path pairs beginning with a previously loaded vertex. -/
def pathPairsFrom : Nat → List Nat → List (Nat × Nat)
  | _, [] => []
  | previous, current :: rest =>
      (previous, current) :: pathPairsFrom current rest

/-- Path pairs plus the closing last-to-first pair. -/
def cyclePairs : List Nat → List (Nat × Nat)
  | [] => []
  | first :: rest =>
      pathPairsFrom first rest ++ [(CliqueInstance.lastFrom first rest, first)]

/-- Canonical physical serialization of the cycle query family. -/
def encodeCyclePairs (vertices : List Nat) : List CliqueSym :=
  (cyclePairs vertices).flatMap encodeCliqueEdge

/-- Finite control of the reverse-output consecutive-pair generator. -/
inductive Label
  | start
  | firstRecord
  | loadFirst
  | saveFirst
  | savePrevious
  | nextRecord
  | loadCurrent
  | saveCurrent
  | pushEdgeMark
  | previous
  | pushPreviousTick
  | pushPairSeparator
  | current
  | pushCurrentTick
  | restoreCurrent
  | pushRecordEnd
  | closeEdgeMark
  | closingLast
  | pushClosingLastTick
  | pushClosingSeparator
  | closingFirst
  | pushClosingFirstTick
  | pushClosingEnd
  | drain
  | halt
deriving DecidableEq, Fintype

/-- Fixed three-counter reverse-output program. -/
def revProgram : Program CliqueSym CliqueSym where
  Label := Label
  main := .start
  op
    | .start => .popInput .halt fun
        | .certificateMark => .firstRecord
        | _ => .drain
    | .firstRecord => .popInput .halt fun
        | .vertexMark => .loadFirst
        | _ => .drain
    | .loadFirst => .popInput .drain fun
        | .tick => .saveFirst
        | .recordEnd => .nextRecord
        | _ => .drain
    | .saveFirst => .inc₁ .savePrevious
    | .savePrevious => .inc₂ .loadFirst
    | .nextRecord => .popInput .closeEdgeMark fun
        | .vertexMark => .loadCurrent
        | _ => .drain
    | .loadCurrent => .popInput .drain fun
        | .tick => .saveCurrent
        | .recordEnd => .pushEdgeMark
        | _ => .drain
    | .saveCurrent => .inc₃ .loadCurrent
    | .pushEdgeMark => .pushOutput .edgeMark .previous
    | .previous => .dec₂ .pushPairSeparator .pushPreviousTick
    | .pushPreviousTick => .pushOutput .tick .previous
    | .pushPairSeparator => .pushOutput .pairSep .current
    | .current => .dec₃ .pushRecordEnd .pushCurrentTick
    | .pushCurrentTick => .pushOutput .tick .restoreCurrent
    | .restoreCurrent => .inc₂ .current
    | .pushRecordEnd => .pushOutput .recordEnd .nextRecord
    | .closeEdgeMark => .pushOutput .edgeMark .closingLast
    | .closingLast => .dec₂ .pushClosingSeparator .pushClosingLastTick
    | .pushClosingLastTick => .pushOutput .tick .closingLast
    | .pushClosingSeparator => .pushOutput .pairSep .closingFirst
    | .closingFirst => .dec₁ .pushClosingEnd .pushClosingFirstTick
    | .pushClosingFirstTick => .pushOutput .tick .closingFirst
    | .pushClosingEnd => .pushOutput .recordEnd .halt
    | .drain => .popInput .halt fun _ => .drain
    | .halt => .halt

/-- Proof-facing controller configuration. -/
def cfg (label : Label) (buffer : Option CliqueSym) (test : Bool)
    (input output : List CliqueSym) (first previous current : List Unit) :
    BuilderCfg revProgram where
  label := some label
  buffer₁ := buffer
  buffer₂ := none
  test := test
  input := input
  output := output
  work₁ := []
  work₂ := []
  counter₁ := first
  counter₂ := previous
  counter₃ := current

end CLRS.Chapter34.Turing.HamiltonianCycle.VerifierMachine.CyclePairs

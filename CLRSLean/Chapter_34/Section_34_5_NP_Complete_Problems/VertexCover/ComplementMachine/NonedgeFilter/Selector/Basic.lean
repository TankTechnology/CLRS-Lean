import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.NonedgeFilter.FilterInput
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Machine
import Mathlib.Tactic.DeriveFintype

/-!
# VERTEX-COVER complement machine: nonedge selector controller

The left half of the input is moved to a work stack.  Because that half was
reversed by `filterInput`, the stack then exposes candidate records in their
original order.  A `true` answer discards one record; a `false` answer copies
one record to the prepend-only output stack.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.VertexCover.ComplementMachine.NonedgeFilter.Selector

open PolyBuilder
open NonedgeFilter

/-- Pointwise selection semantics; `true` means that the source edge exists
and must therefore be omitted from the complement. -/
def selectedEdges : List (Nat × Nat) → List Bool → List (Nat × Nat)
  | edge :: edges, bit :: bits =>
      if bit then selectedEdges edges bits
      else edge :: selectedEdges edges bits
  | _, _ => []

def selectedStream (edges : List (Nat × Nat)) (bits : List Bool) :
    List CliqueSym :=
  (selectedEdges edges bits).flatMap encodeCliqueEdge

def selectedReverseStream (edges : List (Nat × Nat)) (bits : List Bool) :
    List CliqueSym :=
  (selectedStream edges bits).reverse

/-- Typed input encoder consumed by the fixed selector. -/
def inputEncoding (pair : List (Nat × Nat) × List Bool) :
    List (Option CliqueSym) :=
  pairEncoding ((pair.1.flatMap encodeCliqueEdge).reverse)
    (pair.2.map bitSymbol)

inductive Label
  | load | dropSeparator | nextBit | select (bit : Bool)
  | copy | copyPush (symbol : CliqueSym)
  | discard | finish | invalid | halt
deriving DecidableEq, Fintype

def program : Program (Option CliqueSym) CliqueSym where
  Label := Label
  main := .load
  op
    | .load => .moveInputWork₁ .invalid fun
        | none => .dropSeparator
        | some _ => .load
    | .dropSeparator => .popWork₁ .invalid fun
        | none => .nextBit
        | some _ => .invalid
    | .nextBit => .popInput .finish fun
        | some .instanceMark => .select true
        | some .certificateMark => .select false
        | _ => .invalid
    | .select bit => .jump (if bit then .discard else .copy)
    | .copy => .popWork₁ .invalid fun
        | some symbol => .copyPush symbol
        | none => .invalid
    | .copyPush symbol => .pushOutput symbol
        (if symbol = .recordEnd then .nextBit else .copy)
    | .discard => .popWork₁ .invalid fun
        | some .recordEnd => .nextBit
        | some _ => .discard
        | none => .invalid
    | .finish => .halt
    | .invalid => .halt
    | .halt => .halt

def cfg (label : Label)
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool)
    (input : List (Option CliqueSym)) (output : List CliqueSym)
    (work₁ work₂ : List (Option CliqueSym)) : BuilderCfg program where
  label := some label
  buffer₁ := buffer₁
  buffer₂ := buffer₂
  test := test
  input := input
  output := output
  work₁ := work₁
  work₂ := work₂
  counter₁ := []
  counter₂ := []
  counter₃ := []

end CLRS.Chapter34.Turing.VertexCover.ComplementMachine.NonedgeFilter.Selector

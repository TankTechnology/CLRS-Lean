import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.RawReduction
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.NonedgeFilter.FilterInput
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Machine
import Mathlib.Tactic.DeriveFintype

/-!
# VERTEX-COVER complement machine: final guarded selector

The paired input contains one Boolean tag and a candidate complement encoding.
The true branch copies the candidate; the false branch emits the fixed
VERTEX-COVER no-instance used by the total raw reduction.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.VertexCover.ComplementMachine.GuardSelector

open PolyBuilder
open NonedgeFilter

def inputEncoding (input : Bool × List CliqueSym) : List (Option CliqueSym) :=
  pairEncoding [bitSymbol input.1] input.2

def selectedOutput (input : Bool × List CliqueSym) : List CliqueSym :=
  if input.1 then input.2
  else encodeCliqueInstance canonicalVertexCoverNoInstance

inductive Label
  | start | dropSeparator (accept : Bool)
  | load | copy | copyPush (symbol : CliqueSym)
  | clear | fallbackRecordEnd | fallbackEndpointTick
  | fallbackPairSeparator | fallbackEdgeMark
  | fallbackRightFieldSeparator | fallbackLeftFieldSeparator
  | fallbackSecondVertexTick | fallbackFirstVertexTick
  | fallbackInstanceMark | invalid | halt
deriving DecidableEq, Fintype

def program : Program (Option CliqueSym) CliqueSym where
  Label := Label
  main := .start
  op
    | .start => .popInput .invalid fun
        | some .instanceMark => .dropSeparator true
        | some .certificateMark => .dropSeparator false
        | _ => .invalid
    | .dropSeparator accept => .popInput .invalid fun
        | none => if accept then .load else .clear
        | some _ => .invalid
    | .load => .moveInputWork₁ .copy fun _ => .load
    | .copy => .popWork₁ .halt fun
        | some symbol => .copyPush symbol
        | none => .invalid
    | .copyPush symbol => .pushOutput symbol .copy
    | .clear => .popInput .fallbackRecordEnd fun _ => .clear
    | .fallbackRecordEnd => .pushOutput .recordEnd .fallbackEndpointTick
    | .fallbackEndpointTick => .pushOutput .tick .fallbackPairSeparator
    | .fallbackPairSeparator => .pushOutput .pairSep .fallbackEdgeMark
    | .fallbackEdgeMark => .pushOutput .edgeMark .fallbackRightFieldSeparator
    | .fallbackRightFieldSeparator =>
        .pushOutput .fieldSep .fallbackLeftFieldSeparator
    | .fallbackLeftFieldSeparator =>
        .pushOutput .fieldSep .fallbackSecondVertexTick
    | .fallbackSecondVertexTick =>
        .pushOutput .tick .fallbackFirstVertexTick
    | .fallbackFirstVertexTick => .pushOutput .tick .fallbackInstanceMark
    | .fallbackInstanceMark => .pushOutput .instanceMark .halt
    | .invalid => .halt
    | .halt => .halt

def cfg (label : Label) (buffer : Option (Option CliqueSym)) (test : Bool)
    (input : List (Option CliqueSym)) (output : List CliqueSym)
    (work : List (Option CliqueSym)) : BuilderCfg program where
  label := some label
  buffer₁ := buffer
  buffer₂ := none
  test := test
  input := input
  output := output
  work₁ := work
  work₂ := []
  counter₁ := []
  counter₂ := []
  counter₃ := []

end CLRS.Chapter34.Turing.VertexCover.ComplementMachine.GuardSelector

import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.Encoding
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.StatefulFlatMap

/-! # Guarded TSP output selector: pure controller -/

namespace CLRS.Chapter34.Turing.TSPReduction.RawSelector

open PolyBuilder

def guardSymbol : Bool → TSPSym
  | true => .instanceMark
  | false => .certificateMark

/-- A guard tag, one physical separator, and a candidate TSP word. -/
def inputEncoding (input : Bool × List TSPSym) : List (Option TSPSym) :=
  pairEncoding [guardSymbol input.1] input.2

/-- Accepting guards copy the candidate; rejecting guards emit the fixed
rejected word `[]`. -/
def selectedOutput (input : Bool × List TSPSym) : List TSPSym :=
  if input.1 then input.2 else []

inductive Mode
  | start
  | separator (accept : Bool)
  | payload (accept : Bool)
  | invalid
deriving DecidableEq, Fintype

def spec : StatefulFlatMapSpec Mode (Option TSPSym) TSPSym where
  initial := .start
  action mode symbol :=
    match mode with
    | .start =>
        match symbol with
        | some .instanceMark => ([], .separator true)
        | some .certificateMark => ([], .separator false)
        | _ => ([], .invalid)
    | .separator accept =>
        match symbol with
        | none => ([], .payload accept)
        | some _ => ([], .invalid)
    | .payload accept =>
        match symbol with
        | some value => if accept then ([value], .payload accept)
          else ([], .payload accept)
        | none => ([], .invalid)
    | .invalid => ([], .invalid)
  finish _ := []

def stream (input : List (Option TSPSym)) : List TSPSym :=
  rewriteStatefulFlatMap spec input

end CLRS.Chapter34.Turing.TSPReduction.RawSelector

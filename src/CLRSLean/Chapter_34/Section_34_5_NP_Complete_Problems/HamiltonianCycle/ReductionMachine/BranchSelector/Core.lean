import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.Branch
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.StatefulFlatMap
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.NonedgeFilter.FilterInput

/-!
# VERTEX-COVER to HAM-CYCLE: three-way output selector
-/

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.BranchSelector

open HamiltonianCycleReduction
open PolyBuilder
open VertexCover.ComplementMachine.NonedgeFilter

/-- A branch tag, a separator, and the ordinary candidate stream. -/
def inputEncoding (input : Branch × List CliqueSym) : List (Option CliqueSym) :=
  pairEncoding [input.1.symbol] input.2

/-- The total typed target encoding selected by the branch tag. -/
def selectedOutput (input : Branch × List CliqueSym) : List CliqueSym :=
  match input.1 with
  | .ordinary => input.2
  | .yes => encodeHamiltonianCycleInstance canonicalHamiltonianYesInstance
  | .no => encodeHamiltonianCycleInstance canonicalHamiltonianNoInstance

inductive Mode
  | start
  | separator (branch : Branch)
  | payload (branch : Branch)
  | invalid
  deriving DecidableEq, Fintype

/-- A fixed transducer copies the candidate only on the ordinary branch and
emits either fixed degenerate instance when the input ends. -/
def spec : StatefulFlatMapSpec Mode (Option CliqueSym) CliqueSym where
  initial := .start
  action mode symbol :=
    match mode with
    | .start =>
        match symbol with
        | some tag =>
            match Branch.ofSymbol tag with
            | some branch => ([], .separator branch)
            | none => ([], .invalid)
        | none => ([], .invalid)
    | .separator branch =>
        match symbol with
        | none => ([], .payload branch)
        | some _ => ([], .invalid)
    | .payload branch =>
        match symbol with
        | some value =>
            if branch = .ordinary then ([value], .payload branch)
            else ([], .payload branch)
        | none => ([], .invalid)
    | .invalid => ([], .invalid)
  finish mode :=
    match mode with
    | .payload .ordinary => []
    | .payload .yes =>
        encodeHamiltonianCycleInstance canonicalHamiltonianYesInstance
    | .payload .no =>
        encodeHamiltonianCycleInstance canonicalHamiltonianNoInstance
    | _ => []

def stream (input : List (Option CliqueSym)) : List CliqueSym :=
  rewriteStatefulFlatMap spec input

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.BranchSelector

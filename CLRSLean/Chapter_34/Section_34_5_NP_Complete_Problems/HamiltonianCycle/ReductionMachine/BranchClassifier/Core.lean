import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.Branch
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.StatefulFlatMap

/-!
# VERTEX-COVER to HAM-CYCLE: finite-state branch classifier
-/

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.BranchClassifier

open PolyBuilder

/-- Parser phases needed to distinguish the three total-construction cases. -/
inductive Mode
  | start
  | vertices
  | target (positive : Bool)
  | edges (targetPositive edgeSeen : Bool)
  | invalid
  deriving DecidableEq, Fintype

def finishBranch (targetPositive edgeSeen : Bool) : Branch :=
  if edgeSeen then
    if targetPositive then .ordinary else .no
  else .yes

/-- The classifier ignores all numerical magnitudes except whether the target
field and edge suffix are empty. -/
def spec : StatefulFlatMapSpec Mode CliqueSym CliqueSym where
  initial := .start
  action mode symbol :=
    match mode with
    | .start =>
        if symbol = .instanceMark then ([], .vertices) else ([], .invalid)
    | .vertices =>
        if symbol = .tick then ([], .vertices)
        else if symbol = .fieldSep then ([], .target false)
        else ([], .invalid)
    | .target positive =>
        if symbol = .tick then ([], .target true)
        else if symbol = .fieldSep then ([], .edges positive false)
        else ([], .invalid)
    | .edges targetPositive _ => ([], .edges targetPositive true)
    | .invalid => ([], .invalid)
  finish mode :=
    match mode with
    | .edges targetPositive edgeSeen =>
        [(finishBranch targetPositive edgeSeen).symbol]
    | _ => []

/-- Pure stream computed by the classifier controller. -/
def stream (input : List CliqueSym) : List CliqueSym :=
  rewriteStatefulFlatMap spec input

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.BranchClassifier

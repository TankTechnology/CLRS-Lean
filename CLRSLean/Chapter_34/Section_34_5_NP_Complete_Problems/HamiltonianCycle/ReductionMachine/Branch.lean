import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Construction.Instance

/-!
# VERTEX-COVER to HAM-CYCLE: total-construction branch tags
-/

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine

/-- The two degenerate textbook cases and the ordinary gadget case. -/
inductive Branch
  | ordinary
  | yes
  | no
  deriving DecidableEq, Fintype, Repr

/-- A fixed one-symbol representation inside the shared graph alphabet. -/
def Branch.symbol : Branch → CliqueSym
  | .ordinary => .instanceMark
  | .yes => .certificateMark
  | .no => .tick

/-- Partial inverse used by the guarded output selector. -/
def Branch.ofSymbol : CliqueSym → Option Branch
  | .instanceMark => some .ordinary
  | .certificateMark => some .yes
  | .tick => some .no
  | _ => none

@[simp] theorem Branch.ofSymbol_symbol (branch : Branch) :
    Branch.ofSymbol branch.symbol = some branch := by
  cases branch <;> rfl

/-- Semantic branch selected by the total typed reduction. -/
def branch (I : VertexCoverInstance) : Branch :=
  if I.edges = [] then .yes
  else if I.targetSize = 0 then .no
  else .ordinary

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine

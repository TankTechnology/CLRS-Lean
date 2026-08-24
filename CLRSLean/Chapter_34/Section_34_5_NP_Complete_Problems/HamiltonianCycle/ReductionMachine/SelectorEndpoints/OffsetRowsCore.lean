import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.SelectorClique.Formatter

/-!
# HAM-CYCLE selector endpoints: generic offset-row formatter data

This small interface separates the already verified offset-aware pair-row
controller from the triangular selector-clique rows for which it was first
used.  An arbitrary marked row family may now share the same fixed machine.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.SelectorEndpoints

open PolyBuilder

/-- A unary base followed by arbitrary marked rows of lower endpoints. -/
structure OffsetRowsFamily where
  base : Nat
  rows : List (List Nat)
deriving DecidableEq, Repr

/-- Canonical input consumed by the offset-aware pair-row controller. -/
def encodeOffsetRowsFamily (family : OffsetRowsFamily) :
    List UnaryFrameSym :=
  encodeUnaryFrameBlock family.base ++
    family.rows.flatMap fun row => encodeUnaryFrame row ++ [.frameEnd]

/-- Edges emitted from arbitrary rows, with the upper endpoint equal to the
runtime base plus the row ordinal. -/
def offsetRowsEdgeStreamFrom (base row : Nat) :
    List (List Nat) → List CliqueSym
  | [] => []
  | values :: rows =>
      (values.flatMap fun lower =>
        encodeCliqueEdge (lower, base + row)) ++
      offsetRowsEdgeStreamFrom base (row + 1) rows

def offsetRowsEdgeStream (family : OffsetRowsFamily) : List CliqueSym :=
  offsetRowsEdgeStreamFrom family.base 0 family.rows

/-- Exact controller cost for one arbitrary row. -/
def offsetMarkedRowSteps (values : List Nat) (upper : Nat) : Nat :=
  TMClique.pairRowsFormatValuesSteps values upper + 2

/-- Exact controller cost for a suffix of arbitrary rows. -/
def offsetMarkedRowsSteps (base row : Nat) : List (List Nat) → Nat
  | [] => 0
  | values :: rows =>
      offsetMarkedRowSteps values (base + row) +
        offsetMarkedRowsSteps base (row + 1) rows

/-- Exact end-to-end cost, including base loading and final counter cleanup. -/
def offsetRowsFormatRevSteps (family : OffsetRowsFamily) : Nat :=
  2 * family.base + 1 +
    offsetMarkedRowsSteps family.base 0 family.rows +
    (family.base + family.rows.length) + 3

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.SelectorEndpoints

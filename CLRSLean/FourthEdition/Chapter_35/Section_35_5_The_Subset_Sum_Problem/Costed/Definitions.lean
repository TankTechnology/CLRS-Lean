import CLRSLean.FourthEdition.Chapter_35.Section_35_5_The_Subset_Sum_Problem

/-!
# CLRS Section 35.5 - Costed local scans

Execution records for the concrete list passes used by APPROX-SUBSET-SUM.
Each counter is produced by the same recursion as its returned value.
-/

noncomputable section

namespace CLRS
namespace ApproxSubsetSum

/-- Result and unit-operation count of a list-producing scan. -/
structure ListExecution where
  value : List Nat
  work : Nat
deriving Repr

/-- Result and unit-operation count of a natural-number-producing scan. -/
structure NatExecution where
  value : Nat
  work : Nat
deriving Repr

/-- Add {lit}`x` to every element, charging one addition per element. -/
def mapAddWithCost (x : Nat) : List Nat → ListExecution
  | [] => ⟨[], 0⟩
  | y :: ys =>
      let rest := mapAddWithCost x ys
      ⟨(y + x) :: rest.value, rest.work + 1⟩

/-- CLRS MERGE-LISTS, charging one comparison whenever both inputs are
nonempty. -/
def mergeWithCost : (L M : List Nat) → ListExecution
  | [], ys => ⟨ys, 0⟩
  | xs, [] => ⟨xs, 0⟩
  | x :: xs, y :: ys =>
      if x ≤ y then
        let rest := mergeWithCost xs (y :: ys)
        ⟨x :: rest.value, rest.work + 1⟩
      else
        let rest := mergeWithCost (x :: xs) ys
        ⟨y :: rest.value, rest.work + 1⟩
termination_by L M => L.length + M.length

/-- Tail scan of TRIM, charging one threshold comparison per scanned value. -/
def trimAuxWithCost (δ : Real) : Nat → List Nat → ListExecution
  | _last, [] => ⟨[], 0⟩
  | last, y :: ys =>
      if (1 + δ) * (last : Real) < (y : Real) then
        let rest := trimAuxWithCost δ y ys
        ⟨y :: rest.value, rest.work + 1⟩
      else
        let rest := trimAuxWithCost δ last ys
        ⟨rest.value, rest.work + 1⟩

/-- CLRS TRIM with a counter for its tail comparisons. -/
def trimWithCost (δ : Real) : List Nat → ListExecution
  | [] => ⟨[], 0⟩
  | y :: ys =>
      let rest := trimAuxWithCost δ y ys
      ⟨y :: rest.value, rest.work⟩

/-- Keep values at most {lit}`t`, charging one target comparison per value. -/
def filterAtMostWithCost (t : Nat) : List Nat → ListExecution
  | [] => ⟨[], 0⟩
  | y :: ys =>
      let rest := filterAtMostWithCost t ys
      if y ≤ t then
        ⟨y :: rest.value, rest.work + 1⟩
      else
        ⟨rest.value, rest.work + 1⟩

/-- Maximum scan with an explicit accumulator and one comparison per value. -/
def maximumAuxWithCost (best : Nat) : List Nat → NatExecution
  | [] => ⟨best, 0⟩
  | y :: ys =>
      let rest := maximumAuxWithCost (max best y) ys
      ⟨rest.value, rest.work + 1⟩

/-- Maximum of a natural-number list, using {lit}`0` for the empty case. -/
def maximumWithCost (xs : List Nat) : NatExecution :=
  maximumAuxWithCost 0 xs

end ApproxSubsetSum
end CLRS

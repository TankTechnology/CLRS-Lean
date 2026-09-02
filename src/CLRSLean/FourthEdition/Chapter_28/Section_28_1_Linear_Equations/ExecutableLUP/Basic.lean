import CLRSLean.FourthEdition.Chapter_28.Section_28_1_Linear_Equations

/-!
# CLRS Section 28.1 - Executable LUP foundations

Result records and the concrete pivot/elimination executions used by the
dimension-recursive LUP decomposition.
-/

namespace CLRS
namespace Chapter28

open Matrix

/-- The three factors returned by a successful LUP decomposition. -/
structure LUPFactors (n : Nat) (F : Type) where
  perm : Equiv.Perm (Fin n)
  lower : Matrix (Fin n) (Fin n) F
  upper : Matrix (Fin n) (Fin n) F

/-- Result and exact-algebra work of a total LUP execution: pivot comparisons
plus the field operations performed by elimination and factor assembly. -/
structure LUPExecution (n : Nat) (F : Type) where
  result : Option (LUPFactors n F)
  work : Nat

/-- Result and comparison count of scanning a matrix's first column. -/
structure PivotExecution {n : Nat} {F : Type} [Zero F]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F) where
  pivot : Option {p : Fin (n + 1) // A p 0 ≠ 0}
  comparisons : Nat

/-- Result and work of one field-valued arithmetic expression. -/
structure FieldExecution (F : Type) where
  value : F
  work : Nat

/-- Result and field-operation work of a square-matrix construction. -/
structure MatrixExecution (n : Nat) (F : Type) where
  value : Matrix (Fin n) (Fin n) F
  work : Nat

section Pivot

variable {F : Type} [Zero F] [DecidableEq F]

/-- Scan candidate rows from left to right, charging one comparison for each
tested first-column entry. -/
def findPivotListWithCost {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F) :
    List (Fin (n + 1)) → PivotExecution A
  | [] => ⟨none, 0⟩
  | p :: ps =>
      if h : A p 0 = 0 then
        let rest := findPivotListWithCost A ps
        ⟨rest.pivot, rest.comparisons + 1⟩
      else
        ⟨some ⟨p, h⟩, 1⟩

/-- Scan every row for the first nonzero pivot in column zero. -/
def findPivotWithCost {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F) : PivotExecution A :=
  findPivotListWithCost A (List.finRange (n + 1))

end Pivot

section Elimination

variable {F : Type} [Field F]

/-- One entry of the direct Gaussian-elimination update.  A copied pivot-row
entry is free in the field-operation model; every other entry performs one
division, one multiplication, and one subtraction. -/
def eliminateEntryWithCost {n : Nat}
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (_h : B 0 0 ≠ 0)
    (i j : Fin (n + 1)) : FieldExecution F :=
  if i = 0 then
    ⟨B i j, 0⟩
  else
    ⟨B i j - (B i 0 / B 0 0) * B 0 j, 3⟩

/-- Pointwise Gaussian elimination together with the sum of the entry-level
field-operation counters. -/
def eliminateWithCost {n : Nat}
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (h : B 0 0 ≠ 0) :
    MatrixExecution (n + 1) F :=
  ⟨fun i j => (eliminateEntryWithCost B h i j).value,
    ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), (eliminateEntryWithCost B h i j).work⟩

end Elimination

end Chapter28
end CLRS

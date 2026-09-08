import CLRSLean.FourthEdition.Chapter_14.Section_14_4_Longest_Common_Subsequence.Tabulation

/-!
# Section 14.4 — Longest common subsequence

The public {name}`CLRS.Chapter15.lcsLengthTabulated` computes rolling rows from
stored predecessors. Its row invariant proves equality with the legacy recursive
specification {name}`CLRS.Chapter15.lcsLength`. The executed cell counter is exactly
`(m + 1)(n + 1)`; for positive lengths it lies between `mn` and `4mn`.

Each cell uses constant many list/head, arithmetic, and equality operations.
This is a cell-operation bound, excluding equality internals, allocation, and
call-stack costs. The returned row has `n + 1` entries; no peak-memory theorem
is claimed. The legacy reconstruction is functionally correct but still uses
the recursive length oracle, so its runtime is not bounded by this counter.

Main results:

- {name}`CLRS.Chapter15.LCSTabulation.execute_row`: all stored row entries agree
  with the recursive specification.
- {name}`CLRS.Chapter15.LCSTabulation.execute_cells`: actual executed cell count.
- {lit}`lcsExecution_cells_eq_tableCells`, {lit}`lcsExecution_cells_bounds`:
  the table-size formula and quadratic bounds apply to the executed algorithm.

Notation conventions used in this section:

- `xs`, `ys` : the two input sequences
- `m`, `n` : their lengths
-/

namespace CLRS
namespace Chapter15

/-! ## The Θ(mn) table bound -/

/-- The number of table entries of the bottom-up LCS table: one cell for each
    prefix pair {lit}`(i, j)` with {lit}`0 ≤ i ≤ m` and {lit}`0 ≤ j ≤ n`. -/
def lcsTableCells (m n : Nat) : Nat :=
  (m + 1) * (n + 1)

/-- The LCS table has `(m + 1)(n + 1)` entries. -/
theorem lcsTableCells_eq (m n : Nat) : lcsTableCells m n = (m + 1) * (n + 1) := rfl

/-- Arithmetic upper bound for the number of visited cells. Execution is linked
    to this formula by {lit}`lcsExecution_cells_eq_tableCells` below. -/
theorem lcsTableCells_le_four_mn (m n : Nat) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    lcsTableCells m n ≤ 4 * m * n := by
  unfold lcsTableCells
  have h1 : m + 1 ≤ 2 * m := by omega
  have h2 : n + 1 ≤ 2 * n := by omega
  calc
    (m + 1) * (n + 1) ≤ (2 * m) * (2 * n) := Nat.mul_le_mul h1 h2
    _ = 4 * m * n := by ring

/-- Connect the dimension formula to the counter carried by the row execution. -/
theorem lcsExecution_cells_eq_tableCells [DecidableEq α] (xs ys : List α) :
    (LCSTabulation.execute xs ys).cells = lcsTableCells xs.length ys.length :=
  LCSTabulation.execute_cells xs ys

/-- Matching product bounds for the actual cell visits, for nonempty inputs. -/
theorem lcsExecution_cells_bounds [DecidableEq α] (xs ys : List α)
    (hx : 1 ≤ xs.length) (hy : 1 ≤ ys.length) :
    xs.length * ys.length ≤ (LCSTabulation.execute xs ys).cells ∧
    (LCSTabulation.execute xs ys).cells ≤ 4 * xs.length * ys.length := by
  rw [lcsExecution_cells_eq_tableCells]
  exact ⟨Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _),
    lcsTableCells_le_four_mn _ _ hx hy⟩

end Chapter15
end CLRS

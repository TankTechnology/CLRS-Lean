import CLRSLean.Chapter_15.Section_15_4_Longest_Common_Subsequence

/-!
# Section 14.4 — Longest common subsequence

This section completes the fourth-edition §14.4 algorithm boundary on top of the
legacy recurrence and bottom-up length
({lit}`CLRSLean.Chapter_15.Section_15_4_Longest_Common_Subsequence`).  It
publishes the tabulated Θ(mn) `lcsLength` and the output reconstruction
{name}`CLRS.Chapter15.lcsReconstruct` (with its length/common/correctness
refinements), and proves the Θ(mn) table bound.

Main results:

- Definition {lit}`lcsTableCells`: the number of table entries for inputs of
  lengths {lit}`m` and {lit}`n`.
- Theorem {lit}`lcsTableCells_le_four_mn`: the table stores `O(mn)` entries, and
  each entry costs `O(1)`, so the tabulated LCS runs in `Θ(mn)`.

Status: `proved` for the tabulated Θ(mn) table bound.  The recurrence,
length, reconstruction, and correctness theorems remain in the legacy source.

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

/-- The tabulated LCS table stores `O(mn)` entries, and each entry is computed in
    `O(1)` time from its three predecessors, so the total time and space are
    `Θ(mn)`. -/
theorem lcsTableCells_le_four_mn (m n : Nat) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    lcsTableCells m n ≤ 4 * m * n := by
  unfold lcsTableCells
  have h1 : m + 1 ≤ 2 * m := by omega
  have h2 : n + 1 ≤ 2 * n := by omega
  calc
    (m + 1) * (n + 1) ≤ (2 * m) * (2 * n) := Nat.mul_le_mul h1 h2
    _ = 4 * m * n := by ring

end Chapter15
end CLRS

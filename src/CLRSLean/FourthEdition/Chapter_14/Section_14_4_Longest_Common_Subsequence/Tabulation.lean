import CLRSLean.Chapter_15.Section_15_4_Longest_Common_Subsequence

/-!
# LCS by computed rows

Process suffixes from the end of each input. Each row uses the already computed
next row and the completed suffix of its own row. Executable code only reads
list heads/tails and stored numbers; it never calls the recursive LCS oracle.
The invariant identifies every entry of a completed row, not just its first
entry. The counter records one visit per boundary or interior cell.

The returned table is a rolling row. Persistent list storage and call-stack
allocation are not modeled as machine costs; each cell uses at most one
equality test and constant many arithmetic/list operations. Reconstruction
from this rolling table is a separate algorithmic layer.
-/

namespace CLRS.Chapter15.LCSTabulation

structure Row where
  values : List Nat
  cells : Nat
  deriving Repr

/-- Proof-only interpretation of all suffix entries in one row. -/
def specification [DecidableEq α] (xs : List α) : List α → List Nat
  | [] => [0]
  | y :: ys => lcsLength xs (y :: ys) :: specification xs ys

theorem specification_head [DecidableEq α] (xs ys : List α) :
    (specification xs ys).headD 0 = lcsLength xs ys := by
  cases ys with
  | nil => cases xs <;> simp [specification, lcsLength]
  | cons y ys => rfl

/-- Initialize the empty-input row, visiting every boundary cell once. -/
def initial : List α → Row
  | [] => ⟨[0], 1⟩
  | _ :: ys => let rest := initial ys; ⟨0 :: rest.values, rest.cells + 1⟩

theorem initial_values [DecidableEq α] (ys : List α) :
    (initial ys).values = specification ([] : List α) ys := by
  induction ys with
  | nil => rfl
  | cons y ys ih => simp [initial, specification, lcsLength, ih]

theorem initial_cells (ys : List α) : (initial ys).cells = ys.length + 1 := by
  induction ys with
  | nil => rfl
  | cons y ys ih => simp [initial, ih]

/-- Compute one row using only three stored predecessors per interior cell. -/
def nextRow [DecidableEq α] (x : α) : List α → List Nat → Row
  | [], _ => ⟨[0], 1⟩
  | y :: ys, below =>
      let rest := nextRow x ys below.tail
      let v := if x = y then below.tail.headD 0 + 1 else max (below.headD 0) (rest.values.headD 0)
      ⟨v :: rest.values, rest.cells + 1⟩

/-- Every newly computed cell satisfies the LCS specification for its suffix. -/
theorem nextRow_values [DecidableEq α] (x : α) (xs ys : List α) :
    (nextRow x ys (specification xs ys)).values = specification (x :: xs) ys := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
      simp only [nextRow, specification, List.tail_cons, List.headD_cons, ih]
      simp only [specification_head, lcsLength]

theorem nextRow_cells [DecidableEq α] (x : α) (ys : List α) (below : List Nat) :
    (nextRow x ys below).cells = ys.length + 1 := by
  induction ys generalizing below with
  | nil => rfl
  | cons y ys ih => simp [nextRow, ih]

/-- Dynamic programming: compute a row once and pass its stored values to its predecessor. -/
def execute [DecidableEq α] : List α → List α → Row
  | [], ys => initial ys
  | x :: xs, ys =>
      let below := execute xs ys
      let current := nextRow x ys below.values
      ⟨current.values, below.cells + current.cells⟩

theorem execute_row [DecidableEq α] (xs ys : List α) :
    (execute xs ys).values = specification xs ys := by
  induction xs with
  | nil => exact initial_values ys
  | cons x xs ih => simp only [execute, ih, nextRow_values]

/-- The count comes from the actual row loops, including both boundary edges. -/
theorem execute_cells [DecidableEq α] (xs ys : List α) :
    (execute xs ys).cells = (xs.length + 1) * (ys.length + 1) := by
  induction xs with
  | nil => simp [execute, initial_cells]
  | cons x xs ih =>
      simp only [execute, ih, nextRow_cells, List.length_cons]
      ring

theorem specification_length [DecidableEq α] (xs ys : List α) :
    (specification xs ys).length = ys.length + 1 := by
  induction ys with
  | nil => rfl
  | cons y ys ih => simp [specification, ih]

/-- The returned row has only one entry per suffix of the second sequence. -/
theorem execute_row_length [DecidableEq α] (xs ys : List α) :
    (execute xs ys).values.length = ys.length + 1 := by
  rw [execute_row, specification_length]

end CLRS.Chapter15.LCSTabulation

namespace CLRS.Chapter15

/-- The public tabulated length reads the first entry of the computed rolling row. -/
def lcsLengthTabulated [DecidableEq α] (xs ys : List α) : Nat :=
  (LCSTabulation.execute xs ys).values.headD 0

theorem lcsLengthTabulated_correct [DecidableEq α] (xs ys : List α) :
    lcsLengthTabulated xs ys = lcsLength xs ys := by
  rw [lcsLengthTabulated, LCSTabulation.execute_row, LCSTabulation.specification_head]

theorem lcsLengthTabulated_upper_bound [DecidableEq α] (xs ys zs : List α)
    (h : IsCommonSubsequence xs ys zs) : zs.length ≤ lcsLengthTabulated xs ys := by
  rw [lcsLengthTabulated_correct]
  exact lcsLength_upper_bound h

end CLRS.Chapter15

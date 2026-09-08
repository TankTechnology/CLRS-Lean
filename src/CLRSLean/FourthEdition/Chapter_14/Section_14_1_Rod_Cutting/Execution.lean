import CLRSLean.Chapter_15.Section_15_1_Rod_Cutting

/-!
# Counted bottom-up rod cutting

The outer loop computes its preceding array once. The inner loop reads that
stored array once per candidate, retaining its running maximum. Counters record
candidate evaluations and appended table entries in that same execution.
Array access, price lookup, and natural-number operations are primitive events;
their implementation internals and persistent-array copying are not counted.
-/

namespace CLRS.Chapter15.RodExecution

structure Scan where
  value : Nat
  candidates : Nat
  deriving Repr

/-- Scan cuts `1..k` using an already computed revenue array. -/
def scan (price : Nat → Nat) (previous : Array Nat) (n : Nat) : Nat → Scan
  | 0 => ⟨0, 0⟩
  | k + 1 =>
      let rest := scan price previous n k
      let candidate := price (k + 1) + arrGet previous (n - (k + 1))
      ⟨max rest.value candidate, rest.candidates + 1⟩

theorem scan_candidates (price : Nat → Nat) (previous : Array Nat) (n k : Nat) :
    (scan price previous n k).candidates = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [scan, ih]

theorem scan_value (price : Nat → Nat) (previous : Array Nat) (n k : Nat) :
    (scan price previous n k).value =
      (Finset.Icc 1 k).sup (fun i => price i + arrGet previous (n - i)) := by
  induction k with
  | zero => simp [scan]
  | succ k ih =>
      have hs : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
        ext i
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      simp only [scan, ih, hs, Finset.sup_insert]
      exact max_comm _ _

structure Run where
  array : Array Nat
  candidates : Nat
  writes : Nat
  deriving Repr

/-- Append each new optimum once, using only the previously stored prefix. -/
def execute (price : Nat → Nat) : Nat → Run
  | 0 => ⟨#[0], 0, 1⟩
  | j + 1 =>
      let previous := execute price j
      let row := scan price previous.array (j + 1) (j + 1)
      ⟨previous.array.push row.value,
        previous.candidates + row.candidates, previous.writes + 1⟩

/-- The actual stored array refines the previously proved revenue table. -/
theorem execute_array (price : Nat → Nat) (n : Nat) :
    (execute price n).array = rodRevenueArrayAux price n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [execute, ih, scan_value, rodRevenueArrayAux]

theorem execute_entry (price : Nat → Nat) (n k : Nat) (hk : k ≤ n) :
    arrGet (execute price n).array k = bottomUpRodRevenue price k := by
  rw [execute_array]
  exact arrGet_rodRevenueArrayAux price n k hk

/-- Exact candidate visits obtained by adding counters of the executed scans. -/
theorem execute_candidates (price : Nat → Nat) (n : Nat) :
    (execute price n).candidates = (Finset.range (n + 1)).sum (fun j => j) := by
  induction n with
  | zero => simp [execute]
  | succ n ih => simp only [execute, ih, scan_candidates, Finset.sum_range_succ]

/-- Includes the boundary entry at length zero. -/
theorem execute_writes (price : Nat → Nat) (n : Nat) :
    (execute price n).writes = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [execute, ih]

theorem execute_size (price : Nat → Nat) (n : Nat) :
    (execute price n).array.size = n + 1 := by
  rw [execute_array, rodRevenueArrayAux_size]

end CLRS.Chapter15.RodExecution

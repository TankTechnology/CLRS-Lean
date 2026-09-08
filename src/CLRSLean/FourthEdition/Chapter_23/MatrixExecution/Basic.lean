import CLRSLean.FourthEdition.Chapter_23.Section_23_1_All_Pairs_Model
import CLRSLean.FourthEdition.Chapter_14.Section_14_3_Elements_Of_Dynamic_Programming.Execution

/-!
# Stored matrices and counted min-plus products

Every row and cell is appended once. Inner scans return both their minimum
and their actual number of visits. Exact real arithmetic, comparison, and
array access are abstract primitives; allocation and bit costs are excluded.
-/

noncomputable section
namespace CLRS.Chapter24.MatrixExecution
open CLRS.Chapter15.DPExecution

abbrev Stored := Table (WithTop ℝ)

def read (t : Stored) (i j : Fin n) : WithTop ℝ := get t.rows i.val j.val

def cell (f : Fin n → Fin n → WithTop ℝ × Nat) (i j : Nat) : WithTop ℝ × Nat :=
  if hi : i < n then if hj : j < n then f ⟨i, hi⟩ ⟨j, hj⟩ else (⊤, 0) else (⊤, 0)

def tabulate (f : Fin n → Fin n → WithTop ℝ × Nat) : Stored :=
  buildLayers (fun _ => n) (fun i _ j => cell f i j) n

@[simp] theorem tabulate_read (f : Fin n → Fin n → WithTop ℝ × Nat) (i j : Fin n) :
    read (tabulate f) i j = (f i j).1 := by
  have h := buildLayers_correct (fun _ => n) (fun i _ j => cell f i j)
    (fun i j => (cell f i j).1) (by intros; rfl) n i.val i.isLt j.val j.isLt
  simpa [read, tabulate, cell, i.isLt, j.isLt] using h

@[simp] theorem tabulate_writes (f : Fin n → Fin n → WithTop ℝ × Nat) :
    (tabulate f).cellWrites = n * n := by
  simp [tabulate, buildLayers_cellWrites]

theorem tabulate_visits (f : Fin n → Fin n → WithTop ℝ × Nat) (c : Nat)
    (hc : ∀ i j, (f i j).2 = c) : (tabulate f).candidateVisits = n * n * c := by
  have rowVisits (i : Nat) (hi : i < n) :
      ∑ j ∈ Finset.range n, (cell f i j).2 = n * c := by
    calc
      _ = ∑ _j ∈ Finset.range n, c := Finset.sum_congr rfl (fun j hj => by
        simp [cell, hi, Finset.mem_range.mp hj, hc])
      _ = n * c := by simp
  have layers : ∀ k, k ≤ n →
      (buildLayers (fun _ => n) (fun i _ j => cell f i j) k).candidateVisits = k * (n * c) := by
    intro k hk
    induction k with
    | zero => simp [buildLayers]
    | succ k ih =>
      simp only [buildLayers]
      rw [ih (by omega), buildRow_visits, rowVisits k (by omega)]
      ring
  simpa [tabulate, Nat.mul_assoc] using layers n (by omega)

def scanMin (f : Nat → WithTop ℝ) : Nat → WithTop ℝ × Nat
  | 0 => (⊤, 0)
  | k + 1 => let prev := scanMin f k; (min prev.1 (f k), prev.2 + 1)

@[simp] theorem scanMin_visits (f : Nat → WithTop ℝ) (k : Nat) :
    (scanMin f k).2 = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [scanMin, ih]

theorem scanMin_value (f : Nat → WithTop ℝ) (k : Nat) :
    (scanMin f k).1 = (Finset.range k).inf f := by
  induction k with
  | zero => simp [scanMin]
  | succ k ih => simp [scanMin, ih, Finset.range_add_one, min_comm]

def scanFin (f : Fin n → WithTop ℝ) : WithTop ℝ × Nat :=
  scanMin (fun k => if hk : k < n then f ⟨k, hk⟩ else ⊤) n

@[simp] theorem scanFin_visits (f : Fin n → WithTop ℝ) : (scanFin f).2 = n :=
  scanMin_visits _ _

theorem scanFin_value (f : Fin n → WithTop ℝ) :
    (scanFin f).1 = Finset.univ.inf f := by
  rw [scanFin, scanMin_value]
  apply le_antisymm
  · apply Finset.le_inf
    intro i _
    exact (Finset.inf_le (Finset.mem_range.mpr i.isLt)).trans_eq (by simp [i.isLt])
  · apply Finset.le_inf
    intro k hk
    have hkn := Finset.mem_range.mp hk
    simpa [hkn] using (Finset.inf_le (s := Finset.univ) (f := f) (Finset.mem_univ (⟨k, hkn⟩ : Fin n)))

def multiply (n : Nat) (a b : Stored) : Stored :=
  tabulate (fun i j : Fin n => scanFin (fun k => read a i k + read b k j))

@[simp] theorem multiply_read (a b : Stored) (i j : Fin n) :
    read (multiply n a b) i j = WeightedGraph.minPlusMul (read a) (read b) i j := by
  simp [multiply, scanFin_value, WeightedGraph.minPlusMul]

@[simp] theorem multiply_writes (n : Nat) (a b : Stored) :
    (multiply n a b).cellWrites = n * n := tabulate_writes _

@[simp] theorem multiply_visits (n : Nat) (a b : Stored) :
    (multiply n a b).candidateVisits = n ^ 3 := by
  rw [multiply, tabulate_visits _ n (by intros; exact scanFin_visits _)]
  ring

end CLRS.Chapter24.MatrixExecution

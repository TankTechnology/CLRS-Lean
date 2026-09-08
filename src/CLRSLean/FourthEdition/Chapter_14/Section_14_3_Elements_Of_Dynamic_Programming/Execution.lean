import CLRSLean.FourthEdition.Chapter_14.Section_14_3_Elements_Of_Dynamic_Programming

/-!
# Stored dynamic-programming layers

A row is built by appending each cell once. A table is built by appending each
row once; the evaluator receives only previously completed rows. Returned
write and candidate-visit counters are accumulated by these executions.
Array access, arithmetic, and comparisons are unit-cost primitives; this is
not a persistent-array copying or bit-operation runtime model.
-/

namespace CLRS.Chapter15.DPExecution

structure Row (α : Type*) where
  cells : Array α
  writes : Nat
  visits : Nat
  evaluatedIndices : List Nat

def buildRow (f : Nat → α × Nat) : Nat → Row α
  | 0 => ⟨#[], 0, 0, []⟩
  | n + 1 =>
      let prev := buildRow f n
      let next := f n
      ⟨prev.cells.push next.1, prev.writes + 1, prev.visits + next.2, n :: prev.evaluatedIndices⟩

@[simp] theorem buildRow_cells (f : Nat → α × Nat) (n : Nat) :
    (buildRow f n).cells = ((List.range n).map (fun i => (f i).1)).toArray := by
  induction n with
  | zero => rfl
  | succ n ih => simp [buildRow, ih, List.range_succ]

@[simp] theorem buildRow_writes (f : Nat → α × Nat) (n : Nat) :
    (buildRow f n).writes = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [buildRow, ih]

theorem buildRow_visits (f : Nat → α × Nat) (n : Nat) :
    (buildRow f n).visits = ∑ i ∈ Finset.range n, (f i).2 := by
  induction n with
  | zero => simp [buildRow]
  | succ n ih => simp [buildRow, ih, Finset.sum_range_succ]

structure Table (α : Type*) where
  rows : Array (Array α)
  cellWrites : Nat
  candidateVisits : Nat
  evaluatedStates : List (Nat × Nat)

/-- Total lookup; correctness theorems establish that algorithmic reads are in range. -/
def get [Inhabited α] (rows : Array (Array α)) (l i : Nat) : α :=
  ((rows[l]?).getD #[])[i]?.getD default

/-- Complete layers 0 through n-1. Each newly evaluated cell is stored once. -/
def buildLayers (width : Nat → Nat)
    (step : Nat → Array (Array α) → Nat → α × Nat) : Nat → Table α
  | 0 => ⟨#[], 0, 0, []⟩
  | n + 1 =>
      let prev := buildLayers width step n
      let row := buildRow (step n prev.rows) (width n)
      ⟨prev.rows.push row.cells, prev.cellWrites + row.writes,
        prev.candidateVisits + row.visits,
        row.evaluatedIndices.map (fun i => (n,i)) ++ prev.evaluatedStates⟩

@[simp] theorem buildLayers_size (width : Nat → Nat)
    (step : Nat → Array (Array α) → Nat → α × Nat) (n : Nat) :
    (buildLayers width step n).rows.size = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [buildLayers, ih]

lemma get_push_old [Inhabited α] (rows : Array (Array α)) (row : Array α)
    (l i : Nat) (hl : l < rows.size) : get (rows.push row) l i = get rows l i := by
  simp [get, Array.getElem?_push, hl, Nat.ne_of_lt hl]

lemma get_push_new [Inhabited α] (rows : Array (Array α)) (f : Nat → α × Nat)
    (n i : Nat) (hi : i < n) :
    get (rows.push (buildRow f n).cells) rows.size i = (f i).1 := by
  simp [get, hi]

/-- Dependency-order invariant: every completed cell equals its specification.
The local obligation uses only earlier rows; it does not assume a final table. -/
theorem buildLayers_correct [Inhabited α] (width : Nat → Nat)
    (step : Nat → Array (Array α) → Nat → α × Nat) (correct : Nat → Nat → α)
    (hstep : ∀ l rows, rows.size = l →
      (∀ k, k < l → ∀ i, i < width k → get rows k i = correct k i) →
      ∀ i, i < width l → (step l rows i).1 = correct l i)
    (n : Nat) : ∀ l, l < n → ∀ i, i < width l →
      get (buildLayers width step n).rows l i = correct l i := by
  induction n with
  | zero => intros; omega
  | succ n ih =>
      intro l hl i hi
      by_cases heq : l = n
      · subst l
        have hn := buildLayers_size width step n
        have hg := get_push_new (buildLayers width step n).rows
          (step n (buildLayers width step n).rows) (width n) i hi
        rw [hn] at hg
        change get ((buildLayers width step n).rows.push _) n i = _
        rw [hg]
        exact hstep n _ hn ih i hi
      · have hln : l < n := by omega
        change get ((buildLayers width step n).rows.push _) l i = _
        rw [get_push_old _ _ l i (by simpa using hln)]
        exact ih l hln i hi

theorem buildLayers_property [Inhabited α] (width : Nat → Nat)
    (step : Nat → Array (Array α) → Nat → α × Nat) (P : Nat → Nat → α → Prop)
    (hstep : ∀ l rows, rows.size = l →
      (∀ k, k < l → ∀ i, i < width k → P k i (get rows k i)) →
      ∀ i, i < width l → P l i (step l rows i).1)
    (n : Nat) : ∀ l, l < n → ∀ i, i < width l →
      P l i (get (buildLayers width step n).rows l i) := by
  induction n with
  | zero => intros; omega
  | succ n ih =>
      intro l hl i hi
      by_cases heq : l = n
      · subst l
        have hn := buildLayers_size width step n
        have hg := get_push_new (buildLayers width step n).rows
          (step n (buildLayers width step n).rows) (width n) i hi
        rw [hn] at hg
        change P n i (get ((buildLayers width step n).rows.push _) n i)
        rw [hg]
        exact hstep n _ hn ih i hi
      · have hln : l < n := by omega
        change P l i (get ((buildLayers width step n).rows.push _) l i)
        rw [get_push_old _ _ l i (by simpa using hln)]
        exact ih l hln i hi

/-- Exact writes from actual row construction, not a distinct-state estimate. -/
theorem buildLayers_cellWrites (width : Nat → Nat)
    (step : Nat → Array (Array α) → Nat → α × Nat) (n : Nat) :
    (buildLayers width step n).cellWrites = ∑ l ∈ Finset.range n, width l := by
  induction n with
  | zero => simp [buildLayers]
  | succ n ih => simp [buildLayers, ih, Finset.sum_range_succ]

/-- Sum the actual candidate visits when the cell evaluator visits charge(l)
candidates in each state of layer l. -/
theorem buildLayers_candidateVisits (width charge : Nat → Nat)
    (step : Nat → Array (Array α) → Nat → α × Nat)
    (hstep : ∀ l rows i, (step l rows i).2 = charge l) (n : Nat) :
    (buildLayers width step n).candidateVisits =
      ∑ l ∈ Finset.range n, width l * charge l := by
  induction n with
  | zero => simp [buildLayers]
  | succ n ih => simp [buildLayers, ih, buildRow_visits, hstep, Finset.sum_range_succ]

/-- Minimum value, first minimizing index, and actual candidate visits. -/
structure Minimum where
  value : Nat
  index : Nat
  visits : Nat
  deriving Repr, DecidableEq

/-- Scan the inclusive range start,…,start+extra once, retaining the earlier
index when values tie. Each candidate is evaluated exactly once. -/
def minimum (f : Nat → Nat) (start : Nat) : Nat → Minimum
  | 0 => ⟨f start, start, 1⟩
  | extra + 1 =>
      let prev := minimum f start extra
      let value := f (start + extra + 1)
      if value < prev.value then ⟨value, start + extra + 1, prev.visits + 1⟩
      else ⟨prev.value, prev.index, prev.visits + 1⟩

@[simp] theorem minimum_visits (f : Nat → Nat) (start extra : Nat) :
    (minimum f start extra).visits = extra + 1 := by
  induction extra with
  | zero => rfl
  | succ n ih => simp only [minimum]; split <;> simp_all

/-- A scanned minimum is attained in range and below every candidate. -/
theorem minimum_spec (f : Nat → Nat) (start extra : Nat) :
    start ≤ (minimum f start extra).index ∧
    (minimum f start extra).index ≤ start + extra ∧
    (minimum f start extra).value = f (minimum f start extra).index ∧
    ∀ k, start ≤ k → k ≤ start + extra → (minimum f start extra).value ≤ f k := by
  induction extra with
  | zero =>
      change start ≤ start ∧ start ≤ start + 0 ∧ f start = f start ∧ _
      refine ⟨le_rfl, le_rfl, rfl, ?_⟩
      intro k hk hk'
      have he : k = start := by omega
      subst k
      exact le_rfl
  | succ n ih =>
      rcases ih with ⟨hlo, hhi, heq, hmin⟩
      simp only [minimum]
      split
      next h =>
        dsimp only
        refine ⟨by omega, by omega, rfl, ?_⟩
        intro k hk hk'
        by_cases he : k = start + n + 1
        · subst k; exact le_rfl
        · exact (Nat.le_of_lt h).trans (hmin k hk (by omega))
      next h =>
        dsimp only
        refine ⟨hlo, by omega, heq, ?_⟩
        intro k hk hk'
        by_cases he : k = start + n + 1
        · subst k; omega
        · exact hmin k hk (by omega)

/-- The minimum equals a proposed value once its lower-bound and witness
obligations have been established for the actual scanned candidates. -/
theorem minimum_value_eq (f : Nat → Nat) (start extra v : Nat)
    (hlower : ∀ k, start ≤ k → k ≤ start + extra → v ≤ f k)
    (hwitness : ∃ k, start ≤ k ∧ k ≤ start + extra ∧ f k = v) :
    (minimum f start extra).value = v := by
  obtain ⟨hi, hi', heq, hmin⟩ := minimum_spec f start extra
  obtain ⟨k, hk, hk', he⟩ := hwitness
  have hl := hlower _ hi hi'
  have hu := hmin k hk hk'
  omega

/-- The row for a state length has exactly the scheduled number of cells. -/
theorem buildLayers_row_size (width : Nat → Nat)
    (step : Nat → Array (Array α) → Nat → α × Nat) (n l : Nat) (hl : l < n) :
    (((buildLayers width step n).rows[l]?).getD #[]).size = width l := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases he : l = n
      · subst l
        change (((buildLayers width step n).rows.push _)[n]?.getD #[]).size = _
        simp only [Array.getElem?_push, buildLayers_size]
        simp
      · have hln : l < n := by omega
        change (((buildLayers width step n).rows.push _)[l]?.getD #[]).size = _
        simp only [Array.getElem?_push, buildLayers_size, he, if_false]
        exact ih hln

/-- Append-only evaluation creates one stored slot for every counted cell
write. Earlier rows are never overwritten by later evaluations. -/
theorem buildLayers_writes_eq_stored (width : Nat → Nat)
    (step : Nat → Array (Array α) → Nat → α × Nat) (n : Nat) :
    (buildLayers width step n).cellWrites =
      ((buildLayers width step n).rows.toList.map Array.size).sum := by
  induction n with
  | zero => rfl
  | succ n ih => simp [buildLayers, ih]

/-- Extending the table preserves every previously stored cell. -/
theorem buildLayers_get_old [Inhabited α] (width : Nat → Nat)
    (step : Nat → Array (Array α) → Nat → α × Nat) (n l i : Nat) (hl : l < n) :
    get (buildLayers width step (n+1)).rows l i = get (buildLayers width step n).rows l i := by
  apply get_push_old
  simpa using hl

/-- Quadratic cell bound for inclusive intervals in 0,…,N. -/
theorem interval_cells_le_square (N : Nat) :
    (∑ l ∈ Finset.range (N+1), (N+1-l)) ≤ (N+1)^2 := by
  calc
    _ ≤ ∑ _l ∈ Finset.range (N+1), (N+1) :=
      Finset.sum_le_sum (fun l _ => Nat.sub_le _ _)
    _ = _ := by simp [pow_two]

/-- Cubic candidate bound for scans of all splits/roots of every interval. -/
theorem interval_visits_le_cube (N : Nat) :
    (∑ l ∈ Finset.range (N+1), (N+1-l)*l) ≤ (N+1)^3 := by
  calc
    _ ≤ ∑ _l ∈ Finset.range (N+1), (N+1)*(N+1) := by
      apply Finset.sum_le_sum
      intro l hl
      exact Nat.mul_le_mul (Nat.sub_le _ _) (by simpa using (Finset.mem_range.mp hl).le)
    _ = _ := by simp; ring

@[simp] theorem buildRow_indices (f : Nat → α × Nat) (n : Nat) :
    (buildRow f n).evaluatedIndices = (List.range n).reverse := by
  induction n with
  | zero => rfl
  | succ n ih => simp [buildRow, ih, List.range_succ]

/-- Exact domain of the evaluation events emitted by the cell loops. -/
theorem buildLayers_evaluatedStates_mem (width : Nat → Nat)
    (step : Nat → Array (Array α) → Nat → α × Nat) (n l i : Nat) :
    (l,i) ∈ (buildLayers width step n).evaluatedStates ↔ l < n ∧ i < width l := by
  induction n with
  | zero => simp [buildLayers]
  | succ n ih =>
      simp only [buildLayers, buildRow_indices, List.mem_append, List.mem_map,
        List.mem_reverse, List.mem_range]
      rw [ih]
      constructor
      · rintro (⟨j, hj, he⟩ | ⟨hl, hi⟩)
        · cases he
          exact ⟨by omega, hj⟩
        · exact ⟨by omega, hi⟩
      · rintro ⟨hl, hi⟩
        by_cases he : l = n
        · subst l
          exact Or.inl ⟨i, hi, rfl⟩
        · exact Or.inr ⟨by omega, hi⟩

/-- No state is evaluated twice. This is a theorem about the execution's
actual emitted events; no distinct-state assumption is supplied by clients. -/
theorem buildLayers_evaluatedStates_nodup (width : Nat → Nat)
    (step : Nat → Array (Array α) → Nat → α × Nat) (n : Nat) :
    (buildLayers width step n).evaluatedStates.Nodup := by
  induction n with
  | zero => simp [buildLayers]
  | succ n ih =>
      simp only [buildLayers, buildRow_indices]
      rw [List.nodup_append]
      refine ⟨?_, ih, ?_⟩
      · apply List.Nodup.map
        · intro a b h; exact Prod.mk.inj h |>.2
        · exact List.nodup_reverse.mpr List.nodup_range
      · intro x hx y hy he
        subst y
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
        have h := (buildLayers_evaluatedStates_mem width step n n i).mp hy
        omega

/-- The write counter counts exactly the actual evaluation events. -/
theorem buildLayers_cellWrites_eq_events (width : Nat → Nat)
    (step : Nat → Array (Array α) → Nat → α × Nat) (n : Nat) :
    (buildLayers width step n).cellWrites =
      (buildLayers width step n).evaluatedStates.length := by
  induction n with
  | zero => rfl
  | succ n ih => simp [buildLayers, buildRow_indices, ih, Nat.add_comm]
theorem interval_cells_closed (N : Nat) :
    2 * (∑ l ∈ Finset.range (N+1), (N+1-l)) = (N+1)*(N+2) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      have hsum : (∑ l ∈ Finset.range (N+1), (N+2-l)) =
          (∑ l ∈ Finset.range (N+1), (N+1-l)) + (N+1) := by
        calc
          _ = ∑ l ∈ Finset.range (N+1), ((N+1-l)+1) := by
            apply Finset.sum_congr rfl
            intro l hl
            have := Finset.mem_range.mp hl
            omega
          _ = _ := by rw [Finset.sum_add_distrib]; simp
      rw [show N+1+1 = N+2 by omega, Finset.sum_range_succ, hsum]
      have he : N+2-(N+1)=1 := by omega
      rw [he]
      nlinarith

theorem interval_visits_closed (N : Nat) :
    6 * (∑ l ∈ Finset.range (N+1), (N+1-l)*l) = N*(N+1)*(N+2) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      have hsum : (∑ l ∈ Finset.range (N+1), (N+2-l)*l) =
          (∑ l ∈ Finset.range (N+1), (N+1-l)*l) + (∑ l ∈ Finset.range (N+1), l) := by
        calc
          _ = ∑ l ∈ Finset.range (N+1), ((N+1-l)*l+l) := by
            apply Finset.sum_congr rfl
            intro l hl
            have hh := Finset.mem_range.mp hl
            have he : N+2-l = N+1-l+1 := by omega
            rw [he]; ring
          _ = _ := Finset.sum_add_distrib
      rw [show N+1+1 = N+2 by omega, Finset.sum_range_succ, hsum]
      have htri := Finset.sum_range_id_mul_two (N+1)
      simp only [Nat.add_sub_cancel] at htri
      have he : N+2-(N+1)=1 := by omega
      rw [he]
      nlinarith

end CLRS.Chapter15.DPExecution

import CLRSLean.FourthEdition.Chapter_14.Section_14_5_Optimal_Binary_Search_Trees
import CLRSLean.FourthEdition.Chapter_14.Section_14_3_Elements_Of_Dynamic_Programming.Execution

/-!
# Stored optimal-BST costs, weights, and roots

For N keys, layer l contains intervals {lit}`[i,i+l]` with keys i+1 through i+l.
Each weight is updated once from the previous layer; each admissible root is
scanned once using stored child costs. Nonnegative natural weights are used,
without a claim of arbitrary real probability normalization.
-/

namespace CLRS.Chapter15.OBST.Execution
open DPExecution

structure Cell where
  cost : Nat
  weight : Nat
  root : Nat
  deriving Inhabited, Repr, DecidableEq

/-- A constant-work weight update, independent of the number of candidate roots. -/
def nextWeight (p q : Nat → Nat) (rows : Array (Array Cell)) (i l : Nat) : Nat :=
  (get rows l i).weight + p (i+l+1) + q (i+l+1)

def candidate (rows : Array (Array Cell)) (i l w r : Nat) : Nat :=
  (get rows (r-1-i) i).cost + (get rows (i+l-r) r).cost + w

def step (p q : Nat → Nat) : Nat → Array (Array Cell) → Nat → Cell × Nat
  | 0, _, i => (⟨q i, q i, i⟩, 0)
  | l+1, rows, i =>
      let w := nextWeight p q rows i l
      let best := minimum (candidate rows i (l+1) w) (i+1) l
      (⟨best.value, w, best.index⟩, best.visits)

/-- Compute all cost, weight, and root entries for N keys. -/
def execute (p q : Nat → Nat) (N : Nat) : Table Cell :=
  buildLayers (fun l => N+1-l) (step p q) (N+1)

def CorrectCell (p q : Nat → Nat) (l i : Nat) (cell : Cell) : Prop :=
  cell.cost = bottomUpOBST p q i (i+l) ∧ cell.weight = OBST.weight p q i (i+l) ∧
  (0 < l → i < cell.root ∧ cell.root ≤ i+l ∧
    cell.cost = bottomUpOBST p q i (cell.root-1) +
      bottomUpOBST p q cell.root (i+l) + OBST.weight p q i (i+l))

private theorem weight_succ (p q : Nat → Nat) (i l : Nat) :
    OBST.weight p q i (i+l+1) = OBST.weight p q i (i+l) + p (i+l+1) + q (i+l+1) := by
  unfold OBST.weight
  rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
  ring

private theorem candidate_correct (p q : Nat → Nat) (N l i : Nat)
    (rows : Array (Array Cell))
    (hprev : ∀ k, k < l → ∀ i, i < N+1-k → CorrectCell p q k i (get rows k i))
    (hi : i < N+1-l) (r : Nat) (hr : i < r) (hr' : r ≤ i+l) :
    candidate rows i l (OBST.weight p q i (i+l)) r =
      bottomUpOBST p q i (r-1) + bottomUpOBST p q r (i+l) + OBST.weight p q i (i+l) := by
  have hleft := (hprev (r-1-i) (by omega) i (by omega)).1
  have hright := (hprev (i+l-r) (by omega) r (by omega)).1
  have he : i+(r-1-i) = r-1 := by omega
  have he' : r+(i+l-r) = i+l := by omega
  rw [he] at hleft
  rw [he'] at hright
  simp only [candidate, hleft, hright]

private theorem step_correct (p q : Nat → Nat) (N l : Nat)
    (rows : Array (Array Cell))
    (hprev : ∀ k, k < l → ∀ i, i < N+1-k → CorrectCell p q k i (get rows k i))
    (i : Nat) (hi : i < N+1-l) : CorrectCell p q l i (step p q l rows i).1 := by
  cases l with
  | zero =>
      change q i = bottomUpOBST p q i (i+0) ∧ q i = OBST.weight p q i (i+0) ∧ _
      refine ⟨by simpa using ((bottomUpOBST_obstRecurrence p q).1 i).symm, ?_, by simp⟩
      simp [OBST.weight]
  | succ l =>
      have hw : nextWeight p q rows i l = OBST.weight p q i (i+(l+1)) := by
        have h := (hprev l (by omega) i (by omega)).2.1
        simp only [nextWeight, h]
        simpa [Nat.add_assoc] using (weight_succ p q i l).symm
      have hc := candidate_correct p q N (l+1) i rows hprev hi
      let f := candidate rows i (l+1) (nextWeight p q rows i l)
      have hf (r : Nat) (hr : i < r) (hr' : r ≤ i+(l+1)) :
          f r = bottomUpOBST p q i (r-1) + bottomUpOBST p q r (i+(l+1)) +
            OBST.weight p q i (i+(l+1)) := by
        dsimp only [f]
        rw [hw]
        exact hc r hr hr'
      have hbest : (minimum f (i+1) l).value = bottomUpOBST p q i (i+(l+1)) := by
        apply minimum_value_eq
        · intro r hr hr'
          rw [hf r (by omega) (by omega), (bottomUpOBST_obstRecurrence p q).2 (by omega)]
          exact Finset.inf'_le _ (by simp [Finset.mem_Icc]; omega)
        · obtain ⟨hr, he⟩ := (obstRoot_optimal p q).2 (show i < i+(l+1) by omega)
          have hb := Finset.mem_Icc.mp hr
          refine ⟨obstRoot p q i (i+(l+1)), hb.1, by omega, ?_⟩
          exact (hf _ (by omega) hb.2).trans he.symm
      obtain ⟨hlo, hhi, heq, _⟩ := minimum_spec f (i+1) l
      change (minimum f (i+1) l).value = _ ∧ nextWeight p q rows i l = _ ∧
        (0 < l+1 → i < (minimum f (i+1) l).index ∧
          (minimum f (i+1) l).index ≤ i+(l+1) ∧ (minimum f (i+1) l).value = _)
      refine ⟨hbest, hw, fun _ => ⟨by omega, by omega, ?_⟩⟩
      exact heq.trans (hf _ (by omega) (by omega))

/-- Every stored cost/weight is correct, and its stored root attains the optimum. -/
theorem execute_get_correct (p q : Nat → Nat) (N l i : Nat)
    (hl : l ≤ N) (hi : i+l ≤ N) :
    CorrectCell p q l i (get (execute p q N).rows l i) := by
  apply buildLayers_property (fun l => N+1-l) (step p q) (CorrectCell p q)
    (fun l rows _ hp i hi => step_correct p q N l rows hp i hi) (N+1) l (by omega) i
      (by omega)

theorem execute_cost (p q : Nat → Nat) (N i j : Nat) (hij : i ≤ j) (hj : j ≤ N) :
    (get (execute p q N).rows (j-i) i).cost = bottomUpOBST p q i j := by
  have h := (execute_get_correct p q N (j-i) i (by omega) (by omega)).1
  simpa [Nat.add_sub_of_le hij] using h

@[simp] theorem step_visits (p q : Nat → Nat) (l : Nat) (rows : Array (Array Cell)) (i : Nat) :
    (step p q l rows i).2 = l := by cases l <;> simp [step]

theorem execute_cells (p q : Nat → Nat) (N : Nat) :
    (execute p q N).cellWrites = ∑ l ∈ Finset.range (N+1), (N+1-l) :=
  buildLayers_cellWrites _ _ _

theorem execute_candidateVisits (p q : Nat → Nat) (N : Nat) :
    (execute p q N).candidateVisits = ∑ l ∈ Finset.range (N+1), (N+1-l)*l :=
  buildLayers_candidateVisits _ id _ (step_visits p q) _

/-- Correctness of the finite stored table on its represented intervals. -/
def CorrectTable (p q : Nat → Nat) (N : Nat) (rows : Array (Array Cell)) : Prop :=
  ∀ l i, l ≤ N → i+l ≤ N → CorrectCell p q l i (get rows l i)

private theorem stored_root {p q : Nat → Nat} {N : Nat} {rows : Array (Array Cell)}
    (h : CorrectTable p q N rows) (i j : Nat) (hij : i < j) (hj : j ≤ N) :
    i < (get rows (j-i) i).root ∧ (get rows (j-i) i).root ≤ j ∧
    bottomUpOBST p q i j = bottomUpOBST p q i ((get rows (j-i) i).root-1) +
      bottomUpOBST p q (get rows (j-i) i).root j + OBST.weight p q i j := by
  have hc := h (j-i) i (by omega) (by omega)
  have hs := hc.2.2 (by omega)
  have he : i+(j-i) = j := by omega
  dsimp only [CorrectCell] at hc
  rw [he] at hc hs
  exact ⟨hs.1, hs.2.1, hc.1.symm.trans hs.2.2⟩

/-- Reconstruct solely by reading the stored root table. Correctness proofs are
erased and do not evaluate the independent optimum or its root selector. -/
def reconstruct (p q : Nat → Nat) (N : Nat) (rows : Array (Array Cell))
    (h : CorrectTable p q N rows) (i j : Nat) (hij : i ≤ j) (hj : j ≤ N) : BSTPlan i j :=
  if ht : i < j then
    let r := (get rows (j-i) i).root
    have hs := stored_root h i j ht hj
    BSTPlan.node r hs.1 hs.2.1
      (reconstruct p q N rows h i (r-1) (by omega) (by omega))
      (reconstruct p q N rows h r j hs.2.1 hj)
  else
    have he : i = j := by omega
    he ▸ BSTPlan.empty i
termination_by j-i

decreasing_by
  all_goals
    have _hs := stored_root h i j ht hj
    try dsimp only [r] at *
    omega

/-- Every node follows its stored root. -/
theorem reconstruct_reconstructed (p q : Nat → Nat) (N : Nat) (rows : Array (Array Cell))
    (h : CorrectTable p q N rows) (i j : Nat) (hij : i ≤ j) (hj : j ≤ N) :
    ReconstructedBy (fun i j => (get rows (j-i) i).root)
      (reconstruct p q N rows h i j hij hj) := by
  rw [reconstruct]
  split
  next ht =>
    have hs := stored_root h i j ht hj
    exact ⟨rfl,
      reconstruct_reconstructed p q N rows h i _ (by omega) (by omega),
      reconstruct_reconstructed p q N rows h _ j hs.2.1 hj⟩
  next ht =>
    have he : i = j := by omega
    subst j
    trivial
termination_by j-i

decreasing_by all_goals omega

/-- The reconstructed plan attains the independent expected-cost recurrence. -/
theorem reconstruct_cost (p q : Nat → Nat) (N : Nat) (rows : Array (Array Cell))
    (h : CorrectTable p q N rows) (i j : Nat) (hij : i ≤ j) (hj : j ≤ N) :
    expectedCost p q (reconstruct p q N rows h i j hij hj) = bottomUpOBST p q i j := by
  rw [reconstruct]
  split
  next ht =>
    have hs := stored_root h i j ht hj
    rw [expectedCost, reconstruct_cost p q N rows h i _ (by omega) (by omega),
      reconstruct_cost p q N rows h _ j hs.2.1 hj]
    exact hs.2.2.symm
  next ht =>
    have he : i = j := by omega
    subst j
    exact ((bottomUpOBST_obstRecurrence p q).1 i).symm
termination_by j-i

decreasing_by all_goals omega

/-- Build all three tables once, then reconstruct using that returned table. -/
def executePlan (p q : Nat → Nat) (N : Nat) : BSTPlan 0 N × Table Cell :=
  let table := execute p q N
  (reconstruct p q N table.rows (fun l i hl hi => execute_get_correct p q N l i hl hi)
    0 N (Nat.zero_le _) le_rfl, table)

/-- Optimality among every typed competitor, using only natural nonnegative weights. -/
theorem executePlan_correct (p q : Nat → Nat) (N : Nat) (other : BSTPlan 0 N) :
    expectedCost p q (executePlan p q N).1 ≤ expectedCost p q other := by
  have he := reconstruct_cost p q N (execute p q N).rows
    (fun l i hl hi => execute_get_correct p q N l i hl hi) 0 N (Nat.zero_le _) le_rfl
  change expectedCost p q (reconstruct p q N (execute p q N).rows _ 0 N _ _) ≤ _
  rw [he]
  apply obst_opt_le_planCost (opt := bottomUpOBST p q) ?_ other
  refine ⟨fun i => ((bottomUpOBST_obstRecurrence p q).1 i).le, ?_⟩
  intro i j r hij hr
  rw [(bottomUpOBST_obstRecurrence p q).2 hij]
  exact Finset.inf'_le _ hr

/-- Every actual interval-evaluation event is unique. -/
theorem execute_once (p q : Nat → Nat) (N : Nat) :
    (execute p q N).evaluatedStates.Nodup :=
  buildLayers_evaluatedStates_nodup _ _ _

/-- The actual evaluation trace covers exactly the valid interval states. -/
theorem execute_state_iff (p q : Nat → Nat) (N l i : Nat) :
    (l,i) ∈ (execute p q N).evaluatedStates ↔ i+l ≤ N := by
  rw [execute, buildLayers_evaluatedStates_mem]
  omega

/-- Quadratic storage from actual interval writes. -/
theorem execute_cells_le (p q : Nat → Nat) (N : Nat) :
    (execute p q N).cellWrites ≤ (N+1)^2 := by
  rw [execute_cells]
  exact interval_cells_le_square N

/-- Cubic bound on the actual candidate-scan counter. -/
theorem execute_candidateVisits_le (p q : Nat → Nat) (N : Nat) :
    (execute p q N).candidateVisits ≤ (N+1)^3 := by
  rw [execute_candidateVisits]
  exact interval_visits_le_cube N

/-- Reconstruction attains the cost stored in the same returned table. -/
theorem executePlan_cost (p q : Nat → Nat) (N : Nat) :
    expectedCost p q (executePlan p q N).1 =
      (get (executePlan p q N).2.rows N 0).cost := by
  dsimp only [executePlan]
  rw [reconstruct_cost]
  simpa using (execute_cost p q N 0 N (Nat.zero_le _) le_rfl).symm

/-- Exact quadratic count of stored interval cells. -/
theorem execute_cells_closed (p q : Nat → Nat) (N : Nat) :
    2 * (execute p q N).cellWrites = (N+1)*(N+2) := by
  rw [execute_cells]
  exact interval_cells_closed N

/-- Exact cubic count of executed candidates. -/
theorem execute_candidateVisits_closed (p q : Nat → Nat) (N : Nat) :
    6 * (execute p q N).candidateVisits = N*(N+1)*(N+2) := by
  rw [execute_candidateVisits]
  exact interval_visits_closed N

/-- Two-sided quadratic storage bounds, including the diagonal boundary. -/
theorem execute_cells_bounds (p q : Nat → Nat) (N : Nat) :
    (N+1)^2 ≤ 2 * (execute p q N).cellWrites ∧
      (execute p q N).cellWrites ≤ (N+1)^2 := by
  refine ⟨?_, execute_cells_le p q N⟩
  rw [execute_cells_closed]
  nlinarith

/-- Two-sided cubic candidate bounds. -/
theorem execute_candidateVisits_bounds (p q : Nat → Nat) (N : Nat) :
    N^3 ≤ 6 * (execute p q N).candidateVisits ∧
      (execute p q N).candidateVisits ≤ (N+1)^3 := by
  refine ⟨?_, execute_candidateVisits_le p q N⟩
  rw [execute_candidateVisits_closed]
  nlinarith [sq_nonneg (N : ℤ)]

end CLRS.Chapter15.OBST.Execution

import CLRSLean.FourthEdition.Chapter_14.Section_14_2_Matrix_Chain_Multiplication
import CLRSLean.FourthEdition.Chapter_14.Section_14_3_Elements_Of_Dynamic_Programming.Execution

/-!
# Stored matrix-chain costs and splits

The endpoint N denotes matrices indexed 0 through N, hence N+1 matrices.
Layer l stores intervals {lit}`[i,i+l]`; only shorter layers are read. Every split
candidate is evaluated once, and its minimizing index is stored with its cost.
The old recursive optimum is used only in proofs.
-/

namespace CLRS.Chapter15.MatrixChainExecution
open DPExecution

structure Cell where
  cost : Nat
  split : Nat
  deriving Inhabited, Repr, DecidableEq

def candidate (dims : Nat → Nat) (rows : Array (Array Cell))
    (i l k : Nat) : Nat :=
  (get rows (k-i) i).cost + (get rows (i+l-(k+1)) (k+1)).cost +
    dims i * dims (k+1) * dims (i+l+1)

def step (dims : Nat → Nat) : Nat → Array (Array Cell) → Nat → Cell × Nat
  | 0, _, i => (⟨0, i⟩, 0)
  | l+1, rows, i =>
      let best := minimum (candidate dims rows i (l+1)) i l
      (⟨best.value, best.index⟩, best.visits)

/-- Compute and retain all intervals 0≤i≤j≤N. -/
def execute (dims : Nat → Nat) (N : Nat) : Table Cell :=
  buildLayers (fun l => N+1-l) (step dims) (N+1)

/-- The stored split is in range and attains the independently defined optimum. -/
def CorrectCell (dims : Nat → Nat) (l i : Nat) (cell : Cell) : Prop :=
  cell.cost = matrixChainOpt dims i (i+l) ∧
  (0 < l → i ≤ cell.split ∧ cell.split < i+l ∧
    cell.cost = matrixSplitCost dims (matrixChainOpt dims) i (i+l) cell.split)

private theorem candidate_correct (dims : Nat → Nat) (N l i : Nat)
    (rows : Array (Array Cell))
    (hprev : ∀ k, k < l → ∀ i, i < N+1-k → CorrectCell dims k i (get rows k i))
    (hi : i < N+1-l) (k : Nat) (hk : i ≤ k) (hk' : k < i+l) :
    candidate dims rows i l k = matrixSplitCost dims (matrixChainOpt dims) i (i+l) k := by
  have hleft := (hprev (k-i) (by omega) i (by omega)).1
  have hright := (hprev (i+l-(k+1)) (by omega) (k+1) (by omega)).1
  have he : i + (k-i) = k := by omega
  have he' : k+1+(i+l-(k+1)) = i+l := by omega
  rw [he] at hleft
  rw [he'] at hright
  simp only [candidate, matrixSplitCost, hleft, hright]

private theorem step_correct (dims : Nat → Nat) (N l : Nat)
    (rows : Array (Array Cell))
    (hprev : ∀ k, k < l → ∀ i, i < N+1-k → CorrectCell dims k i (get rows k i))
    (i : Nat) (hi : i < N+1-l) : CorrectCell dims l i (step dims l rows i).1 := by
  cases l with
  | zero =>
      simp [CorrectCell, step, matrixChainOpt]
  | succ l =>
      have hc := candidate_correct dims N (l+1) i rows hprev hi
      let f := candidate dims rows i (l+1)
      have hbest : (minimum f i l).value = matrixChainOpt dims i (i+(l+1)) := by
        apply minimum_value_eq
        · intro k hk hk'
          dsimp only [f]
          rw [hc k hk (by omega)]
          exact (matrixChainOpt_lowerBound dims).2 (by simp [Finset.mem_Icc]; omega)
        · obtain ⟨hk, heq⟩ := matrixChainSplit_optimal dims i (i+(l+1)) (by omega)
          have hb := Finset.mem_Icc.mp hk
          refine ⟨matrixChainSplit dims i (i+(l+1)), hb.1, by omega, ?_⟩
          exact (hc _ hb.1 (by omega)).trans heq.symm
      obtain ⟨hlo, hhi, heq, _⟩ := minimum_spec f i l
      change (minimum f i l).value = _ ∧
        (0 < l+1 → i ≤ (minimum f i l).index ∧ (minimum f i l).index < i+(l+1) ∧
          (minimum f i l).value = _)
      refine ⟨hbest, fun _ => ⟨hlo, by omega, ?_⟩⟩
      exact heq.trans (hc _ hlo (by omega))

/-- Every stored entry is the optimum, with a valid tight stored split. -/
theorem execute_get_correct (dims : Nat → Nat) (N l i : Nat)
    (hl : l ≤ N) (hi : i+l ≤ N) :
    CorrectCell dims l i (get (execute dims N).rows l i) := by
  apply buildLayers_property (fun l => N+1-l) (step dims) (CorrectCell dims)
    (fun l rows _ hp i hi => step_correct dims N l rows hp i hi) (N+1) l (by omega) i
      (by omega)

/-- A direct cost-table refinement for interval {lit}`[i,j]`. -/
theorem execute_cost (dims : Nat → Nat) (N i j : Nat) (hij : i ≤ j) (hj : j ≤ N) :
    (get (execute dims N).rows (j-i) i).cost = matrixChainOpt dims i j := by
  have h := (execute_get_correct dims N (j-i) i (by omega) (by omega)).1
  simpa [Nat.add_sub_of_le hij] using h

@[simp] theorem step_visits (dims : Nat → Nat) (l : Nat) (rows : Array (Array Cell)) (i : Nat) :
    (step dims l rows i).2 = l := by cases l <;> simp [step]

/-- Each interval cell is written once by the actual layered execution. -/
theorem execute_cells (dims : Nat → Nat) (N : Nat) :
    (execute dims N).cellWrites = ∑ l ∈ Finset.range (N+1), (N+1-l) :=
  buildLayers_cellWrites _ _ _

/-- Candidate visits come from the returned minimum-scan counters. -/
theorem execute_candidateVisits (dims : Nat → Nat) (N : Nat) :
    (execute dims N).candidateVisits = ∑ l ∈ Finset.range (N+1), (N+1-l)*l :=
  buildLayers_candidateVisits _ id _ (step_visits dims) _

/-- A finite stored table has the certified cost/split contract on its domain. -/
def CorrectTable (dims : Nat → Nat) (N : Nat) (rows : Array (Array Cell)) : Prop :=
  ∀ l i, l ≤ N → i+l ≤ N → CorrectCell dims l i (get rows l i)

private theorem stored_split {dims : Nat → Nat} {N : Nat} {rows : Array (Array Cell)}
    (h : CorrectTable dims N rows) (i j : Nat) (hij : i < j) (hj : j ≤ N) :
    i ≤ (get rows (j-i) i).split ∧ (get rows (j-i) i).split < j ∧
    matrixChainOpt dims i j =
      matrixSplitCost dims (matrixChainOpt dims) i j (get rows (j-i) i).split := by
  have hc := h (j-i) i (by omega) (by omega)
  have hs := hc.2 (by omega)
  have he : i+(j-i) = j := by omega
  dsimp only [CorrectCell] at hc
  rw [he] at hc hs
  exact ⟨hs.1, hs.2.1, hc.1.symm.trans hs.2.2⟩

/-- Reconstruct using stored indices only. The finite-domain proof is erased;
no recursive optimum or legacy split selector is evaluated here. -/
def reconstruct (dims : Nat → Nat) (N : Nat) (rows : Array (Array Cell))
    (h : CorrectTable dims N rows) (i j : Nat) (hij : i ≤ j) (hj : j ≤ N) : ChainPlan i j :=
  if ht : i < j then
    let k := (get rows (j-i) i).split
    have hs := stored_split h i j ht hj
    ChainPlan.split i k j
      (reconstruct dims N rows h i k hs.1 (by omega))
      (reconstruct dims N rows h (k+1) j (by omega) hj)
  else
    have he : i = j := by omega
    he ▸ ChainPlan.single i
termination_by j-i

decreasing_by
  all_goals
    have _hs := stored_split h i j ht hj
    try dsimp only [k] at *
    omega

/-- The plan follows the stored split in every subinterval. -/
theorem reconstruct_reconstructed (dims : Nat → Nat) (N : Nat) (rows : Array (Array Cell))
    (h : CorrectTable dims N rows) (i j : Nat) (hij : i ≤ j) (hj : j ≤ N) :
    ChainPlan.ReconstructedBy (fun i j => (get rows (j-i) i).split)
      (reconstruct dims N rows h i j hij hj) := by
  rw [reconstruct]
  split
  next ht =>
    have hs := stored_split h i j ht hj
    exact ChainPlan.ReconstructedBy.split i _ j rfl
      (reconstruct_reconstructed dims N rows h i _ hs.1 (by omega))
      (reconstruct_reconstructed dims N rows h _ j (by omega) hj)
  next ht =>
    have he : i = j := by omega
    subst j
    exact ChainPlan.ReconstructedBy.single i
termination_by j-i

decreasing_by
  all_goals
    omega

/-- Stored-table reconstruction attains the independent optimum. -/
theorem reconstruct_cost (dims : Nat → Nat) (N : Nat) (rows : Array (Array Cell))
    (h : CorrectTable dims N rows) (i j : Nat) (hij : i ≤ j) (hj : j ≤ N) :
    ChainPlan.cost dims (reconstruct dims N rows h i j hij hj) = matrixChainOpt dims i j := by
  rw [reconstruct]
  split
  next ht =>
    have hs := stored_split h i j ht hj
    rw [ChainPlan.cost, reconstruct_cost dims N rows h i _ hs.1 (by omega),
      reconstruct_cost dims N rows h _ j (by omega) hj]
    exact hs.2.2.symm
  next ht =>
    have he : i = j := by omega
    subst j
    simp [ChainPlan.cost, matrixChainOpt]
termination_by j-i

decreasing_by
  all_goals
    omega

/-- Build a table once and reconstruct the complete chain from that same table. -/
def executePlan (dims : Nat → Nat) (N : Nat) : ChainPlan 0 N × Table Cell :=
  let table := execute dims N
  (reconstruct dims N table.rows (fun l i hl hi => execute_get_correct dims N l i hl hi)
    0 N (Nat.zero_le _) le_rfl, table)

theorem executePlan_correct (dims : Nat → Nat) (N : Nat) :
    MatrixChainOptimalPlan dims (executePlan dims N).1 := by
  intro other
  have he := reconstruct_cost dims N (execute dims N).rows
    (fun l i hl hi => execute_get_correct dims N l i hl hi) 0 N (Nat.zero_le _) le_rfl
  change ChainPlan.cost dims (reconstruct dims N (execute dims N).rows _ 0 N _ _) ≤ _
  rw [he]
  exact matrixChain_opt_le_planCost (matrixChainOpt_lowerBound dims) other

/-- Every actual interval-evaluation event is unique. -/
theorem execute_once (dims : Nat → Nat) (N : Nat) :
    (execute dims N).evaluatedStates.Nodup :=
  buildLayers_evaluatedStates_nodup _ _ _

/-- The actual evaluation trace covers exactly the valid interval states. -/
theorem execute_state_iff (dims : Nat → Nat) (N l i : Nat) :
    (l,i) ∈ (execute dims N).evaluatedStates ↔ i+l ≤ N := by
  rw [execute, buildLayers_evaluatedStates_mem]
  omega

/-- Quadratic storage from actual interval writes. -/
theorem execute_cells_le (dims : Nat → Nat) (N : Nat) :
    (execute dims N).cellWrites ≤ (N+1)^2 := by
  rw [execute_cells]
  exact interval_cells_le_square N

/-- Cubic bound on the actual candidate-scan counter. -/
theorem execute_candidateVisits_le (dims : Nat → Nat) (N : Nat) :
    (execute dims N).candidateVisits ≤ (N+1)^3 := by
  rw [execute_candidateVisits]
  exact interval_visits_le_cube N

/-- The reconstructed plan's cost equals the optimum in the same returned table. -/
theorem executePlan_cost (dims : Nat → Nat) (N : Nat) :
    ChainPlan.cost dims (executePlan dims N).1 =
      (get (executePlan dims N).2.rows N 0).cost := by
  dsimp only [executePlan]
  rw [reconstruct_cost]
  simpa using (execute_cost dims N 0 N (Nat.zero_le _) le_rfl).symm

/-- Exact quadratic count of stored interval cells. -/
theorem execute_cells_closed (dims : Nat → Nat) (N : Nat) :
    2 * (execute dims N).cellWrites = (N+1)*(N+2) := by
  rw [execute_cells]
  exact interval_cells_closed N

/-- Exact cubic count of executed candidates. -/
theorem execute_candidateVisits_closed (dims : Nat → Nat) (N : Nat) :
    6 * (execute dims N).candidateVisits = N*(N+1)*(N+2) := by
  rw [execute_candidateVisits]
  exact interval_visits_closed N

/-- Two-sided quadratic storage bounds, including the diagonal boundary. -/
theorem execute_cells_bounds (dims : Nat → Nat) (N : Nat) :
    (N+1)^2 ≤ 2 * (execute dims N).cellWrites ∧
      (execute dims N).cellWrites ≤ (N+1)^2 := by
  refine ⟨?_, execute_cells_le dims N⟩
  rw [execute_cells_closed]
  nlinarith

/-- Two-sided cubic candidate bounds. -/
theorem execute_candidateVisits_bounds (dims : Nat → Nat) (N : Nat) :
    N^3 ≤ 6 * (execute dims N).candidateVisits ∧
      (execute dims N).candidateVisits ≤ (N+1)^3 := by
  refine ⟨?_, execute_candidateVisits_le dims N⟩
  rw [execute_candidateVisits_closed]
  nlinarith [sq_nonneg (N : ℤ)]

end CLRS.Chapter15.MatrixChainExecution

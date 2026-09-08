import CLRSLean.FourthEdition.Chapter_23.Section_23_3_Johnsons_Algorithm.Dijkstra
import CLRSLean.FourthEdition.Chapter_23.Section_23_3_Johnsons_Algorithm.Potential

/-!
# Stored Johnson execution with an indexed scan queue

Vertices are explicitly {lit}`Fin n`. The returned array retains one complete row per
source. Execution first materializes the augmented edge matrix, computes and caches
Bellman–Ford potentials, and materializes one reweighted matrix. Each source then
runs stored Dijkstra once and appends its restored row. No shortest-distance oracle
is called by the execution definitions.

The returned work is the sum of actual candidate visits, row evaluations/writes,
queue construction/settlements, and completed-row appends. In this indexed
real-operation model, the dense matrices and scan queue give a cubic upper bound.
Indexed array access, graph edge/weight queries, and real arithmetic are primitives;
Lean finite-set membership implementation, persistent-array copying,
bit complexity, and a binary-heap runtime are outside this model. Correctness
requires a graph with no negative cycle; no rejection API is implemented.
-/

noncomputable section
namespace CLRS.Chapter24.JohnsonExecution

/-- Execute one source, then materialize the restored original-weight row. -/
def sourceRow (prepared : Prepared n) (s : Fin n) : Vector × Nat :=
  let computed := dijkstraStored prepared.weights s
  let out := vector (fun v : Fin n =>
    (vecRead computed.1 v + vecRead prepared.potential v - vecRead prepared.potential s, 1))
  (out, computed.2 + out.writes + out.visits)

theorem sourceRow_work_le (prepared : Prepared n) (s : Fin n) :
    (sourceRow prepared s).2 ≤ 3 * n ^ 2 + 6 * n := by
  have hd := dijkstraStored_work_le prepared.weights s
  simp only [sourceRow, vector_writes]
  rw [vector_visits _ 1 (by intros; rfl)]
  nlinarith

theorem sourceRow_read (G : WeightedGraph (Fin n)) (hNC : G.NoNegCycle) (s v : Fin n) :
    vecRead (sourceRow (prepare G) s).1 v = G.johnsonAllPairsDist hNC s v := by
  let Gh := G.reweightedGraph (G.johnsonPotential hNC)
  have hnn : Gh.Nonneg := G.johnsonReweightedNonneg hNC
  let δ : Fin n → WithTop ℝ := fun v => Gh.relaxDist s (Fintype.card (Fin n) - 1) v
  have hδ : ∀ v, Gh.IsShortestDist s v (δ v) :=
    fun v => Gh.relaxDist_isShortestDist (Gh.noNegCycle_of_nonneg hnn) s v
  have hd := dijkstraStored_correct Gh (prepare G).weights (prepare_weights G hNC) hnn s δ hδ v
  have hl := Gh.dijkstraLoop_correct hnn s δ hδ n (by simp) v
  simp only [sourceRow, vector_read, prepare_potential G hNC, hd]
  simpa [WeightedGraph.johnsonAllPairsDist, Gh] using
    congrArg (fun d : WithTop ℝ => d + (G.johnsonPotential hNC v : WithTop ℝ) -
      (G.johnsonPotential hNC s : WithTop ℝ)) hl.symm

structure Result (n : Nat) where
  rows : Array Vector
  work : Nat

/-- Append one completed source row per iteration; the inner cell loop never reruns Dijkstra. -/
def sourceRows (prepared : Prepared n) : (k : Nat) → k ≤ n → Result n
  | 0, _ => ⟨#[], 0⟩
  | k + 1, hk =>
    let previous := sourceRows prepared k (by omega)
    let next := sourceRow prepared ⟨k, by omega⟩
    ⟨previous.rows.push next.1, previous.work + next.2 + 1⟩

@[simp] theorem sourceRows_size (prepared : Prepared n) (k : Nat) (hk : k ≤ n) :
    (sourceRows prepared k hk).rows.size = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [sourceRows, ih]

theorem sourceRows_get (prepared : Prepared n) (k : Nat) (hk : k ≤ n)
    (i : Nat) (hi : i < k) :
    (sourceRows prepared k hk).rows[i]? = some (sourceRow prepared ⟨i, by omega⟩).1 := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases he : i = k
    · subst i
      simp only [sourceRows, Array.getElem?_push, sourceRows_size, ite_true]
    · have hi' : i < k := by omega
      simp only [sourceRows, Array.getElem?_push]
      rw [sourceRows_size]
      simp only [he, if_false]
      exact ih (by omega) hi'

theorem sourceRows_work_le (prepared : Prepared n) (k : Nat) (hk : k ≤ n) :
    (sourceRows prepared k hk).work ≤ k * (3 * n ^ 2 + 6 * n + 1) := by
  induction k with
  | zero => simp [sourceRows]
  | succ k ih =>
    have hs := sourceRow_work_le prepared (⟨k, by omega⟩ : Fin n)
    have hp := ih (by omega)
    simp only [sourceRows]
    nlinarith

def read (result : Result n) (i j : Fin n) : WithTop ℝ :=
  ((result.rows[i.val]?).map (fun row => vecRead row j)).getD ⊤

/-- Stored Johnson execution for explicitly indexed vertices, with a scan priority queue. -/
def johnsonStored (G : WeightedGraph (Fin n)) : Result n :=
  let prepared := prepare G
  let rows := sourceRows prepared n (Nat.le_refl n)
  { rows with work := prepared.work + rows.work }

@[simp] theorem johnsonStored_size (G : WeightedGraph (Fin n)) :
    (johnsonStored G).rows.size = n := sourceRows_size _ _ _

theorem johnsonStored_read (G : WeightedGraph (Fin n)) (hNC : G.NoNegCycle) (i j : Fin n) :
    read (johnsonStored G) i j = G.johnsonAllPairsDist hNC i j := by
  simp only [read, johnsonStored, sourceRows_get _ n (Nat.le_refl n) i.val i.isLt,
    Option.map_some, Option.getD_some]
  exact sourceRow_read G hNC i j

theorem johnsonStored_correct (G : WeightedGraph (Fin n)) (hNC : G.NoNegCycle) (i j : Fin n) :
    G.IsShortestDist i j (read (johnsonStored G) i j) := by
  rw [johnsonStored_read G hNC]
  exact G.johnsonAllPairsDist_correct hNC i j

/-- Every source has its own retained, fully materialized row. -/
theorem johnsonStored_row (G : WeightedGraph (Fin n)) (i : Fin n) :
    (johnsonStored G).rows[i.val]? = some (sourceRow (prepare G) i).1 :=
  sourceRows_get _ n (Nat.le_refl n) i.val i.isLt

@[simp] theorem sourceRow_width (prepared : Prepared n) (s : Fin n) :
    (sourceRow prepared s).1.cells.size = n := by
  simp [sourceRow, vector]

/-- A specification bridge useful for finite examples, independent of Dijkstra tie choices. -/
theorem johnsonStored_eq_relaxDist (G : WeightedGraph (Fin n)) (hNC : G.NoNegCycle)
    (i j : Fin n) : read (johnsonStored G) i j = G.relaxDist i (n - 1) j := by
  have hs := johnsonStored_correct G hNC i j
  have hr : G.IsShortestDist i j (G.relaxDist i (n - 1) j) := by
    simpa using G.relaxDist_isShortestDist hNC i j
  have hle {a b : WithTop ℝ} (ha : G.IsShortestDist i j a)
      (hb : G.IsShortestDist i j b) : a ≤ b := by
    obtain ht | ⟨p, hp, hw⟩ := hb.2
    · rw [ht]; exact le_top
    · rw [← hw]; exact ha.1 p hp
  exact le_antisymm (hle hs hr) (hle hr hs)

theorem johnsonStored_work_le_polynomial (G : WeightedGraph (Fin n)) :
    (johnsonStored G).work ≤ 4 * n ^ 3 + 14 * n ^ 2 + 12 * n + 4 := by
  have hs := sourceRows_work_le (prepare G) n (Nat.le_refl n)
  simp only [johnsonStored, prepare_work]
  nlinarith

theorem johnsonStored_work_le (G : WeightedGraph (Fin n)) :
    (johnsonStored G).work ≤ 16 * (n + 1) ^ 3 := by
  have hs := johnsonStored_work_le_polynomial G
  nlinarith [Nat.zero_le (n ^ 3), Nat.zero_le (n ^ 2)]

end CLRS.Chapter24.JohnsonExecution

import CLRSLean.FourthEdition.Chapter_23.MatrixExecution.Basic
import CLRSLean.FourthEdition.Chapter_23.Section_23_3_Johnsons_Algorithm

/-!
# Stored rows and synchronous Bellman–Ford execution

Rows and edge tables are materialized before use. Every cell append and scanned
candidate contributes to a counter returned by the actual loops. Bellman–Ford
reads the previous stored row and a cached dense edge table; no recursive
relaxation oracle is called during a round. Exact real arithmetic, graph edge/weight queries, and indexed array access are
abstract primitives. The model excludes Lean finite-set membership implementation,
bit costs, and persistent-array copying.
-/

noncomputable section
namespace CLRS.Chapter24.JohnsonExecution
open CLRS.Chapter15.DPExecution
open MatrixExecution (Stored)

abbrev Vector := Row (WithTop ℝ)

def vecRead (row : Vector) (i : Fin n) : WithTop ℝ := row.cells[i.val]?.getD ⊤

def vector (f : Fin n → WithTop ℝ × Nat) : Vector :=
  buildRow (fun i => if hi : i < n then f ⟨i, hi⟩ else (⊤, 0)) n

@[simp] theorem vector_read (f : Fin n → WithTop ℝ × Nat) (i : Fin n) :
    vecRead (vector f) i = (f i).1 := by
  simp [vecRead, vector, i.isLt]

@[simp] theorem vector_writes (f : Fin n → WithTop ℝ × Nat) : (vector f).writes = n := by
  simp [vector]

theorem vector_visits (f : Fin n → WithTop ℝ × Nat) (c : Nat) (hc : ∀ i, (f i).2 = c) :
    (vector f).visits = n * c := by
  rw [vector, buildRow_visits]
  calc
    _ = ∑ _i ∈ Finset.range n, c := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [Finset.mem_range.mp hi, hc]
    _ = _ := by simp

variable {V : Type} [Fintype V] [DecidableEq V]

def edgeTable (G : WeightedGraph V) (e : Fin n ≃ V) : Stored :=
  MatrixExecution.tabulate (fun i j => (if (e i, e j) ∈ G.edges then (G.w (e i) (e j) : WithTop ℝ) else ⊤, 1))

@[simp] theorem edgeTable_read (G : WeightedGraph V) (e : Fin n ≃ V) (i j : Fin n) :
    MatrixExecution.read (edgeTable G e) i j =
      if (e i, e j) ∈ G.edges then (G.w (e i) (e j) : WithTop ℝ) else ⊤ := by
  simp [edgeTable]

@[simp] theorem edgeTable_writes (G : WeightedGraph V) (e : Fin n ≃ V) :
    (edgeTable G e).cellWrites = n * n := MatrixExecution.tabulate_writes _

@[simp] theorem edgeTable_visits (G : WeightedGraph V) (e : Fin n ≃ V) :
    (edgeTable G e).candidateVisits = n * n := by
  simpa [edgeTable] using MatrixExecution.tabulate_visits
    (fun i j : Fin n => (if (e i, e j) ∈ G.edges then (G.w (e i) (e j) : WithTop ℝ) else ⊤, 1)) 1
    (by intros; rfl)

def bfRound (weights : Stored) (prev : Vector) (n : Nat) : Vector :=
  vector (fun v : Fin n =>
    let candidates := MatrixExecution.scanFin (fun u : Fin n =>
      vecRead prev u + MatrixExecution.read weights u v)
    (min (vecRead prev v) candidates.1, candidates.2 + 1))

@[simp] theorem bfRound_writes (weights : Stored) (prev : Vector) (n : Nat) :
    (bfRound weights prev n).writes = n := vector_writes _

@[simp] theorem bfRound_visits (weights : Stored) (prev : Vector) (n : Nat) :
    (bfRound weights prev n).visits = n * (n + 1) := by
  apply vector_visits
  intro i
  simp

omit [DecidableEq V] in
private theorem inf_fin_equiv (e : Fin n ≃ V) (f : V → WithTop ℝ) :
    Finset.univ.inf (fun i : Fin n => f (e i)) = Finset.univ.inf f := by
  apply le_antisymm
  · apply Finset.le_inf
    intro v _
    simpa using (Finset.inf_le (s := Finset.univ) (f := fun i : Fin n => f (e i))
      (Finset.mem_univ (e.symm v)))
  · apply Finset.le_inf
    intro i _
    exact Finset.inf_le (Finset.mem_univ (e i))

theorem bfRound_read (G : WeightedGraph V) (e : Fin n ≃ V) (weights : Stored)
    (hw : ∀ i j, MatrixExecution.read weights i j =
      if (e i, e j) ∈ G.edges then (G.w (e i) (e j) : WithTop ℝ) else ⊤)
    (prev : Vector) (d : V → WithTop ℝ) (hd : ∀ i, vecRead prev i = d (e i)) (v : Fin n) :
    vecRead (bfRound weights prev n) v = G.relaxStep d (e v) := by
  simp only [bfRound, vector_read, MatrixExecution.scanFin_value, hd, hw]
  simp_rw [add_ite, add_top]
  rw [inf_fin_equiv e (fun u => if (u, e v) ∈ G.edges then d u + (G.w u (e v) : WithTop ℝ) else ⊤)]
  simp [WeightedGraph.relaxStep, WeightedGraph.preds, Finset.inf_ite]


def bfLoop (weights : Stored) (s : Fin n) : Nat → Vector × Nat
  | 0 =>
      let initial := vector (fun i : Fin n => (if i = s then 0 else ⊤, 1))
      (initial, initial.writes + initial.visits)
  | k + 1 =>
      let prev := bfLoop weights s k
      let next := bfRound weights prev.1 n
      (next, prev.2 + next.writes + next.visits)

theorem bfLoop_read (G : WeightedGraph V) (e : Fin n ≃ V) (weights : Stored)
    (hw : ∀ i j, MatrixExecution.read weights i j =
      if (e i, e j) ∈ G.edges then (G.w (e i) (e j) : WithTop ℝ) else ⊤)
    (s : Fin n) (k : Nat) (v : Fin n) :
    vecRead (bfLoop weights s k).1 v = G.relaxDist (e s) k (e v) := by
  induction k generalizing v with
  | zero => simp [bfLoop, WeightedGraph.relaxDist, e.injective.eq_iff]
  | succ k ih =>
    change vecRead (bfRound weights (bfLoop weights s k).1 n) v = _
    rw [bfRound_read G e weights hw _ (G.relaxDist (e s) k) (fun i => ?_)]
    · rfl
    · exact ih i

@[simp] theorem bfLoop_work (weights : Stored) (s : Fin n) (k : Nat) :
    (bfLoop weights s k).2 = 2 * n + k * (n * (n + 2)) := by
  induction k with
  | zero =>
    simp only [bfLoop, vector_writes]
    rw [vector_visits _ 1 (by intros; rfl)]
    omega
  | succ k ih =>
    simp only [bfLoop, bfRound_writes, bfRound_visits, ih]
    ring

end CLRS.Chapter24.JohnsonExecution

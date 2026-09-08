import CLRSLean.FourthEdition.Chapter_23.MatrixExecution.Basic
import CLRSLean.FourthEdition.Chapter_23.Section_23_2_Floyd_Warshall.NegativeCycle

/-!
# Counted stored Floyd–Warshall and repeated squaring

Each recursive call is bound once. A Floyd phase reads the completed previous
matrix and writes the next matrix; a squaring phase calls the counted min-plus
product. Cumulative counters include initialization. No recursive specification
is invoked by a cell evaluator.
-/
noncomputable section
namespace CLRS.Chapter24.MatrixExecution

structure Run where
  table : Stored
  writes : Nat
  visits : Nat

def initialRun (f : Fin n → Fin n → WithTop ℝ) : Run :=
  let t := tabulate (fun i j => (f i j, 0))
  ⟨t, t.cellWrites, t.candidateVisits⟩

@[simp] theorem initialRun_read (f : Fin n → Fin n → WithTop ℝ) (i j : Fin n) :
    read (initialRun f).table i j = f i j := tabulate_read _ _ _

@[simp] theorem initialRun_writes (f : Fin n → Fin n → WithTop ℝ) :
    (initialRun f).writes = n * n := tabulate_writes _

@[simp] theorem initialRun_visits (f : Fin n → Fin n → WithTop ℝ) :
    (initialRun f).visits = 0 := by
  change (tabulate (fun i j => (f i j, 0))).candidateVisits = 0
  rw [tabulate_visits _ 0 (by intros; rfl)]
  simp

def floyd (initial : Fin n → Fin n → WithTop ℝ) : List (Fin n) → Run
  | [] => initialRun initial
  | k :: ks =>
    let prev := floyd initial ks
    let next := tabulate (fun i j =>
      (min (read prev.table i j) (read prev.table i k + read prev.table k j), 1))
    ⟨next, prev.writes + next.cellWrites, prev.visits + next.candidateVisits⟩

theorem floyd_read (initial : Fin n → Fin n → WithTop ℝ) (ks : List (Fin n))
    (i j : Fin n) :
    read (floyd initial ks).table i j = WeightedGraph.floydFrom initial ks i j := by
  induction ks generalizing i j with
  | nil => exact initialRun_read _ _ _
  | cons k ks ih => simp only [floyd, tabulate_read, WeightedGraph.floydFrom, ih]

@[simp] theorem floyd_writes (initial : Fin n → Fin n → WithTop ℝ) (ks : List (Fin n)) :
    (floyd initial ks).writes = (ks.length + 1) * (n * n) := by
  induction ks with
  | nil => simp [floyd]
  | cons k ks ih => simp [floyd, ih, Nat.add_mul]

@[simp] theorem floyd_visits (initial : Fin n → Fin n → WithTop ℝ) (ks : List (Fin n)) :
    (floyd initial ks).visits = ks.length * (n * n) := by
  induction ks with
  | nil => simp [floyd]
  | cons k ks ih =>
    simp only [floyd, List.length_cons]
    rw [ih, tabulate_visits _ 1 (by intros; rfl)]
    ring

def square (initial : Fin n → Fin n → WithTop ℝ) : Nat → Run
  | 0 => initialRun initial
  | q + 1 =>
    let prev := square initial q
    let next := multiply n prev.table prev.table
    ⟨next, prev.writes + next.cellWrites, prev.visits + next.candidateVisits⟩

theorem square_read (initial : Fin n → Fin n → WithTop ℝ) (q : Nat) :
    (read (square initial q).table : Fin n → Fin n → WithTop ℝ) =
      (fun a => WeightedGraph.minPlusMul a a)^[q] initial := by
  induction q with
  | zero => funext i j; exact initialRun_read _ _ _
  | succ q ih =>
    funext i j
    simp only [square, multiply_read, Function.iterate_succ_apply', ih]

@[simp] theorem square_writes (initial : Fin n → Fin n → WithTop ℝ) (q : Nat) :
    (square initial q).writes = (q + 1) * (n * n) := by
  induction q with
  | zero => simp [square]
  | succ q ih => simp [square, ih, Nat.add_mul]

@[simp] theorem square_visits (initial : Fin n → Fin n → WithTop ℝ) (q : Nat) :
    (square initial q).visits = q * n ^ 3 := by
  induction q with
  | zero => simp [square]
  | succ q ih => simp [square, ih, Nat.add_mul]

/-- Cycle-safe stored Floyd execution, including negative self-edges. -/
def cycleFloyd (G : WeightedGraph (Fin n)) : Run :=
  floyd G.cycleWeightMatrix Finset.univ.toList

@[simp] theorem cycleFloyd_read (G : WeightedGraph (Fin n)) (i j : Fin n) :
    read (cycleFloyd G).table i j = G.cycleFloydWarshall i j := floyd_read _ _ _ _

/-- Exactly the counted Floyd cell update on every vertex pair and pivot. -/
@[simp] theorem cycleFloyd_visits (G : WeightedGraph (Fin n)) :
    (cycleFloyd G).visits = n ^ 3 := by
  simp [cycleFloyd, pow_succ, Nat.mul_assoc]

/-- Correctness of the actual stored output under the valid-input premise. -/
theorem cycleFloyd_shortest (G : WeightedGraph (Fin n)) (hNC : G.NoNegCycle) (i j : Fin n) :
    G.IsShortestDist i j (read (cycleFloyd G).table i j) := by
  rw [cycleFloyd_read, WeightedGraph.cycleFloydWarshall_eq_floydWarshall G hNC]
  exact G.floydWarshall_isShortestDist hNC i j

/-- The stored result detects a negative cycle in either direction. -/
theorem cycleFloyd_negative_iff (G : WeightedGraph (Fin n)) :
    (∃ i : Fin n, read (cycleFloyd G).table i i < 0) ↔ ¬ G.NoNegCycle := by
  simp only [cycleFloyd_read]
  exact G.cycleFloydWarshall_negative_iff

/-- Counted repeated squaring of the graph matrix. -/
def faster (G : WeightedGraph (Fin n)) : Run := square G.weightMatrix (WeightedGraph.numSquarings (V := Fin n))

@[simp] theorem faster_read (G : WeightedGraph (Fin n)) (i j : Fin n) :
    read (faster G).table i j = G.fasterAPSP i j := by
  change read (square G.weightMatrix (WeightedGraph.numSquarings (V := Fin n))).table i j = _
  rw [square_read]
  rfl

end CLRS.Chapter24.MatrixExecution

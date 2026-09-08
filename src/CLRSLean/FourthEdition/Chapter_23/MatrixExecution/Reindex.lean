import CLRSLean.FourthEdition.Chapter_23.MatrixExecution.Algorithms

/-!
# Finite-carrier interfaces for stored matrix execution

An explicit vertex/index equivalence supplies array indices. Its construction
is not included in the scalar-operation counters. The equivalence itself is
arbitrary; the refinement theorems relate results to the original graph.
-/
noncomputable section
namespace CLRS.Chapter24.MatrixExecution
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Encode a mathematical matrix with the caller's vertex enumeration. -/
def encode (e : V ≃ Fin n) (a : V → V → WithTop ℝ) : Fin n → Fin n → WithTop ℝ :=
  fun i j => a (e.symm i) (e.symm j)

omit [DecidableEq V] in
theorem encode_minPlus (e : V ≃ Fin n) (a b : V → V → WithTop ℝ) :
    WeightedGraph.minPlusMul (encode e a) (encode e b) =
      encode e (WeightedGraph.minPlusMul a b) := by
  funext i j
  apply le_antisymm
  · apply Finset.le_inf
    intro v _
    exact (Finset.inf_le (f := fun k => encode e a i k + encode e b k j)
      (Finset.mem_univ (e v))).trans_eq (by simp [encode])
  · apply Finset.le_inf
    intro k _
    exact Finset.inf_le (Finset.mem_univ (e.symm k))

omit [Fintype V] [DecidableEq V] in
theorem encode_floyd (e : V ≃ Fin n) (a : V → V → WithTop ℝ) (ks : List V) :
    WeightedGraph.floydFrom (encode e a) (ks.map e) =
      encode e (WeightedGraph.floydFrom a ks) := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    funext i j
    simp [List.map_cons, WeightedGraph.floydFrom, ih, encode]

def floydOn (e : V ≃ Fin n) (a : V → V → WithTop ℝ) (ks : List V) : Run :=
  floyd (encode e a) (ks.map e)

@[simp] theorem floydOn_read (e : V ≃ Fin n) (a : V → V → WithTop ℝ)
    (ks : List V) (i j : V) :
    read (floydOn e a ks).table (e i) (e j) = WeightedGraph.floydFrom a ks i j := by
  simp [floydOn, floyd_read, encode_floyd, encode]

def squareOn (e : V ≃ Fin n) (a : V → V → WithTop ℝ) (q : Nat) : Run :=
  square (encode e a) q

omit [DecidableEq V] in
theorem encode_square (e : V ≃ Fin n) (a : V → V → WithTop ℝ) (q : Nat) :
    (fun b => WeightedGraph.minPlusMul b b)^[q] (encode e a) =
      encode e ((fun b => WeightedGraph.minPlusMul b b)^[q] a) := by
  induction q with
  | zero => rfl
  | succ q ih => simp only [Function.iterate_succ_apply', ih, encode_minPlus]

@[simp] theorem squareOn_read (e : V ≃ Fin n) (a : V → V → WithTop ℝ) (q : Nat)
    (i j : V) : read (squareOn e a q).table (e i) (e j) =
      ((fun b => WeightedGraph.minPlusMul b b)^[q] a) i j := by
  simp [squareOn, square_read, encode_square, encode]

/-- Actual stored cycle-safe Floyd result over the original vertex type. -/
def cycleFloydOn (e : V ≃ Fin n) (G : WeightedGraph V) : Run :=
  floydOn e G.cycleWeightMatrix Finset.univ.toList

@[simp] theorem cycleFloydOn_read (e : V ≃ Fin n) (G : WeightedGraph V) (i j : V) :
    read (cycleFloydOn e G).table (e i) (e j) = G.cycleFloydWarshall i j :=
  floydOn_read _ _ _ _ _

theorem cycleFloydOn_shortest (e : V ≃ Fin n) (G : WeightedGraph V)
    (hNC : G.NoNegCycle) (i j : V) :
    G.IsShortestDist i j (read (cycleFloydOn e G).table (e i) (e j)) := by
  rw [cycleFloydOn_read, WeightedGraph.cycleFloydWarshall_eq_floydWarshall G hNC]
  exact G.floydWarshall_isShortestDist hNC i j

/-- Scan the actual stored diagonal, returning the minimum and visit count. -/
def diagonalScan (n : Nat) (t : Stored) : WithTop ℝ × Nat :=
  scanFin (fun i : Fin n => read t i i)

@[simp] theorem diagonalScan_visits (n : Nat) (t : Stored) :
    (diagonalScan n t).2 = n := scanFin_visits _

/-- The counted diagonal scan detects exactly the negative-cycle inputs. -/
theorem diagonalScan_negative_iff (e : V ≃ Fin n) (G : WeightedGraph V) :
    (diagonalScan n (cycleFloydOn e G).table).1 < 0 ↔ ¬ G.NoNegCycle := by
  rw [diagonalScan, scanFin_value, Finset.inf_lt_iff]
  have hex : (∃ i : Fin n, i ∈ Finset.univ ∧ read (cycleFloydOn e G).table i i < 0) ↔
      ∃ v, G.cycleFloydWarshall v v < 0 := by
    constructor
    · rintro ⟨i, _, hi⟩
      refine ⟨e.symm i, ?_⟩
      have heq := cycleFloydOn_read e G (e.symm i) (e.symm i)
      simp only [Equiv.apply_symm_apply] at heq
      exact heq ▸ hi
    · rintro ⟨v, hv⟩
      exact ⟨e v, Finset.mem_univ _, by simpa using hv⟩
  exact hex.trans G.cycleFloydWarshall_negative_iff

/-- Counted Floyd updates, excluding the separately counted final diagonal scan. -/
@[simp] theorem cycleFloydOn_visits (e : V ≃ Fin n) (G : WeightedGraph V) :
    (cycleFloydOn e G).visits = n ^ 3 := by
  have hcard : Fintype.card V = n := by simpa using Fintype.card_congr e
  simp [cycleFloydOn, floydOn, hcard, pow_succ, Nat.mul_assoc]

/-- Stored repeated squaring over the original graph carrier. -/
def fasterOn (e : V ≃ Fin n) (G : WeightedGraph V) : Run :=
  squareOn e G.weightMatrix (WeightedGraph.numSquarings (V := V))

@[simp] theorem fasterOn_read (e : V ≃ Fin n) (G : WeightedGraph V) (i j : V) :
    read (fasterOn e G).table (e i) (e j) = G.fasterAPSP i j := squareOn_read _ _ _ _ _

theorem fasterOn_shortest (e : V ≃ Fin n) (G : WeightedGraph V)
    (hNC : G.NoNegCycle) (i j : V) :
    G.IsShortestDist i j (read (fasterOn e G).table (e i) (e j)) := by
  rw [fasterOn_read]
  exact G.fasterAPSP_eq_shortestDist hNC ⟨i⟩ i j

@[simp] theorem fasterOn_visits (e : V ≃ Fin n) (G : WeightedGraph V) :
    (fasterOn e G).visits = WeightedGraph.numSquarings (V := V) * n ^ 3 := square_visits _ _

/-- The old Floyd budget is exactly the updates of this stored execution. -/
theorem cycleFloydOn_visits_eq_budget (e : V ≃ Fin n) (G : WeightedGraph V) :
    (cycleFloydOn e G).visits = G.floydWarshallCost := by
  have hc : Fintype.card V = n := by simpa using Fintype.card_congr e
  rw [cycleFloydOn_visits, G.floydWarshall_O_cubed, hc]
  ring

/-- The old squaring budget is exactly the executed min-plus candidate visits. -/
theorem fasterOn_visits_eq_budget (e : V ≃ Fin n) (G : WeightedGraph V) :
    (fasterOn e G).visits = G.fasterAPSPCost := by
  have hc : Fintype.card V = n := by simpa using Fintype.card_congr e
  rw [fasterOn_visits]
  simp [WeightedGraph.fasterAPSPCost, WeightedGraph.minPlusMulCost, hc, pow_succ, Nat.mul_assoc]

end CLRS.Chapter24.MatrixExecution

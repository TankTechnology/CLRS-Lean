import CLRSLean.FourthEdition.Chapter_23.Section_23_3_Johnsons_Algorithm.Storage

/-!
Stored Johnson preprocessing: materialize the augmented edge matrix, execute
synchronous Bellman–Ford rounds, retain the potential vector, and materialize one
reweighted matrix. Correctness assumes absence of negative cycles; execution does
not implement a negative-cycle failure API. Counters use the indexed real-operation
model of the storage primitives.
-/

noncomputable section
namespace CLRS.Chapter24.JohnsonExecution
open MatrixExecution (Stored)


def potentialPhase (G : WeightedGraph (Fin n)) : Vector × Nat :=
  let e := finSuccEquiv n
  let weights := edgeTable G.johnsonAugmentedGraph e
  let relaxed := bfLoop weights (e.symm none) n
  let potential := vector (fun v : Fin n => (vecRead relaxed.1 (e.symm (some v)), 1))
  (potential, weights.cellWrites + weights.candidateVisits + relaxed.2 + potential.writes + potential.visits)


theorem potentialPhase_read (G : WeightedGraph (Fin n)) (hNC : G.NoNegCycle) (v : Fin n) :
    vecRead (potentialPhase G).1 v = (G.johnsonPotential hNC v : WithTop ℝ) := by
  unfold potentialPhase
  rw [vector_read, bfLoop_read G.johnsonAugmentedGraph (finSuccEquiv n) _
    (edgeTable_read G.johnsonAugmentedGraph (finSuccEquiv n))]
  simpa using (G.johnsonPotential_eq hNC v).symm


theorem potentialPhase_work (G : WeightedGraph (Fin n)) :
    (potentialPhase G).2 = 2 * (n + 1) ^ 2 + 2 * (n + 1) +
      n * ((n + 1) * (n + 3)) + 2 * n := by
  simp only [potentialPhase, edgeTable_writes, edgeTable_visits, bfLoop_work, vector_writes]
  rw [vector_visits _ 1 (by intros; rfl)]
  ring


def reweightTable (G : WeightedGraph (Fin n)) (potential : Vector) : Stored :=
  MatrixExecution.tabulate (fun u v : Fin n =>
    (if (u, v) ∈ G.edges then (G.w u v : WithTop ℝ) + vecRead potential u - vecRead potential v else ⊤, 1))

@[simp] theorem reweightTable_writes (G : WeightedGraph (Fin n)) (potential : Vector) :
    (reweightTable G potential).cellWrites = n * n := MatrixExecution.tabulate_writes _

@[simp] theorem reweightTable_visits (G : WeightedGraph (Fin n)) (potential : Vector) :
    (reweightTable G potential).candidateVisits = n * n := by
  unfold reweightTable
  simpa using MatrixExecution.tabulate_visits
    (fun u v : Fin n =>
      (if (u, v) ∈ G.edges then (G.w u v : WithTop ℝ) + vecRead potential u - vecRead potential v else ⊤, 1))
    1 (by intros; rfl)

structure Prepared (n : Nat) where
  potential : Vector
  weights : Stored
  work : Nat


def prepare (G : WeightedGraph (Fin n)) : Prepared n :=
  let potential := potentialPhase G
  let weights := reweightTable G potential.1
  ⟨potential.1, weights, potential.2 + weights.cellWrites + weights.candidateVisits⟩

@[simp] theorem prepare_potential (G : WeightedGraph (Fin n)) (hNC : G.NoNegCycle) (v : Fin n) :
    vecRead (prepare G).potential v = (G.johnsonPotential hNC v : WithTop ℝ) :=
  potentialPhase_read G hNC v


theorem prepare_weights (G : WeightedGraph (Fin n)) (hNC : G.NoNegCycle) (u v : Fin n) :
    MatrixExecution.read (prepare G).weights u v =
      if (u, v) ∈ (G.reweightedGraph (G.johnsonPotential hNC)).edges then
        ((G.reweightedGraph (G.johnsonPotential hNC)).w u v : WithTop ℝ) else ⊤ := by
  simp only [prepare, reweightTable, MatrixExecution.tabulate_read, potentialPhase_read G hNC]
  simp only [WeightedGraph.reweightedGraph, WeightedGraph.reweightedWeight]
  split <;> simp [WithTop.coe_add]


theorem prepare_work (G : WeightedGraph (Fin n)) :
    (prepare G).work = n ^ 3 + 8 * n ^ 2 + 11 * n + 4 := by
  simp only [prepare, potentialPhase_work, reweightTable_writes, reweightTable_visits]
  ring

end CLRS.Chapter24.JohnsonExecution

import CLRSLean.FourthEdition.Chapter_23.Section_23_3_Johnsons_Algorithm.Storage
import CLRSLean.FourthEdition.Chapter_23.Section_23_3_Johnsons_Algorithm.Queue
import CLRSLean.FourthEdition.Chapter_23.Section_23_3_Johnsons_Algorithm.DijkstraCore

/-!
Stored Dijkstra with a list scan queue. The accumulated work counts candidate visits,
row-cell evaluations and writes, queue construction, and successful settlements.
This indexed real-operation model treats array access and real arithmetic as primitive;
it does not claim a binary-heap bound or a bit-complexity bound.
-/

noncomputable section
namespace CLRS.Chapter24.JohnsonExecution
open MatrixExecution (Stored)

structure QueueState (n : Nat) where
  row : Vector
  queue : List (Fin n)

def view (st : QueueState n) : WeightedGraph.DijkstraState (Fin n) where
  S := Finset.univ \ st.queue.toFinset
  d := vecRead st.row

def initState (weights : Stored) (s : Fin n) : QueueState n × Nat :=
  let row := vector (fun v : Fin n => (if v = s then 0 else MatrixExecution.read weights s v, 1))
  let queue := initialQueue s n le_rfl
  (⟨row, queue.1⟩, row.writes + row.visits + queue.2)

@[simp] theorem initState_work (weights : Stored) (s : Fin n) :
    (initState weights s).2 = 3 * n := by
  simp only [initState, vector_writes, initialQueue_visits]
  rw [vector_visits _ 1 (by intros; rfl)]
  omega

@[simp] theorem initState_nodup (weights : Stored) (s : Fin n) :
    (initState weights s).1.queue.Nodup := initialQueue_nodup s n le_rfl

theorem initState_length_le (weights : Stored) (s : Fin n) :
    (initState weights s).1.queue.length ≤ n := initialQueue_length_le s n le_rfl

def MatrixCorrect (G : WeightedGraph (Fin n)) (weights : Stored) : Prop :=
  ∀ i j, MatrixExecution.read weights i j =
    if (i, j) ∈ G.edges then (G.w i j : WithTop ℝ) else ⊤

theorem initState_view (G : WeightedGraph (Fin n)) (weights : Stored) (hw : MatrixCorrect G weights)
    (s : Fin n) : view (initState weights s).1 = G.dijkstraInit s := by
  apply WeightedGraph.DijkstraState.ext
  · ext v
    simp [view, initState, initialQueue_mem, v.isLt, WeightedGraph.dijkstraInit]
  · funext v
    simp [view, initState, hw s v, WeightedGraph.dijkstraInit]

def relaxRow (weights : Stored) (row : Vector) (u : Fin n) : Vector :=
  vector (fun v : Fin n => (min (vecRead row v) (vecRead row u + MatrixExecution.read weights u v), 1))

@[simp] theorem relaxRow_writes (weights : Stored) (row : Vector) (u : Fin n) :
    (relaxRow weights row u).writes = n := vector_writes _

@[simp] theorem relaxRow_visits (weights : Stored) (row : Vector) (u : Fin n) :
    (relaxRow weights row u).visits = n := by
  simpa [relaxRow] using vector_visits (fun v : Fin n =>
    (min (vecRead row v) (vecRead row u + MatrixExecution.read weights u v), 1)) 1 (by intros; rfl)

def advance (weights : Stored) (st : QueueState n) (u : Fin n) (rest : List (Fin n)) : QueueState n :=
  ⟨relaxRow weights st.row u, rest⟩

theorem advance_view (G : WeightedGraph (Fin n)) (weights : Stored) (hw : MatrixCorrect G weights)
    (st : QueueState n) (hq : st.queue.Nodup) (u : Fin n) (rest : List (Fin n))
    (hp : st.queue.Perm (u :: rest)) :
    view (advance weights st u rest) = G.dijkstraSettle (view st) u := by
  have hnew := List.nodup_cons.mp (hp.nodup_iff.mp hq)
  apply WeightedGraph.DijkstraState.ext
  · ext v
    have hm : v ∈ st.queue ↔ v = u ∨ v ∈ rest := by simpa using hp.mem_iff
    simp only [view, advance, WeightedGraph.dijkstraSettle, Finset.mem_sdiff,
      Finset.mem_univ, List.mem_toFinset, true_and, Finset.mem_insert]
    rw [hm]
    by_cases hv : v = u
    · subst v; simp [hnew.1]
    · simp [hv]
  · funext v
    simp only [view, advance, relaxRow, vector_read, WeightedGraph.dijkstraSettle]
    rw [hw u v]
    by_cases he : (u, v) ∈ G.edges <;> simp [he]


def run (weights : Stored) : Nat → QueueState n → QueueState n × Nat
  | 0, st => (st, 0)
  | k + 1, st =>
      let found := extractMin (vecRead st.row) st.queue
      match found.1 with
      | none => (st, found.2)
      | some (u, rest) =>
          let next := advance weights st u rest
          let result := run weights k next
          (result.1, found.2 + next.row.writes + next.row.visits + 1 + result.2)


theorem run_invariant (G : WeightedGraph (Fin n)) (weights : Stored) (hw : MatrixCorrect G weights)
    (hnn : G.Nonneg) (s : Fin n) (δ : Fin n → WithTop ℝ)
    (hδ : ∀ v, G.IsShortestDist s v (δ v)) (k : Nat)
    (st : QueueState n) (hq : st.queue.Nodup)
    (hinv : G.DijkstraInvariant hnn s δ hδ (view st)) :
    G.DijkstraInvariant hnn s δ hδ (view (run weights k st).1) := by
  induction k generalizing st with
  | zero => exact hinv
  | succ k ih =>
    simp only [run]
    split
    · exact hinv
    · rename_i u rest he
      obtain ⟨hp, hm⟩ := extractMin_spec (vecRead st.row) st.queue he
      have hn := List.nodup_cons.mp (hp.nodup_iff.mp hq)
      apply ih _ hn.2
      rw [advance_view G weights hw st hq u rest hp]
      apply G.dijkstraSettle_invariant hnn s δ hδ (view st) hinv u
      · have hu : u ∈ st.queue := hp.mem_iff.mpr (by simp)
        simpa [view] using hu
      · intro v hv
        apply hm v
        simpa [view] using hv

theorem run_queue_empty (weights : Stored) (k : Nat) (st : QueueState n)
    (hlen : st.queue.length ≤ k) : (run weights k st).1.queue = [] := by
  induction k generalizing st with
  | zero => simpa [run] using hlen
  | succ k ih =>
    simp only [run]
    split
    · rename_i he
      exact (extractMin_none (vecRead st.row) st.queue).mp he
    · rename_i u rest he
      obtain ⟨hp, _⟩ := extractMin_spec (vecRead st.row) st.queue he
      have hl := hp.length_eq
      apply ih
      change rest.length ≤ k
      simp only [List.length_cons] at hl
      omega

theorem run_work_le (weights : Stored) (k : Nat) (st : QueueState n)
    (hlen : st.queue.length ≤ n) : (run weights k st).2 ≤ k * (3 * n + 1) := by
  induction k generalizing st with
  | zero => simp [run]
  | succ k ih =>
    simp only [run]
    split
    · simp only [extractMin_visits]
      nlinarith
    · rename_i u rest he
      obtain ⟨hp, _⟩ := extractMin_spec (vecRead st.row) st.queue he
      have hl := hp.length_eq
      have hr : rest.length ≤ n := by simp only [List.length_cons] at hl; omega
      have hind := ih (advance weights st u rest) hr
      simp only [advance] at hind
      simp only [extractMin_visits, advance, relaxRow_writes, relaxRow_visits]
      nlinarith


def dijkstraStored (weights : Stored) (s : Fin n) : Vector × Nat :=
  let initial := initState weights s
  let result := run weights n initial.1
  (result.1.row, initial.2 + result.2)

theorem dijkstraStored_correct (G : WeightedGraph (Fin n)) (weights : Stored)
    (hw : MatrixCorrect G weights) (hnn : G.Nonneg) (s : Fin n) (δ : Fin n → WithTop ℝ)
    (hδ : ∀ v, G.IsShortestDist s v (δ v)) (v : Fin n) :
    vecRead (dijkstraStored weights s).1 v = δ v := by
  have hi : G.DijkstraInvariant hnn s δ hδ (view (initState weights s).1) := by
    rw [initState_view G weights hw s]
    exact G.dijkstraInit_invariant hnn s δ hδ
  have hf := run_invariant G weights hw hnn s δ hδ n (initState weights s).1
    (initState_nodup weights s) hi
  have hq := run_queue_empty weights n (initState weights s).1 (initState_length_le weights s)
  exact hf.hsettled v (by simp [view, hq])

theorem dijkstraStored_work_le (weights : Stored) (s : Fin n) :
    (dijkstraStored weights s).2 ≤ 3 * n ^ 2 + 4 * n := by
  have hr := run_work_le weights n (initState weights s).1 (initState_length_le weights s)
  simp only [dijkstraStored, initState_work]
  nlinarith

end CLRS.Chapter24.JohnsonExecution

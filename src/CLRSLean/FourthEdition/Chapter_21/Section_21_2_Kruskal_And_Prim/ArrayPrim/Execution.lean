import CLRSLean.FourthEdition.Chapter_21.Section_21_2_Kruskal_And_Prim.ArrayPrim.Invariant

/-!
# Incremental array Prim execution

A single prepared index list is reused by all extraction scans. The graph is
supplied as stored adjacency lists satisfying `Adjacency.represents`.
Initialization writes the queue cells and the index-list cells; there is no
conversion from an unordered edge-set representation inside this algorithm.
Each successful extraction deactivates one cell and reads just that vertex's
adjacency row. The loop returns its chosen edges, final array, and counters.
-/
namespace CLRS.MST.ExecutablePrim.ArrayPrim
open Finset
variable {n : Nat} {E : Type} [LinearOrder E]

def indexPrefix (n : Nat) : Nat → List (Fin n) × Nat
  | 0 => ([], 0)
  | i + 1 =>
    let old := indexPrefix n i
    if h : i < n then (⟨i,h⟩ :: old.1, old.2 + 1) else old

theorem indexPrefix_spec (i : Nat) (hi : i ≤ n) :
    (indexPrefix n i).1.length = i ∧ (indexPrefix n i).2 = i ∧
      ∀ v : Fin n, v ∈ (indexPrefix n i).1 ↔ v.val < i := by
  induction i with
  | zero => simp [indexPrefix]
  | succ i ih =>
    have old := ih (by omega)
    have hin : i < n := by omega
    simp only [indexPrefix, hin, ↓reduceDIte, List.length_cons, old.1, old.2.1]
    refine ⟨trivial,trivial,?_⟩
    intro v
    simp only [List.mem_cons, old.2.2 v, Fin.ext_iff]
    omega

/-- The counters refer to queue cells, adjacency rows, comparisons, and visits. -/
structure Result (n : Nat) (E : Type) where
  edges : List E
  cells : Cells n E
  rounds : Nat
  extracts : Nat
  queueReads : Nat
  queueWrites : Nat
  comparisons : Nat
  edgeVisits : Nat
  adjacencyReads : Nat
  preparationWrites : Nat
  deriving Repr

def run {G : FiniteGraph (Fin n) E} (adj : Adjacency G) (w : E → Nat)
    (indices : List (Fin n)) : Nat → Cells n E → Result n E
  | 0, q => ⟨[],q,0,0,0,0,0,0,0,0⟩
  | fuel + 1, q =>
    let choice := scan q indices
    match choice.choice with
    | none => ⟨[],q,1,0,choice.reads,0,choice.comparisons,0,0,0⟩
    | some (u,c) =>
      match c.parent with
      | none => ⟨[],q,1,0,choice.reads,0,choice.comparisons,0,0,0⟩
      | some e =>
        let next := advance adj w q u
        let rest := run adj w indices fuel next.cells
        ⟨e :: rest.edges, rest.cells, rest.rounds + 1, rest.extracts + 1,
          choice.reads + 1 + next.edgeVisits + rest.queueReads,
          1 + next.writes + rest.queueWrites,
          choice.comparisons + next.tests + rest.comparisons,
          next.edgeVisits + rest.edgeVisits, rest.adjacencyReads + 1, 0⟩

/-- Start at the supplied root, scan its row, then allow n further extraction attempts. -/
def execute {G : FiniteGraph (Fin n) E} (adj : Adjacency G) (w : E → Nat)
    (root : Fin n) : Result n E :=
  let initial := initialCells (E := E) n
  let indices := indexPrefix n n
  let seed := advance adj w initial.1 root
  let rest := run adj w indices.1 n seed.cells
  { rest with
    extracts := rest.extracts + 1
    queueReads := 1 + seed.edgeVisits + rest.queueReads
    queueWrites := 1 + seed.writes + rest.queueWrites
    comparisons := seed.tests + rest.comparisons
    edgeVisits := seed.edgeVisits + rest.edgeVisits
    adjacencyReads := rest.adjacencyReads + 1
    preparationWrites := initial.2 + indices.2 }

/-- Active vertices are the remaining potential, weighted by any nonnegative cost. -/
def remaining (weight : Fin n → Nat) (q : Cells n E) : Nat :=
  ∑ v : Fin n, if (read q v).active then weight v else 0

omit [LinearOrder E] in
theorem remaining_deactivate (weight : Fin n → Nat) (q : Cells n E) (u : Fin n)
    (hu : (read q u).active = true) :
    remaining weight (deactivate q u) + weight u = remaining weight q := by
  have hnew := Finset.sum_erase_add (Finset.univ : Finset (Fin n))
    (fun v => if (read (deactivate q u) v).active then weight v else 0) (mem_univ u)
  have hold := Finset.sum_erase_add (Finset.univ : Finset (Fin n))
    (fun v => if (read q v).active then weight v else 0) (mem_univ u)
  have hs : (∑ v ∈ Finset.univ.erase u,
      if (read (deactivate q u) v).active then weight v else 0) =
      ∑ v ∈ Finset.univ.erase u, if (read q v).active then weight v else 0 := by
    apply Finset.sum_congr rfl
    intro v hv
    have huv : u ≠ v := (Finset.ne_of_mem_erase hv).symm
    simp [huv]
  rw [hs] at hnew
  simp only [deactivate_active, ↓reduceIte, Bool.false_eq_true, Nat.add_zero] at hnew
  simp only [hu, ↓reduceIte] at hold
  simp only [remaining, deactivate_active]
  omega

@[simp] theorem remaining_advance {G : FiniteGraph (Fin n) E} (adj : Adjacency G)
    (w : E → Nat) (weight : Fin n → Nat) (q : Cells n E) (u : Fin n) :
    remaining weight (advance adj w q u).cells = remaining weight (deactivate q u) := by
  simp [remaining, advance]

/-- A removed adjacency row is subtracted from the remaining scan potential. -/
theorem advance_remaining {G : FiniteGraph (Fin n) E} (adj : Adjacency G)
    (w : E → Nat) (q : Cells n E) (u : Fin n) (hu : (read q u).active = true) :
    remaining (fun v => (adj.rows[v.val]).length) (advance adj w q u).cells +
      (advance adj w q u).edgeVisits = remaining (fun v => (adj.rows[v.val]).length) q := by
  rw [remaining_advance]
  have hc := (relaxAll_counts w (deactivate q u) adj.rows[u.val]).1
  change remaining _ (deactivate q u) +
    (relaxAll w (deactivate q u) adj.rows[u.val]).edgeVisits = _
  rw [hc]
  exact remaining_deactivate _ q u hu

/-- The inequalities account for every counter emitted by the loop. -/
theorem run_counts {G : FiniteGraph (Fin n) E} (adj : Adjacency G) (w : E → Nat)
    (indices : List (Fin n)) (fuel : Nat) (q : Cells n E) :
    let r := run adj w indices fuel q
    r.rounds ≤ fuel ∧
    r.extracts + remaining (fun _ => 1) r.cells ≤ remaining (fun _ => 1) q ∧
    r.edgeVisits + remaining (fun v => (adj.rows[v.val]).length) r.cells ≤
      remaining (fun v => (adj.rows[v.val]).length) q ∧
    r.queueReads ≤ fuel * indices.length + r.extracts + r.edgeVisits ∧
    r.queueWrites ≤ r.extracts + r.edgeVisits ∧
    r.comparisons ≤ fuel * indices.length + r.edgeVisits ∧
    r.adjacencyReads = r.extracts ∧ r.preparationWrites = 0 := by
  induction fuel generalizing q with
  | zero => simp [run]
  | succ fuel ih =>
    have hc := scan_counts q indices
    simp only [run, Nat.add_mul, Nat.one_mul]
    split
    · simp only
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial, trivial⟩ <;> omega
    · rename_i u c hscan
      have hu := (scan_some q indices u c hscan).2.2.1
      have hcell := (scan_some q indices u c hscan).2.1
      rw [hcell] at hu
      split
      · simp only
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial, trivial⟩ <;> omega
      · have hi := ih (advance adj w q u).cells
        have hp := advance_remaining adj w q u hu
        have hv : remaining (fun _ => 1) (advance adj w q u).cells + 1 =
            remaining (fun _ => 1) q := by
          rw [remaining_advance]; exact remaining_deactivate _ q u hu
        have ha := relaxAll_counts w (deactivate q u) adj.rows[u.val]
        change (advance adj w q u).edgeVisits = _ ∧
          (advance adj w q u).tests ≤ _ ∧
          (advance adj w q u).writes ≤ (advance adj w q u).tests at ha
        simp only
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> omega

/-- The generated execution visits at most the input's two incidences per edge. -/
theorem execute_edgeVisits_le {G : FiniteGraph (Fin n) E} (adj : Adjacency G)
    (w : E → Nat) (root : Fin n) : (execute adj w root).edgeVisits ≤ 2 * G.edges.card := by
  have hc := (run_counts adj w (indexPrefix n n).1 n
    (advance adj w (initialCells n).1 root).cells).2.2.1
  have hs := advance_remaining adj w (initialCells (E := E) n).1 root (by simp)
  have ht : remaining (fun v => (adj.rows[v.val]).length) (initialCells (E := E) n).1 =
      2 * G.edges.card := by simp [remaining, adj.total_length]
  rw [ht] at hs
  simp only [execute]
  omega

/-- Each active vertex is extracted at most once, including the initial root. -/
theorem execute_extracts_le {G : FiniteGraph (Fin n) E} (adj : Adjacency G)
    (w : E → Nat) (root : Fin n) : (execute adj w root).extracts ≤ n := by
  have hc := (run_counts adj w (indexPrefix n n).1 n
    (advance adj w (initialCells n).1 root).cells).2.1
  have hs : remaining (fun _ => 1) (advance adj w (initialCells (E := E) n).1 root).cells + 1 = n := by
    rw [remaining_advance]
    simpa [remaining] using remaining_deactivate (fun _ => 1)
      (initialCells (E := E) n).1 root (by simp)
  simp only [execute]
  omega

/-- The actual work units include preparation, array reads/writes, and key comparisons. -/
def cellWork (r : Result n E) : Nat :=
  r.preparationWrites + r.queueReads + r.queueWrites + r.adjacencyReads + r.comparisons

theorem execute_cost_bound {G : FiniteGraph (Fin n) E} (adj : Adjacency G)
    (w : E → Nat) (root : Fin n) :
    cellWork (execute adj w root) ≤ 2 * n * n + 5 * n + 6 * G.edges.card := by
  have hi := indexPrefix_spec n (Nat.le_refl n)
  have hc := run_counts adj w (indexPrefix n n).1 n
    (advance adj w (initialCells n).1 root).cells
  have hs := relaxAll_counts w (deactivate (initialCells (E := E) n).1 root)
    adj.rows[root.val]
  have hr := advance_remaining adj w (initialCells (E := E) n).1 root (by simp)
  have hv : remaining (fun _ => 1) (advance adj w (initialCells (E := E) n).1 root).cells + 1 =
      remaining (fun _ => 1) (initialCells (E := E) n).1 := by
    rw [remaining_advance]; exact remaining_deactivate _ _ root (by simp)
  have hinit : remaining (fun _ => 1) (initialCells (E := E) n).1 = n := by
    simp [remaining]
  have htotal : remaining (fun v => (adj.rows[v.val]).length) (initialCells (E := E) n).1 =
      2 * G.edges.card := by simp [remaining, adj.total_length]
  change (advance adj w (initialCells n).1 root).edgeVisits = _ ∧
    (advance adj w (initialCells n).1 root).tests ≤ _ ∧
    (advance adj w (initialCells n).1 root).writes ≤
      (advance adj w (initialCells n).1 root).tests at hs
  rw [hinit] at hv
  rw [htotal] at hr
  simp only [cellWork, execute, initialCells_writes, hi.1, hi.2.1] at *
  nlinarith [hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2.1]

/-- When the finite index universe is exactly the graph vertices, the bound uses |V|. -/
theorem execute_cost_bound_vertices {G : FiniteGraph (Fin n) E} (adj : Adjacency G)
    (w : E → Nat) (root : Fin n) (hV : G.vertices = Finset.univ) :
    cellWork (execute adj w root) ≤
      2 * G.vertices.card * G.vertices.card + 5 * G.vertices.card + 6 * G.edges.card := by
  simpa [hV] using execute_cost_bound adj w root

end CLRS.MST.ExecutablePrim.ArrayPrim

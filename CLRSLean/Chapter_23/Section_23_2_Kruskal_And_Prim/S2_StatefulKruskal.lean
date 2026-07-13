import CLRSLean.Chapter_21
import CLRSLean.Chapter_23.Section_23_2_Kruskal_And_Prim

/-!
# Chapter 23 - Incremental costed Kruskal

This module refines the mathematical Kruskal pass to the real costed
`Batteries.UnionFind` machine proved correct in Chapter 21.  Vertices are
represented by `Fin n`, so every graph endpoint is directly usable as a
fixed-universe union-find node.

Each scanned edge performs one fused union operation.  Batteries union runs
the two required finds and links their roots only when they differ.  The
Boolean acceptance decision is taken from the pre-state partition; rejected
edges therefore retain path compression while leaving both the represented
partition and selected edge set unchanged.
-/

namespace CLRS
namespace MST

open Finset

variable {n : Nat} {E : Type} [DecidableEq E]

namespace Graph

/-- Connectivity after inserting one undirected edge has exactly the same
three-way relational form as a disjoint-set merge. -/
theorem connected_insert_edge_iff {G : Graph (Fin n) E} {A : Finset E}
    {e : E} {u v : Fin n} :
    G.ConnectedIn (insert e A) u v ↔
      G.ConnectedIn A u v ∨
        (G.ConnectedIn A u (G.src e) ∧
          G.ConnectedIn A (G.dst e) v) ∨
        (G.ConnectedIn A u (G.dst e) ∧
          G.ConnectedIn A (G.src e) v) := by
  constructor
  · exact connected_insert_edge_cases
  · intro h
    have hmono : A ⊆ insert e A := Finset.subset_insert e A
    rcases h with hbase | hbridge
    · exact connected_mono hmono hbase
    · have hedge : G.ConnectedIn (insert e A) (G.src e) (G.dst e) :=
        connected_of_mem_edge (Finset.mem_insert_self e A)
      rcases hbridge with ⟨hus, hdv⟩ | ⟨hud, hsv⟩
      · exact connected_trans (connected_mono hmono hus)
          (connected_trans hedge (connected_mono hmono hdv))
      · exact connected_trans (connected_mono hmono hud)
          (connected_trans (connected_symm hedge) (connected_mono hmono hsv))

/-- With no selected edges, graph connectivity is equality. -/
theorem connected_empty_iff {G : Graph (Fin n) E} {u v : Fin n} :
    G.ConnectedIn ∅ u v ↔ u = v := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail _ hadj _ =>
        rcases hadj with ⟨e, he, _⟩
        simp at he
  · rintro rfl
    exact connected_refl G ∅ u

end Graph

namespace StatefulKruskal

abbrev UFMachine (n : Nat) := Chapter21.Analysis.Costed.Machine n
abbrev UFOperation (n : Nat) := Chapter21.Analysis.Costed.Operation n

/-- Executable Kruskal state: the Chapter 21 machine, selected edges, and
accumulated concrete union-find work. -/
structure State (n : Nat) (E : Type) where
  machine : UFMachine n
  selected : Finset E
  cost : Nat

/-- The initial singleton forest and empty edge set. -/
def initial (n : Nat) (E : Type) [DecidableEq E] : State n E where
  machine := Chapter21.Analysis.Costed.Machine.initial n
  selected := ∅
  cost := 0

/-- The executable cycle decision in the pre-state partition. -/
def accepts (s : State n E) (G : Graph (Fin n) E) (e : E) : Bool :=
  !((s.machine.forest.checkEquiv
    (s.machine.node (G.src e)) (s.machine.node (G.dst e))).2)

/-- Concrete two-find cost of the executable `checkEquiv` cycle query. -/
def cycleQueryCost (s : State n E) (G : Graph (Fin n) E) (e : E) : Nat :=
  let x := s.machine.node (G.src e)
  let y := s.machine.node (G.dst e)
  Chapter21.Analysis.Costed.findEdges s.machine.forest x +
    Chapter21.Analysis.Costed.findEdges (s.machine.forest.find x).1
      (Chapter21.Analysis.Costed.secondNodeAfterFind s.machine.forest x y) + 2

/-- The Chapter 21 union charge covers the preceding equivalence query: both
perform the same two finds, while union reserves one additional link unit. -/
theorem cycleQueryCost_le_unionStepCost
    (s : State n E) (G : Graph (Fin n) E) (e : E) :
    cycleQueryCost s G e ≤
      (Chapter21.Analysis.Costed.step s.machine
        (.union (G.src e) (G.dst e))).cost := by
  simp [cycleQueryCost, Chapter21.Analysis.Costed.step,
    Chapter21.Analysis.Costed.unionCost]

/-- One executable cycle query followed by the Chapter 21 union operation.
The union state performs the actual merge; charging twice its cost covers both
two-find traversals, since the query omits only the union's constant link. -/
def step (G : Graph (Fin n) E) (s : State n E) (e : E) : State n E :=
  let one := Chapter21.Analysis.Costed.step s.machine
    (.union (G.src e) (G.dst e))
  { machine := one.state
    selected := if accepts s G e then insert e s.selected else s.selected
    cost := s.cost + 2 * one.cost }

/-- The charged step bounds the actual query-plus-union work. -/
theorem query_add_union_le_charged_step
    (s : State n E) (G : Graph (Fin n) E) (e : E) :
    cycleQueryCost s G e +
        (Chapter21.Analysis.Costed.step s.machine
          (.union (G.src e) (G.dst e))).cost ≤
      2 * (Chapter21.Analysis.Costed.step s.machine
        (.union (G.src e) (G.dst e))).cost := by
  have h := cycleQueryCost_le_unionStepCost s G e
  omega

/-- Incrementally scan a fixed edge order. -/
def scan (G : Graph (Fin n) E) : List E → State n E → State n E
  | [], s => s
  | e :: es, s => scan G es (step G s e)

/-- The central state invariant: union-find equivalence is exactly graph
connectivity in the currently selected forest. -/
def Valid (G : Graph (Fin n) E) (s : State n E) : Prop :=
  ∀ (u v : Fin n),
    (Chapter21.Forest.partition s.machine.forest).sameSet (u : Nat) v ↔
      G.ConnectedIn s.selected u v

@[simp]
theorem accepts_eq_true_iff (G : Graph (Fin n) E) (s : State n E) (e : E) :
    accepts s G e = true ↔
      ¬(Chapter21.Forest.partition s.machine.forest).sameSet
        (G.src e) (G.dst e) := by
  rw [accepts, Bool.not_eq_true_eq_eq_false,
    Chapter21.Forest.checkEquiv_eq_false_iff]
  simp [Chapter21.Analysis.Costed.Machine.node]

theorem accepts_eq_false_iff (G : Graph (Fin n) E) (s : State n E) (e : E) :
    accepts s G e = false ↔
      (Chapter21.Forest.partition s.machine.forest).sameSet
        (G.src e) (G.dst e) := by
  rw [accepts, Bool.not_eq_false_eq_eq_true,
    Chapter21.Forest.checkEquiv_correct]
  simp [Chapter21.Analysis.Costed.Machine.node]

/-- A valid machine makes the executable cycle decision exactly the usual
graph cycle test. -/
theorem accepts_eq_true_iff_not_connected {G : Graph (Fin n) E}
    {s : State n E} (hs : Valid G s) (e : E) :
    accepts s G e = true ↔
      ¬G.ConnectedIn s.selected (G.src e) (G.dst e) := by
  rw [accepts_eq_true_iff]
  exact not_congr (hs (G.src e) (G.dst e))

/-- One real Chapter 21 union preserves the graph-connectivity invariant. -/
theorem step_valid {G : Graph (Fin n) E} {s : State n E}
    (hs : Valid G s) (e : E) : Valid G (step G s e) := by
  intro u v
  by_cases hacc : accepts s G e = true
  · have hnot :
        ¬(Chapter21.Forest.partition s.machine.forest).sameSet
          (G.src e) (G.dst e) :=
      (accepts_eq_true_iff G s e).1 hacc
    simp only [step, hacc, if_pos]
    change
      (Chapter21.Forest.partition
        (s.machine.forest.union (s.machine.node (G.src e))
          (s.machine.node (G.dst e)))).sameSet u v ↔
        G.ConnectedIn (insert e s.selected) u v
    rw [Chapter21.Forest.union_sameSet_iff]
    simp only [Chapter21.Analysis.Costed.Machine.node]
    rw [Graph.connected_insert_edge_iff]
    simpa using
      or_congr (hs u v)
        (or_congr
          (and_congr (hs u (G.src e)) (hs (G.dst e) v))
          (and_congr (hs u (G.dst e)) (hs (G.src e) v)))
  · have hfalse : accepts s G e = false := by
      cases h : accepts s G e <;> simp [h] at hacc ⊢
    have hsame :
        (Chapter21.Forest.partition s.machine.forest).sameSet
          (G.src e) (G.dst e) :=
      (accepts_eq_false_iff G s e).1 hfalse
    simp only [step, hfalse]
    change
      (Chapter21.Forest.partition
        (s.machine.forest.union (s.machine.node (G.src e))
          (s.machine.node (G.dst e)))).sameSet u v ↔
        G.ConnectedIn s.selected u v
    rw [Chapter21.Forest.union_refines_merge]
    have hnode :
        (Chapter21.Forest.partition s.machine.forest).sameSet
          (s.machine.node (G.src e)) (s.machine.node (G.dst e)) := by
      simpa [Chapter21.Analysis.Costed.Machine.node] using hsame
    rw [(Chapter21.Forest.partition s.machine.forest).merge_related_sameSet_iff
      hnode]
    exact hs u v

/-- The invariant is inductive over the full edge scan. -/
theorem scan_valid {G : Graph (Fin n) E} {s : State n E}
    (hs : Valid G s) (edges : List E) : Valid G (scan G edges s) := by
  induction edges generalizing s with
  | nil => exact hs
  | cons e edges ih => exact ih (step_valid hs e)

/-- Singleton initialization represents empty-graph connectivity exactly. -/
theorem initial_valid (G : Graph (Fin n) E) : Valid G (initial n E) := by
  intro u v
  change
    (Chapter21.Forest.partition (Chapter21.Forest.singletonForest n)).sameSet
        (u : Nat) v ↔ G.ConnectedIn ∅ u v
  rw [Graph.connected_empty_iff]
  change (Chapter21.Forest.singletonForest n).Equiv (u : Nat) v ↔ u = v
  rw [Chapter21.Forest.singletonForest_equiv_iff]
  exact Fin.ext_iff.symm

/-- Every reachable incremental Kruskal state remains connectivity-faithful. -/
theorem scan_initial_valid (G : Graph (Fin n) E) (edges : List E) :
    Valid G (scan G edges (initial n E)) :=
  scan_valid (initial_valid G) edges

/-- The graph-level cycle test used by the mathematical Kruskal pass. -/
noncomputable def connectivityAccept (G : Graph (Fin n) E)
    (A : Finset E) (e : E) : Bool := by
  classical
  exact if G.ConnectedIn A (G.src e) (G.dst e) then false else true

/-- A valid state makes the machine decision extensionally equal to the
mathematical connectivity decision. -/
theorem accepts_eq_connectivityAccept {G : Graph (Fin n) E}
    {s : State n E} (hs : Valid G s) (e : E) :
    accepts s G e = connectivityAccept G s.selected e := by
  classical
  apply Bool.eq_iff_iff.2
  rw [accepts_eq_true_iff_not_connected hs]
  simp [connectivityAccept]

/-- Stateful execution selects exactly the same edges as the mathematical
Kruskal recursion driven by graph connectivity. -/
theorem scan_selected_eq_kruskal {G : Graph (Fin n) E}
    {s : State n E} (hs : Valid G s) (edges : List E) :
    (scan G edges s).selected =
      kruskal (connectivityAccept G) edges s.selected := by
  induction edges generalizing s with
  | nil => rfl
  | cons e edges ih =>
      simp only [scan, kruskal]
      rw [← accepts_eq_connectivityAccept hs e]
      by_cases hacc : accepts s G e = true
      · simpa [step, hacc] using ih (step_valid hs e)
      · have hfalse : accepts s G e = false := by
          cases h : accepts s G e <;> simp [h] at hacc ⊢
        simpa [step, hfalse] using ih (step_valid hs e)

/-- Reader-facing empty-prefix refinement theorem. -/
theorem scan_initial_selected_eq_kruskal (G : Graph (Fin n) E)
    (edges : List E) :
    (scan G edges (initial n E)).selected =
      kruskal (connectivityAccept G) edges ∅ :=
  scan_selected_eq_kruskal (initial_valid G) edges

/-! ## Concrete work bounds -/

/-- The exact Chapter 21 operation trace generated by a fused Kruskal scan. -/
def unionOperations (G : Graph (Fin n) E) (edges : List E) :
    List (UFOperation n) :=
  edges.map fun e => .union (G.src e) (G.dst e)

@[simp]
theorem unionOperations_length (G : Graph (Fin n) E) (edges : List E) :
    (unionOperations G edges).length = edges.length := by
  simp [unionOperations]

/-- The machine threaded by Kruskal is exactly the Chapter 21 costed run. -/
theorem scan_machine_eq_run (G : Graph (Fin n) E) (edges : List E)
    (s : State n E) :
    (scan G edges s).machine =
      (Chapter21.Analysis.Costed.run s.machine
        (unionOperations G edges)).state := by
  induction edges generalizing s with
  | nil => rfl
  | cons e edges ih =>
      simpa [scan, step, unionOperations, Chapter21.Analysis.Costed.run] using
        ih (step G s e)

/-- The charged Kruskal work is twice the Chapter 21 union trace: one charge
for the executable cycle query and one for the following union. -/
theorem scan_cost_eq_run (G : Graph (Fin n) E) (edges : List E)
    (s : State n E) :
    (scan G edges s).cost = s.cost + 2 *
      (Chapter21.Analysis.Costed.run s.machine
        (unionOperations G edges)).cost := by
  induction edges generalizing s with
  | nil => simp [scan, unionOperations, Chapter21.Analysis.Costed.run]
  | cons e edges ih =>
      rw [scan, ih]
      simp only [step, unionOperations, List.map_cons,
        Chapter21.Analysis.Costed.run]
      omega

/-- The union-find part of incremental Kruskal has the Chapter 21
`O((E + V) alpha(V))` concrete bound. -/
theorem scan_initial_cost_le_inverseAckermann
    (G : Graph (Fin n) E) (edges : List E) :
    (scan G edges (initial n E)).cost ≤
      18 * (edges.length + n) *
        Chapter21.Analysis.inverseAckermann n := by
  rw [scan_cost_eq_run]
  have h := Chapter21.Analysis.Ackermann.run_cost_le_inverseAckermann n
    (unionOperations G edges)
  rw [unionOperations_length] at h
  simp only [initial, zero_add]
  nlinarith

/-- Comparison-sort work model used for the end-to-end CLRS bound. -/
def comparisonSortWork (m : Nat) : Nat :=
  m * (Nat.log2 m + 1)

/-- End-to-end Kruskal work: sorting, one constant scan action per edge, and
the concrete Chapter 21 union-find execution. -/
def totalWork (G : Graph (Fin n) E) (edges : List E) : Nat :=
  comparisonSortWork edges.length + edges.length +
    (scan G edges (initial n E)).cost

/-- Exact decomposition of the implementation-level Kruskal work model. -/
theorem totalWork_eq (G : Graph (Fin n) E) (edges : List E) :
    totalWork G edges =
      edges.length * (Nat.log2 edges.length + 1) + edges.length +
        (scan G edges (initial n E)).cost :=
  rfl

/-- Sorting, linear scan, and inverse-Ackermann union-find work composed in
one explicit bound. -/
theorem totalWork_le_sort_add_scan_add_inverseAckermann
    (G : Graph (Fin n) E) (edges : List E) :
    totalWork G edges ≤
      edges.length * (Nat.log2 edges.length + 1) + edges.length +
        18 * (edges.length + n) *
          Chapter21.Analysis.inverseAckermann n := by
  exact Nat.add_le_add_left
    (scan_initial_cost_le_inverseAckermann G edges)
    (comparisonSortWork edges.length + edges.length)

/-- Textbook `O(E log E)` endpoint with an explicit constant.  The final
side condition records the standard domination `alpha(V) = O(log E)`; keeping
it visible avoids hiding an asymptotic fact inside the concrete cost model. -/
theorem totalWork_le_forty_mul_edge_log
    (G : Graph (Fin n) E) (edges : List E)
    (hvertices : n ≤ edges.length)
    (halpha : Chapter21.Analysis.inverseAckermann n ≤
      Nat.log2 edges.length + 1) :
    totalWork G edges ≤
      40 * edges.length * (Nat.log2 edges.length + 1) := by
  have hwork := totalWork_le_sort_add_scan_add_inverseAckermann G edges
  have hlog : 1 ≤ Nat.log2 edges.length + 1 := by omega
  nlinarith

end StatefulKruskal
end MST
end CLRS

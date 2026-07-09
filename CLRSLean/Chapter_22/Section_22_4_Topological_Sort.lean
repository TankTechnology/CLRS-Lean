import Mathlib
import CLRSLean.Chapter_22.Section_22_1_Representing_Graphs

/-! # Section 22.4 - Topological Sort

This section gives Kahn's algorithm for topological sorting on the finite graph
model from Section 22.1 and proves that it returns a valid topological order
whenever the input graph is a DAG.

The main declarations are:

- {lit}`Graph.IsDAG`: a directed graph has no directed cycle.
- {lit}`Graph.indegree`: the number of incoming edges of a vertex.
- {lit}`Graph.IsTopologicalOrder`: a list of all vertices where every edge goes
  from an earlier vertex to a later one.
- {lit}`Graph.kahnAux`: the fuelled recursive core of Kahn's algorithm.
- {lit}`Graph.topologicalSort`: the entry point.
- {lit}`Graph.topologicalSort_isTopologicalOrder`: correctness for DAGs.

The proof follows the standard invariant for Kahn's algorithm: the accumulator
contains an initial segment of the final order, it is disjoint from the
remaining vertices, the current indegree of each remaining vertex counts only
incoming edges from remaining vertices, and every edge between two accumulator
vertices is already ordered.

The key fact is that a nonempty subset of a finite DAG always contains a source
vertex (a vertex with no incoming edge from the subset).  This is obtained from
well-foundedness of the adjacency relation on any finite subset of a DAG.
-/

namespace CLRS
namespace Chapter22

namespace Graph

variable {V : Type} [DecidableEq V]

/-- A directed acyclic graph: no vertex can reach itself by a non-trivial path. -/
def IsDAG (G : Graph V) : Prop := ∀ v, ¬Relation.TransGen G.Adj v v

/-- Adjacency is decidable because each vertex has a finite adjacency set. -/
instance adjDecidableRel (G : Graph V) : DecidableRel G.Adj :=
  fun u v => decidable_of_iff (v ∈ G.adj u) (by unfold Adj; exact Iff.rfl)

/-- Number of incoming edges of {lit}`v` from vertices of the graph. -/
def indegree (G : Graph V) (v : V) : Nat :=
  (G.vertices.filter (fun u => v ∈ G.adj u)).card

/-- A topological order of {lit}`G` is a permutation of the vertices in which
every directed edge goes forward. -/
def IsTopologicalOrder (G : Graph V) (order : List V) : Prop :=
  order.Nodup ∧
  (∀ v, v ∈ order ↔ v ∈ G.vertices) ∧
  (∀ u ∈ G.vertices, ∀ v ∈ G.adj u, List.idxOf u order < List.idxOf v order)

section Kahn

open Classical

/-- One step of Kahn's algorithm.  The function is fuelled by a natural number.

If a vertex of current indegree zero exists in {lit}`remaining`, one such vertex
is chosen classically, removed from {lit}`remaining`, the
indegrees of its remaining out-neighbors are decremented, and it is appended to
the accumulator.  Otherwise the accumulator is returned. -/
noncomputable def kahnAux (G : Graph V) (fuel : Nat) (remaining : Finset V) (indeg : V → Nat) (acc : List V) : List V :=
  match fuel with
  | 0 => acc
  | fuel + 1 =>
      if _h : remaining.Nonempty then
        if hex : ∃ v, v ∈ remaining ∧ indeg v = 0 then
          let v := Classical.choose hex
          let remaining' := remaining.erase v
          let indeg' (w : V) : Nat := if w ∈ remaining' ∧ G.Adj v w then indeg w - 1 else indeg w
          kahnAux G fuel remaining' indeg' (acc ++ [v])
        else
          acc
      else
        acc

/-- Entry point for Kahn's algorithm.  The fuel is one more than the number of
vertices, which is enough to remove every vertex. -/
noncomputable def topologicalSort (G : Graph V) : List V :=
  kahnAux G (G.vertices.card + 1) G.vertices G.indegree []

/-- Invariant for {name}`Graph.kahnAux`.

- {lit}`nodup`: the accumulator has no duplicate vertices.
- {lit}`remaining_subset`: all remaining vertices are graph vertices.
- {lit}`acc_mem`: every accumulator vertex is a graph vertex.
- {lit}`cover`: every graph vertex is either in the accumulator or remaining.
- {lit}`disjoint`: the accumulator and the remaining set are disjoint.
- {lit}`preds_placed`: every predecessor of an accumulator vertex is already in
  the accumulator.
- {lit}`indeg_eq`: for each remaining vertex, its current indegree equals the
  number of incoming edges from remaining vertices.
- {lit}`edge_ordered`: every edge between two accumulator vertices is ordered
  correctly in the accumulator. -/
structure KahnInvariant (G : Graph V) (remaining : Finset V) (indeg : V → Nat) (acc : List V) : Prop where
  nodup : acc.Nodup
  remaining_subset : remaining ⊆ G.vertices
  acc_mem : ∀ v, v ∈ acc → v ∈ G.vertices
  cover : ∀ v, v ∈ G.vertices → v ∈ acc ∨ v ∈ remaining
  disjoint : ∀ v, v ∈ acc → ¬v ∈ remaining
  preds_placed : ∀ y ∈ acc, ∀ u ∈ G.vertices, G.Adj u y → u ∈ acc
  indeg_eq : ∀ v ∈ remaining, indeg v = (remaining.filter (fun u => G.Adj u v)).card
  edge_ordered : ∀ u ∈ acc, ∀ v ∈ G.adj u, v ∈ acc → List.idxOf u acc < List.idxOf v acc

-- The adjacency relation is well-founded on any finite subset of a DAG.

/-- In a finite DAG, the adjacency relation is well-founded on any finset
{lit}`S`.  The proof first shows well-foundedness of the transitive closure
{lit}`Relation.TransGen G.Adj` using the no-descending-sequence characterisation;
an infinite descending sequence inside {lit}`S` must repeat (pigeonhole), and a
repeat gives a non-trivial cycle.  Well-foundedness of {lit}`G.Adj` follows
because {lit}`G.Adj` is a subrelation of its transitive closure. -/
lemma finite_DAG_wellFoundedOn (G : Graph V) (S : Finset V) (hDAG : G.IsDAG) : (S : Set V).WellFoundedOn G.Adj := by
  have hwf : (S : Set V).WellFoundedOn (Relation.TransGen G.Adj) := by
    letI : IsStrictOrder V (Relation.TransGen G.Adj) := {
      toIrrefl := ⟨fun a h => hDAG a h⟩
      toIsTrans := ⟨fun _ _ _ h1 h2 => Relation.TransGen.trans h1 h2⟩
    }
    rw [Set.wellFoundedOn_iff_no_descending_seq]
    intro f hf
    -- The descending sequence takes values in the finite set S, so it repeats.
    have hrep : ∃ (i j : ℕ), i < j ∧ f i = f j := by
      by_contra h
      push Not at h
      have hinj : Function.Injective f := by
        intro i j heq
        by_contra hne
        cases lt_or_gt_of_ne hne with
        | inl hij => exact h i j hij heq
        | inr hji => exact h j i hji heq.symm
      have hcard : (Finset.image f (Finset.range (S.card + 1))).card = S.card + 1 := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
      have hsub : Finset.image f (Finset.range (S.card + 1)) ⊆ S := by
        intro x hx
        simp at hx
        rcases hx with ⟨n, -, rfl⟩
        exact hf n
      have hcard_le : (Finset.image f (Finset.range (S.card + 1))).card ≤ S.card :=
        Finset.card_le_card hsub
      linarith
    rcases hrep with ⟨i, j, hij, heq⟩
    have htrans : Relation.TransGen G.Adj (f j) (f i) :=
      f.map_rel_iff'.mpr (show j > i by exact hij)
    rw [← heq] at htrans
    exact hDAG (f i) htrans
  exact hwf.mono' (fun _ _ _ _ h => Relation.TransGen.single h)

/-- In a DAG with the Kahn invariant, any nonempty remaining set contains a
vertex of current indegree zero. -/
lemma exists_zero_indegree (G : Graph V) {remaining : Finset V} {indeg : V → Nat} {acc : List V}
    (hinv : G.KahnInvariant remaining indeg acc) (hDAG : G.IsDAG)
    (hnonempty : remaining.Nonempty) :
    ∃ v, v ∈ remaining ∧ indeg v = 0 := by
  have hwf : WellFounded (fun (a b : V) => G.Adj a b ∧ a ∈ remaining ∧ b ∈ remaining) := by
    convert G.finite_DAG_wellFoundedOn remaining hDAG
    simp [Set.wellFoundedOn_iff]
  have hne : (remaining : Set V).Nonempty := by simpa using hnonempty
  let v := WellFounded.min hwf (remaining : Set V) hne
  have hv1 : v ∈ remaining := WellFounded.min_mem hwf (remaining : Set V) hne
  have hv2 : ∀ u ∈ remaining, ¬G.Adj u v := by
    intro u hu huv
    have h := WellFounded.not_lt_min hwf (remaining : Set V) (x := u) hu
    exact h ⟨huv, hu, hv1⟩
  use v, hv1
  rw [hinv.indeg_eq v hv1]
  apply Finset.card_eq_zero.mpr
  ext u
  simp
  intro hu hadj
  exact hv2 u hu hadj

/-- The Kahn invariant holds for the initial call. -/
lemma kahnInvariant_init (G : Graph V) : G.KahnInvariant G.vertices G.indegree [] := by
  constructor
  · simp
  · simp
  · simp
  · intro v hv
    simp [hv]
  · simp
  · simp
  · intro v hv
    simp [indegree, Adj]
  · intro y hy
    simp at hy

/-- The Kahn invariant is preserved by one recursive step. -/
lemma kahnInvariant_step (G : Graph V) {remaining : Finset V} {indeg : V → Nat} {acc : List V}
    (hinv : G.KahnInvariant remaining indeg acc) (hDAG : G.IsDAG)
    (hnonempty : remaining.Nonempty) :
    let hex := G.exists_zero_indegree hinv hDAG hnonempty
    let v := Classical.choose hex
    let remaining' := remaining.erase v
    let indeg' (w : V) : Nat := if w ∈ remaining' ∧ G.Adj v w then indeg w - 1 else indeg w
    G.KahnInvariant remaining' indeg' (acc ++ [v]) := by
  intro hex v remaining' indeg'
  have hv : v ∈ remaining ∧ indeg v = 0 := Classical.choose_spec hex
  have hv_not_acc : v ∉ acc := by
    intro h
    exact hinv.disjoint v h hv.1
  constructor
  · -- nodup
    apply List.Nodup.append
    · exact hinv.nodup
    · simp
    · intro a ha hb
      have hav : a = v := by
        rw [List.mem_singleton] at hb
        exact hb
      rw [hav] at ha
      exact hv_not_acc ha
  · -- remaining_subset
    intro x hx
    exact hinv.remaining_subset (Finset.mem_of_mem_erase hx)
  · -- acc_mem
    intro x hx
    simp at hx
    rcases hx with (hx | hx)
    · exact hinv.acc_mem x hx
    · rw [hx]
      exact hinv.remaining_subset hv.1
  · -- cover
    intro x hx
    by_cases hxv : x = v
    · left
      simp [hxv]
    · rcases hinv.cover x hx with (hacc | hrem)
      · left
        simp [hacc]
      · right
        simp [remaining', hrem, hxv]
  · -- disjoint
    intro x hx
    simp at hx
    rcases hx with (hx | hx)
    · intro h'
      have : x ∈ remaining := Finset.mem_of_mem_erase h'
      exact hinv.disjoint x hx this
    · rw [hx]
      intro h
      rw [Finset.mem_erase] at h
      exfalso
      exact h.1 rfl
  · -- preds_placed
    intro y hy u hu hadj
    simp at hy
    rcases hy with (hy | hy)
    · have h := hinv.preds_placed y hy u hu hadj
      exact List.mem_append_left _ h
    · rw [hy] at hadj
      have hu_not_rem : u ∉ remaining := by
        by_contra hu_rem
        have : u ∈ remaining.filter (fun x => G.Adj x v) := by
          simp [hu_rem, hadj]
        have hcard : (remaining.filter (fun x => G.Adj x v)).card = 0 := by
          rw [← hinv.indeg_eq v hv.1]
          exact hv.2
        rw [Finset.card_eq_zero] at hcard
        simp [hcard] at this
      have hu_acc : u ∈ acc := by
        rcases hinv.cover u hu with (hacc | hrem)
        · exact hacc
        · contradiction
      exact List.mem_append_left _ hu_acc
  · -- indeg_eq
    intro w hw
    have hw_rem : w ∈ remaining := Finset.mem_of_mem_erase hw
    by_cases hvw : G.Adj v w
    · -- v → w contributes one to the old filter but not the new one.
      rw [show indeg' w = indeg w - 1 by simp [indeg', hw, hvw]]
      rw [hinv.indeg_eq w hw_rem]
      have hfilter : remaining.filter (fun u => G.Adj u w) =
          (remaining'.filter (fun u => G.Adj u w)) ∪ {v} := by
        ext u
        simp [remaining', Finset.mem_erase]
        by_cases huv : u = v
        · simp [huv, hv.1, hvw]
        · simp [huv]
      have hdisj : Disjoint (remaining'.filter (fun u => G.Adj u w)) {v} := by
        rw [Finset.disjoint_singleton_right]
        simp [remaining']
      rw [hfilter, Finset.card_union_of_disjoint hdisj, Finset.card_singleton]
      omega
    · -- v does not point to w, so the filter is unchanged.
      rw [show indeg' w = indeg w by simp [indeg', hw, hvw]]
      rw [hinv.indeg_eq w hw_rem]
      have hfilter : remaining.filter (fun u => G.Adj u w) =
          remaining'.filter (fun u => G.Adj u w) := by
        ext u
        simp [remaining', Finset.mem_erase]
        by_cases huv : u = v
        · simp [huv, hvw]
        · simp [huv]
      rw [hfilter]
  · -- edge_ordered
    intro u hu y hy hyacc
    simp at hu hyacc
    rcases hu with (hu | rfl)
    · rcases hyacc with (hyacc | rfl)
      · -- u and y are both in the old accumulator.
        have h1 : List.idxOf u (acc ++ [v]) = List.idxOf u acc := by
          apply List.idxOf_append_of_mem
          exact hu
        have h2 : List.idxOf y (acc ++ [v]) = List.idxOf y acc := by
          apply List.idxOf_append_of_mem
          exact hyacc
        rw [h1, h2]
        exact hinv.edge_ordered u hu y hy hyacc
      · -- y is the newly added vertex v.
        have h1 : List.idxOf u (acc ++ [v]) = List.idxOf u acc := by
          apply List.idxOf_append_of_mem
          exact hu
        have h2 : List.idxOf v (acc ++ [v]) = acc.length := by
          have hv' : v ∉ acc := hv_not_acc
          rw [List.idxOf_append_of_notMem hv']
          rw [List.idxOf_cons_eq [] (rfl)]
          simp
        rw [h1, h2]
        have h3 : List.idxOf u acc < acc.length := by
          apply List.idxOf_lt_length_of_mem
          exact hu
        linarith
    · -- u is the newly added vertex v; this is impossible.
      rcases hyacc with (hyacc | rfl)
      · -- y is in the accumulator, contradicting preds_placed.
        exfalso
        have hadj : G.Adj v y := hy
        have h1 : v ∈ G.vertices := hinv.remaining_subset hv.1
        have h2 : v ∈ acc := hinv.preds_placed y hyacc v h1 hadj
        exact hinv.disjoint v h2 hv.1
      · -- y = v gives a self-loop, contradicting the DAG assumption.
        exfalso
        have hadj : G.Adj v v := hy
        exact hDAG v (Relation.TransGen.single hadj)

/-- Soundness of {name}`Graph.kahnAux`: if the invariant holds, the graph is a
DAG, and the fuel is at least the number of remaining vertices, then the result
is a topological order. -/
theorem kahnAux_sound (G : Graph V) {fuel : Nat} {remaining : Finset V} {indeg : V → Nat} {acc : List V}
    (hinv : G.KahnInvariant remaining indeg acc) (hDAG : G.IsDAG)
    (hfuel : remaining.card ≤ fuel) :
    G.IsTopologicalOrder (G.kahnAux fuel remaining indeg acc) := by
  induction fuel generalizing remaining indeg acc with
  | zero =>
      have rem_empty : remaining = ∅ := by
        apply Finset.card_eq_zero.mp
        linarith [hfuel]
      simp [kahnAux]
      constructor
      · exact hinv.nodup
      constructor
      · intro v
        constructor
        · intro hv
          exact hinv.acc_mem v hv
        · intro hv
          have : v ∈ acc ∨ v ∈ remaining := hinv.cover v hv
          simp [rem_empty] at this
          exact this
      · intro u hu y hy
        have hu_acc : u ∈ acc := by
          have : u ∈ acc ∨ u ∈ remaining := hinv.cover u hu
          simp [rem_empty] at this
          exact this
        have hy_acc : y ∈ acc := by
          have hy_vert : y ∈ G.vertices := G.adj_sub u hu hy
          have : y ∈ acc ∨ y ∈ remaining := hinv.cover y hy_vert
          simp [rem_empty] at this
          exact this
        exact hinv.edge_ordered u hu_acc y hy hy_acc
  | succ n ih =>
      by_cases hrem : remaining.Nonempty
      · -- There is a zero-indegree vertex; take one step.
        have hex := G.exists_zero_indegree hinv hDAG hrem
        let v := Classical.choose hex
        have hv : v ∈ remaining ∧ indeg v = 0 := Classical.choose_spec hex
        let remaining' := remaining.erase v
        let indeg' (w : V) : Nat := if w ∈ remaining' ∧ G.Adj v w then indeg w - 1 else indeg w
        have hinv' : G.KahnInvariant remaining' indeg' (acc ++ [v]) :=
          G.kahnInvariant_step hinv hDAG hrem
        have hfuel' : remaining'.card ≤ n := by
          have hcard : remaining.card = remaining'.card + 1 := by
            rw [Finset.card_erase_add_one hv.1]
          linarith [hfuel, hcard]
        have heq : G.kahnAux (n + 1) remaining indeg acc =
            G.kahnAux n remaining' indeg' (acc ++ [v]) := by
          simp [kahnAux, hrem, dif_pos hex, v, remaining', indeg']
        rw [heq]
        exact ih hinv' hfuel'
      · -- remaining is empty; the accumulator already contains every vertex.
        have rem_empty : remaining = ∅ := by
          rw [Finset.nonempty_iff_ne_empty] at hrem
          simpa using hrem
        simp [kahnAux, rem_empty]
        constructor
        · exact hinv.nodup
        constructor
        · intro v
          constructor
          · intro hv
            exact hinv.acc_mem v hv
          · intro hv
            have : v ∈ acc ∨ v ∈ remaining := hinv.cover v hv
            simp [rem_empty] at this
            exact this
        · intro u hu y hy
          have hu_acc : u ∈ acc := by
            have : u ∈ acc ∨ u ∈ remaining := hinv.cover u hu
            simp [rem_empty] at this
            exact this
          have hy_acc : y ∈ acc := by
            have hy_vert : y ∈ G.vertices := G.adj_sub u hu hy
            have : y ∈ acc ∨ y ∈ remaining := hinv.cover y hy_vert
            simp [rem_empty] at this
            exact this
          exact hinv.edge_ordered u hu_acc y hy hy_acc

/-- Kahn's algorithm returns a topological order for every DAG. -/
theorem topologicalSort_isTopologicalOrder (G : Graph V) (hDAG : G.IsDAG) :
    G.IsTopologicalOrder G.topologicalSort := by
  have hinv := G.kahnInvariant_init
  have hfuel : G.vertices.card ≤ G.vertices.card + 1 := by linarith
  exact G.kahnAux_sound hinv hDAG hfuel

end Kahn

end Graph

end Chapter22
end CLRS

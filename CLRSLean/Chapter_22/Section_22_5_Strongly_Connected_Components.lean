import Mathlib
import CLRSLean.Chapter_22.Section_22_1_Representing_Graphs
import CLRSLean.Chapter_22.Section_22_3_DFS

/-! # Section 22.5 - Strongly Connected Components

This section gives Kosaraju's two-pass depth-first-search algorithm for
computing the strongly connected components of a directed graph on the finite
graph model from Section 22.1, and proves that the returned components form a
valid SCC partition.

The algorithm:
1. Run DFS on {lit}`G` and record finish times.
2. Sort vertices by decreasing finish time.
3. Run DFS on the transpose graph {lit}`Gᵀ` in that order, collecting each DFS
   tree as one component.

The main declarations are:

- {lit}`CLRS.Chapter22.Graph.transpose`,
- {lit}`CLRS.Chapter22.Graph.StronglyConnected`,
- {lit}`CLRS.Chapter22.Graph.IsSCC`,
- {lit}`CLRS.Chapter22.Graph.IsSCCPartition`,
- {lit}`CLRS.Chapter22.Graph.dfsFromListCollect`,
- {lit}`CLRS.Chapter22.Graph.kosarajuComponents`,
- {lit}`CLRS.Chapter22.Graph.kosarajuComponents_isSCCPartition`.

The current proof establishes the structural partition properties (subsets of
vertices, pairwise disjointness, and coverage) directly from the DFS collecting
invariant.  Strong connectivity and maximality of every component reduce to the
standard DFS finish-time ordering of SCCs; the missing purely DFS-theoretic
lemma is isolated as {lit}`CLRS.Chapter22.Graph.scc_finish_order` and is the
next target for this section.
-/

namespace CLRS
namespace Chapter22

namespace Graph

variable {V : Type} [DecidableEq V]
variable (G : Graph V)

/-! ## Transpose graph and strong connectivity -/

/-- The transpose (reverse) of a finite directed graph. -/
def transpose (G : Graph V) : Graph V where
  vertices := G.vertices
  adj := fun v => G.vertices.filter (fun u => v ∈ G.adj u)
  adj_sub := by
    intro v hv
    exact Finset.filter_subset _ G.vertices
  adj_outside := by
    intro v hv
    ext u
    simp
    intro hu hadj
    exact hv (G.adj_mem_right hadj)

@[simp]
theorem transpose_vertices (G : Graph V) : G.transpose.vertices = G.vertices :=
  rfl

@[simp]
theorem transpose_Adj (G : Graph V) (u v : V) :
    G.transpose.Adj u v ↔ G.Adj v u := by
  simp [Adj, transpose]
  intro h
  exact G.adj_mem_left h

/-- Two vertices are strongly connected when they are reachable from each other. -/
def StronglyConnected (G : Graph V) (u v : V) : Prop :=
  G.Reachable u v ∧ G.Reachable v u

theorem stronglyConnected_refl (u : V) : G.StronglyConnected u u :=
  ⟨G.reachable_refl u, G.reachable_refl u⟩

theorem stronglyConnected_symm {u v : V}
    (h : G.StronglyConnected u v) : G.StronglyConnected v u :=
  ⟨h.2, h.1⟩

theorem stronglyConnected_trans {u v w : V}
    (huv : G.StronglyConnected u v) (hvw : G.StronglyConnected v w) :
    G.StronglyConnected u w :=
  ⟨G.reachable_trans huv.1 hvw.1, G.reachable_trans hvw.2 huv.2⟩

/-- A strongly connected component is a nonempty maximal subset of vertices in
which every pair of vertices is strongly connected. -/
def IsSCC (G : Graph V) (C : Set V) : Prop :=
  C.Nonempty ∧ C ⊆ G.vertices ∧
    (∀ u ∈ C, ∀ v ∈ C, G.StronglyConnected u v) ∧
    (∀ w ∈ G.vertices, (∀ u ∈ C, G.StronglyConnected u w) → w ∈ C)

/-- A list of finsets is an SCC partition of {lit}`G` if each element is an SCC of
{lit}`G` and the elements partition the vertex set. -/
def IsSCCPartition (G : Graph V) (ccs : List (Finset V)) : Prop :=
  (∀ C ∈ ccs, (C : Set V) ⊆ G.vertices) ∧
  (∀ C ∈ ccs, C.Nonempty) ∧
  (∀ C ∈ ccs, ∀ u ∈ C, ∀ v ∈ C, G.StronglyConnected u v) ∧
  (∀ C ∈ ccs, ∀ w ∈ G.vertices \ C, ¬ (∀ u ∈ C, G.StronglyConnected u w)) ∧
  (∀ v ∈ G.vertices, ∃! C ∈ ccs, v ∈ C)


/-! ## Collecting DFS and Kosaraju's algorithm -/

open Classical

/-- Run DFS from a list of starting vertices and collect, for each white start
vertex, the finset of vertices that turn black during that visit.  Components
are accumulated in reverse order. -/
noncomputable def dfsFromListCollect (G : Graph V) (fuel : Nat) :
    List V → DFSState V → List (Finset V) → List (Finset V) × DFSState V
  | [], s, acc => (acc, s)
  | u :: us, s, acc =>
      if s.color u = Color.white then
        let s' := dfsVisit G fuel u s
        let comp := G.vertices.filter (fun v => s.color v = Color.white ∧ s'.color v = Color.black)
        dfsFromListCollect G fuel us s' (comp :: acc)
      else
        dfsFromListCollect G fuel us s acc

/-- Finish-time comparison used to sort vertices in decreasing order. -/
@[irreducible]
def finishLe (s : DFSState V) (u v : V) : Bool :=
  Nat.blt ((s.f v).getD 0) ((s.f u).getD 0)

/-- Kosaraju's algorithm: DFS on {lit}`G` for finish times, then DFS on
{lit}`Gᵀ` in decreasing finish-time order, collecting each DFS tree. -/
noncomputable def kosarajuComponents (G : Graph V) : List (Finset V) :=
  let s1 := G.dfs
  let order := G.vertices.toList.mergeSort (finishLe s1)
  (dfsFromListCollect G.transpose (G.vertices.card + 1) order dfsInit []).1

/-! ## Basic structural facts about collecting DFS -/

/-- Invariant maintained by {name}`Graph.dfsFromListCollect`:
* accumulated components are pairwise disjoint subsets of vertices;
* every component is nonempty;
* every vertex placed in a component is black in the current state;
* every black vertex of {lit}`G` already belongs to some accumulated component;
* the current state has no gray vertices. -/
structure CollectInvariant (G : Graph V) (s : DFSState V) (acc : List (Finset V)) : Prop where
  pairwise : acc.Pairwise (fun C D => Disjoint C D)
  subset : ∀ C ∈ acc, (C : Set V) ⊆ G.vertices
  nonempty : ∀ C ∈ acc, C.Nonempty
  black : ∀ C ∈ acc, ∀ v ∈ C, s.color v = Color.black
  cover : ∀ v ∈ G.vertices, s.color v = Color.black → ∃ C ∈ acc, v ∈ C
  no_gray : ∀ v, s.color v = Color.white ∨ s.color v = Color.black

/-- The collecting invariant holds for the empty accumulator and the initial
DFS state. -/
theorem collectInvariant_init (G : Graph V) :
    CollectInvariant G dfsInit ([] : List (Finset V)) := by
  constructor
  · simp
  · simp
  · simp
  · simp
  · simp [dfsInit]
  · simp [dfsInit]

/-- A DFS visit from a white vertex with positive fuel turns that vertex black. -/
theorem dfsVisit_blackens_u_of_pos {G : Graph V} {fuel : Nat} {u : V} {s : DFSState V}
    (hfuel : 0 < fuel) (hwhite : s.color u = Color.white) :
    (dfsVisit G fuel u s).color u = Color.black := by
  rcases fuel with _ | n
  · omega
  · exact dfsVisit_blackens_u G hwhite

/-- One step of {name}`Graph.dfsFromListCollect` preserves the collecting
invariant. -/
theorem collectInvariant_step (G : Graph V) {fuel : Nat}
    (hfuel : 0 < fuel) {u : V} (hu : u ∈ G.vertices) (_us : List V)
    {s : DFSState V} {acc : List (Finset V)} (hwhite : s.color u = Color.white)
    (hinv : CollectInvariant G s acc) :
    let s' := dfsVisit G fuel u s
    let comp := G.vertices.filter (fun v => s.color v = Color.white ∧ s'.color v = Color.black)
    CollectInvariant G s' (comp :: acc) := by
  intro s' comp
  have hng : ∀ v, s'.color v = Color.white ∨ s'.color v = Color.black := by
    apply dfsVisit_output_no_gray
    intro v
    cases hinv.no_gray v <;> simp [*]
  constructor
  · -- pairwise disjoint: the new component is white in `s`, old components are black in `s`.
    apply List.Pairwise.cons
    · intro C hC
      apply Finset.disjoint_left.mpr
      intro v hvComp hvC
      have hvComp' : v ∈ comp := by simpa using hvComp
      rw [show comp = G.vertices.filter (fun v => s.color v = Color.white ∧ s'.color v = Color.black) by rfl] at hvComp'
      simp [Finset.mem_filter] at hvComp'
      rcases hvComp' with ⟨_, hwhite, _⟩
      have hblack : s.color v = Color.black := hinv.black C hC v hvC
      simp [hwhite] at hblack
    · exact hinv.pairwise
  · -- subset of vertices
    intro C hC
    by_cases hC' : C = comp
    · subst hC'
      intro v hv
      have hv' : v ∈ comp := by simpa using hv
      rw [show comp = G.vertices.filter (fun v => s.color v = Color.white ∧ s'.color v = Color.black) by rfl] at hv'
      simp [Finset.mem_filter] at hv'
      exact hv'.1
    · have hCacc : C ∈ acc := by
        simpa [hC'] using hC
      exact hinv.subset C hCacc
  · -- nonempty
    intro C hC
    by_cases hC' : C = comp
    · subst hC'
      use u
      have : u ∈ comp := by
        rw [show comp = G.vertices.filter (fun v => s.color v = Color.white ∧ s'.color v = Color.black) by rfl]
        simp [Finset.mem_filter]
        exact ⟨hu, hwhite, dfsVisit_blackens_u_of_pos hfuel hwhite⟩
      simpa using this
    · have hCacc : C ∈ acc := by
        simpa [hC'] using hC
      exact hinv.nonempty C hCacc
  · -- black in s'
    intro C hC v hv
    by_cases hC' : C = comp
    · subst hC'
      have hv' : v ∈ comp := by simpa using hv
      rw [show comp = G.vertices.filter (fun v => s.color v = Color.white ∧ s'.color v = Color.black) by rfl] at hv'
      simp [Finset.mem_filter] at hv'
      exact hv'.2.2
    · have hCacc : C ∈ acc := by
        simpa [hC'] using hC
      apply dfsVisit_preserves_black
      exact hinv.black C hCacc v hv
  · -- cover of black vertices in s'
    intro v hv hblack
    by_cases hwhite : s.color v = Color.white
    · use comp
      constructor
      · simp
      · rw [Finset.mem_filter]
        exact ⟨hv, hwhite, hblack⟩
    · have hblack_old : s.color v = Color.black := by
        cases hinv.no_gray v with
        | inl hw => contradiction
        | inr hb => exact hb
      rcases hinv.cover v hv hblack_old with ⟨C, hC, hvC⟩
      exact ⟨C, List.mem_cons_of_mem comp hC, hvC⟩
  · exact hng

/-- The collecting invariant is preserved through an entire vertex list. -/
theorem dfsFromListCollect_invariant (G : Graph V) {fuel : Nat}
    (hfuel : 0 < fuel) {vs : List V} (hvs : ∀ v ∈ vs, v ∈ G.vertices)
    (s0 : DFSState V) (acc : List (Finset V))
    (hinv : CollectInvariant G s0 acc) :
    CollectInvariant G (dfsFromListCollect G fuel vs s0 acc).2
      (dfsFromListCollect G fuel vs s0 acc).1 := by
  induction vs generalizing s0 acc with
  | nil => simpa [dfsFromListCollect]
  | cons u us ih =>
      simp [dfsFromListCollect]
      split_ifs with hwhite
      · exact ih (fun v hv => hvs v (by simp [hv])) _ _
          (collectInvariant_step G hfuel (hvs u (by simp)) us hwhite hinv)
      · exact ih (fun v hv => hvs v (by simp [hv])) _ _ hinv


/-- The final state of {name}`Graph.dfsFromListCollect` is exactly the state of
the underlying DFS, independent of the accumulator. -/
theorem dfsFromListCollect_state_eq {G : Graph V} {fuel : Nat}
    (vs : List V) (s0 : DFSState V) (acc : List (Finset V)) :
    (dfsFromListCollect G fuel vs s0 acc).2 = dfsFromList G fuel vs s0 := by
  induction vs generalizing s0 acc with
  | nil => simp [dfsFromListCollect, dfsFromList]
  | cons u us ih =>
      simp [dfsFromListCollect, dfsFromList]
      split_ifs with hwhite
      · rw [ih]
      · rw [ih]

/-- After {name}`Graph.dfsFromListCollect` processes a list containing every
vertex (with positive fuel), every vertex is black. -/
theorem dfsFromListCollect_all_black {G : Graph V} {fuel : Nat}
    {vs : List V} {s0 : DFSState V} {acc : List (Finset V)}
    (h0 : ∀ v, s0.color v = Color.white ∨ s0.color v = Color.black)
    (hfuel : 0 < fuel) (hvs : ∀ v ∈ G.vertices, v ∈ vs) :
    ∀ v ∈ G.vertices, (dfsFromListCollect G fuel vs s0 acc).2.color v = Color.black := by
  intro v hv
  rw [dfsFromListCollect_state_eq]
  have h := (dfsFromList_all_black G s0 h0 hfuel vs).1
  exact h v (hvs v hv)

/-- Core DFS finish-time lemma (admitted).

Consider a DFS state `s` of {lit}`G` and a white vertex `r` whose finish time is
maximal among all white vertices.  Then the DFS tree of {lit}`G.transpose` rooted
at `r` visits exactly the SCC of `r` in {lit}`G`.

This is the standard Kosaraju argument: the first white vertex in decreasing
finish-time order lies in a source SCC of the still-unvisited transpose graph,
so the second DFS cannot escape its SCC. -/
theorem scc_finish_order {G : Graph V} {s : DFSState V} {r : V}
    (hr : r ∈ G.vertices) (hwhite : s.color r = Color.white)
    (hmax : ∀ v, s.color v = Color.white → finishLe s v r)
    (hfuel : 0 < fuel) :
    let s' := dfsVisit G.transpose fuel r s
    let C := G.transpose.vertices.filter (fun v => s.color v = Color.white ∧ s'.color v = Color.black)
    G.IsSCC (C : Set V) := by
  sorry

/-! ## Kosaraju produces a partition of the vertex set -/

theorem kosaraju_order_subset_vertices (G : Graph V) :
    let order := G.vertices.toList.mergeSort (finishLe (G.dfs))
    ∀ v ∈ order, v ∈ G.transpose.vertices := by
  intro order v hv
  have hperm : order.Perm G.vertices.toList := List.mergeSort_perm _ _
  have : v ∈ G.vertices.toList := hperm.mem_iff.mp hv
  simpa [transpose_vertices]

theorem kosarajuComponents_subset (G : Graph V) (C : Finset V)
    (hC : C ∈ G.kosarajuComponents) : (C : Set V) ⊆ G.vertices := by
  simp only [kosarajuComponents] at hC
  let order := G.vertices.toList.mergeSort (finishLe (G.dfs))
  have hinv := collectInvariant_init G.transpose
  have hfuel : 0 < G.transpose.vertices.card + 1 := by omega
  have hinv' := dfsFromListCollect_invariant G.transpose hfuel
    (kosaraju_order_subset_vertices G) dfsInit [] hinv
  exact hinv'.subset C hC

theorem kosarajuComponents_pairwise_disjoint (G : Graph V) :
    G.kosarajuComponents.Pairwise (fun C D => Disjoint C D) := by
  simp only [kosarajuComponents]
  let order := G.vertices.toList.mergeSort (finishLe (G.dfs))
  have hinv := collectInvariant_init G.transpose
  have hfuel : 0 < G.transpose.vertices.card + 1 := by omega
  have hinv' := dfsFromListCollect_invariant G.transpose hfuel
    (kosaraju_order_subset_vertices G) dfsInit [] hinv
  exact hinv'.pairwise

theorem kosarajuComponents_cover (G : Graph V) :
    ∀ v ∈ G.vertices, ∃ C ∈ G.kosarajuComponents, v ∈ C := by
  intro v hv
  simp [kosarajuComponents]
  let order := G.vertices.toList.mergeSort (finishLe (G.dfs))
  have hperm : order.Perm G.vertices.toList := List.mergeSort_perm _ _
  have hmem : ∀ x ∈ G.transpose.vertices, x ∈ order := by
    intro x hx
    have hx' : x ∈ G.vertices := by simpa using hx
    exact hperm.mem_iff.mpr (Finset.mem_toList.mpr hx')
  have hinv := collectInvariant_init G.transpose
  have hfuel : 0 < G.transpose.vertices.card + 1 := by omega
  have hinv' := dfsFromListCollect_invariant G.transpose hfuel
    (kosaraju_order_subset_vertices G) dfsInit [] hinv
  have hinit : ∀ (v : V), dfsInit.color v = Color.white ∨ dfsInit.color v = Color.black := by
    intro v; apply Or.inl; rfl
  have hblack := dfsFromListCollect_all_black (G := G.transpose) (acc := []) hinit hfuel hmem
  have hcover := hinv'.cover v (by simpa using hv) (hblack v (by simpa using hv))
  rcases hcover with ⟨C, hC, hvC⟩
  use C
  exact ⟨hC, hvC⟩

/-- Every component returned by {name}`Graph.kosarajuComponents` is nonempty. -/
theorem kosarajuComponents_nonempty (G : Graph V) (C : Finset V)
    (hC : C ∈ G.kosarajuComponents) : C.Nonempty := by
  simp only [kosarajuComponents] at hC
  let order := G.vertices.toList.mergeSort (finishLe (G.dfs))
  have hinv := collectInvariant_init G.transpose
  have hfuel : 0 < G.transpose.vertices.card + 1 := by omega
  have hinv' := dfsFromListCollect_invariant G.transpose hfuel
    (kosaraju_order_subset_vertices G) dfsInit [] hinv
  exact hinv'.nonempty C hC

/-- In a pairwise-disjoint list of finsets, two distinct members cannot share a
vertex. -/
theorem unique_mem_of_pairwise_disjoint_cover {ccs : List (Finset V)}
    (hdisj : ccs.Pairwise (fun C D => Disjoint C D))
    {C D : Finset V}
    (hC : C ∈ ccs) (hD : D ∈ ccs) (hv : ∃ v, v ∈ C ∧ v ∈ D) : C = D := by
  induction ccs generalizing C D with
  | nil => simp at hC
  | cons E es ih =>
      rcases List.pairwise_cons.mp hdisj with ⟨hE, hdisj'⟩
      rcases hv with ⟨v, hvC, hvD⟩
      cases hC with
      | head =>
        cases hD with
        | head => rfl
        | tail _ hD =>
          have hdisjED : Disjoint E D := hE D hD
          have hnot : v ∉ D := Finset.disjoint_left.mp hdisjED (by simpa using hvC)
          exact False.elim (hnot (by simpa using hvD))
      | tail _ hC =>
        cases hD with
        | head =>
          have hdisjEC : Disjoint E C := hE C hC
          have hnot : v ∉ C := Finset.disjoint_left.mp hdisjEC (by simpa using hvD)
          exact False.elim (hnot (by simpa using hvC))
        | tail _ hD =>
          exact ih hdisj' hC hD ⟨v, hvC, hvD⟩

/-! ## SCC correctness (deferred DFS-theory core) -/

/-- Core DFS-theoretic lemma (admitted): every component returned by
{name}`Graph.kosarajuComponents` is strongly connected and maximal.

This is the only remaining gap for full SCC correctness.  It follows from
{name}`Graph.scc_finish_order`: a vertex chosen as the first white vertex in
decreasing finish-time order belongs to a source SCC of the still-unvisited
transpose graph, so the second DFS visits precisely its SCC. -/
theorem kosarajuComponent_scc_core (G : Graph V) (C : Finset V)
    (hC : C ∈ G.kosarajuComponents) :
    (∀ u ∈ C, ∀ v ∈ C, G.StronglyConnected u v) ∧
    (∀ w ∈ G.vertices, (∀ u ∈ C, G.StronglyConnected u w) → w ∈ C) := by
  sorry

/-- The components returned by {name}`Graph.kosarajuComponents` are exactly the
strongly connected components of {lit}`G`.

The structural properties (nonempty, subset, partition, disjointness, coverage)
are proved above; the DFS finish-time argument needed for strong-connectivity
and maximality is isolated in {name}`Graph.kosarajuComponent_scc_core`. -/
theorem kosarajuComponents_eq_sccs (G : Graph V) (C : Finset V)
    (hC : C ∈ G.kosarajuComponents) :
    G.IsSCC (C : Set V) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- non-empty
    exact kosarajuComponents_nonempty G C hC
  · -- subset of vertices
    exact kosarajuComponents_subset G C hC
  · -- pairwise strongly connected
    exact (kosarajuComponent_scc_core G C hC).1
  · -- maximal
    exact (kosarajuComponent_scc_core G C hC).2

/-- {name}`Graph.kosarajuComponents` is a valid SCC partition of {lit}`G`. -/
theorem kosarajuComponents_isSCCPartition (G : Graph V) :
    G.IsSCCPartition G.kosarajuComponents := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro C hC; exact kosarajuComponents_subset G C hC
  · intro C hC; exact (kosarajuComponents_eq_sccs G C hC).1
  · intro C hC u hu v hv
    exact (kosarajuComponents_eq_sccs G C hC).2.2.1 u hu v hv
  · intro C hC w hw hsc
    simp at hw
    apply hw.2
    exact (kosarajuComponents_eq_sccs G C hC).2.2.2 w hw.1 (fun u hu => hsc u hu)
  · intro v hv
    have ⟨C, hC, hvC⟩ := kosarajuComponents_cover G v hv
    use C
    constructor
    · exact ⟨hC, hvC⟩
    · intro D hD
      exact unique_mem_of_pairwise_disjoint_cover
        (kosarajuComponents_pairwise_disjoint G)
        hD.1 hC ⟨v, hD.2, hvC⟩

end Graph

end Chapter22
end CLRS

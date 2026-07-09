import Mathlib
import CLRSLean.Chapter_22.Section_22_1_Representing_Graphs
import CLRSLean.Chapter_22.Section_22_3_DFS
import CLRSLean.Chapter_22.Section_22_3_DFS_SCC
import CLRSLean.Chapter_22.Section_22_3_DFS_Bridge

/-! # Section 22.5 - Strongly Connected Components

This section gives Kosaraju's two-pass depth-first-search algorithm for
computing the strongly connected components of a directed graph on the finite
graph model from Section 22.1.

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

This file covers the algorithm, structural properties, and the core
finish-time-ordering lemmas ({lit}`scc_finish_time_order`
and {lit}`scc_finish_order`), as well as the final SCC correctness
theorems.

Current status:

- The finish-time-ordering proof ({lit}`Graph.scc_finish_time_order`) is
  complete.
- The second-pass invariant proof culminates in
  {lit}`Graph.kosarajuComponent_scc_core`, so the final
  {lit}`Graph.kosarajuComponents_isSCCPartition` theorem is fully proved.
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

theorem IsSCC_eq_of_nonempty_inter {C D : Set V}
    (hC : G.IsSCC C) (hD : G.IsSCC D) (h : ∃ x, x ∈ C ∧ x ∈ D) : C = D := by
  rcases h with ⟨x, hxC, hxD⟩
  apply Set.Subset.antisymm
  · intro c hc
    have hsc : ∀ d ∈ D, G.StronglyConnected c d := by
      intro d hd
      have hcx := hC.2.2.1 c hc x hxC
      have hxd := hD.2.2.1 x hxD d hd
      exact ⟨G.reachable_trans hcx.1 hxd.1, G.reachable_trans hxd.2 hcx.2⟩
    have hsc' : ∀ u ∈ D, G.StronglyConnected u c := by
      intro u hu
      exact G.stronglyConnected_symm (hsc u hu)
    exact hD.2.2.2 c (hC.2.1 hc) hsc'
  · intro d hd
    have hsc : ∀ c ∈ C, G.StronglyConnected d c := by
      intro c hc
      have hdx := hD.2.2.1 d hd x hxD
      have hxc := hC.2.2.1 x hxC c hc
      exact ⟨G.reachable_trans hdx.1 hxc.1, G.reachable_trans hxc.2 hdx.2⟩
    have hsc' : ∀ u ∈ C, G.StronglyConnected u d := by
      intro u hu
      exact G.stronglyConnected_symm (hsc u hu)
    exact hC.2.2.2 d (hD.2.1 hd) hsc'

theorem IsSCC_eq_or_disjoint {C D : Set V}
    (hC : G.IsSCC C) (hD : G.IsSCC D) : C = D ∨ Disjoint C D := by
  by_cases h : ∃ x, x ∈ C ∧ x ∈ D
  · left
    exact G.IsSCC_eq_of_nonempty_inter hC hD h
  · right
    rw [Set.disjoint_iff]
    intro x hx
    exact h ⟨x, hx.1, hx.2⟩

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
  decide (finishTime s v ≤ finishTime s u)

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

/-- The strongly connected component of {lit}`r` in {lit}`G`. -/
def sccOf (G : Graph V) (r : V) : Set V := {v | G.StronglyConnected r v}

theorem reachable_target_mem_vertices {u v : V} (hu : u ∈ G.vertices) (hr : G.Reachable u v) :
    v ∈ G.vertices := by
  induction hr with
  | refl => exact hu
  | tail _ hadj _ => exact G.adj_mem_right hadj

theorem transpose_reachable {u v : V} : G.transpose.Reachable u v ↔ G.Reachable v u := by
  constructor
  · intro hr
    induction hr with
    | refl => exact Relation.ReflTransGen.refl
    | @tail x y _ hadj ih =>
        have hGadj : G.Adj y x := by simpa using hadj
        exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single hGadj) ih
  · intro hr
    induction hr with
    | refl => exact Relation.ReflTransGen.refl
    | @tail x y _ hadj ih =>
        have hGadj : G.transpose.Adj y x := by simpa using hadj
        exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single hGadj) ih

theorem transpose_sccOf_eq (r : V) : G.transpose.sccOf r = G.sccOf r := by
  ext v
  simp [sccOf, StronglyConnected, transpose_reachable G]
  rw [and_comm]

theorem isSCC_sccOf {r : V} (hr : r ∈ G.vertices) : G.IsSCC (G.sccOf r) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · use r
    exact stronglyConnected_refl G r
  · intro v hv
    exact reachable_target_mem_vertices G hr hv.1
  · intro u hu v hv
    exact ⟨G.reachable_trans hu.2 hv.1, G.reachable_trans hv.2 hu.1⟩
  · intro w hw hsc
    exact hsc r (stronglyConnected_refl G r)

theorem finishLe_iff_le {s : DFSState V} {u v : V} :
    finishLe s u v ↔ finishTime s v ≤ finishTime s u := by
  simp [finishLe]

theorem WhiteReachable.of_reachable_through_set {s : DFSState V} {u v : V} {S : Set V}
    (hS : ∀ w, G.Reachable u w → G.Reachable w v → w ∈ S)
    (hwhite : ∀ w ∈ S, s.color w = Color.white)
    (huv : G.Reachable u v) :
    WhiteReachable G s u v := by
  induction huv with
  | refl => exact whiteReachable_refl G s u
  | @tail x y hux hadj ih =>
      have hyS : y ∈ S := hS y (G.reachable_trans hux (G.reachable_adj hadj)) (G.reachable_refl y)
      have ih' : WhiteReachable G s u x := ih (fun w h1 h2 => hS w h1 (G.reachable_trans h2 (G.reachable_adj hadj)))
      exact whiteReachable_step G ih' hadj (hwhite y hyS)

theorem maxFinish_sccOf_eq {s : DFSState V} {r : V} (hr : r ∈ G.vertices)
    (hmax : ∀ v, s.color v = Color.white → finishTime (G.dfs) v ≤ finishTime (G.dfs) r)
    (hwhite : ∀ v ∈ G.sccOf r, s.color v = Color.white) :
    maxFinish G (G.dfs) (G.sccOf r) = finishTime (G.dfs) r := by
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro v hv
    simp [sccOf] at hv
    exact hmax v (hwhite v hv.2)
  · have hsub : (G.sccOf r : Set V) ⊆ G.vertices := (isSCC_sccOf G hr).2.1
    exact finish_le_maxFinish G hsub (stronglyConnected_refl G r)

theorem maxFinish_white_scc_le {s : DFSState V} {r : V} {K : Set V}
    (_hK : G.IsSCC K) (hmax : ∀ v, s.color v = Color.white → finishTime (G.dfs) v ≤ finishTime (G.dfs) r)
    (hwhite : ∀ v ∈ K, s.color v = Color.white) :
    maxFinish G (G.dfs) K ≤ finishTime (G.dfs) r := by
  apply Finset.sup_le
  intro v hv
  simp at hv
  rcases hv with ⟨_, hvK⟩
  exact hmax v (hwhite v hvK)

/-! ## Graph-theoretic lemmas for SCC finish-time ordering -/

/-- If {lit}`x` is the first-discovered vertex of SCC {lit}`C` (in
{lit}`G.dfs`), then {lit}`x` can reach every vertex in {lit}`C`.  This is
purely graph-theoretic: it follows from the SCC property that every pair in
{lit}`C` is strongly connected. -/
theorem firstDiscovered_reachable_scc {C : Set V} (hC_nonempty : C.Nonempty)
    (hCsub : C ⊆ G.vertices) (hCsc : ∀ u ∈ C, ∀ v ∈ C, G.StronglyConnected u v)
    (v : V) (hv : v ∈ C) :
    let r := firstDiscoveredVertex G (s := G.dfs) (C := C) hC_nonempty hCsub
    G.Reachable r v := by
  intro r
  have hrC : r ∈ C := firstDiscoveredVertex_mem G (s := G.dfs) (C := C) hC_nonempty hCsub
  exact (hCsc r hrC v hv).1

/-- If there is an edge from {lit}`u` in SCC {lit}`C` to {lit}`y` in SCC
{lit}`D`, then every vertex in {lit}`C` can reach every vertex in {lit}`D`.
This uses the SCC property: within {lit}`C`, {lit}`x` reaches {lit}`u`; within
{lit}`D`, {lit}`y` reaches {lit}`w`. -/
theorem reachable_scc_to_scc {C D : Set V} (hCsc : ∀ u ∈ C, ∀ v ∈ C, G.StronglyConnected u v)
    (hDsc : ∀ u ∈ D, ∀ v ∈ D, G.StronglyConnected u v)
    (hedge : ∃ u ∈ C, ∃ v ∈ D, G.Adj u v)
    {x : V} (hx : x ∈ C) {w : V} (hw : w ∈ D) :
    G.Reachable x w := by
  rcases hedge with ⟨u, hu, v, hv, hadj⟩
  have hxu : G.Reachable x u := (hCsc x hx u hu).1
  have hvw : G.Reachable v w := (hDsc v hv w hw).1
  exact G.reachable_trans hxu (G.reachable_trans (G.reachable_adj hadj) hvw)

/-- Distinct SCCs with an edge from {lit}`C` to {lit}`D` have no path from
{lit}`D` back to {lit}`C`.  If such a path existed, {lit}`C` and {lit}`D`
would be a single SCC. -/
theorem no_reachable_scc_reverse {C D : Set V} (hC : G.IsSCC C) (hD : G.IsSCC D)
    (hne : C ≠ D) (hedge : ∃ u ∈ C, ∃ v ∈ D, G.Adj u v) (x y : V)
    (hx : x ∈ D) (hy : y ∈ C) : ¬ G.Reachable x y := by
  intro hreach
  apply hne
  apply IsSCC_eq_of_nonempty_inter G hC hD
  -- Find a vertex in the intersection: we'll show that y ∈ C ∩ D
  -- Since C and D must be equal
  rcases hC with ⟨⟨rC, hrC⟩, hCsub, hCsc, hCmax⟩
  rcases hD with ⟨⟨rD, hrD⟩, hDsub, hDsc, hDmax⟩
  rcases hedge with ⟨u, hu, v, hv, hadj⟩
  -- We show that y ∈ D (so y is in C ∩ D, giving the intersection)
  have hyV : y ∈ G.vertices := hCsub hy
  have h_forall : ∀ u ∈ D, G.StronglyConnected u y := by
    intro d hd
    -- d →* x (within D) → y (via x→*y) gives one direction
    -- y →* u (within C) → v (edge) →* d (within D) gives the other
    have hdx : G.Reachable d x := (hDsc d hd x hx).1
    have hxy : G.Reachable x y := hreach
    have hyu : G.Reachable y u := (hCsc y hy u hu).1
    have hvd : G.Reachable v d := (hDsc v hv d hd).1
    have hdy : G.Reachable d y := G.reachable_trans hdx hxy
    have hyd : G.Reachable y d :=
      G.reachable_trans hyu (G.reachable_trans (G.reachable_adj hadj) hvd)
    exact ⟨hdy, hyd⟩
  have hyD : y ∈ D := hDmax y hyV h_forall
  exact ⟨y, hy, hyD⟩

/-- If {lit}`u, v ∈ C` (same SCC) and {lit}`w` lies on a path from {lit}`u` to
{lit}`v`, then {lit}`w ∈ C`.  This is the SCC-path-closure property: SCCs are closed under
intermediate vertices on reachability paths. -/
theorem IsSCC.path_mem {C : Set V} (hC : G.IsSCC C) {u v w : V}
    (hu : u ∈ C) (hv : v ∈ C) (h1 : G.Reachable u w) (h2 : G.Reachable w v) :
    w ∈ C := by
  have hwV : w ∈ G.vertices := reachable_target_mem_vertices G (hC.2.1 hu) h1
  apply hC.2.2.2 w hwV
  intro x hx
  have hsc_xu : G.StronglyConnected x u := hC.2.2.1 x hx u hu
  have hsc_uv : G.StronglyConnected u v := hC.2.2.1 u hu v hv
  have hsc_uw : G.StronglyConnected u w := ⟨h1, G.reachable_trans h2 hsc_uv.2⟩
  exact ⟨G.reachable_trans hsc_xu.1 hsc_uw.1, G.reachable_trans hsc_uw.2 hsc_xu.2⟩

open Classical in
/-- Core finish-time ordering of distinct SCCs (CLRS Lemma 22.14).

If {lit}`C` and {lit}`D` are distinct strongly connected components of {lit}`G`
and there is an edge from {lit}`C` to {lit}`D`, then the maximum finish time in
{lit}`C` (after the first DFS) is strictly larger than the maximum finish time in
{lit}`D`. -/
theorem scc_finish_time_order {C D : Set V}
    (hC : G.IsSCC C) (hD : G.IsSCC D) (hne : C ≠ D)
    (hedge : ∃ u ∈ C, ∃ v ∈ D, G.Adj u v) :
    maxFinish G (G.dfs) D < maxFinish G (G.dfs) C := by
  have hC_nonempty : C.Nonempty := hC.1
  have hCsub : C ⊆ G.vertices := hC.2.1
  have hCsc : ∀ u ∈ C, ∀ v ∈ C, G.StronglyConnected u v := hC.2.2.1
  have hD_nonempty : D.Nonempty := hD.1
  have hDsub : D ⊆ G.vertices := hD.2.1
  have hDsc : ∀ u ∈ D, ∀ v ∈ D, G.StronglyConnected u v := hD.2.2.1
  let rC := firstDiscoveredVertex G (s := G.dfs) (C := C) hC_nonempty hCsub
  let rD := firstDiscoveredVertex G (s := G.dfs) (C := D) hD_nonempty hDsub
  have hrC_mem : rC ∈ C := firstDiscoveredVertex_mem G (s := G.dfs) (C := C) hC_nonempty hCsub
  have hrD_mem : rD ∈ D := firstDiscoveredVertex_mem G (s := G.dfs) (C := D) hD_nonempty hDsub
  have hdisc_min_C : ∀ v ∈ C, discoveryTime (G.dfs) rC ≤ discoveryTime (G.dfs) v :=
    fun v hv => firstDiscoveredVertex_min G (s := G.dfs) (C := C) hC_nonempty hCsub hv
  have hdisc_min_D : ∀ v ∈ D, discoveryTime (G.dfs) rD ≤ discoveryTime (G.dfs) v :=
    fun v hv => firstDiscoveredVertex_min G (s := G.dfs) (C := D) hD_nonempty hDsub hv
  -- Obtain max-finish witnesses
  rcases maxFinish_exists G (s := G.dfs) (C := C) hC_nonempty hCsub with ⟨c, hcC, hc_max⟩
  rcases maxFinish_exists G (s := G.dfs) (C := D) hD_nonempty hDsub with ⟨d, hdD, hd_max⟩
  rw [hc_max, hd_max]
  -- Compare discovery times of rC and rD
  by_cases hd_lt : discoveryTime (G.dfs) rC < discoveryTime (G.dfs) rD
  · -- Case 1: rC discovered first.  Use exists_discovery_state.
    have h_rC_vert : rC ∈ G.vertices := hCsub hrC_mem
    rcases exists_discovery_state G rC h_rC_vert with ⟨s, f, hs_white, hs_black, hdisc_eq, h_nonwhite, h_bf_s, h_gray_s, h_f_pres, h_fuel, h_later⟩
    -- hdisc_eq: d[rC] = s.time.  h_nonwhite: non-white w in s → d[w] < s.time = d[rC].
    -- h_bf_s: black-finish invariant for s.
    -- h_f_pres: f-preservation for dfsVisit output.
    -- h_fuel: f ≥ |whiteReachableSet s rC| + 1
    -- All of C ∪ D is white in s (otherwise d[v] < d[rC], contradicting firstDiscoveredVertex_min)
    have hwhite_C : ∀ v ∈ C, s.color v = Color.white := by
      intro v hv; by_cases hw : s.color v = Color.white; · exact hw
      · have h_lt := h_nonwhite v hw; rw [← hdisc_eq] at h_lt
        have h_le := hdisc_min_C v hv; omega
    have hwhite_D : ∀ v ∈ D, s.color v = Color.white := by
      intro v hv; by_cases hw : s.color v = Color.white; · exact hw
      · have h_lt := h_nonwhite v hw; rw [← hdisc_eq] at h_lt
        have hle := hdisc_min_D v hv; omega
    -- In particular, the max-finish vertex d ∈ D is white in s
    have hwhite_d : s.color d = Color.white := hwhite_D d hdD
    have hne_d_rC : d ≠ rC := by
      intro heq; subst d; apply hne
      exact IsSCC_eq_of_nonempty_inter G hC hD ⟨rC, hrC_mem, hdD⟩
    -- Construct an explicit white path: rC →* u → v →* d, where (u,v) is the C→D edge.
    -- All vertices in C ∪ D are white in s, and IsSCC.path_mem guarantees the path
    -- segments stay within C (for rC→*u) and D (for v→*d), so all vertices are white.
    rcases hedge with ⟨u, hu, v, hv, hadj⟩
    -- Segment rC →* u within C (all vertices in C, all white)
    have h_wr_rC_u : WhiteReachable G s rC u := by
      have h_reach : G.Reachable rC u := (hCsc rC hrC_mem u hu).1
      apply WhiteReachable.of_reachable_through_set G (S := C) ?_ (hwhite_C) h_reach
      intro w h1 h2; exact IsSCC.path_mem G hC hrC_mem hu h1 h2
    -- Edge u → v: v ∈ D is white in s
    have hwhite_v : s.color v = Color.white := hwhite_D v hv
    -- Step via the edge
    have h_wr_rC_v : WhiteReachable G s rC v :=
      whiteReachable_step G h_wr_rC_u hadj hwhite_v
    -- Segment v →* d within D (all vertices in D, all white)
    have h_wr_v_d : WhiteReachable G s v d := by
      have h_reach : G.Reachable v d := (hDsc v hv d hdD).1
      apply WhiteReachable.of_reachable_through_set G (S := D) ?_ (hwhite_D) h_reach
      intro w h1 h2; exact IsSCC.path_mem G hD hv hdD h1 h2
    -- Compose: rC →* v →* d
    have h_wr_rC_d : WhiteReachable G s rC d :=
      whiteReachable_trans G h_wr_rC_v h_wr_v_d
    -- By the white-path theorem, dfsVisit from rC blackens d
    have h_card : f ≥ (whiteReachableSet G s rC).card + 1 := h_fuel
    have h_black_d : (dfsVisit G f rC s).color d = Color.black := by
      apply dfsVisit_white_path_black G hs_white (hCsub hrC_mem) h_card
      exact WhiteReachable.mem_set G (hCsub hrC_mem) h_wr_rC_d
    -- d finishes before rC in the dfsVisit output
    have h_finish_lt : finishTime (dfsVisit G f rC s) d < finishTime (dfsVisit G f rC s) rC := by
      apply dfsVisit_finish_lt_source_finish G (by omega) hs_white h_bf_s hwhite_d h_black_d hne_d_rC
    -- f values preserved from dfsVisit to G.dfs (from exists_discovery_state)
    have h_f_preserved_d : finishTime (G.dfs) d = finishTime (dfsVisit G f rC s) d :=
      h_f_pres d h_black_d
    have h_f_preserved_rC : finishTime (G.dfs) rC = finishTime (dfsVisit G f rC s) rC :=
      h_f_pres rC hs_black
    have h_goal : finishTime (G.dfs) d < finishTime (G.dfs) c := by
      calc
        finishTime (G.dfs) d = finishTime (dfsVisit G f rC s) d := h_f_preserved_d
        _ < finishTime (dfsVisit G f rC s) rC := h_finish_lt
        _ = finishTime (G.dfs) rC := h_f_preserved_rC.symm
        _ ≤ finishTime (G.dfs) c := by
          have h := finish_le_maxFinish G (s := G.dfs) (C := C) hCsub hrC_mem
          rw [hc_max] at h; exact h
    omega
  · -- Case 2: rD discovered first (or same time), i.e., d[rD] ≤ d[rC].
    -- Since D cannot reach C, rC is not in rD's DFS tree, so rD finishes before
    -- rC is discovered: f[rD] < d[rC].
    have h_no_rev : ¬ G.Reachable rD rC :=
      no_reachable_scc_reverse G hC hD hne hedge rD rC hrD_mem hrC_mem
    have hd_le : discoveryTime (G.dfs) rD ≤ discoveryTime (G.dfs) rC := by omega
    -- Use exists_discovery_state for rD
    have h_rD_vert : rD ∈ G.vertices := hDsub hrD_mem
    rcases exists_discovery_state G rD h_rD_vert with
      ⟨s, f, hs_white, hs_black, hdisc_eq, h_nonwhite, h_bf_s, h_gray_s, h_f_pres, h_fuel, h_later⟩
    -- All of D is white in s
    have hwhite_D : ∀ v ∈ D, s.color v = Color.white := by
      intro v hv; by_cases hw : s.color v = Color.white; · exact hw
      · have h_lt := h_nonwhite v hw; rw [← hdisc_eq] at h_lt
        have hle := hdisc_min_D v hv; omega
    -- rC also white in s (d[rC] ≥ d[rD] = s.time)
    have hwhite_rC : s.color rC = Color.white := by
      by_cases hw : s.color rC = Color.white; · exact hw
      · have h_lt := h_nonwhite rC hw; rw [← hdisc_eq] at h_lt; omega
    -- rC NOT white-reachable from rD (D cannot reach C)
    have h_no_wr : ¬ WhiteReachable G s rD rC := by
      intro hwr; apply h_no_rev
      -- WhiteReachable implies Reachable (drop the color condition)
      have h_reach : G.Reachable rD rC :=
        hwr.mono (fun x y h => h.1)
      exact h_reach
    -- rC stays white after rD's dfsVisit (otherwise white-reachable)
    have h_rC_white_out : (dfsVisit G f rD s).color rC = Color.white := by
      by_cases hb : (dfsVisit G f rD s).color rC = Color.black
      · have h_wr : WhiteReachable G s rD rC :=
          dfsVisit_blackens_implies_whiteReachable G hs_white (by omega) hwhite_rC hb
        exact absurd h_wr h_no_wr
      · have h_no_gray : (dfsVisit G f rD s).color rC ≠ Color.gray := by
          intro hg; have h_input_gray : s.color rC = Color.gray := dfsVisit_no_new_gray G rC hg
          rw [hwhite_rC] at h_input_gray
          contradiction
        cases hcolor : (dfsVisit G f rD s).color rC with
        | white => rfl; | gray => exact (h_no_gray hcolor).elim; | black => exact (hb hcolor).elim
    -- Contradiction argument: if f[rD] ≥ d[rC], then d[rC] ∈ [s.time, result.time),
    -- so rC was discovered during rD's dfsVisit → white-reachable → contradiction.
    have h_finish_lt_disc : finishTime (G.dfs) rD < discoveryTime (G.dfs) rC := by
      have h_f_visit_rD_eq : finishTime (dfsVisit G f rD s) rD = (dfsVisit G f rD s).time - 1 :=
        dfsVisit_finishTime_source_eq_pred_time G (by omega) hs_white
      have h_visit_time_gt_f : (dfsVisit G f rD s).time > finishTime (dfsVisit G f rD s) rD := by
        have h_eq : finishTime (dfsVisit G f rD s) rD = (dfsVisit G f rD s).time - 1 := h_f_visit_rD_eq
        -- Since finishTime ≥ 0 in Nat, time ≥ 1, so time > time - 1 = f
        have h_time_pos : (dfsVisit G f rD s).time ≥ 1 := by
          have h_time_ge : (dfsVisit G f rD s).time ≥ s.time :=
            G.dfsVisit_time_ge (fuel := f) (u := rD) (s := s)
          have h_s_time : s.time = discoveryTime (G.dfs) rD := hdisc_eq.symm
          -- s.time could be 0, but dfsVisit advances clock at least by 1 for setDiscovery
          -- Actually, dfsVisit always increments the clock by at least 1 when fuel > 0 and u is white.
          -- Using dfsVisit_time_gt_of_white: if 0 < fuel and u is white, time > s.time.
          have h_time_gt_s : (dfsVisit G f rD s).time > s.time :=
            dfsVisit_time_gt_of_white G (by omega) hs_white
          omega
        omega
      have h_f_G_rD : finishTime (G.dfs) rD = finishTime (dfsVisit G f rD s) rD := h_f_pres rD hs_black
      rw [h_f_G_rD]
      by_contra h_ge
      -- h_ge: ¬ f_visit[rD] < d[rC], i.e., f_visit[rD] ≥ d[rC]
      -- Then d[rC] ≤ f_visit[rD] < (dfsVisit ...).time
      have h_disc_lt_time : discoveryTime (G.dfs) rC < (dfsVisit G f rD s).time := by omega
      have h_disc_ge_s_time : discoveryTime (G.dfs) rC ≥ s.time := by
        rw [← hdisc_eq]; exact hd_le
      -- d[rC] ∈ [s.time, result.time): rC would have to be discovered during
      -- or before this local visit, but the bridge says a still-white vertex is
      -- discovered only at or after the local visit's output time.
      have h_disc_ge_time : discoveryTime (G.dfs) rC ≥ (dfsVisit G f rD s).time := by
        have h_white_rC_out : (dfsVisit G f rD s).color rC = Color.white := h_rC_white_out
        have h_nonwhite_final : (G.dfs).color rC ≠ Color.white := by
          rw [G.dfs_all_black (hCsub hrC_mem)]; decide
        exact h_later rC h_white_rC_out h_nonwhite_final
      omega
    -- All vertices in D finish before rD (white-path, same as Case 1)
    have h_finish_D_lt_rD : ∀ v ∈ D, v ≠ rD → finishTime (G.dfs) v < finishTime (G.dfs) rD := by
      intro v hv hne
      have hwhite_v : s.color v = Color.white := hwhite_D v hv
      have h_reach : G.Reachable rD v := (hDsc rD hrD_mem v hv).1
      have h_wr : WhiteReachable G s rD v :=
        WhiteReachable.of_reachable_through_set G (S := D)
          (fun w h1 h2 => IsSCC.path_mem G hD hrD_mem hv h1 h2) (hwhite_D) h_reach
      have h_black_v : (dfsVisit G f rD s).color v = Color.black := by
        apply dfsVisit_white_path_black G hs_white (hDsub hrD_mem) h_fuel
        exact WhiteReachable.mem_set G (hDsub hrD_mem) h_wr
      have h_finish_lt : finishTime (dfsVisit G f rD s) v < finishTime (dfsVisit G f rD s) rD := by
        apply dfsVisit_finish_lt_source_finish G (by omega) hs_white h_bf_s hwhite_v h_black_v hne
      have h_f_G_v := h_f_pres v h_black_v
      have h_f_G_rD := h_f_pres rD hs_black
      simpa [h_f_G_v, h_f_G_rD] using h_finish_lt
    -- maxFinish(D) = f[rD]
    have h_maxFinish_D_eq : maxFinish G (G.dfs) D = finishTime (G.dfs) rD := by
      rcases maxFinish_exists G (s := G.dfs) (C := D) hD_nonempty hDsub with ⟨v, hv, hmax⟩
      by_cases h_v_rD : v = rD; · subst v; rw [hmax]
      · have h_lt : finishTime (G.dfs) v < finishTime (G.dfs) rD := h_finish_D_lt_rD v hv h_v_rD
        have h_le : finishTime (G.dfs) rD ≤ maxFinish G (G.dfs) D :=
          finish_le_maxFinish G (s := G.dfs) hDsub hrD_mem
        have : maxFinish G (G.dfs) D = finishTime (G.dfs) v := hmax
        have : finishTime (G.dfs) rD ≤ maxFinish G (G.dfs) D := h_le
        omega
    rw [← hd_max, h_maxFinish_D_eq]
    have h_rC_max : finishTime (G.dfs) rC ≤ finishTime (G.dfs) c := by
      have h := finish_le_maxFinish G (s := G.dfs) (C := C) hCsub hrC_mem
      rw [hc_max] at h; exact h
    have h_disc_lt_fin : discoveryTime (G.dfs) rC < finishTime (G.dfs) rC :=
      dfs_discovery_lt_finish G (hCsub hrC_mem)
    omega

theorem whiteReachableSet_subset_scc {s : DFSState V} {r : V}
    (hr : r ∈ G.transpose.vertices) (hwhite : s.color r = Color.white)
    (hmax : ∀ v, s.color v = Color.white → finishTime (G.dfs) v ≤ finishTime (G.dfs) r)
    (hrespects : ∀ K, G.IsSCC K → (∀ v ∈ K, s.color v = Color.white) ∨ (∀ v ∈ K, s.color v = Color.black)) :
    (whiteReachableSet G.transpose s r : Set V) ⊆ G.sccOf r := by
  have hrG : r ∈ G.vertices := by simpa using hr
  have hC : G.IsSCC (G.sccOf r) := isSCC_sccOf G hrG
  have hC_white : ∀ v ∈ G.sccOf r, s.color v = Color.white := by
    rcases hrespects (G.sccOf r) hC with (hw | hb)
    · exact hw
    · have : s.color r = Color.black := hb r (stronglyConnected_refl G r)
      simp [this] at hwhite
  have hCmax : maxFinish G (G.dfs) (G.sccOf r) = finishTime (G.dfs) r :=
    maxFinish_sccOf_eq G hrG hmax hC_white
  have hstable := whiteReachableIter_stable G.transpose s r hr
  intro v hv
  rw [hstable] at hv
  have h : ∀ n, ∀ v ∈ whiteReachableIter G.transpose s r n, v ∈ G.sccOf r := by
    intro n
    induction n with
    | zero =>
        intro v hv
        simp [whiteReachableIter] at hv
        rw [hv]
        exact stronglyConnected_refl G r
    | succ n ih =>
        intro v hv
        simp [whiteReachableIter, whiteReachableSucc, Finset.mem_filter, Finset.mem_biUnion] at hv
        rcases hv with (h | ⟨⟨w, hw, hadj⟩, hwhite_v⟩)
        · exact ih v h
        · have hw_scc : w ∈ G.sccOf r := ih w hw
          by_contra hne
          have htadj : G.transpose.Adj w v := by
            simp [Adj] at hadj ⊢
            exact hadj
          have hGadj : G.Adj v w := by
            have h := htadj
            simp [transpose_Adj] at h ⊢
            exact h
          have hvV : v ∈ G.vertices := G.adj_mem_left hGadj
          let D := G.sccOf v
          have hD : G.IsSCC D := isSCC_sccOf G hvV
          have hDneC : D ≠ G.sccOf r := by
            intro heq
            have hvinD : v ∈ D := stronglyConnected_refl G v
            rw [heq] at hvinD
            simp [sccOf] at hvinD
            tauto
          have hedge : ∃ u ∈ D, ∃ v ∈ G.sccOf r, G.Adj u v :=
            ⟨v, stronglyConnected_refl G v, w, hw_scc, hGadj⟩
          have hord := scc_finish_time_order G hD hC hDneC hedge
          have hD_white : ∀ v ∈ D, s.color v = Color.white := by
            rcases hrespects D hD with (hw' | hb')
            · exact hw'
            · have : s.color v = Color.black := hb' v (stronglyConnected_refl G v)
              simp [this] at hwhite_v
          have hDmax : maxFinish G (G.dfs) D ≤ finishTime (G.dfs) r :=
            maxFinish_white_scc_le G hD hmax hD_white
          linarith [hord, hCmax, hDmax]
  exact h (G.transpose.vertices.card + 1) v hv

/-- Core DFS finish-time lemma.

Consider a DFS state {lit}`s` of {lit}`G` and a white vertex {lit}`r` whose finish time is
maximal among all white vertices.  Then the DFS tree of {lit}`G.transpose` rooted
at {lit}`r` visits exactly the SCC of {lit}`r` in {lit}`G`.

The extra {lit}`respects` assumption guarantees that every SCC of {lit}`G` is
either completely white or completely black in {lit}`s`; this holds during
Kosaraju's second pass. -/
theorem scc_finish_order {G : Graph V} {s : DFSState V} {r : V}
    (hr : r ∈ G.transpose.vertices) (hwhite : s.color r = Color.white)
    (hmax : ∀ v, s.color v = Color.white → finishTime (G.dfs) v ≤ finishTime (G.dfs) r)
    (hfuel : fuel ≥ G.transpose.vertices.card + 1)
    (hrespects : ∀ K, G.IsSCC K → (∀ v ∈ K, s.color v = Color.white) ∨ (∀ v ∈ K, s.color v = Color.black)) :
    let s' := dfsVisit G.transpose fuel r s
    let C := G.transpose.vertices.filter (fun v => s.color v = Color.white ∧ s'.color v = Color.black)
    G.IsSCC (C : Set V) := by
  intro s' C
  have hrG : r ∈ G.vertices := by simpa using hr
  have hCr : G.IsSCC (G.sccOf r) := isSCC_sccOf G hrG
  have hCr_white : ∀ v ∈ G.sccOf r, s.color v = Color.white := by
    rcases hrespects (G.sccOf r) hCr with (hw | hb)
    · exact hw
    · have : s.color r = Color.black := hb r (stronglyConnected_refl G r)
      simp [this] at hwhite
  have hsubset : (C : Set V) ⊆ G.sccOf r := by
    intro v hv
    simp [C] at hv
    rcases hv with ⟨hvV, hwhite_v, hblack_v⟩
    have hw : v ∈ whiteReachableSet G.transpose s r := by
      apply WhiteReachable.mem_set G.transpose hr
      exact dfsVisit_blackens_implies_whiteReachable G.transpose hwhite (by omega) hwhite_v hblack_v
    exact whiteReachableSet_subset_scc G hr hwhite hmax hrespects hw
  have hsupset : G.sccOf r ⊆ (C : Set V) := by
    intro v hv
    have hwhite_v : s.color v = Color.white := hCr_white v hv
    have hvV : v ∈ G.transpose.vertices := by
      simpa using reachable_target_mem_vertices G hrG hv.1
    have hblack_v : s'.color v = Color.black := by
      have htr : G.transpose.Reachable r v := by
        rw [transpose_reachable G]
        exact (G.stronglyConnected_symm hv).1
      have hw : WhiteReachable G.transpose s r v :=
        WhiteReachable.of_reachable_through_set G.transpose
          (fun w h1 h2 => by
            have hC' : G.transpose.IsSCC (G.transpose.sccOf r) :=
              isSCC_sccOf G.transpose (by simpa using hrG)
            have hw_in : w ∈ G.transpose.sccOf r :=
              IsSCC.path_mem G.transpose hC' (stronglyConnected_refl G.transpose r) (by rw [transpose_sccOf_eq G r]; exact hv) h1 h2
            rw [transpose_sccOf_eq G r] at hw_in
            exact hw_in)
          (fun w hw => by
            exact hCr_white w hw)
          htr
      have hcard : (whiteReachableSet G.transpose s r).card ≤ G.transpose.vertices.card := by
        apply Finset.card_le_card
        exact whiteReachableSet_subset_vertices G.transpose s r hr
      have hfuel' : fuel ≥ (whiteReachableSet G.transpose s r).card + 1 := by omega
      exact dfsVisit_white_path_black G.transpose hwhite hr hfuel' (WhiteReachable.mem_set G.transpose hr hw)
    simp [C]
    exact ⟨hvV, hwhite_v, hblack_v⟩
  rw [Set.Subset.antisymm hsubset hsupset]
  exact hCr

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

/-!
## SCC correctness

The remaining section proves that each component collected by the second DFS
pass is exactly one strongly connected component, then packages those facts as
the final SCC-partition theorem.
-/

omit [DecidableEq V] in
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

/-! ## SCC correctness — helper lemmas -/

/-- In a list {lit}`u :: us` with {lit}`Pairwise (finishLe (G.dfs))`, every
element of {lit}`us` has finish time at most that of {lit}`u`.  This is the key
property that lets us satisfy the {lit}`hmax` precondition of
{lit}`scc_finish_order` at each step of the
second DFS pass. -/
lemma pairwise_head_max_finishTime (u : V) (us : List V)
    (hp : (u :: us).Pairwise (fun a b => finishTime (G.dfs) b < finishTime (G.dfs) a))
    (v : V) (hv : v ∈ us) :
    finishTime (G.dfs) v ≤ finishTime (G.dfs) u := by
  induction us generalizing u with
  | nil => simp at hv
  | cons w ws ih =>
      rcases List.pairwise_cons.mp hp with ⟨h_uw, hp'⟩
      -- h_uw : ∀ a', a' ∈ (w :: ws) → finishTime (G.dfs) a' < finishTime (G.dfs) u
      -- This means for w in particular: finishTime w < finishTime u
      have hlt_w_u : finishTime (G.dfs) w < finishTime (G.dfs) u := h_uw w (by simp)
      rcases List.mem_cons.mp hv with (rfl | hv')
      · omega
      · have hle : finishTime (G.dfs) v ≤ finishTime (G.dfs) w :=
          ih w hp' hv'
        omega

/-! ## SCC correctness — infrastructure lemmas -/

/-- A {name}`dfsVisit` from a source {lit}`u ∈ G.vertices` does not change the
{lit}`f` field of any vertex {lit}`v ∉ G.vertices`.  All {lit}`f`-changing
operations ({lit}`setFinish`) are on sources or recursively visited neighbours,
all of which are in {lit}`G.vertices`. -/
lemma dfsVisit_preserves_f_of_not_mem_vertices {fuel : Nat} {u v : V} {s : DFSState V}
    (hu : u ∈ G.vertices) (hv : v ∉ G.vertices) :
    (dfsVisit G fuel u s).f v = s.f v := by
  induction fuel generalizing u s with
  | zero => simp [dfsVisit]
  | succ n ih =>
      by_cases hwhite : s.color u = Color.white
      · let s1 := s.setColor u Color.gray |>.setDiscovery u
        let step := fun (s' : DFSState V) (w : V) =>
          if s'.color w = Color.white then dfsVisit G n w (s'.setParent w u) else s'
        let s2 := List.foldl step s1 (G.adj u).toList
        let s3 := s2.setColor u Color.black |>.setFinish u
        have h_eq : dfsVisit G (n+1) u s = s3 := by
          simp [dfsVisit, hwhite, s1, step, s2, s3]
        rw [h_eq]
        have h_s1 : s1.f v = s.f v := by simp [s1]
        have hne : v ≠ u := by intro heq; subst v; exact hv hu
        -- The fold over G.adj u preserves f v because every recursive call
        -- has source w ∈ G.adj u ⊆ G.vertices, hence v ≠ w, and the IH applies.
        -- General lemma: the fold preserves f v for any list whose elements are in G.vertices
        have h_fold_preserves : ∀ (l : List V) (s0 : DFSState V),
            (∀ w ∈ l, w ∈ G.vertices) →
            (List.foldl (fun (s' : DFSState V) (w : V) =>
              if s'.color w = Color.white then dfsVisit G n w (s'.setParent w u) else s')
            s0 l).f v = s0.f v := by
          intro l
          induction l with
          | nil => intro s0 _; rfl
          | cons w ws ih_ws =>
              intro s0 h_all
              have hw_vert : w ∈ G.vertices := h_all w (by simp)
              have h_ws : ∀ w' ∈ ws, w' ∈ G.vertices := by
                intro w' hw'; apply h_all w'; simp [hw']
              simp
              by_cases hw_white : s0.color w = Color.white
              · simp [hw_white]
                have h_rest := ih_ws (dfsVisit G n w (s0.setParent w u)) h_ws
                rw [h_rest]
                have h_rec : (dfsVisit G n w (s0.setParent w u)).f v =
                    (s0.setParent w u).f v :=
                  ih (u := w) (s := s0.setParent w u) hw_vert
                rw [h_rec]; simp
              · simp [hw_white]
                exact ih_ws s0 h_ws
        have h_all_adj : ∀ w ∈ (G.adj u).toList, w ∈ G.vertices := by
          intro w hw
          have hw_adj : w ∈ G.adj u := by simpa [Finset.mem_toList] using hw
          exact G.adj_sub u hu hw_adj
        have h_s2 : s2.f v = s1.f v :=
          h_fold_preserves (G.adj u).toList s1 h_all_adj
        have h_s3 : s3.f v = s2.f v := by
          simp [s3, hne]
        rw [h_s3, h_s2, h_s1]
      · simp [dfsVisit, hwhite]

/-- {name}`dfsFromList` preserves the {lit}`f` field of any vertex outside
{lit}`G.vertices`, provided all sources in the list are in {lit}`G.vertices`. -/
lemma dfsFromList_preserves_f_of_not_mem_vertices (fuel : Nat) (vs : List V) (s : DFSState V)
    (v : V) (hv : v ∉ G.vertices) (hvs : ∀ x ∈ vs, x ∈ G.vertices) :
    (dfsFromList G fuel vs s).f v = s.f v := by
  induction vs generalizing s with
  | nil => simp [dfsFromList]
  | cons u us ih =>
      have hu : u ∈ G.vertices := hvs u (by simp)
      have h_us : ∀ x ∈ us, x ∈ G.vertices := by
        intro x hx; apply hvs x; simp [hx]
      simp [dfsFromList]
      by_cases hwhite : s.color u = Color.white
      · simp [hwhite]
        rw [ih (dfsVisit G fuel u s) h_us,
          dfsVisit_preserves_f_of_not_mem_vertices G hu (v := v) hv]
      · simp [hwhite]
        exact ih s h_us

/-- For a vertex {lit}`v ∉ G.vertices`, the first DFS never sets its finish
time, so {lit}`finishTime (G.dfs) v = 0`. -/
lemma finishTime_zero_of_not_mem_vertices {v : V} (hv : v ∉ G.vertices) :
    finishTime (G.dfs) v = 0 := by
  have h_f_none : (G.dfs).f v = none := by
    have h_init : (dfsInit (V := V)).f v = none := rfl
    have h_preserve : (dfsFromList G (G.vertices.card + 1) G.vertices.toList dfsInit).f v =
        (dfsInit (V := V)).f v :=
      dfsFromList_preserves_f_of_not_mem_vertices G (G.vertices.card + 1)
        G.vertices.toList dfsInit v hv (by
          intro x hx
          simpa [Finset.mem_toList] using hx)
    simpa [dfs, h_init] using h_preserve
  simp [finishTime, h_f_none]

/-! ## SCC correctness core -/

/-- Core DFS-theoretic lemma: every component returned by
{name}`Graph.kosarajuComponents` is strongly connected and maximal.

The proof applies {name}`Graph.scc_finish_order` at each step of the second DFS
pass.  The first white vertex in decreasing finish-time order is maximal among
the currently white vertices, so its transpose DFS tree is exactly its SCC. -/
theorem kosarajuComponent_scc_core (G : Graph V) (C : Finset V)
    (hC : C ∈ G.kosarajuComponents) :
    (∀ u ∈ C, ∀ v ∈ C, G.StronglyConnected u v) ∧
    (∀ w ∈ G.vertices, (∀ u ∈ C, G.StronglyConnected u w) → w ∈ C) := by
  -- 1. Setup
  simp [kosarajuComponents] at hC
  let order := G.vertices.toList.mergeSort (finishLe (G.dfs))
  let fuel := G.vertices.card + 1
  have hfuel : fuel ≥ G.transpose.vertices.card + 1 := by
    simp [fuel]
  have hfuel_pos : 0 < fuel := by omega
  have hperm : order.Perm G.vertices.toList := by
    simpa [order] using List.mergeSort_perm G.vertices.toList (finishLe (G.dfs))
  have h_order_verts : ∀ v, v ∈ order → v ∈ G.transpose.vertices := by
    intro v hv
    have hvG : v ∈ G.vertices := by
      have : v ∈ G.vertices.toList := (hperm.mem_iff).mp hv
      simpa [Finset.mem_toList] using this
    simpa

  -- 2. Sortedness: `order` is Pairwise (finishTime b ≤ finishTime a).
  --    `finishLe` is the boolean form of this non-strict comparison, so the
  --    standard merge-sort pairwise theorem applies directly.
  have h_pairwise_le : order.Pairwise (fun a b => finishTime (G.dfs) b ≤ finishTime (G.dfs) a) := by
    have hpair : order.Pairwise (fun a b => finishLe (G.dfs) a b = true) := by
      dsimp [order]
      apply List.pairwise_mergeSort
      · intro a b c hab hbc
        simp [finishLe] at hab hbc ⊢
        omega
      · intro a b
        simp [finishLe]
        exact Nat.le_total (finishTime (G.dfs) b) (finishTime (G.dfs) a)
    exact hpair.imp (by
      intro a b hab
      simpa [finishLe] using hab)

  -- 3. head-max lemma for ≤ (non-strict)
  have h_head_max_le : ∀ (u : V) (us : List V),
      (u :: us).Pairwise (fun a b => finishTime (G.dfs) b ≤ finishTime (G.dfs) a) →
      ∀ v ∈ us, finishTime (G.dfs) v ≤ finishTime (G.dfs) u := by
    intro u us hp v hv
    induction us generalizing u with
    | nil => simp at hv
    | cons w ws ih =>
        rcases List.pairwise_cons.mp hp with ⟨h_uw, hp'⟩
        have hle_w_u : finishTime (G.dfs) w ≤ finishTime (G.dfs) u := h_uw w (by simp)
        rcases List.mem_cons.mp hv with (rfl | hv')
        · exact hle_w_u
        · have hle : finishTime (G.dfs) v ≤ finishTime (G.dfs) w := ih w hp' hv'
          omega

  -- 4. Main induction over dfsFromListCollect
  have h_main : ∀ (vs : List V) (s : DFSState V) (acc : List (Finset V)),
      vs.Pairwise (fun a b => finishTime (G.dfs) b ≤ finishTime (G.dfs) a) →
      (∀ v ∈ vs, v ∈ G.transpose.vertices) →
      (∀ C ∈ acc, G.IsSCC (C : Set V)) →
      (∀ v, v ∈ G.vertices → s.color v = Color.white → v ∈ vs) →
      (∀ K, G.IsSCC K → (∀ v ∈ K, s.color v = Color.white) ∨ (∀ v ∈ K, s.color v = Color.black)) →
      (∀ v, s.color v = Color.white ∨ s.color v = Color.black) →
      let (acc', _) := dfsFromListCollect G.transpose fuel vs s acc
      ∀ C ∈ acc', G.IsSCC (C : Set V) := by
    intro vs s acc hp_vs hvs_verts h_acc h_white_in_vs h_respects h_ng
    induction vs generalizing s acc with
    | nil => simp [dfsFromListCollect]; exact h_acc
    | cons u us ih =>
        simp [dfsFromListCollect]
        rcases List.pairwise_cons.mp hp_vs with ⟨h_u_head, hp_us⟩
        have hu_vert : u ∈ G.transpose.vertices := hvs_verts u (by simp)
        have h_us_verts : ∀ v ∈ us, v ∈ G.transpose.vertices := by
          intro v hv; apply hvs_verts v; simp [hv]
        by_cases hu_white : s.color u = Color.white
        · -- Process white u
          let s' := dfsVisit G.transpose fuel u s
          let comp := G.vertices.filter (fun v => s.color v = Color.white ∧ s'.color v = Color.black)
          -- hmax
          have hmax_u : ∀ v, s.color v = Color.white → finishTime (G.dfs) v ≤ finishTime (G.dfs) u := by
            intro v hv_white
            by_cases hvV : v ∈ G.vertices
            · have hv_in_vs : v ∈ u :: us := h_white_in_vs v hvV hv_white
              rcases List.mem_cons.mp hv_in_vs with (rfl | hv_us)
              · rfl
              · exact h_head_max_le u us hp_vs v hv_us
            · rw [finishTime_zero_of_not_mem_vertices G hvV]; omega
          -- comp is an SCC
          have h_comp_scc : G.IsSCC (comp : Set V) :=
            scc_finish_order hu_vert hu_white hmax_u hfuel h_respects
          -- u becomes black in s'
          have hu_black_s' : s'.color u = Color.black := by
            simpa [s'] using dfsVisit_blackens_u_pos G.transpose hfuel_pos hu_white
          -- G.sccOf u is all-white in s
          have h_sccOf_u_white : ∀ v ∈ G.sccOf u, s.color v = Color.white := by
            rcases h_respects (G.sccOf u) (isSCC_sccOf G (by simpa using hu_vert)) with (hw | hb)
            · exact hw
            · have : s.color u = Color.black := hb u (stronglyConnected_refl G u)
              simp [this] at hu_white
          -- Preserve white→vs invariant (P4)
          have h_white_in_us : ∀ v, v ∈ G.vertices → s'.color v = Color.white → v ∈ us := by
            intro x hxV hx_white_s'
            by_cases hx_in_us : x ∈ us
            · exact hx_in_us
            · have hx_white_s : s.color x = Color.white := by
                by_contra hnot
                have hblack_s : s.color x = Color.black := by
                  cases h_ng x with | inl hw => exact absurd hw hnot | inr hb => exact hb
                have hblack_s' : s'.color x = Color.black :=
                  dfsVisit_preserves_black G.transpose hblack_s
                rw [hblack_s'] at hx_white_s'; simp at hx_white_s'
              have hx_in_vs : x ∈ u :: us := h_white_in_vs x hxV hx_white_s
              rcases List.mem_cons.mp hx_in_vs with (rfl | h)
              · rw [hu_black_s'] at hx_white_s'; simp at hx_white_s'
              · exact absurd h hx_in_us
          -- Preserve SCC monochromatic invariant (P5)
          have h_respects' : ∀ K, G.IsSCC K → (∀ v ∈ K, s'.color v = Color.white) ∨
              (∀ v ∈ K, s'.color v = Color.black) := by
            intro K hK
            rcases h_respects K hK with (hw | hb)
            · by_cases hK_eq : (K : Set V) = G.sccOf u
              · subst hK_eq; right
                intro v hv
                have hpath : G.transpose.Reachable u v := by
                  rw [transpose_reachable G]
                  exact ((isSCC_sccOf G (by simpa using hu_vert)).2.2.1 v hv u
                    (stronglyConnected_refl G u)).1
                have h_wr : WhiteReachable G.transpose s u v :=
                  WhiteReachable.of_reachable_through_set G.transpose
                    (fun w h1 h2 => by
                      have h_sccT : G.transpose.IsSCC (G.transpose.sccOf u) :=
                        isSCC_sccOf G.transpose (by simpa using hu_vert)
                      have hu_sccT : u ∈ G.transpose.sccOf u := stronglyConnected_refl G.transpose u
                      have hv_sccT : v ∈ G.transpose.sccOf u := by
                        rw [transpose_sccOf_eq G u]; exact hv
                      have hw_sccT : w ∈ G.transpose.sccOf u :=
                        IsSCC.path_mem G.transpose h_sccT hu_sccT hv_sccT h1 h2
                      rw [transpose_sccOf_eq G u] at hw_sccT; exact hw_sccT)
                    (fun w hw => h_sccOf_u_white w hw) hpath
                have hfuel_wr : fuel ≥ (whiteReachableSet G.transpose s u).card + 1 := by
                  have hcard_wr : (whiteReachableSet G.transpose s u).card ≤ G.transpose.vertices.card :=
                    Finset.card_le_card (whiteReachableSet_subset_vertices G.transpose s u hu_vert)
                  have htcard : G.transpose.vertices.card = G.vertices.card := by simp
                  have hfuel_eq : fuel = G.vertices.card + 1 := rfl
                  omega
                have h_mem_set : v ∈ whiteReachableSet G.transpose s u :=
                  WhiteReachable.mem_set G.transpose hu_vert h_wr
                exact dfsVisit_white_path_black G.transpose hu_white hu_vert hfuel_wr h_mem_set
              · have h_disjoint : Disjoint (K : Set V) (G.sccOf u) :=
                  (IsSCC_eq_or_disjoint G hK (isSCC_sccOf G (by simpa using hu_vert))).resolve_left hK_eq
                left; intro v hvK
                have hv_not_scc : v ∉ G.sccOf u :=
                  (Set.disjoint_left.mp h_disjoint) hvK
                have hv_not_wr : v ∉ whiteReachableSet G.transpose s u := by
                  intro hwr; apply hv_not_scc
                  exact whiteReachableSet_subset_scc G hu_vert hu_white hmax_u h_respects hwr
                have hfuel_wr2 : fuel ≥ (whiteReachableSet G.transpose s u).card + 1 := by
                  have hcard_wr : (whiteReachableSet G.transpose s u).card ≤ G.transpose.vertices.card :=
                    Finset.card_le_card (whiteReachableSet_subset_vertices G.transpose s u hu_vert)
                  have htcard : G.transpose.vertices.card = G.vertices.card := by simp
                  have hfuel_eq : fuel = G.vertices.card + 1 := rfl
                  omega
                have h_not_black : s'.color v ≠ Color.black := by
                  dsimp [s']
                  have hiff := dfsVisit_blackens_iff_whiteReachable G.transpose hu_white hu_vert
                    (hw v hvK) hfuel_wr2
                  rw [hiff]; exact hv_not_wr
                have h_ng_s' : ∀ w, s'.color w = Color.white ∨ s'.color w = Color.black :=
                  dfsVisit_output_no_gray G.transpose h_ng
                cases h_ng_s' v with | inl hw' => exact hw' | inr hb' => exact absurd hb' h_not_black
            · right; intro v hv; apply dfsVisit_preserves_black G.transpose; exact hb v hv
          -- Preserve no-gray invariant (P6)
          have h_ng' : ∀ v, s'.color v = Color.white ∨ s'.color v = Color.black :=
            dfsVisit_output_no_gray G.transpose h_ng
          -- Recurse
          have h_mem : ∀ C' ∈ (comp :: acc), G.IsSCC (C' : Set V) := by
            intro C' hC'; rcases List.mem_cons.mp hC' with (rfl | hC'_acc)
            · exact h_comp_scc
            · exact h_acc C' hC'_acc
          have h_ih := ih s' (comp :: acc) hp_us h_us_verts h_mem h_white_in_us h_respects' h_ng'
          simpa [s', comp, dfsFromListCollect, hu_white] using h_ih
        · -- u non-white: skip
          have h_white_in_us : ∀ v, v ∈ G.vertices → s.color v = Color.white → v ∈ us := by
            intro x hxV hx
            have hx_in_vs : x ∈ u :: us := h_white_in_vs x hxV hx
            rcases List.mem_cons.mp hx_in_vs with (rfl | hx_us)
            · exact absurd hx hu_white
            · exact hx_us
          have h_ih := ih s acc hp_us h_us_verts h_acc h_white_in_us h_respects h_ng
          simpa [dfsFromListCollect, hu_white] using h_ih

  -- 5. Apply to initial state
  have h_init_sccs : ∀ C ∈ ([] : List (Finset V)), G.IsSCC (C : Set V) := by
    intro C h; simp at h
  have h_init_respects : ∀ K, G.IsSCC K → (∀ v ∈ K, (dfsInit (V := V)).color v = Color.white) ∨
      (∀ v ∈ K, (dfsInit (V := V)).color v = Color.black) := by
    intro K _; left; intro v _; rfl
  have h_init_ng : ∀ v, (dfsInit (V := V)).color v = Color.white ∨
      (dfsInit (V := V)).color v = Color.black := by
    intro v; left; rfl
  have h_init_white_in_order : ∀ v, v ∈ G.vertices →
      (dfsInit (V := V)).color v = Color.white → v ∈ order := by
    intro v hvV _
    have : v ∈ G.vertices.toList := by simpa [Finset.mem_toList] using hvV
    exact (hperm.mem_iff).mpr this
  have h_all_sccs := h_main order dfsInit [] h_pairwise_le h_order_verts
    h_init_sccs h_init_white_in_order h_init_respects h_init_ng
  have hC_scc : G.IsSCC (C : Set V) := h_all_sccs C hC
  exact ⟨hC_scc.2.2.1, hC_scc.2.2.2⟩

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

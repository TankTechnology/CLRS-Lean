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

theorem StronglyConnected.reachable {u v : V} (h : G.StronglyConnected u v) :
    G.Reachable u v :=
  h.1

theorem StronglyConnected.reverse_reachable {u v : V} (h : G.StronglyConnected u v) :
    G.Reachable v u :=
  h.2

theorem stronglyConnected_refl (u : V) : G.StronglyConnected u u :=
  ⟨G.reachable_refl u, G.reachable_refl u⟩

theorem stronglyConnected_symm {u v : V}
    (h : G.StronglyConnected u v) : G.StronglyConnected v u :=
  ⟨StronglyConnected.reverse_reachable G h, StronglyConnected.reachable G h⟩

theorem stronglyConnected_trans {u v w : V}
    (huv : G.StronglyConnected u v) (hvw : G.StronglyConnected v w) :
    G.StronglyConnected u w :=
  ⟨G.reachable_trans (StronglyConnected.reachable G huv) (StronglyConnected.reachable G hvw),
    G.reachable_trans (StronglyConnected.reverse_reachable G hvw)
      (StronglyConnected.reverse_reachable G huv)⟩

/-- A strongly connected component is a nonempty maximal subset of vertices in
which every pair of vertices is strongly connected. -/
def IsSCC (G : Graph V) (C : Set V) : Prop :=
  C.Nonempty ∧ C ⊆ G.vertices ∧
    (∀ u ∈ C, ∀ v ∈ C, G.StronglyConnected u v) ∧
    (∀ w ∈ G.vertices, (∀ u ∈ C, G.StronglyConnected u w) → w ∈ C)

theorem IsSCC.nonempty {C : Set V} (hC : G.IsSCC C) : C.Nonempty :=
  hC.1

theorem IsSCC.subset_vertices {C : Set V} (hC : G.IsSCC C) : C ⊆ G.vertices :=
  hC.2.1

theorem IsSCC.stronglyConnected {C : Set V} (hC : G.IsSCC C) :
    ∀ u ∈ C, ∀ v ∈ C, G.StronglyConnected u v :=
  hC.2.2.1

theorem IsSCC.maximal {C : Set V} (hC : G.IsSCC C) :
    ∀ w ∈ G.vertices, (∀ u ∈ C, G.StronglyConnected u w) → w ∈ C :=
  hC.2.2.2

theorem IsSCC_eq_of_nonempty_inter {C D : Set V}
    (hC : G.IsSCC C) (hD : G.IsSCC D) (h : ∃ x, x ∈ C ∧ x ∈ D) : C = D := by
  rcases h with ⟨x, hxC, hxD⟩
  apply Set.Subset.antisymm
  · intro c hc
    have hsc : ∀ d ∈ D, G.StronglyConnected c d := by
      intro d hd
      have hcx := IsSCC.stronglyConnected G hC c hc x hxC
      have hxd := IsSCC.stronglyConnected G hD x hxD d hd
      exact ⟨G.reachable_trans (StronglyConnected.reachable G hcx)
          (StronglyConnected.reachable G hxd),
        G.reachable_trans (StronglyConnected.reverse_reachable G hxd)
          (StronglyConnected.reverse_reachable G hcx)⟩
    have hsc' : ∀ u ∈ D, G.StronglyConnected u c := by
      intro u hu
      exact G.stronglyConnected_symm (hsc u hu)
    exact IsSCC.maximal G hD c (IsSCC.subset_vertices G hC hc) hsc'
  · intro d hd
    have hsc : ∀ c ∈ C, G.StronglyConnected d c := by
      intro c hc
      have hdx := IsSCC.stronglyConnected G hD d hd x hxD
      have hxc := IsSCC.stronglyConnected G hC x hxC c hc
      exact ⟨G.reachable_trans (StronglyConnected.reachable G hdx)
          (StronglyConnected.reachable G hxc),
        G.reachable_trans (StronglyConnected.reverse_reachable G hxc)
          (StronglyConnected.reverse_reachable G hdx)⟩
    have hsc' : ∀ u ∈ C, G.StronglyConnected u d := by
      intro u hu
      exact G.stronglyConnected_symm (hsc u hu)
    exact IsSCC.maximal G hC d (IsSCC.subset_vertices G hD hd) hsc'

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
        exact ⟨hu, hwhite, dfsVisit_blackens_u_pos G hfuel hwhite⟩
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
    exact reachable_target_mem_vertices G hr (StronglyConnected.reachable G hv)
  · intro u hu v hv
    exact ⟨G.reachable_trans (StronglyConnected.reverse_reachable G hu)
      (StronglyConnected.reachable G hv),
      G.reachable_trans (StronglyConnected.reverse_reachable G hv)
        (StronglyConnected.reachable G hu)⟩
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
  · have hsub : (G.sccOf r : Set V) ⊆ G.vertices :=
      IsSCC.subset_vertices G (isSCC_sccOf G hr)
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

/-- If every finish time in {lit}`C` is at most the finish time of {lit}`r ∈ C`,
then {lit}`r` attains {name}`maxFinish`. -/
theorem maxFinish_eq_of_forall_finish_le {s : DFSState V} {C : Set V} {r : V}
    (hsub : C ⊆ G.vertices) (hr : r ∈ C)
    (hle : ∀ v ∈ C, finishTime s v ≤ finishTime s r) :
    maxFinish G s C = finishTime s r := by
  apply Nat.le_antisymm
  · rw [maxFinish]
    apply Finset.sup_le
    intro v hv
    simp at hv
    exact hle v hv.2
  · exact finish_le_maxFinish G hsub hr

/-- A DFS state is SCC-monochrome when every SCC of {lit}`G` is either entirely
white or entirely black in that state.  This is the main invariant of the
second pass of Kosaraju's algorithm. -/
def SCCMonochrome (G : Graph V) (s : DFSState V) : Prop :=
  ∀ K, G.IsSCC K → (∀ v ∈ K, s.color v = Color.white) ∨
    (∀ v ∈ K, s.color v = Color.black)

/-- If SCCs are monochromatic and {lit}`r` is white, then every vertex in
{lit}`r`'s SCC is white. -/
theorem sccOf_white_of_monochrome {s : DFSState V} {r : V}
    (hr : r ∈ G.vertices) (hwhite : s.color r = Color.white)
    (hmono : G.SCCMonochrome s) :
    ∀ v ∈ G.sccOf r, s.color v = Color.white := by
  have hC : G.IsSCC (G.sccOf r) := isSCC_sccOf G hr
  rcases hmono (G.sccOf r) hC with (hw | hb)
  · exact hw
  · have hblack : s.color r = Color.black := hb r (stronglyConnected_refl G r)
    rw [hblack] at hwhite
    contradiction

/-- The SCC-specific invariant used while proving correctness of Kosaraju's
second DFS pass.  It tracks the proof obligations that are not already part of
the collecting-DFS invariant. -/
structure KosarajuSCCInvariant (G : Graph V) (vs : List V) (s : DFSState V)
    (acc : List (Finset V)) : Prop where
  acc_scc : ∀ C ∈ acc, G.IsSCC (C : Set V)
  white_in_vs : ∀ v, v ∈ G.vertices → s.color v = Color.white → v ∈ vs
  scc_monochrome : G.SCCMonochrome s
  no_gray : ∀ v, s.color v = Color.white ∨ s.color v = Color.black

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
  exact StronglyConnected.reachable G (hCsc r hrC v hv)

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
  have hxu : G.Reachable x u := StronglyConnected.reachable G (hCsc x hx u hu)
  have hvw : G.Reachable v w := StronglyConnected.reachable G (hDsc v hv w hw)
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
    have hdx : G.Reachable d x := StronglyConnected.reachable G (hDsc d hd x hx)
    have hxy : G.Reachable x y := hreach
    have hyu : G.Reachable y u := StronglyConnected.reachable G (hCsc y hy u hu)
    have hvd : G.Reachable v d := StronglyConnected.reachable G (hDsc v hv d hd)
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
  have hwV : w ∈ G.vertices := reachable_target_mem_vertices G (IsSCC.subset_vertices G hC hu) h1
  apply IsSCC.maximal G hC w hwV
  intro x hx
  have hsc_xu : G.StronglyConnected x u := IsSCC.stronglyConnected G hC x hx u hu
  have hsc_uv : G.StronglyConnected u v := IsSCC.stronglyConnected G hC u hu v hv
  have hsc_uw : G.StronglyConnected u w :=
    ⟨h1, G.reachable_trans h2 (StronglyConnected.reverse_reachable G hsc_uv)⟩
  exact ⟨G.reachable_trans (StronglyConnected.reachable G hsc_xu)
      (StronglyConnected.reachable G hsc_uw),
    G.reachable_trans (StronglyConnected.reverse_reachable G hsc_uw)
      (StronglyConnected.reverse_reachable G hsc_xu)⟩

/-- Inside an all-white SCC, reachability between two component vertices is
white-reachability. -/
theorem WhiteReachable.of_isSCC {s : DFSState V} {C : Set V} {u v : V}
    (hC : G.IsSCC C) (hu : u ∈ C) (hv : v ∈ C)
    (hwhite : ∀ w ∈ C, s.color w = Color.white) :
    WhiteReachable G s u v := by
  have hreach : G.Reachable u v :=
    StronglyConnected.reachable G (IsSCC.stronglyConnected G hC u hu v hv)
  exact WhiteReachable.of_reachable_through_set G (S := C)
    (fun w h1 h2 => IsSCC.path_mem G hC hu hv h1 h2) hwhite hreach

/-- If all vertices of SCCs {lit}`C` and {lit}`D` are white and there is an edge
from {lit}`C` to {lit}`D`, then white-reachability crosses from any vertex of
{lit}`C` to any vertex of {lit}`D`. -/
theorem WhiteReachable.across_scc_edge {s : DFSState V} {C D : Set V} {r d : V}
    (hC : G.IsSCC C) (hD : G.IsSCC D) (hr : r ∈ C) (hd : d ∈ D)
    (hwhite_C : ∀ w ∈ C, s.color w = Color.white)
    (hwhite_D : ∀ w ∈ D, s.color w = Color.white)
    (hedge : ∃ u ∈ C, ∃ v ∈ D, G.Adj u v) :
    WhiteReachable G s r d := by
  rcases hedge with ⟨u, hu, v, hv, hadj⟩
  have h_wr_r_u : WhiteReachable G s r u :=
    WhiteReachable.of_isSCC G hC hr hu hwhite_C
  have h_wr_r_v : WhiteReachable G s r v :=
    whiteReachable_step G h_wr_r_u hadj (hwhite_D v hv)
  have h_wr_v_d : WhiteReachable G s v d :=
    WhiteReachable.of_isSCC G hD hv hd hwhite_D
  exact whiteReachable_trans G h_wr_r_v h_wr_v_d

/-- White-reachability forgets to ordinary reachability, so a non-reachable
target is not white-reachable. -/
theorem not_whiteReachable_of_not_reachable {s : DFSState V} {u v : V}
    (hno : ¬ G.Reachable u v) : ¬ WhiteReachable G s u v := by
  intro hwr
  exact hno (hwr.mono (fun _ _ h => h.1))

/-- At the discovery state of {lit}`r`, any vertex whose final discovery time is
not earlier than {lit}`r`'s is still white. -/
theorem white_at_discovery_state_of_discovery_ge {s : DFSState V} {r v : V}
    (hdisc_eq : discoveryTime (G.dfs) r = s.time)
    (h_nonwhite : ∀ w, s.color w ≠ Color.white → discoveryTime (G.dfs) w < s.time)
    (hge : discoveryTime (G.dfs) r ≤ discoveryTime (G.dfs) v) :
    s.color v = Color.white := by
  by_cases hw : s.color v = Color.white
  · exact hw
  · have hlt := h_nonwhite v hw
    rw [← hdisc_eq] at hlt
    omega

/-- Set version of {name}`Graph.white_at_discovery_state_of_discovery_ge`. -/
theorem set_white_at_discovery_state_of_min_discovery {s : DFSState V} {C : Set V} {r : V}
    (hdisc_eq : discoveryTime (G.dfs) r = s.time)
    (h_nonwhite : ∀ w, s.color w ≠ Color.white → discoveryTime (G.dfs) w < s.time)
    (hmin : ∀ v ∈ C, discoveryTime (G.dfs) r ≤ discoveryTime (G.dfs) v) :
    ∀ v ∈ C, s.color v = Color.white := by
  intro v hv
  exact white_at_discovery_state_of_discovery_ge G hdisc_eq h_nonwhite (hmin v hv)

/-- If {lit}`rC` is discovered before {lit}`rD`, and each is first-discovered in
its set, then both sets are white at {lit}`rC`'s discovery state. -/
theorem sets_white_at_earlier_discovery_state {s : DFSState V} {C D : Set V} {rC rD : V}
    (hdisc_eq : discoveryTime (G.dfs) rC = s.time)
    (h_nonwhite : ∀ w, s.color w ≠ Color.white → discoveryTime (G.dfs) w < s.time)
    (hmin_C : ∀ v ∈ C, discoveryTime (G.dfs) rC ≤ discoveryTime (G.dfs) v)
    (hmin_D : ∀ v ∈ D, discoveryTime (G.dfs) rD ≤ discoveryTime (G.dfs) v)
    (hlt : discoveryTime (G.dfs) rC < discoveryTime (G.dfs) rD) :
    (∀ v ∈ C, s.color v = Color.white) ∧ (∀ v ∈ D, s.color v = Color.white) := by
  constructor
  · exact set_white_at_discovery_state_of_min_discovery G hdisc_eq h_nonwhite hmin_C
  · apply set_white_at_discovery_state_of_min_discovery G hdisc_eq h_nonwhite
    intro v hv
    have hle := hmin_D v hv
    omega

/-- A white vertex that is not white-reachable from a white DFS root remains
white after that root's visit. -/
theorem dfsVisit_preserves_white_of_not_whiteReachable {fuel : Nat} {s : DFSState V}
    {u v : V} (hu_white : s.color u = Color.white) (hfuel : 0 < fuel)
    (hv_white : s.color v = Color.white) (hno : ¬ WhiteReachable G s u v) :
    (dfsVisit G fuel u s).color v = Color.white := by
  by_cases hb : (dfsVisit G fuel u s).color v = Color.black
  · have hwr : WhiteReachable G s u v :=
      dfsVisit_blackens_implies_whiteReachable G hu_white hfuel hv_white hb
    exact absurd hwr hno
  · have hno_gray : (dfsVisit G fuel u s).color v ≠ Color.gray := by
      intro hg
      have h_input_gray : s.color v = Color.gray := dfsVisit_no_new_gray G v hg
      rw [hv_white] at h_input_gray
      contradiction
    cases hcolor : (dfsVisit G fuel u s).color v with
    | white => rfl
    | gray => exact (hno_gray hcolor).elim
    | black => exact (hb hcolor).elim

/-- If a local visit finishes its source, leaves another vertex white, and the
full DFS later discovers that vertex, then the source finishes before that
vertex is discovered in the full DFS. -/
theorem finish_before_discovery_of_visit_output_white {fuel : Nat} {s : DFSState V}
    {u v : V} (hu_white : s.color u = Color.white) (hfuel : 0 < fuel)
    (hfinish_pres :
      finishTime (G.dfs) u = finishTime (dfsVisit G fuel u s) u)
    (hv_white_out : (dfsVisit G fuel u s).color v = Color.white)
    (hlater : ∀ w, (dfsVisit G fuel u s).color w = Color.white →
      (G.dfs).color w ≠ Color.white →
      (dfsVisit G fuel u s).time ≤ discoveryTime (G.dfs) w)
    (hv_final_nonwhite : (G.dfs).color v ≠ Color.white) :
    finishTime (G.dfs) u < discoveryTime (G.dfs) v := by
  have hfinish_visit :
      finishTime (dfsVisit G fuel u s) u = (dfsVisit G fuel u s).time - 1 :=
    dfsVisit_finishTime_source_eq_pred_time G hfuel hu_white
  have htime_gt_finish :
      (dfsVisit G fuel u s).time > finishTime (dfsVisit G fuel u s) u := by
    have htime_gt_s : (dfsVisit G fuel u s).time > s.time :=
      dfsVisit_time_gt_of_white G hfuel hu_white
    omega
  rw [hfinish_pres]
  by_contra hnot
  have hdisc_lt_time :
      discoveryTime (G.dfs) v < (dfsVisit G fuel u s).time := by
    omega
  have hdisc_ge_time :
      (dfsVisit G fuel u s).time ≤ discoveryTime (G.dfs) v :=
    hlater v hv_white_out hv_final_nonwhite
  omega

/-- If a white-reachable vertex is blackened during a local visit, then its full
DFS finish time is strictly before the source's full DFS finish time. -/
theorem finish_lt_source_in_full_dfs_of_whiteReachable_visit {fuel : Nat} {s : DFSState V}
    {u v : V} (hu_vert : u ∈ G.vertices) (hu_white : s.color u = Color.white)
    (hbf : ∀ w, s.color w = Color.black → finishTime s w < s.time)
    (hfuel : fuel ≥ (whiteReachableSet G s u).card + 1)
    (hv_white : s.color v = Color.white) (hwr : WhiteReachable G s u v)
    (hne : v ≠ u)
    (hpres : ∀ w, (dfsVisit G fuel u s).color w = Color.black →
      finishTime (G.dfs) w = finishTime (dfsVisit G fuel u s) w) :
    finishTime (G.dfs) v < finishTime (G.dfs) u := by
  have hfuel_pos : 0 < fuel := by omega
  have hblack_v : (dfsVisit G fuel u s).color v = Color.black := by
    apply dfsVisit_white_path_black G hu_white hu_vert hfuel
    exact WhiteReachable.mem_set G hu_vert hwr
  have hfinish_lt :
      finishTime (dfsVisit G fuel u s) v < finishTime (dfsVisit G fuel u s) u := by
    apply dfsVisit_finish_lt_source_finish G hfuel_pos hu_white hbf hv_white hblack_v hne
  have hblack_u : (dfsVisit G fuel u s).color u = Color.black :=
    dfsVisit_blackens_u_pos G hfuel_pos hu_white
  have h_f_v := hpres v hblack_v
  have h_f_u := hpres u hblack_u
  simpa [h_f_v, h_f_u] using hfinish_lt

/-- If an SCC is white in a discovery state, and a local DFS visit from a vertex
in that SCC has finish times preserved into the full DFS, then that source
attains the SCC's maximum full-DFS finish time. -/
theorem maxFinish_eq_of_white_scc_visit_source {fuel : Nat} {s : DFSState V}
    {C : Set V} {r : V} (hC : G.IsSCC C) (hr : r ∈ C)
    (hwhite_C : ∀ v ∈ C, s.color v = Color.white)
    (hr_white : s.color r = Color.white)
    (hbf : ∀ w, s.color w = Color.black → finishTime s w < s.time)
    (hfuel : fuel ≥ (whiteReachableSet G s r).card + 1)
    (hpres : ∀ w, (dfsVisit G fuel r s).color w = Color.black →
      finishTime (G.dfs) w = finishTime (dfsVisit G fuel r s) w) :
    maxFinish G (G.dfs) C = finishTime (G.dfs) r := by
  have hCsub : C ⊆ G.vertices := IsSCC.subset_vertices G hC
  apply maxFinish_eq_of_forall_finish_le G (s := G.dfs) hCsub hr
  intro v hv
  by_cases hvr : v = r
  · subst v
    rfl
  · have hv_white : s.color v = Color.white := hwhite_C v hv
    have hwr : WhiteReachable G s r v :=
      WhiteReachable.of_isSCC G hC hr hv hwhite_C
    exact le_of_lt (finish_lt_source_in_full_dfs_of_whiteReachable_visit G
      (hCsub hr) hr_white hbf hfuel hv_white hwr hvr hpres)

/-- If two distinct SCCs are white in a discovery state and there is an edge from
the first to the second, then a local DFS visit from the first SCC finishes each
target SCC vertex before the source. -/
theorem finish_lt_source_of_white_scc_edge_visit {fuel : Nat} {s : DFSState V}
    {C D : Set V} {r d : V} (hC : G.IsSCC C) (hD : G.IsSCC D)
    (hne : C ≠ D) (hedge : ∃ u ∈ C, ∃ v ∈ D, G.Adj u v)
    (hr : r ∈ C) (hd : d ∈ D)
    (hwhite_C : ∀ v ∈ C, s.color v = Color.white)
    (hwhite_D : ∀ v ∈ D, s.color v = Color.white)
    (hbf : ∀ w, s.color w = Color.black → finishTime s w < s.time)
    (hfuel : fuel ≥ (whiteReachableSet G s r).card + 1)
    (hpres : ∀ w, (dfsVisit G fuel r s).color w = Color.black →
      finishTime (G.dfs) w = finishTime (dfsVisit G fuel r s) w) :
    finishTime (G.dfs) d < finishTime (G.dfs) r := by
  have hCsub : C ⊆ G.vertices := IsSCC.subset_vertices G hC
  have hr_white : s.color r = Color.white := hwhite_C r hr
  have hd_white : s.color d = Color.white := hwhite_D d hd
  have hne_dr : d ≠ r := by
    intro heq
    subst d
    apply hne
    exact IsSCC_eq_of_nonempty_inter G hC hD ⟨r, hr, hd⟩
  have hwr : WhiteReachable G s r d :=
    WhiteReachable.across_scc_edge G hC hD hr hd hwhite_C hwhite_D hedge
  exact finish_lt_source_in_full_dfs_of_whiteReachable_visit G (hCsub hr)
    hr_white hbf hfuel hd_white hwr hne_dr hpres

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
  have hC_nonempty : C.Nonempty := IsSCC.nonempty G hC
  have hCsub : C ⊆ G.vertices := IsSCC.subset_vertices G hC
  have hD_nonempty : D.Nonempty := IsSCC.nonempty G hD
  have hDsub : D ⊆ G.vertices := IsSCC.subset_vertices G hD
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
    have hsets_white :=
      sets_white_at_earlier_discovery_state G hdisc_eq h_nonwhite hdisc_min_C hdisc_min_D hd_lt
    have hwhite_C : ∀ v ∈ C, s.color v = Color.white := hsets_white.1
    have hwhite_D : ∀ v ∈ D, s.color v = Color.white := hsets_white.2
    have h_goal : finishTime (G.dfs) d < finishTime (G.dfs) c := by
      have h_finish_d_lt_rC :
          finishTime (G.dfs) d < finishTime (G.dfs) rC :=
        finish_lt_source_of_white_scc_edge_visit G hC hD hne hedge hrC_mem hdD
          hwhite_C hwhite_D h_bf_s h_fuel h_f_pres
      calc
        finishTime (G.dfs) d < finishTime (G.dfs) rC := h_finish_d_lt_rC
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
    have hwhite_D : ∀ v ∈ D, s.color v = Color.white :=
      set_white_at_discovery_state_of_min_discovery G hdisc_eq h_nonwhite hdisc_min_D
    -- rC also white in s (d[rC] ≥ d[rD] = s.time)
    have hwhite_rC : s.color rC = Color.white :=
      white_at_discovery_state_of_discovery_ge G hdisc_eq h_nonwhite hd_le
    -- rC NOT white-reachable from rD (D cannot reach C)
    have h_no_wr : ¬ WhiteReachable G s rD rC :=
      not_whiteReachable_of_not_reachable G h_no_rev
    -- rC stays white after rD's dfsVisit (otherwise white-reachable)
    have h_rC_white_out : (dfsVisit G f rD s).color rC = Color.white :=
      dfsVisit_preserves_white_of_not_whiteReachable G hs_white (by omega) hwhite_rC h_no_wr
    -- Since rC stays white after rD's local visit but is black in the full DFS,
    -- the discovery-state bridge forces rD to finish before rC is discovered.
    have h_finish_lt_disc : finishTime (G.dfs) rD < discoveryTime (G.dfs) rC := by
      have h_f_G_rD : finishTime (G.dfs) rD = finishTime (dfsVisit G f rD s) rD := h_f_pres rD hs_black
      have h_nonwhite_final : (G.dfs).color rC ≠ Color.white := by
        rw [G.dfs_all_black (hCsub hrC_mem)]; decide
      exact finish_before_discovery_of_visit_output_white G hs_white (by omega)
        h_f_G_rD h_rC_white_out h_later h_nonwhite_final
    -- maxFinish(D) = f[rD]
    have h_maxFinish_D_eq : maxFinish G (G.dfs) D = finishTime (G.dfs) rD :=
      maxFinish_eq_of_white_scc_visit_source G hD hrD_mem hwhite_D hs_white h_bf_s h_fuel
        h_f_pres
    rw [← hd_max, h_maxFinish_D_eq]
    have h_rC_max : finishTime (G.dfs) rC ≤ finishTime (G.dfs) c := by
      have h := finish_le_maxFinish G (s := G.dfs) (C := C) hCsub hrC_mem
      rw [hc_max] at h; exact h
    have h_disc_lt_fin : discoveryTime (G.dfs) rC < finishTime (G.dfs) rC :=
      dfs_discovery_lt_finish G (hCsub hrC_mem)
    omega

/-- If {lit}`r` is maximal among the currently white vertices and SCCs are
monochrome, then a white predecessor of a vertex in {lit}`r`'s SCC is also in
{lit}`r`'s SCC.  This is the local contradiction step used when traversing the
transpose graph in Kosaraju's second pass. -/
theorem white_predecessor_mem_sccOf_of_max_finish {s : DFSState V} {r v w : V}
    (hr : r ∈ G.vertices) (hwhite_r : s.color r = Color.white)
    (hmax : ∀ x, s.color x = Color.white → finishTime (G.dfs) x ≤ finishTime (G.dfs) r)
    (hrespects : G.SCCMonochrome s)
    (hw_scc : w ∈ G.sccOf r) (hGadj : G.Adj v w)
    (hwhite_v : s.color v = Color.white) :
    v ∈ G.sccOf r := by
  have hC : G.IsSCC (G.sccOf r) := isSCC_sccOf G hr
  have hC_white : ∀ x ∈ G.sccOf r, s.color x = Color.white :=
    sccOf_white_of_monochrome G hr hwhite_r hrespects
  have hCmax : maxFinish G (G.dfs) (G.sccOf r) = finishTime (G.dfs) r :=
    maxFinish_sccOf_eq G hr hmax hC_white
  by_contra hne
  have hvV : v ∈ G.vertices := G.adj_mem_left hGadj
  let D := G.sccOf v
  have hD : G.IsSCC D := isSCC_sccOf G hvV
  have hDneC : D ≠ G.sccOf r := by
    intro heq
    have hvinD : v ∈ D := stronglyConnected_refl G v
    rw [heq] at hvinD
    exact hne hvinD
  have hedge : ∃ u ∈ D, ∃ v ∈ G.sccOf r, G.Adj u v :=
    ⟨v, stronglyConnected_refl G v, w, hw_scc, hGadj⟩
  have hord := scc_finish_time_order G hD hC hDneC hedge
  have hD_white : ∀ x ∈ D, s.color x = Color.white := by
    rcases hrespects D hD with (hw' | hb')
    · exact hw'
    · have hblack : s.color v = Color.black := hb' v (stronglyConnected_refl G v)
      rw [hblack] at hwhite_v
      contradiction
  have hDmax : maxFinish G (G.dfs) D ≤ finishTime (G.dfs) r :=
    maxFinish_white_scc_le G hD hmax hD_white
  linarith [hord, hCmax, hDmax]

theorem whiteReachableSet_subset_scc {s : DFSState V} {r : V}
    (hr : r ∈ G.transpose.vertices) (hwhite : s.color r = Color.white)
    (hmax : ∀ v, s.color v = Color.white → finishTime (G.dfs) v ≤ finishTime (G.dfs) r)
    (hrespects : G.SCCMonochrome s) :
    (whiteReachableSet G.transpose s r : Set V) ⊆ G.sccOf r := by
  have hrG : r ∈ G.vertices := by simpa using hr
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
          have htadj : G.transpose.Adj w v := by
            simp [Adj] at hadj ⊢
            exact hadj
          have hGadj : G.Adj v w := by
            have h := htadj
            simp [transpose_Adj] at h ⊢
            exact h
          exact white_predecessor_mem_sccOf_of_max_finish G hrG hwhite hmax hrespects
            hw_scc hGadj hwhite_v
  exact h (G.transpose.vertices.card + 1) v hv

/-- A transpose DFS visit from a white root blackens every vertex in that root's
original SCC, provided that SCC is still white. -/
theorem dfsVisit_transpose_blackens_sccOf {s : DFSState V} {r v : V}
    (hr : r ∈ G.transpose.vertices) (hwhite_r : s.color r = Color.white)
    (hfuel : fuel ≥ G.transpose.vertices.card + 1)
    (h_scc_white : ∀ w ∈ G.sccOf r, s.color w = Color.white)
    (hv : v ∈ G.sccOf r) :
    (dfsVisit G.transpose fuel r s).color v = Color.black := by
  have h_sccT : G.transpose.IsSCC (G.transpose.sccOf r) :=
    isSCC_sccOf G.transpose hr
  have hr_sccT : r ∈ G.transpose.sccOf r := stronglyConnected_refl G.transpose r
  have hv_sccT : v ∈ G.transpose.sccOf r := by
    rw [transpose_sccOf_eq G r]
    exact hv
  have hwhite_sccT : ∀ w ∈ G.transpose.sccOf r, s.color w = Color.white := by
    intro w hw
    rw [transpose_sccOf_eq G r] at hw
    exact h_scc_white w hw
  have h_wr : WhiteReachable G.transpose s r v :=
    WhiteReachable.of_isSCC G.transpose h_sccT hr_sccT hv_sccT hwhite_sccT
  have hcard : (whiteReachableSet G.transpose s r).card ≤ G.transpose.vertices.card := by
    apply Finset.card_le_card
    exact whiteReachableSet_subset_vertices G.transpose s r hr
  have hfuel_wr : fuel ≥ (whiteReachableSet G.transpose s r).card + 1 := by omega
  exact dfsVisit_white_path_black G.transpose hwhite_r hr hfuel_wr
    (WhiteReachable.mem_set G.transpose hr h_wr)

/-- A vertex that is white before a transpose DFS visit and black afterwards
belongs to the source's original SCC when the source has maximal white finish
time. -/
theorem transpose_visit_blackened_white_mem_sccOf {fuel : Nat} {s : DFSState V}
    {r v : V} (hr : r ∈ G.transpose.vertices) (hwhite_r : s.color r = Color.white)
    (hfuel : 0 < fuel)
    (hmax : ∀ x, s.color x = Color.white → finishTime (G.dfs) x ≤ finishTime (G.dfs) r)
    (hrespects : G.SCCMonochrome s)
    (hv_white : s.color v = Color.white)
    (hv_black : (dfsVisit G.transpose fuel r s).color v = Color.black) :
    v ∈ G.sccOf r := by
  have hwr : WhiteReachable G.transpose s r v :=
    dfsVisit_blackens_implies_whiteReachable G.transpose hwhite_r hfuel hv_white hv_black
  have hv_wr_set : v ∈ whiteReachableSet G.transpose s r :=
    WhiteReachable.mem_set G.transpose hr hwr
  exact whiteReachableSet_subset_scc G hr hwhite_r hmax hrespects hv_wr_set

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
    (hrespects : G.SCCMonochrome s) :
    let s' := dfsVisit G.transpose fuel r s
    let C := G.transpose.vertices.filter (fun v => s.color v = Color.white ∧ s'.color v = Color.black)
    G.IsSCC (C : Set V) := by
  intro s' C
  have hrG : r ∈ G.vertices := by simpa using hr
  have hCr : G.IsSCC (G.sccOf r) := isSCC_sccOf G hrG
  have hCr_white : ∀ v ∈ G.sccOf r, s.color v = Color.white :=
    sccOf_white_of_monochrome G hrG hwhite hrespects
  have hsubset : (C : Set V) ⊆ G.sccOf r := by
    intro v hv
    simp [C] at hv
    rcases hv with ⟨_, hwhite_v, hblack_v⟩
    exact transpose_visit_blackened_white_mem_sccOf G hr hwhite (by omega)
      hmax hrespects hwhite_v hblack_v
  have hsupset : G.sccOf r ⊆ (C : Set V) := by
    intro v hv
    have hwhite_v : s.color v = Color.white := hCr_white v hv
    have hvV : v ∈ G.transpose.vertices := by
      simpa using reachable_target_mem_vertices G hrG (StronglyConnected.reachable G hv)
    have hblack_v : s'.color v = Color.black := by
      exact dfsVisit_transpose_blackens_sccOf G hr hwhite hfuel hCr_white hv
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

/-- Every vertex of {lit}`G` appears in the order used by Kosaraju's second DFS. -/
theorem kosaraju_order_contains_vertices (G : Graph V) :
    let order := G.vertices.toList.mergeSort (finishLe (G.dfs))
    ∀ v ∈ G.vertices, v ∈ order := by
  intro order v hv
  have hperm : order.Perm G.vertices.toList := List.mergeSort_perm _ _
  exact hperm.mem_iff.mpr (Finset.mem_toList.mpr hv)

/-- The order used by Kosaraju's second DFS is non-increasing by first-pass
finish time. -/
theorem kosaraju_order_pairwise_finish_le (G : Graph V) :
    let order := G.vertices.toList.mergeSort (finishLe (G.dfs))
    order.Pairwise (fun a b => finishTime (G.dfs) b ≤ finishTime (G.dfs) a) := by
  intro order
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

/-- The initial state for Kosaraju's second pass satisfies the SCC-specific
induction invariant. -/
lemma kosaraju_initial_scc_invariant (G : Graph V) :
    let order := G.vertices.toList.mergeSort (finishLe (G.dfs))
    G.KosarajuSCCInvariant order dfsInit ([] : List (Finset V)) := by
  intro order
  refine { acc_scc := ?_, white_in_vs := ?_, scc_monochrome := ?_, no_gray := ?_ }
  · intro C h; simp at h
  · intro v hvV _
    simpa [order] using kosaraju_order_contains_vertices G v hvV
  · intro K _; left; intro v _; rfl
  · intro v; left; rfl

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
  have hmem : ∀ x ∈ G.transpose.vertices, x ∈ order := by
    intro x hx
    have hx' : x ∈ G.vertices := by simpa using hx
    exact kosaraju_order_contains_vertices G x hx'
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
    (hp : (u :: us).Pairwise (fun a b => finishTime (G.dfs) b ≤ finishTime (G.dfs) a))
    (v : V) (hv : v ∈ us) :
    finishTime (G.dfs) v ≤ finishTime (G.dfs) u := by
  induction us generalizing u with
  | nil => simp at hv
  | cons w ws ih =>
      rcases List.pairwise_cons.mp hp with ⟨h_uw, hp'⟩
      have hle_w_u : finishTime (G.dfs) w ≤ finishTime (G.dfs) u := h_uw w (by simp)
      rcases List.mem_cons.mp hv with (rfl | hv')
      · exact hle_w_u
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

/-- If the current white vertices still appear in a finish-time-sorted list
headed by {lit}`u`, then {lit}`u` has maximum first-pass finish time among all
white vertices. -/
lemma white_finish_le_head_of_pairwise_order {s : DFSState V} {u : V} {us : List V}
    (hp : (u :: us).Pairwise (fun a b => finishTime (G.dfs) b ≤ finishTime (G.dfs) a))
    (hwhite_in : ∀ v, v ∈ G.vertices → s.color v = Color.white → v ∈ u :: us) :
    ∀ v, s.color v = Color.white → finishTime (G.dfs) v ≤ finishTime (G.dfs) u := by
  intro v hv_white
  by_cases hvV : v ∈ G.vertices
  · have hv_in_vs : v ∈ u :: us := hwhite_in v hvV hv_white
    rcases List.mem_cons.mp hv_in_vs with (rfl | hv_us)
    · rfl
    · exact pairwise_head_max_finishTime G u us hp v hv_us
  · rw [finishTime_zero_of_not_mem_vertices G hvV]
    omega

/-- After a DFS visit from {lit}`u` turns {lit}`u` black, every vertex that is
white in the output and was covered by {lit}`u :: us` beforehand must lie in
the tail {lit}`us`. -/
lemma white_vertices_in_tail_after_visit (H : Graph V) {fuel : Nat} {u : V}
    {s s' : DFSState V} {us : List V}
    (hs' : s' = dfsVisit H fuel u s)
    (hu_black : s'.color u = Color.black)
    (hng : ∀ v, s.color v = Color.white ∨ s.color v = Color.black)
    (hwhite_in : ∀ v, v ∈ G.vertices → s.color v = Color.white → v ∈ u :: us) :
    ∀ v, v ∈ G.vertices → s'.color v = Color.white → v ∈ us := by
  intro x hxV hx_white_s'
  by_cases hx_in_us : x ∈ us
  · exact hx_in_us
  · have hx_white_s : s.color x = Color.white := by
      by_contra hnot
      have hblack_s : s.color x = Color.black := by
        cases hng x with
        | inl hw => exact absurd hw hnot
        | inr hb => exact hb
      have hblack_s' : s'.color x = Color.black := by
        rw [hs']
        exact dfsVisit_preserves_black H hblack_s
      rw [hblack_s'] at hx_white_s'
      simp at hx_white_s'
    have hx_in_vs : x ∈ u :: us := hwhite_in x hxV hx_white_s
    rcases List.mem_cons.mp hx_in_vs with (rfl | h)
    · rw [hu_black] at hx_white_s'
      simp at hx_white_s'
    · exact absurd h hx_in_us

/-- If the head of {lit}`u :: us` is not white, then every white vertex covered
by the list must already lie in the tail {lit}`us`. -/
lemma white_vertices_in_tail_of_head_not_white {s : DFSState V} {u : V} {us : List V}
    (hu_not_white : s.color u ≠ Color.white)
    (hwhite_in : ∀ v, v ∈ G.vertices → s.color v = Color.white → v ∈ u :: us) :
    ∀ v, v ∈ G.vertices → s.color v = Color.white → v ∈ us := by
  intro x hxV hx
  have hx_in_vs : x ∈ u :: us := hwhite_in x hxV hx
  rcases List.mem_cons.mp hx_in_vs with (rfl | hx_us)
  · exact absurd hx hu_not_white
  · exact hx_us

/-- In Kosaraju's second pass, a white SCC disjoint from the SCC being visited
stays white. -/
lemma kosaraju_visit_preserves_disjoint_white_scc {s : DFSState V} {u : V} {K : Set V}
    (hu : u ∈ G.transpose.vertices) (hu_white : s.color u = Color.white)
    (hK : G.IsSCC K) (hK_white : ∀ v ∈ K, s.color v = Color.white)
    (hK_ne : K ≠ G.sccOf u)
    (hmax : ∀ v, s.color v = Color.white → finishTime (G.dfs) v ≤ finishTime (G.dfs) u)
    (hrespects : G.SCCMonochrome s) :
    ∀ v ∈ K, (dfsVisit G.transpose (G.vertices.card + 1) u s).color v = Color.white := by
  intro v hvK
  have h_disjoint : Disjoint K (G.sccOf u) :=
    (IsSCC_eq_or_disjoint G hK (isSCC_sccOf G (by simpa using hu))).resolve_left hK_ne
  have hv_not_scc : v ∉ G.sccOf u :=
    (Set.disjoint_left.mp h_disjoint) hvK
  have hv_not_wr : v ∉ whiteReachableSet G.transpose s u := by
    intro hwr; apply hv_not_scc
    exact whiteReachableSet_subset_scc G hu hu_white hmax hrespects hwr
  have hno_wr : ¬ WhiteReachable G.transpose s u v := by
    intro hwr
    exact hv_not_wr (WhiteReachable.mem_set G.transpose hu hwr)
  exact dfsVisit_preserves_white_of_not_whiteReachable G.transpose hu_white (by omega)
    (hK_white v hvK) hno_wr

/-- A white-started visit in Kosaraju's second pass preserves the invariant that
each SCC is monochromatic in the current DFS state. -/
lemma kosaraju_visit_preserves_scc_monochrome {s : DFSState V} {u : V}
    (hu : u ∈ G.transpose.vertices) (hu_white : s.color u = Color.white)
    (hmax : ∀ v, s.color v = Color.white → finishTime (G.dfs) v ≤ finishTime (G.dfs) u)
    (hrespects : G.SCCMonochrome s) :
    G.SCCMonochrome (dfsVisit G.transpose (G.vertices.card + 1) u s) := by
  have h_sccOf_u_white : ∀ v ∈ G.sccOf u, s.color v = Color.white := by
    exact sccOf_white_of_monochrome G (by simpa using hu) hu_white hrespects
  intro K hK
  rcases hrespects K hK with (hw | hb)
  · by_cases hK_eq : K = G.sccOf u
    · right
      intro v hv
      have hfuel : G.vertices.card + 1 ≥ G.transpose.vertices.card + 1 := by simp
      exact dfsVisit_transpose_blackens_sccOf G hu hu_white hfuel h_sccOf_u_white
        (by simpa [hK_eq] using hv)
    · left
      exact kosaraju_visit_preserves_disjoint_white_scc G hu hu_white hK hw hK_eq hmax hrespects
  · right; intro v hv; exact dfsVisit_preserves_black G.transpose (hb v hv)

/-- A white head in Kosaraju's second-pass order advances the SCC induction
invariant after collecting the component discovered by that visit. -/
lemma kosaraju_scc_invariant_after_white_head {fuel : Nat} (hfuel_eq : fuel = G.vertices.card + 1)
    (hfuel : fuel ≥ G.transpose.vertices.card + 1) (hfuel_pos : 0 < fuel)
    {u : V} {us : List V} {s : DFSState V} {acc : List (Finset V)}
    (hp_vs : (u :: us).Pairwise (fun a b => finishTime (G.dfs) b ≤ finishTime (G.dfs) a))
    (hu_vert : u ∈ G.transpose.vertices) (hu_white : s.color u = Color.white)
    (hinv : G.KosarajuSCCInvariant (u :: us) s acc) :
    let s' := dfsVisit G.transpose fuel u s
    let comp := G.vertices.filter (fun v => s.color v = Color.white ∧ s'.color v = Color.black)
    G.KosarajuSCCInvariant us s' (comp :: acc) := by
  intro s' comp
  have hmax_u : ∀ v, s.color v = Color.white → finishTime (G.dfs) v ≤ finishTime (G.dfs) u :=
    white_finish_le_head_of_pairwise_order G hp_vs hinv.white_in_vs
  have h_comp_scc : G.IsSCC (comp : Set V) :=
    scc_finish_order hu_vert hu_white hmax_u hfuel hinv.scc_monochrome
  have hu_black_s' : s'.color u = Color.black := by
    simpa [s'] using dfsVisit_blackens_u_pos G.transpose hfuel_pos hu_white
  have h_white_in_us : ∀ v, v ∈ G.vertices → s'.color v = Color.white → v ∈ us :=
    white_vertices_in_tail_after_visit G G.transpose rfl hu_black_s'
      hinv.no_gray hinv.white_in_vs
  have h_respects' : G.SCCMonochrome s' := by
    simpa [s', hfuel_eq] using
      kosaraju_visit_preserves_scc_monochrome G hu_vert hu_white hmax_u hinv.scc_monochrome
  have h_ng' : ∀ v, s'.color v = Color.white ∨ s'.color v = Color.black :=
    dfsVisit_output_no_gray G.transpose hinv.no_gray
  have h_mem : ∀ C' ∈ (comp :: acc), G.IsSCC (C' : Set V) := by
    intro C' hC'
    rcases List.mem_cons.mp hC' with (rfl | hC'_acc)
    · exact h_comp_scc
    · exact hinv.acc_scc C' hC'_acc
  exact {
    acc_scc := h_mem
    white_in_vs := h_white_in_us
    scc_monochrome := h_respects'
    no_gray := h_ng'
  }

/-- A non-white head in Kosaraju's second-pass order can be skipped while
preserving the SCC induction invariant on the tail. -/
lemma kosaraju_scc_invariant_after_nonwhite_head {u : V} {us : List V}
    {s : DFSState V} {acc : List (Finset V)}
    (hu_not_white : s.color u ≠ Color.white)
    (hinv : G.KosarajuSCCInvariant (u :: us) s acc) :
    G.KosarajuSCCInvariant us s acc := by
  exact {
    acc_scc := hinv.acc_scc
    white_in_vs := white_vertices_in_tail_of_head_not_white G hu_not_white hinv.white_in_vs
    scc_monochrome := hinv.scc_monochrome
    no_gray := hinv.no_gray
  }

/-- The SCC-specific induction for Kosaraju's second pass.

If the remaining roots are in non-increasing first-pass finish-time order and
the SCC invariant holds for the current state, then every component collected
from this suffix is an SCC of {lit}`G`. -/
lemma dfsFromListCollect_kosaraju_sccs {fuel : Nat} (hfuel_eq : fuel = G.vertices.card + 1)
    (vs : List V) (s : DFSState V) (acc : List (Finset V))
    (hp_vs : vs.Pairwise (fun a b => finishTime (G.dfs) b ≤ finishTime (G.dfs) a))
    (hvs_verts : ∀ v ∈ vs, v ∈ G.transpose.vertices)
    (hinv : G.KosarajuSCCInvariant vs s acc) :
    let (acc', _) := dfsFromListCollect G.transpose fuel vs s acc
    ∀ C ∈ acc', G.IsSCC (C : Set V) := by
  have hfuel : fuel ≥ G.transpose.vertices.card + 1 := by
    rw [hfuel_eq]
    simp
  have hfuel_pos : 0 < fuel := by
    rw [hfuel_eq]
    omega
  induction vs generalizing s acc with
  | nil => simp [dfsFromListCollect]; exact hinv.acc_scc
  | cons u us ih =>
      simp [dfsFromListCollect]
      rcases List.pairwise_cons.mp hp_vs with ⟨h_u_head, hp_us⟩
      have hu_vert : u ∈ G.transpose.vertices := hvs_verts u (by simp)
      have h_us_verts : ∀ v ∈ us, v ∈ G.transpose.vertices := by
        intro v hv; apply hvs_verts v; simp [hv]
      by_cases hu_white : s.color u = Color.white
      · let s' := dfsVisit G.transpose fuel u s
        let comp := G.vertices.filter (fun v => s.color v = Color.white ∧ s'.color v = Color.black)
        have hinv' : G.KosarajuSCCInvariant us s' (comp :: acc) := by
          simpa [s', comp] using
            kosaraju_scc_invariant_after_white_head G hfuel_eq hfuel hfuel_pos hp_vs
              hu_vert hu_white hinv
        have h_ih := ih s' (comp :: acc) hp_us h_us_verts hinv'
        simpa [s', comp, dfsFromListCollect, hu_white] using h_ih
      · have hinv' : G.KosarajuSCCInvariant us s acc :=
          kosaraju_scc_invariant_after_nonwhite_head G hu_white hinv
        have h_ih := ih s acc hp_us h_us_verts hinv'
        simpa [dfsFromListCollect, hu_white] using h_ih

/-! ## SCC correctness core -/

/-- Core DFS-theoretic lemma: every component returned by
{name}`Graph.kosarajuComponents` is an SCC of {lit}`G`.

The proof applies {name}`Graph.scc_finish_order` at each step of the second DFS
pass.  The first white vertex in decreasing finish-time order is maximal among
the currently white vertices, so its transpose DFS tree is exactly its SCC. -/
theorem kosarajuComponent_scc_core (G : Graph V) (C : Finset V)
    (hC : C ∈ G.kosarajuComponents) :
    G.IsSCC (C : Set V) := by
  -- 1. Setup
  simp [kosarajuComponents] at hC
  let order := G.vertices.toList.mergeSort (finishLe (G.dfs))
  let fuel := G.vertices.card + 1
  have h_order_verts : ∀ v, v ∈ order → v ∈ G.transpose.vertices := by
    exact kosaraju_order_subset_vertices G

  have h_pairwise_le : order.Pairwise (fun a b => finishTime (G.dfs) b ≤ finishTime (G.dfs) a) := by
    simpa [order] using kosaraju_order_pairwise_finish_le G

  -- Apply the second-pass induction to the initial state.
  have h_init_invariant : G.KosarajuSCCInvariant order dfsInit ([] : List (Finset V)) := by
    simpa [order] using kosaraju_initial_scc_invariant G
  have h_all_sccs := dfsFromListCollect_kosaraju_sccs G (fuel := fuel) (by rfl) order dfsInit []
    h_pairwise_le h_order_verts h_init_invariant
  exact h_all_sccs C (by simpa [fuel] using hC)

/-- The components returned by {name}`Graph.kosarajuComponents` are exactly the
strongly connected components of {lit}`G`.

The DFS finish-time argument needed for SCC-ness is isolated in
{name}`Graph.kosarajuComponent_scc_core`. -/
theorem kosarajuComponents_eq_sccs (G : Graph V) (C : Finset V)
    (hC : C ∈ G.kosarajuComponents) :
    G.IsSCC (C : Set V) :=
  kosarajuComponent_scc_core G C hC

/-- Vertices in the same component returned by Kosaraju's algorithm are
strongly connected. -/
theorem kosarajuComponents_stronglyConnected (G : Graph V) (C : Finset V)
    (hC : C ∈ G.kosarajuComponents) :
    ∀ u ∈ C, ∀ v ∈ C, G.StronglyConnected u v :=
  (kosarajuComponents_eq_sccs G C hC).stronglyConnected

/-- A component returned by Kosaraju's algorithm cannot be enlarged by any
outside vertex while preserving strong connectivity with the component. -/
theorem kosarajuComponents_not_stronglyConnected_outside (G : Graph V) (C : Finset V)
    (hC : C ∈ G.kosarajuComponents) :
    ∀ w ∈ G.vertices \ C, ¬ (∀ u ∈ C, G.StronglyConnected u w) := by
  intro w hw hsc
  simp at hw
  exact hw.2 (IsSCC.maximal G (kosarajuComponents_eq_sccs G C hC) w hw.1
    (fun u hu => hsc u hu))

/-- Every vertex of {lit}`G` belongs to a unique component returned by
Kosaraju's algorithm. -/
theorem kosarajuComponents_exists_unique (G : Graph V) :
    ∀ v ∈ G.vertices, ∃! C ∈ G.kosarajuComponents, v ∈ C := by
  intro v hv
  have ⟨C, hC, hvC⟩ := kosarajuComponents_cover G v hv
  use C
  constructor
  · exact ⟨hC, hvC⟩
  · intro D hD
    exact unique_mem_of_pairwise_disjoint_cover
      (kosarajuComponents_pairwise_disjoint G)
      hD.1 hC ⟨v, hD.2, hvC⟩

/-- {name}`Graph.kosarajuComponents` is a valid SCC partition of {lit}`G`. -/
theorem kosarajuComponents_isSCCPartition (G : Graph V) :
    G.IsSCCPartition G.kosarajuComponents := by
  exact ⟨kosarajuComponents_subset G, kosarajuComponents_nonempty G,
    kosarajuComponents_stronglyConnected G, kosarajuComponents_not_stronglyConnected_outside G,
    kosarajuComponents_exists_unique G⟩

end Graph

end Chapter22
end CLRS

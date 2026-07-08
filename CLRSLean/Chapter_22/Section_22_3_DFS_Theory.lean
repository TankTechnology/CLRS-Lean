import Mathlib
import CLRSLean.Chapter_22.Section_22_1_Representing_Graphs
import CLRSLean.Chapter_22.Section_22_3_DFS

/-! # DFS theory: white-path reachability

This file collects the DFS-theoretic consequences of the functional DFS model
that are needed for Section 22.5 (Kosaraju's SCC algorithm).  The main result
is the white-path theorem for a single `dfsVisit`: starting from a white vertex,
the visit blackens exactly the vertices reachable through white vertices.
-/

namespace CLRS
namespace Chapter22
namespace Graph

variable {V : Type} [DecidableEq V] (G : Graph V)

section Reachability

/-! ## Reachability through white vertices -/

/-- `WhiteReachable s u v` holds when `v` can be reached from `u` by a path
whose every step lands on a vertex that is white in `s`.  The source `u` itself
need not be white; this is handled separately in the theorems. -/
def WhiteReachable (s : DFSState V) (u v : V) : Prop :=
  Relation.ReflTransGen (fun x y => G.Adj x y ∧ s.color y = Color.white) u v

theorem whiteReachable_refl (s : DFSState V) (u : V) : WhiteReachable G s u u :=
  Relation.ReflTransGen.refl

theorem whiteReachable_trans {s : DFSState V} {u v w : V}
    (huv : WhiteReachable G s u v) (hvw : WhiteReachable G s v w) :
    WhiteReachable G s u w :=
  Relation.ReflTransGen.trans huv hvw

theorem whiteReachable_step {s : DFSState V} {u v w : V}
    (huv : WhiteReachable G s u v) (hadj : G.Adj v w) (hw : s.color w = Color.white) :
    WhiteReachable G s u w :=
  Relation.ReflTransGen.tail huv ⟨hadj, hw⟩

/-- Every vertex on a white path (except possibly the source) is white. -/
theorem whiteReachable_target_white {u v : V} {s : DFSState V}
    (hwhite : s.color u = Color.white) (hr : WhiteReachable G s u v) :
    s.color v = Color.white := by
  induction hr with
  | refl => exact hwhite
  | tail _ hstep _ => exact hstep.2

/-! ## White-reachable set as a finite iteration

We compute the set of white-reachable vertices by iterating a monotone operator.
Because the graph is finite, this iteration stabilises within `|V|` steps,
giving a finite characterisation of `WhiteReachable` that supports induction on
the size of the reachable set.
-/

/-- One step of the white-reachability operator. -/
def whiteReachableSucc (s : DFSState V) (U : Finset V) : Finset V :=
  Finset.filter (fun v => s.color v = Color.white) (U.biUnion (fun w => G.adj w))

/-- Iterated white reachability from {lit}`u`. -/
def whiteReachableIter (s : DFSState V) (u : V) : Nat → Finset V
  | 0 => {u}
  | n + 1 => whiteReachableIter s u n ∪ whiteReachableSucc G s (whiteReachableIter s u n)

/-- The white-reachable set is the iteration stabilised at `|V|`. -/
noncomputable def whiteReachableSet (s : DFSState V) (u : V) : Finset V :=
  whiteReachableIter G s u (G.vertices.card)

theorem whiteReachableIter_subset_vertices (s : DFSState V) (u : V) (hu : u ∈ G.vertices)
    (n : Nat) : whiteReachableIter G s u n ⊆ G.vertices := by
  induction n with
  | zero => simp [whiteReachableIter, hu]
  | succ n ih =>
      intro v hv
      simp [whiteReachableIter, whiteReachableSucc, Finset.mem_filter, Finset.mem_biUnion] at hv
      rcases hv with (h | ⟨⟨w, hw, hadj⟩, hwhite⟩)
      · exact ih h
      · exact G.adj_mem_right hadj

theorem whiteReachableSet_subset_vertices (s : DFSState V) (u : V) (hu : u ∈ G.vertices) :
    whiteReachableSet G s u ⊆ G.vertices :=
  whiteReachableIter_subset_vertices G s u hu (G.vertices.card)

theorem whiteReachableIter_mono (s : DFSState V) (u : V) (n : Nat) :
    whiteReachableIter G s u n ⊆ whiteReachableIter G s u (n + 1) := by
  simp [whiteReachableIter]

theorem whiteReachableIter_mono_le (s : DFSState V) (u : V) {n m : Nat} (h : n ≤ m) :
    whiteReachableIter G s u n ⊆ whiteReachableIter G s u m := by
  induction h with
  | refl => rfl
  | step h ih => exact ih.trans (whiteReachableIter_mono G s u _)

theorem whiteReachableIter_eventually_stable (s : DFSState V) (u : V) (hu : u ∈ G.vertices) :
    ∃ k ≤ G.vertices.card, whiteReachableIter G s u k = whiteReachableIter G s u (k + 1) := by
  by_contra h
  push_neg at h
  have hcard_pos : 1 ≤ G.vertices.card := Finset.one_le_card.mpr ⟨u, hu⟩
  have hmono := whiteReachableIter_mono G s u
  have h_strict : ∀ k ≤ G.vertices.card, whiteReachableIter G s u k ⊂ whiteReachableIter G s u (k + 1) := by
    intro k hk
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hmono k, ?_⟩
    intro heq
    exact h k hk heq
  have h_card : ∀ k ≤ G.vertices.card + 1,
      (whiteReachableIter G s u k).card ≥ k + 1 := by
    intro k hk
    induction k with
    | zero =>
        simp [whiteReachableIter]
    | succ k ih =>
        have hk' : k ≤ G.vertices.card := by omega
        have hlt := Finset.card_lt_card (h_strict k hk')
        have hle := ih (by omega)
        omega
  have h_ub := Finset.card_le_card (whiteReachableIter_subset_vertices G s u hu (G.vertices.card + 1))
  have h_mono_card := Finset.card_le_card (hmono (G.vertices.card))
  have h_lb := h_card (G.vertices.card) (by omega)
  simp at h_ub h_mono_card h_lb
  omega

theorem whiteReachableIter_stable_at (s : DFSState V) (u : V) {k : Nat}
    (heq : whiteReachableIter G s u k = whiteReachableIter G s u (k + 1)) (m : Nat) :
    whiteReachableIter G s u k = whiteReachableIter G s u (k + m) := by
  have hsucc : whiteReachableSucc G s (whiteReachableIter G s u k) ⊆ whiteReachableIter G s u k := by
    have h := heq
    simp [whiteReachableIter] at h
    exact h
  induction m with
  | zero => simp
  | succ m ih =>
      calc
        whiteReachableIter G s u k = whiteReachableIter G s u (k + m) := ih
        _ = whiteReachableIter G s u (k + m + 1) := by
          have h1 : whiteReachableIter G s u (k + m + 1)
              = whiteReachableIter G s u (k + m) ∪ whiteReachableSucc G s (whiteReachableIter G s u (k + m)) := rfl
          rw [h1, ← ih]
          rw [Finset.union_eq_left.2 hsucc]

theorem whiteReachableIter_stable (s : DFSState V) (u : V) (hu : u ∈ G.vertices) :
    whiteReachableSet G s u = whiteReachableIter G s u (G.vertices.card + 1) := by
  rcases whiteReachableIter_eventually_stable G s u hu with ⟨k, hk, heq⟩
  have h1 : whiteReachableSet G s u = whiteReachableIter G s u k := by
    dsimp [whiteReachableSet]
    have heq1 := whiteReachableIter_stable_at G s u heq (G.vertices.card - k)
    have : k + (G.vertices.card - k) = G.vertices.card := by omega
    rw [this] at heq1
    exact heq1.symm
  have h2 : whiteReachableIter G s u k = whiteReachableIter G s u (G.vertices.card + 1) := by
    have heq2 := whiteReachableIter_stable_at G s u heq (G.vertices.card + 1 - k)
    have : k + (G.vertices.card + 1 - k) = G.vertices.card + 1 := by omega
    rw [this] at heq2
    exact heq2
  rw [h1, h2]

theorem whiteReachableIter_to_WhiteReachable {s : DFSState V} {u v : V} {n : Nat}
    (hv : v ∈ whiteReachableIter G s u n) : WhiteReachable G s u v := by
  induction n generalizing v with
  | zero =>
      simp [whiteReachableIter, Finset.mem_singleton] at hv
      subst v
      exact whiteReachable_refl G s u
  | succ n ih =>
      simp [whiteReachableIter, whiteReachableSucc, Finset.mem_filter, Finset.mem_biUnion] at hv
      rcases hv with (h | ⟨⟨w, hw, hadj⟩, hwhite⟩)
      · exact ih h
      · exact whiteReachable_step G (ih hw) hadj hwhite

theorem WhiteReachable.mem_iter {s : DFSState V} {u v : V}
    (hr : WhiteReachable G s u v) : ∃ n, v ∈ whiteReachableIter G s u n := by
  induction hr with
  | refl => use 0; simp [whiteReachableIter]
  | @tail w v' hwr hadj ih =>
      rcases ih with ⟨n, hn⟩
      use n + 1
      simp [whiteReachableIter, whiteReachableSucc, Finset.mem_filter, Finset.mem_biUnion]
      refine Or.inr ⟨⟨w, hn, hadj.1⟩, hadj.2⟩

theorem WhiteReachable.mem_set {s : DFSState V} {u v : V} (hu : u ∈ G.vertices)
    (hr : WhiteReachable G s u v) : v ∈ whiteReachableSet G s u := by
  rcases hr.mem_iter G with ⟨n, hn⟩
  have hstable := whiteReachableIter_stable G s u hu
  rw [hstable]
  by_cases h : n ≤ G.vertices.card + 1
  · exact whiteReachableIter_mono_le G s u h hn
  · have : n ≥ G.vertices.card + 2 := by omega
    rcases whiteReachableIter_eventually_stable G s u hu with ⟨k, hk, heq⟩
    have h1 := whiteReachableIter_stable_at G s u heq (n - k)
    have h2 := whiteReachableIter_stable_at G s u heq (G.vertices.card + 1 - k)
    have hkn : k + (n - k) = n := by omega
    have hkcard : k + (G.vertices.card + 1 - k) = G.vertices.card + 1 := by omega
    rw [hkn] at h1
    rw [hkcard] at h2
    rw [← h1, h2] at hn
    exact hn

theorem mem_whiteReachableSet_iff {s : DFSState V} {u v : V} (hu : u ∈ G.vertices) :
    v ∈ whiteReachableSet G s u ↔ WhiteReachable G s u v := by
  constructor
  · intro hv
    exact whiteReachableIter_to_WhiteReachable G hv
  · intro hr
    exact WhiteReachable.mem_set G hu hr

/-- Every vertex belongs to its own white-reachable set. -/
theorem mem_whiteReachableSet_self (s : DFSState V) (u : V) : u ∈ whiteReachableSet G s u := by
  have h0 : u ∈ whiteReachableIter G s u 0 := by simp [whiteReachableIter]
  exact whiteReachableIter_mono_le G s u (by linarith) h0

/-- Iteration-level decomposition: a vertex different from `u` that appears in
`iter (n+1)` can be reached from a white neighbour of `u` within `n` iterations
of the gray state. -/
theorem mem_whiteReachableIter_self (s : DFSState V) (u : V) (n : Nat) :
    u ∈ whiteReachableIter G s u n := by
  induction n with
  | zero => simp [whiteReachableIter]
  | succ n ih => simp [whiteReachableIter, ih]

theorem mem_whiteReachableIter_succ_of_mem {s : DFSState V} {u v : V} {n : Nat}
    (h : v ∈ whiteReachableIter G s u n) :
    v ∈ whiteReachableIter G s u (n + 1) :=
  whiteReachableIter_mono G s u n h

theorem whiteReachableIter_decomp {s : DFSState V} {u v : V} (hu : u ∈ G.vertices)
    (n : Nat) (hv : v ∈ whiteReachableIter G s u (n + 1)) (hne : v ≠ u) :
    ∃ x, G.Adj u x ∧ s.color x = Color.white ∧
      v ∈ whiteReachableIter G (s.setColor u Color.gray) x n := by
  induction n generalizing v with
  | zero =>
      have h_eq : whiteReachableIter G s u (0 + 1) = {u} ∪ whiteReachableSucc G s {u} := rfl
      rw [h_eq] at hv
      simp [whiteReachableSucc, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_singleton] at hv
      rcases hv with (rfl | h)
      · contradiction
      · use v
        constructor
        · exact h.1
        constructor
        · exact h.2
        · exact mem_whiteReachableIter_self G (s.setColor u Color.gray) v 0
  | succ n ih =>
      have h_eq : whiteReachableIter G s u ((n + 1) + 1)
          = whiteReachableIter G s u (n + 1) ∪ whiteReachableSucc G s (whiteReachableIter G s u (n + 1)) := rfl
      rw [h_eq] at hv
      simp [whiteReachableSucc, Finset.mem_filter, Finset.mem_biUnion] at hv
      rcases hv with (h | ⟨⟨w, hw, hadj_wv⟩, hwhite_v⟩)
      · rcases ih h hne with ⟨x, hadj, hwhite, hvx⟩
        use x, hadj, hwhite
        exact mem_whiteReachableIter_succ_of_mem G hvx
      · by_cases hwu : w = u
        · subst w
          use v
          constructor
          · exact hadj_wv
          constructor
          · exact hwhite_v
          · exact mem_whiteReachableIter_self G (s.setColor u Color.gray) v (n + 1)
        · rcases ih hw (by simpa using hwu) with ⟨x, hadj_ux, hwhite_x, hvx⟩
          use x
          constructor
          · exact hadj_ux
          constructor
          · exact hwhite_x
          · have hwhite_v_gray : (s.setColor u Color.gray).color v = Color.white := by
              simp [hwhite_v]
              exact hne
            simp [whiteReachableIter, whiteReachableSucc, Finset.mem_filter, Finset.mem_biUnion]
            refine Or.inr ⟨⟨w, hvx, hadj_wv⟩, hwhite_v_gray⟩

/-- If `v` lies in the white-reachable set and `v ≠ u`, then `v` can be reached
from a white neighbour `x` of `u` without using `u`. -/
theorem whiteReachableSet_decomp {s : DFSState V} {u v : V} (hu : u ∈ G.vertices)
    (hwhite : s.color u = Color.white) (hv : v ∈ whiteReachableSet G s u) (hne : v ≠ u) :
    ∃ x, G.Adj u x ∧ s.color x = Color.white ∧
      v ∈ whiteReachableSet G (s.setColor u Color.gray) x := by
  have hstable := whiteReachableIter_stable G s u hu
  have : v ∈ whiteReachableIter G s u (G.vertices.card + 1) := by
    rw [← hstable]
    exact hv
  rcases whiteReachableIter_decomp G hu (G.vertices.card) this hne with ⟨x, hadj, hwhite_x, hvx⟩
  use x, hadj, hwhite_x
  have hstable_x := whiteReachableIter_stable G (s.setColor u Color.gray) x (G.adj_mem_right hadj)
  rw [hstable_x]
  exact mem_whiteReachableIter_succ_of_mem G hvx

/-- Extract the first step of a non-trivial white path. -/
theorem WhiteReachable.exists_first_step {s : DFSState V} {u v : V}
    (hr : WhiteReachable G s u v) (hne : v ≠ u) :
    ∃ x, G.Adj u x ∧ s.color x = Color.white ∧ WhiteReachable G s x v := by
  induction hr with
  | refl => contradiction
  | @tail a b hab hbc ih =>
      by_cases hau : a = u
      · subst a
        use b
        exact ⟨hbc.1, hbc.2, whiteReachable_refl G s b⟩
      · rcases ih hau with ⟨x, hx1, hx2, hx3⟩
        use x, hx1, hx2
        exact whiteReachable_step G hx3 hbc.1 hbc.2

/-- Variant of {name}`whiteReachableSet_decomp` that guarantees the chosen
neighbour is different from `u`. -/
theorem whiteReachableSet_decomp_ne {s : DFSState V} {u v : V} (hu : u ∈ G.vertices)
    (hwhite : s.color u = Color.white) (hv : v ∈ whiteReachableSet G s u) (hne : v ≠ u) :
    ∃ x, G.Adj u x ∧ s.color x = Color.white ∧ x ≠ u ∧
      v ∈ whiteReachableSet G (s.setColor u Color.gray) x := by
  rcases whiteReachableSet_decomp G hu hwhite hv hne with ⟨x, hadj, hwhite_x, hvx⟩
  by_cases hxne : x = u
  · subst x
    have hr' := whiteReachableIter_to_WhiteReachable G hvx
    rcases WhiteReachable.exists_first_step G hr' hne with ⟨z, hadj_z, hwhite_z_gray, hr_zv⟩
    have hzne : z ≠ u := by
      intro hzu
      subst z
      have : (s.setColor u Color.gray).color u = Color.white := hwhite_z_gray
      simp at this
    have hwhite_z : s.color z = Color.white := by
      simp [hzne] at hwhite_z_gray
      exact hwhite_z_gray
    use z
    constructor
    · exact hadj_z
    constructor
    · exact hwhite_z
    constructor
    · exact hzne
    · exact WhiteReachable.mem_set G (G.adj_mem_right hadj_z) hr_zv
  · use x, hadj, hwhite_x, hxne, hvx

theorem whiteReachable_gray_to_white {s : DFSState V} {u x v : V}
    (hwhite : s.color u = Color.white)
    (hr : WhiteReachable G (s.setColor u Color.gray) x v) :
    WhiteReachable G s x v := by
  induction hr with
  | refl => exact whiteReachable_refl G s x
  | @tail y z hwy hadj' ih =>
      have hwhite_z : s.color z = Color.white := by
        have : (s.setColor u Color.gray).color z = Color.white := hadj'.2
        simp at this
        by_cases h : z = u
        · subst z
          simp [hwhite] at this
        · simpa [h] using this
      exact whiteReachable_step G ih hadj'.1 hwhite_z

/-- If every white vertex of `s'` is also white in `s`, then a white path in `s'`
is also a white path in `s`. -/
theorem whiteReachable_mono_of_color_superset {s s' : DFSState V} {u v : V}
    (h : ∀ z, s'.color z = Color.white → s.color z = Color.white) :
    WhiteReachable G s' u v → WhiteReachable G s u v := by
  intro hr
  induction hr with
  | refl => exact whiteReachable_refl G s u
  | @tail x y _ hstep ih =>
      have hwhite_y : s.color y = Color.white := h y hstep.2
      exact whiteReachable_step G ih hstep.1 hwhite_y

/-- If two states agree on colors, white reachability is equivalent. -/
theorem WhiteReachable.color_eq {s s' : DFSState V} {u v : V}
    (h : ∀ z, s.color z = s'.color z) :
    WhiteReachable G s u v ↔ WhiteReachable G s' u v := by
  constructor
  · apply whiteReachable_mono_of_color_superset
    intro z hz
    rw [← h z]
    exact hz
  · apply whiteReachable_mono_of_color_superset
    intro z hz
    rw [h z]
    exact hz

/-- Monotonicity of the white-reachable set with respect to the set of white
vertices. -/
theorem whiteReachableSet_mono_of_color_superset {s s' : DFSState V} {u : V} (hu : u ∈ G.vertices)
    (h : ∀ z, s'.color z = Color.white → s.color z = Color.white) :
    whiteReachableSet G s' u ⊆ whiteReachableSet G s u := by
  intro v hv
  have hr := whiteReachableIter_to_WhiteReachable G hv
  exact WhiteReachable.mem_set G hu (whiteReachable_mono_of_color_superset G h hr)

/-- If two states agree on colors, their white-reachable sets are equal. -/
theorem whiteReachableSet_eq_of_color_eq {s s' : DFSState V} {u : V} (hu : u ∈ G.vertices)
    (h : ∀ z, s.color z = s'.color z) :
    whiteReachableSet G s u = whiteReachableSet G s' u := by
  apply Finset.Subset.antisymm
  · apply whiteReachableSet_mono_of_color_superset G hu
    intro z hz
    rw [← h z]
    exact hz
  · apply whiteReachableSet_mono_of_color_superset G hu
    intro z hz
    rw [h z]
    exact hz

/-- Subset relationship induced by a white path. -/
theorem whiteReachableSet_subset_of_WhiteReachable {s : DFSState V} {u v : V} (hu : u ∈ G.vertices)
    (hr : WhiteReachable G s u v) :
    whiteReachableSet G s v ⊆ whiteReachableSet G s u := by
  intro x hx
  have hr2 := whiteReachableIter_to_WhiteReachable G hx
  exact WhiteReachable.mem_set G hu (whiteReachable_trans G hr hr2)

theorem whiteReachableSet_neighbor_ssubset {s : DFSState V} {u x : V} (hu : u ∈ G.vertices)
    (hwhite : s.color u = Color.white) (hadj : G.Adj u x) (hx : s.color x = Color.white)
    (hxne : x ≠ u) :
    whiteReachableSet G (s.setColor u Color.gray) x ⊂ whiteReachableSet G s u := by
  have hsub : whiteReachableSet G (s.setColor u Color.gray) x ⊆ whiteReachableSet G s u := by
    intro v hv
    have hr := whiteReachableIter_to_WhiteReachable G hv
    have hr' : WhiteReachable G s u v := by
      have h1 : G.Adj u x := hadj
      have h2 := whiteReachable_gray_to_white G hwhite hr
      exact whiteReachable_step G (whiteReachable_refl G s u) h1 hx |>.trans h2
    exact WhiteReachable.mem_set G hu hr'
  have hne : u ∉ whiteReachableSet G (s.setColor u Color.gray) x := by
    intro h
    have hr := whiteReachableIter_to_WhiteReachable G h
    have hwhite_x : (s.setColor u Color.gray).color x = Color.white := by
      simp [hx, hxne]
    have hwhite_u : (s.setColor u Color.gray).color u = Color.white :=
      whiteReachable_target_white (G := G) hwhite_x hr
    simp at hwhite_u
  have hmem : u ∈ whiteReachableSet G s u := by
    rw [mem_whiteReachableSet_iff G hu]
    exact whiteReachable_refl G s u
  exact Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => hne (heq ▸ hmem)⟩

end Reachability
/-! ## Converse of the white-path theorem

If a `dfsVisit` call turns a vertex black, that vertex was either black already
or reachable through white vertices from the source.
-/

/-- `dfsVisit` never turns a non-white vertex into a white one. -/
theorem dfsVisit_does_not_create_white {fuel : Nat} {u x : V} {s : DFSState V}
    (hnw : s.color x ≠ Color.white) :
    (dfsVisit G fuel u s).color x ≠ Color.white := by
  induction fuel generalizing u s with
  | zero =>
      intro h
      simp [dfsVisit] at h
      contradiction
  | succ n ih =>
      by_cases hwhite_u : s.color u = Color.white
      · -- u is white, so the visit expands
        by_cases hxu : x = u
        · -- x = u: final color is black
          have : (dfsVisit G (n+1) u s).color x = Color.black := by
            rw [hxu]
            simp [dfsVisit, hwhite_u]
          rw [this]
          intro h
          contradiction
        · -- x ≠ u: the color comes from the fold over the adjacency list
          have h2 : (dfsVisit G (n+1) u s).color x = (List.foldl (fun (s' : DFSState V) (w : V) =>
              if s'.color w = Color.white then dfsVisit G n w (s'.setParent w u) else s')
              (s.setColor u Color.gray |>.setDiscovery u) (G.adj u).toList).color x := by
            simp [dfsVisit, hwhite_u, hxu]
          rw [h2]
          let step := fun (s' : DFSState V) (v : V) =>
            if s'.color v = Color.white then dfsVisit G n v (s'.setParent v u) else s'
          have hnw' : (s.setColor u Color.gray |>.setDiscovery u).color x ≠ Color.white := by
            simp [hxu]
            exact hnw
          have hfold : ∀ (s1 : DFSState V), s1.color x ≠ Color.white →
              (List.foldl step s1 (G.adj u).toList).color x ≠ Color.white := by
            intro s1 hs1x
            induction (G.adj u).toList generalizing s1 with
            | nil =>
                simpa using hs1x
            | cons w ws ih' =>
                rw [List.foldl_cons]
                by_cases hw : s1.color w = Color.white
                · have hstep : step s1 w = dfsVisit G n w (s1.setParent w u) := by
                    simp [step, hw]
                  rw [hstep]
                  apply ih'
                  have hsp : (s1.setParent w u).color x = s1.color x := by simp
                  have hsp_nw : (s1.setParent w u).color x ≠ Color.white := by
                    intro h
                    apply hs1x
                    rwa [hsp] at h
                  exact ih (u := w) (s := s1.setParent w u) hsp_nw
                · have hstep : step s1 w = s1 := by
                    simp [step, hw]
                  rw [hstep]
                  exact ih' s1 hs1x
          exact hfold (s.setColor u Color.gray |>.setDiscovery u) hnw'
      · -- u is not white, the state is unchanged
        have h2 : (dfsVisit G (n+1) u s).color x = s.color x := by
          simp [dfsVisit, hwhite_u]
        rw [h2]
        exact hnw

/-- If `dfsVisit` leaves a vertex white, it was white before the call. -/
theorem dfsVisit_output_white_imp_input_white {fuel : Nat} {u x : V} {s : DFSState V}
    (hout : (dfsVisit G fuel u s).color x = Color.white) :
    s.color x = Color.white := by
  by_contra h
  push Not at h
  have := dfsVisit_does_not_create_white (G := G) (fuel := fuel) (u := u) (x := x) (s := s) h
  contradiction

/-- If a fold over adjacency lists leaves a vertex white, it was white before
the fold. -/
theorem dfsVisit_fold_output_white_imp_input_white {n : Nat} {u x : V} {s1 : DFSState V} {l : List V}
    (hout : (List.foldl (fun (s' : DFSState V) (w : V) =>
        if s'.color w = Color.white then dfsVisit G n w (s'.setParent w u) else s') s1 l).color x = Color.white) :
    s1.color x = Color.white := by
  induction l generalizing s1 with
  | nil =>
      simpa using hout
  | cons w ws ih =>
      rw [List.foldl_cons] at hout
      by_cases hw : s1.color w = Color.white
      · rw [if_pos hw] at hout
        have h2 := ih hout
        have h4 : (s1.setParent w u).color x = s1.color x := by simp
        have h5 : (s1.setParent w u).color x = Color.white := by
          exact dfsVisit_output_white_imp_input_white (G := G) (fuel := n) (u := w) (x := x) (s := s1.setParent w u) h2
        rwa [h4] at h5
      · rw [if_neg hw] at hout
        exact ih hout

/-- A fold step preserves black vertices. -/
theorem dfsVisit_fold_preserves_black_general {n : Nat} {u x : V} {s1 : DFSState V} {l : List V}
    (hb : s1.color x = Color.black) :
    (l.foldl (fun (s' : DFSState V) (w : V) =>
      if s'.color w = Color.white then dfsVisit G n w (s'.setParent w u) else s') s1).color x = Color.black := by
  have step_pres : ∀ (s' : DFSState V) (w : V),
      s'.color x = Color.black →
      (if s'.color w = Color.white then dfsVisit G n w (s'.setParent w u) else s').color x = Color.black :=
    fun s' w => dfsVisit_fold_step_preserves_black G
  induction l generalizing s1 with
  | nil => simpa
  | cons w ws ih =>
      simp
      exact ih (step_pres s1 w hb)

/-- If a vertex `v` occurs in the fold list and is white at the start of the
fold, then it is black after the fold (provided fuel is large enough). -/
theorem dfsVisit_fold_blackens_member {n : Nat} {u v : V} {s1 : DFSState V} {l : List V}
    (hn : 0 < n) (hv : v ∈ l) (hwhite : s1.color v = Color.white) :
    (l.foldl (fun (s' : DFSState V) (w : V) =>
      if s'.color w = Color.white then dfsVisit G n w (s'.setParent w u) else s') s1).color v = Color.black := by
  induction l generalizing s1 with
  | nil => simp at hv
  | cons w ws ih =>
      simp at hv
      cases hv with
      | inl hvw =>
          subst v
          simp
          by_cases hw : s1.color w = Color.white
          · rw [if_pos hw]
            have hsp : (s1.setParent w u).color w = Color.white := by simp [hw]
            have hhead : (dfsVisit G n w (s1.setParent w u)).color w = Color.black :=
              dfsVisit_blackens_u_pos G hn hsp
            exact dfsVisit_fold_preserves_black_general (l := ws) G hhead
          · rw [if_neg hw]
            contradiction
      | inr hvw =>
          simp
          by_cases hw : s1.color w = Color.white
          · rw [if_pos hw]
            by_cases hblack : (dfsVisit G n w (s1.setParent w u)).color v = Color.black
            · exact dfsVisit_fold_preserves_black_general (l := ws) G hblack
            · apply ih
              · exact hvw
              · -- The recursive call on `w` cannot leave `v` gray: if it is not
                -- black after the call, it must still be white.
                have hng : (dfsVisit G n w (s1.setParent w u)).color v ≠ Color.gray := by
                  intro h
                  have := dfsVisit_no_new_gray (G := G) (fuel := n) (u := w) (s := s1.setParent w u) v h
                  simp [hwhite] at this
                cases hcolor : (dfsVisit G n w (s1.setParent w u)).color v with
                | white => rfl
                | gray => contradiction
                | black => contradiction
          · rw [if_neg hw]
            exact ih hvw hwhite

/-- Locate the recursive fold step that first blackens a white vertex `v`.
The returned state `s2` is the state just before that recursive call, so `v`
(and the chosen neighbour) are still white in `s2`. -/
theorem dfsVisit_fold_blackens_loc {n : Nat} {u v : V} {s1 : DFSState V}
    (hwhite_v1 : s1.color v = Color.white)
    (hfold_black : (List.foldl (fun (s' : DFSState V) (w : V) =>
        if s'.color w = Color.white then dfsVisit G n w (s'.setParent w u) else s') s1 (G.adj u).toList).color v = Color.black) :
    ∃ w ∈ (G.adj u).toList, ∃ s2 : DFSState V,
      s2.color w = Color.white ∧
      s2.color v = Color.white ∧
      (dfsVisit G n w (s2.setParent w u)).color v = Color.black ∧
      (∀ z, s2.color z = Color.white → s1.color z = Color.white) := by
  revert hfold_black
  generalize (G.adj u).toList = l
  intro hfold_black
  induction l generalizing s1 with
  | nil =>
      rw [List.foldl_nil] at hfold_black
      rw [hwhite_v1] at hfold_black
      contradiction
  | cons w ws ih' =>
      rw [List.foldl_cons] at hfold_black
      by_cases hw : s1.color w = Color.white
      · rw [if_pos hw] at hfold_black
        by_cases hblack : (dfsVisit G n w (s1.setParent w u)).color v = Color.black
        · refine ⟨w, ?_, s1, hw, hwhite_v1, hblack, fun _ h => h⟩
          simp
        · have hwhite' : (dfsVisit G n w (s1.setParent w u)).color v = Color.white := by
            have hspv : (s1.setParent w u).color v = Color.white := by
              have : (s1.setParent w u).color v = s1.color v := by simp
              rw [this, hwhite_v1]
            have hng : (dfsVisit G n w (s1.setParent w u)).color v ≠ Color.gray := by
              intro h
              have := dfsVisit_no_new_gray G v h
              rw [hspv] at this
              contradiction
            cases hcolor : (dfsVisit G n w (s1.setParent w u)).color v with
            | white => rfl
            | gray => contradiction
            | black => contradiction
          have h' := ih' hwhite' hfold_black
          rcases h' with ⟨w', hw'mem, s2, h2w, h2v, h2b, h2mono⟩
          have mono2 : ∀ z, s2.color z = Color.white → s1.color z = Color.white := by
            intro z hz
            have h2 := h2mono z hz
            exact dfsVisit_output_white_imp_input_white (G := G) (fuel := n) (u := w) (x := z) (s := s1.setParent w u) h2
          refine ⟨w', ?_, s2, h2w, h2v, h2b, mono2⟩
          simp [hw'mem]
      · rw [if_neg hw] at hfold_black
        have h' := ih' hwhite_v1 hfold_black
        rcases h' with ⟨w', hw'mem, s2, h2w, h2v, h2b, h2mono⟩
        refine ⟨w', ?_, s2, h2w, h2v, h2b, fun z hz => h2mono z hz⟩
        simp [hw'mem]

/-- Variant of {name}`dfsVisit_fold_blackens_loc` that also returns the prefix
processed before the blackening call and guarantees the accumulator satisfies
the black-vertex finish-time invariant and the discovery-time invariant. -/
theorem dfsVisit_fold_blackens_loc_prefix {n : Nat} {u v : V} {s1 : DFSState V}
    (hinv : ∀ v, s1.color v = Color.black → finishTime s1 v < s1.time)
    (hwhite_v1 : s1.color v = Color.white)
    (hfold_black : (List.foldl (fun (s' : DFSState V) (w : V) =>
        if s'.color w = Color.white then dfsVisit G n w (s'.setParent w u) else s') s1 (G.adj u).toList).color v = Color.black) :
    ∃ (pre post : List V) (w : V) (s2 : DFSState V),
      (G.adj u).toList = pre ++ w :: post ∧
      s2 = List.foldl (fun (s' : DFSState V) (w : V) =>
        if s'.color w = Color.white then dfsVisit G n w (s'.setParent w u) else s') s1 pre ∧
      s2.color w = Color.white ∧
      s2.color v = Color.white ∧
      (dfsVisit G n w (s2.setParent w u)).color v = Color.black ∧
      (∀ z, s2.color z = Color.white → s1.color z = Color.white) ∧
      (∀ z, s2.color z = Color.black → finishTime s2 z < s2.time) := by
  revert hfold_black
  generalize (G.adj u).toList = l
  intro hfold_black
  induction l generalizing s1 with
  | nil =>
      rw [List.foldl_nil] at hfold_black
      rw [hwhite_v1] at hfold_black
      contradiction
  | cons w ws ih' =>
      rw [List.foldl_cons] at hfold_black
      by_cases hw : s1.color w = Color.white
      · rw [if_pos hw] at hfold_black
        by_cases hblack : (dfsVisit G n w (s1.setParent w u)).color v = Color.black
        · refine ⟨[], ws, w, s1, by simp, by simp, hw, hwhite_v1, hblack, fun _ h => h, hinv⟩
        · let s1' := dfsVisit G n w (s1.setParent w u)
          have hwhite' : s1'.color v = Color.white := by
            have hspv : (s1.setParent w u).color v = Color.white := by
              have : (s1.setParent w u).color v = s1.color v := by simp
              rw [this, hwhite_v1]
            have hng : s1'.color v ≠ Color.gray := by
              intro h
              have := dfsVisit_no_new_gray G v h
              rw [hspv] at this
              contradiction
            cases hcolor : s1'.color v with
            | white => rfl
            | gray => contradiction
            | black => contradiction
          have hinv' : ∀ z, s1'.color z = Color.black → finishTime s1' z < s1'.time := by
            by_cases hn0 : n = 0
            · -- n = 0: the call returns the input state unchanged
              have h_eq : s1' = s1.setParent w u := by
                simp [s1', hn0, dfsVisit]
              intro z hz
              rw [h_eq] at hz ⊢
              have hz1 : s1.color z = Color.black := by
                simpa using hz
              have h1 : finishTime (s1.setParent w u) z = finishTime s1 z := by
                simp [finishTime]
              have h2 : (s1.setParent w u).time = s1.time := by
                simp
              rw [h1, h2]
              exact hinv z hz1
            · -- n > 0: output invariant from the recursive visit
              have hsp_inv : ∀ z, (s1.setParent w u).color z = Color.black → finishTime (s1.setParent w u) z < (s1.setParent w u).time := by
                intro z hz
                have hz1 : s1.color z = Color.black := by
                  simpa using hz
                have h1 : finishTime (s1.setParent w u) z = finishTime s1 z := by
                  simp [finishTime]
                have h2 : (s1.setParent w u).time = s1.time := by
                  simp
                rw [h1, h2]
                exact hinv z hz1
              exact dfsVisit_black_finish_lt_time G (by omega) (by simpa using hw) hsp_inv
          have h' := ih' hinv' hwhite' hfold_black
          rcases h' with ⟨pre', post', w', s2, heq, hs2, h2w, h2v, h2b, h2mono, h2inv⟩
          have mono2 : ∀ z, s2.color z = Color.white → s1.color z = Color.white := by
            intro z hz
            have h2 := h2mono z hz
            exact dfsVisit_output_white_imp_input_white (G := G) (fuel := n) (u := w) (x := z) (s := s1.setParent w u) h2
          refine ⟨w :: pre', post', w', s2, by simp [heq], by simp [hs2, hw, s1'], h2w, h2v, h2b, mono2, h2inv⟩
      · rw [if_neg hw] at hfold_black
        have h' := ih' hinv hwhite_v1 hfold_black
        rcases h' with ⟨pre', post', w', s2, heq, hs2, h2w, h2v, h2b, h2mono, h2inv⟩
        refine ⟨w :: pre', post', w', s2, by simp [heq], by simp [hs2, hw], h2w, h2v, h2b, fun z hz => h2mono z hz, h2inv⟩

/-- A recursive `dfsVisit` call that blackens a white vertex `v` discovers a
white path from its source to `v`. -/
theorem dfsVisit_blackens_implies_whiteReachable {fuel : Nat} {u v : V} {s : DFSState V}
    (hwhite : s.color u = Color.white) (hfuel : 0 < fuel)
    (hwhite_v : s.color v = Color.white)
    (hb : (dfsVisit G fuel u s).color v = Color.black) :
    WhiteReachable G s u v := by
  induction fuel generalizing u v s with
  | zero => linarith
  | succ n ih =>
      simp [dfsVisit, hwhite] at hb
      by_cases hvu : v = u
      · subst v
        exact whiteReachable_refl G s u
      · let s1 := s.setColor u Color.gray |>.setDiscovery u
        let gray := s.setColor u Color.gray
        have hwhite_v1 : s1.color v = Color.white := by
          have hs1 : s1 = (s.setColor u Color.gray).setDiscovery u := rfl
          rw [hs1]
          simp [hvu, hwhite_v]
        have hfold_black : (List.foldl (fun (s' : DFSState V) (w : V) =>
            if s'.color w = Color.white then dfsVisit G n w (s'.setParent w u) else s') s1 (G.adj u).toList).color v = Color.black := by
          simpa [hvu] using hb
        have hloc := dfsVisit_fold_blackens_loc G hwhite_v1 hfold_black
        rcases hloc with ⟨w, hwmem, s2, hwhite_w2, hwhite_v2_s2, hblack2, hmono⟩
        have hwhite_v2 : (s2.setParent w u).color v = Color.white := by
          have h1 : (s2.setParent w u).color v = s2.color v := by simp
          rw [h1, hwhite_v2_s2]
        have hsp_white : (s2.setParent w u).color w = Color.white := by
          simp [hwhite_w2]
        have hn_pos : 0 < n := by
          by_contra h
          push Not at h
          have : n = 0 := by omega
          subst n
          simp [dfsVisit] at hblack2
          rw [hwhite_v2_s2] at hblack2
          contradiction
        have hr_wv := ih (u := w) (v := v) (s := s2.setParent w u)
            hsp_white hn_pos hwhite_v2 hblack2
        have hmono' : ∀ z, (s2.setParent w u).color z = Color.white → s1.color z = Color.white := by
          intro z hz
          have h2 : s2.color z = Color.white := by
            have h1 : (s2.setParent w u).color z = s2.color z := by simp
            rwa [h1] at hz
          exact hmono z h2
        have hr_wv_s1 : WhiteReachable G s1 w v :=
          whiteReachable_mono_of_color_superset G hmono' hr_wv
        have hcolors : ∀ z, s1.color z = gray.color z := by
          intro z
          have hs1' : s1 = (s.setColor u Color.gray).setDiscovery u := rfl
          have hgray' : gray = s.setColor u Color.gray := rfl
          rw [hs1', hgray']
          by_cases hz : z = u
          · simp [hz]
          · simp [hz]
        have hr_wv_gray : WhiteReachable G gray w v := by
          rwa [WhiteReachable.color_eq G hcolors] at hr_wv_s1
        have hadj_uw : G.Adj u w := by
          simp [Finset.mem_toList] at hwmem
          exact hwmem
        have hwu : w ≠ u := by
          intro h
          subst w
          have h1 : s1.color u = Color.white := hmono u hwhite_w2
          have h2 : s1.color u = Color.gray := by
            have hs1' : s1 = (s.setColor u Color.gray).setDiscovery u := rfl
            rw [hs1']
            simp
          rw [h2] at h1
          contradiction
        have hw_white_gray : gray.color w = Color.white := by
          have h1 : s1.color w = Color.white := hmono w hwhite_w2
          dsimp [gray]
          simp [hwu]
          have hs1' : s1 = (s.setColor u Color.gray).setDiscovery u := rfl
          rw [hs1'] at h1
          simpa [hwu] using h1
        have hr_uw_gray : WhiteReachable G gray u w :=
          whiteReachable_step G (whiteReachable_refl G gray u) hadj_uw hw_white_gray
        have hr_uv_gray : WhiteReachable G gray u v :=
          whiteReachable_trans G hr_uw_gray hr_wv_gray
        exact whiteReachable_gray_to_white G hwhite hr_uv_gray

section WhitePathForward

/-! ## Forward direction of the white-path theorem

If a vertex `v` is reachable from a white source `u` through white vertices,
then a sufficiently fuelled `dfsVisit` from `u` blackens `v`.
-/

/-- If a DFS visit from `w` blackens exactly the white-reachable set from `w`
(among vertices that were white before the visit), and leaves `v` non-black,
then any white path from `x` to `v` that existed before the visit remains white
after the visit. -/
theorem WhiteReachable.preserved_after_visit {fuel : Nat} {s' : DFSState V} {w x v : V}
    (hw : w ∈ G.vertices)
    (hblack_iff : ∀ y, s'.color y = Color.white →
        ((dfsVisit G fuel w s').color y = Color.black ↔ y ∈ whiteReachableSet G s' w))
    (hwhite_x : s'.color x = Color.white)
    (hpath : WhiteReachable G s' x v)
    (hnv : (dfsVisit G fuel w s').color v ≠ Color.black) :
    WhiteReachable G (dfsVisit G fuel w s') x v := by
  let s'' := dfsVisit G fuel w s'
  have hwhite_or_black {z} (hz : s'.color z = Color.white) :
      s''.color z = Color.white ∨ s''.color z = Color.black := by
    by_cases hb : s''.color z = Color.black
    · right; exact hb
    · left
      exact dfsVisit_white_stays_white_or_black G hz hb
  have hmem_self (a : V) : a ∈ whiteReachableSet G s' a := by
    have h0 : a ∈ whiteReachableIter G s' a 0 := by simp [whiteReachableIter]
    exact whiteReachableIter_mono_le G s' a (by linarith) h0
  have hwhite_v : s'.color v = Color.white :=
    whiteReachable_target_white (G := G) hwhite_x hpath
  have hP : ∀ a, WhiteReachable G s' x a → WhiteReachable G s' a v → s''.color a ≠ Color.black → WhiteReachable G s'' x a := by
    intro a hr_xa
    induction hr_xa with
    | refl =>
        intro _ _
        exact whiteReachable_refl G s'' x
    | @tail p q hpq hstep ih =>
        intro hr_qv hnblack_q
        have hwhite_q_s' : s'.color q = Color.white := hstep.2
        have hr_pv : WhiteReachable G s' p v :=
          whiteReachable_trans G (whiteReachable_step G (whiteReachable_refl G s' p) hstep.1 hstep.2) hr_qv
        have hwhite_p_s' : s'.color p = Color.white :=
          whiteReachable_target_white (G := G) hwhite_x hpq
        have hnblack_p : s''.color p ≠ Color.black := by
          intro hb
          have hpw : p ∈ whiteReachableSet G s' w := (hblack_iff p hwhite_p_s').mp hb
          have hpw' := whiteReachableIter_to_WhiteReachable G hpw
          have hpv : p ∈ G.vertices :=
            whiteReachableIter_subset_vertices G s' w hw (G.vertices.card) hpw
          have hsubset := whiteReachableSet_subset_of_WhiteReachable G hw hpw'
          have hvp_set : v ∈ whiteReachableSet G s' p :=
            WhiteReachable.mem_set G hpv hr_pv
          have hvw : v ∈ whiteReachableSet G s' w := hsubset hvp_set
          have hb_v : s''.color v = Color.black := (hblack_iff v hwhite_v).mpr hvw
          contradiction
        have hwhite_p_s'' : s''.color p = Color.white :=
          (hwhite_or_black hwhite_p_s').resolve_right hnblack_p
        have hwhite_q_s'' : s''.color q = Color.white :=
          (hwhite_or_black hwhite_q_s').resolve_right hnblack_q
        have hr_xp_s'' := ih hr_pv hnblack_p
        exact whiteReachable_step G hr_xp_s'' hstep.1 hwhite_q_s''
  exact hP v hpath (whiteReachable_refl G s' v) hnv

/-- Forward direction of the white-path theorem.

A sufficiently fuelled `dfsVisit` from a white source `u` blackens every vertex
that is reachable from `u` through white vertices. -/
theorem dfsVisit_white_path_black {fuel : Nat} {u v : V} {s : DFSState V}
    (hwhite : s.color u = Color.white) (hu : u ∈ G.vertices)
    (hfuel : fuel ≥ (whiteReachableSet G s u).card + 1)
    (hv : v ∈ whiteReachableSet G s u) :
    (dfsVisit G fuel u s).color v = Color.black := by
  generalize hM : (whiteReachableSet G s u).card = M
  revert fuel u v s hwhite hu hfuel hv hM
  induction M using Nat.strongRecOn with
  | ind M ih =>
    intro fuel u v s hwhite hu hfuel hv hM
    have h0fuel : 0 < fuel := by omega
    by_cases hvu : v = u
    · subst v
      exact dfsVisit_blackens_u_pos G h0fuel hwhite
    · have hne : v ≠ u := hvu
      rcases whiteReachableSet_decomp_ne G hu hwhite hv hne with ⟨x, hadj, hwhite_x, hxne, hvx⟩
      let s1 := s.setColor u Color.gray |>.setDiscovery u
      let gray := s.setColor u Color.gray
      have hwhite_x_s1 : s1.color x = Color.white := by
        simp [s1, hxne, hwhite_x]
      have hvx_s1 : v ∈ whiteReachableSet G s1 x := by
        have hcolors : ∀ z, s1.color z = gray.color z := by
          intro z
          simp [s1, gray]
        rw [whiteReachableSet_eq_of_color_eq G (G.adj_mem_right hadj) hcolors]
        exact hvx
      let step := fun (s' : DFSState V) (w : V) =>
        if s'.color w = Color.white then dfsVisit G (fuel - 1) w (s'.setParent w u) else s'
      have hinv : ∀ (l' : List V) (s' : DFSState V),
          l' ⊆ (G.adj u).toList →
          x ∈ l' →
          (∀ z, s'.color z = Color.white → s1.color z = Color.white) →
          (s'.color x = Color.white ∧ v ∈ whiteReachableSet G s' x) →
          (List.foldl step s' l').color v = Color.black := by
        intro l' s' hlsub hxmem hmono hP
        induction l' generalizing s' with
        | nil =>
            simp at hxmem
        | cons w ws ih' =>
            have hwmem : w ∈ (G.adj u).toList := by
              apply hlsub
              simp
            have hws_sub : ws ⊆ (G.adj u).toList := by
              intro y hy
              apply hlsub
              simp [hy]
            simp at hxmem
            rcases hxmem with (rfl | hxws)
            · -- w = x
              simp [step]
              rw [if_pos hP.1]
              let s0 := s'.setParent x u
              have hwhite_x_s0 : s0.color x = Color.white := by simp [s0, hP.1]
              have hcolors0 : ∀ z, s0.color z = s'.color z := by simp [s0]
              have hvx_s0 : v ∈ whiteReachableSet G s0 x := by
                rw [whiteReachableSet_eq_of_color_eq G (G.adj_mem_right hadj) hcolors0]
                exact hP.2
              have hcard_x : (whiteReachableSet G s0 x).card < M := by
                have h1 : whiteReachableSet G s0 x = whiteReachableSet G s' x :=
                  whiteReachableSet_eq_of_color_eq G (G.adj_mem_right hadj) hcolors0
                have h2 : whiteReachableSet G s' x ⊆ whiteReachableSet G s1 x :=
                  whiteReachableSet_mono_of_color_superset G (G.adj_mem_right hadj) hmono
                have h3 : whiteReachableSet G s1 x = whiteReachableSet G gray x := by
                  apply whiteReachableSet_eq_of_color_eq G (G.adj_mem_right hadj)
                  intro z
                  simp [s1, gray]
                have h4 : (whiteReachableSet G gray x).card < (whiteReachableSet G s u).card := by
                  apply Finset.card_lt_card
                  exact whiteReachableSet_neighbor_ssubset G hu hwhite hadj hwhite_x hxne
                rw [h1]
                apply Nat.lt_of_le_of_lt (Finset.card_le_card h2)
                rw [h3]
                linarith [hM]
              have hfuel_x : fuel - 1 ≥ (whiteReachableSet G s0 x).card + 1 := by
                omega
              have hblack_x : (dfsVisit G (fuel - 1) x s0).color v = Color.black := by
                exact @ih (whiteReachableSet G s0 x).card (by linarith [hM, hcard_x]) (fuel - 1) x v s0 hwhite_x_s0 (G.adj_mem_right hadj) hfuel_x hvx_s0 (by rfl)
              exact dfsVisit_fold_preserves_black_general G hblack_x
            · -- w ≠ x
              simp [step]
              by_cases hw : s'.color w = Color.white
              · rw [if_pos hw]
                let s0 := s'.setParent w u
                let s'' := dfsVisit G (fuel - 1) w s0
                have hadj_w : G.Adj u w := by
                  simp [Finset.mem_toList] at hwmem
                  exact hwmem
                have hcolors0 : ∀ z, s0.color z = s'.color z := by simp [s0]
                have hcard_w : (whiteReachableSet G s0 w).card < M := by
                  have h1 : whiteReachableSet G s0 w = whiteReachableSet G s' w :=
                    whiteReachableSet_eq_of_color_eq G (G.adj_mem_right hadj_w) hcolors0
                  have h2 : whiteReachableSet G s' w ⊆ whiteReachableSet G s1 w :=
                    whiteReachableSet_mono_of_color_superset G (G.adj_mem_right hadj_w) hmono
                  have h3 : whiteReachableSet G s1 w = whiteReachableSet G gray w := by
                    apply whiteReachableSet_eq_of_color_eq G (G.adj_mem_right hadj_w)
                    intro z
                    simp [s1, gray]
                  have h4 : (whiteReachableSet G gray w).card < (whiteReachableSet G s u).card := by
                    have hwne : w ≠ u := by
                      intro hwu
                      subst w
                      have : s1.color u = Color.white := hmono u (by simpa using hw)
                      simp [s1] at this
                    have hwhite_w_s : s.color w = Color.white := by
                      have h1 : s1.color w = Color.white := hmono w hw
                      simp [s1, hwne] at h1
                      exact h1
                    apply Finset.card_lt_card
                    exact whiteReachableSet_neighbor_ssubset G hu hwhite hadj_w hwhite_w_s hwne
                  rw [h1]
                  apply Nat.lt_of_le_of_lt (Finset.card_le_card h2)
                  rw [h3]
                  linarith [hM]
                have hfuel_w : fuel - 1 ≥ (whiteReachableSet G s0 w).card + 1 := by
                  omega
                have hwhite_v_s0 : s0.color v = Color.white := by
                  have hvx_s0 : v ∈ whiteReachableSet G s0 x := by
                    rw [whiteReachableSet_eq_of_color_eq G (G.adj_mem_right hadj) hcolors0]
                    exact hP.2
                  have hpath : WhiteReachable G s0 x v :=
                    whiteReachableIter_to_WhiteReachable G hvx_s0
                  exact whiteReachable_target_white (G := G) (by simp [s0, hP.1]) hpath
                have hblack_iff : ∀ y, s0.color y = Color.white →
                    (s''.color y = Color.black ↔ y ∈ whiteReachableSet G s0 w) := by
                  intro y hy_white
                  constructor
                  · intro hblack
                    exact WhiteReachable.mem_set G (G.adj_mem_right hadj_w)
                      (dfsVisit_blackens_implies_whiteReachable G (by simp [s0]; exact hw) (by omega) hy_white hblack)
                  · intro hy
                    exact @ih (whiteReachableSet G s0 w).card (by linarith [hM, hcard_w]) (fuel - 1) w y s0 (by simp [s0]; exact hw) (G.adj_mem_right hadj_w) hfuel_w hy (by rfl)
                have hP'' : s''.color v = Color.black ∨ (s''.color x = Color.white ∧ v ∈ whiteReachableSet G s'' x) := by
                  by_cases hblack_v : s''.color v = Color.black
                  · left; exact hblack_v
                  · right
                    have hwhite_x_s0 : s0.color x = Color.white := by simp [s0, hP.1]
                    have hwhite_x_s'' : s''.color x = Color.white := by
                      have hnx : s''.color x ≠ Color.black := by
                        intro hb
                        have hxw : x ∈ whiteReachableSet G s0 w := (hblack_iff x hwhite_x_s0).mp hb
                        have hxw' := whiteReachableIter_to_WhiteReachable G hxw
                        have hsubset := whiteReachableSet_subset_of_WhiteReachable G (G.adj_mem_right hadj_w) hxw'
                        have hvx_s' : WhiteReachable G s' x v := whiteReachableIter_to_WhiteReachable G hP.2
                        have hvx_s0 : WhiteReachable G s0 x v :=
                          (WhiteReachable.color_eq G (fun z => (hcolors0 z).symm)).mpr hvx_s'
                        have hvx_s0_set : v ∈ whiteReachableSet G s0 x :=
                          WhiteReachable.mem_set G (G.adj_mem_right hadj) hvx_s0
                        have hvw : v ∈ whiteReachableSet G s0 w := hsubset hvx_s0_set
                        have hb_v := (hblack_iff v hwhite_v_s0).mpr hvw
                        contradiction
                      exact dfsVisit_white_stays_white_or_black G hwhite_x_s0 hnx
                    have hv_s'' : v ∈ whiteReachableSet G s'' x := by
                      have hpath_s' : WhiteReachable G s' x v := whiteReachableIter_to_WhiteReachable G hP.2
                      have hpath : WhiteReachable G s0 x v :=
                        (WhiteReachable.color_eq G (fun z => (hcolors0 z).symm)).mpr hpath_s'
                      have hpreserved := WhiteReachable.preserved_after_visit G (G.adj_mem_right hadj_w) hblack_iff hwhite_x_s0 hpath hblack_v
                      exact WhiteReachable.mem_set G (G.adj_mem_right hadj) hpreserved
                    exact ⟨hwhite_x_s'', hv_s''⟩
                have hmono'' : ∀ z, s''.color z = Color.white → s1.color z = Color.white := by
                  intro z hz
                  have h1 : s0.color z = Color.white := dfsVisit_output_white_imp_input_white (G := G) hz
                  have h2 : s'.color z = Color.white := by simpa [s0] using h1
                  exact hmono z h2
                rcases hP'' with (hblack_v' | hP''')
                · exact dfsVisit_fold_preserves_black_general G hblack_v'
                · exact ih' s'' hws_sub hxws hmono'' hP'''
              · rw [if_neg hw]
                exact ih' s' hws_sub hxws hmono hP
      have hxmem : x ∈ (G.adj u).toList := by
        rw [Finset.mem_toList]
        exact hadj
      have hfold_black : (List.foldl step s1 (G.adj u).toList).color v = Color.black :=
        hinv (G.adj u).toList s1 (fun _ h => h) hxmem (fun _ h => h) ⟨hwhite_x_s1, hvx_s1⟩
      have : (dfsVisit G fuel u s).color v = (List.foldl step s1 (G.adj u).toList).color v := by
        cases fuel with
        | zero => linarith
        | succ n =>
            simp [dfsVisit, hwhite, hvu, s1, step]
      rw [this]
      exact hfold_black

/-- A sufficiently fuelled `dfsVisit` from a white source `u` blackens exactly
the white vertices that are reachable from `u` through white vertices. -/
theorem dfsVisit_blackens_iff_whiteReachable {fuel : Nat} {u v : V} {s : DFSState V}
    (hwhite_u : s.color u = Color.white) (hu : u ∈ G.vertices)
    (hwhite_v : s.color v = Color.white)
    (hfuel : fuel ≥ (whiteReachableSet G s u).card + 1) :
    (dfsVisit G fuel u s).color v = Color.black ↔ v ∈ whiteReachableSet G s u := by
  constructor
  · intro hb
    exact WhiteReachable.mem_set G hu (dfsVisit_blackens_implies_whiteReachable G hwhite_u (by omega) hwhite_v hb)
  · intro hv
    exact dfsVisit_white_path_black G hwhite_u hu hfuel hv

end WhitePathForward

end Graph
end Chapter22
end CLRS

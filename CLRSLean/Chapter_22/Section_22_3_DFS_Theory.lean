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

/-! ### Fold decomposition lemma (sub-problem 1) -/

/-- When the adjacency list decomposes as `pre ++ v :: post` and the fold
accumulator at `pre` is `s2` with `s2.color v = Color.white`, the full fold
equals the fold over `post` starting from the recursive dfsVisit on `v`.
This pure `List.foldl` identity uses a named step function to avoid
lambda-matching issues. -/
lemma dfsVisit_fold_split_at_white_neighbor {n : Nat} {u v : V}
    (s_init : DFSState V) (pre post : List V) (s2 : DFSState V)
    (hadj_eq : (G.adj u).toList = pre ++ v :: post)
    (hs2_eq : s2 = List.foldl (fun s' x =>
      if s'.color x = Color.white then dfsVisit G n x (s'.setParent x u) else s') s_init pre)
    (hv_white_s2 : s2.color v = Color.white) :
    (List.foldl (fun s' x =>
      if s'.color x = Color.white then dfsVisit G n x (s'.setParent x u) else s')
      s_init (G.adj u).toList) =
    (List.foldl (fun s' x =>
      if s'.color x = Color.white then dfsVisit G n x (s'.setParent x u) else s')
      (dfsVisit G n v (s2.setParent v u)) post) := by
  let step : DFSState V → V → DFSState V := fun s' x =>
    if s'.color x = Color.white then dfsVisit G n x (s'.setParent x u) else s'
  have h_step : step s2 v = dfsVisit G n v (s2.setParent v u) := by
    dsimp [step]; rw [if_pos hv_white_s2]
  have h_foldl_step : List.foldl step s2 (v :: post) = List.foldl step (step s2 v) post := rfl
  calc
    List.foldl step s_init (G.adj u).toList
        = List.foldl step s_init (pre ++ v :: post) := by rw [hadj_eq]
    _ = List.foldl step (List.foldl step s_init pre) (v :: post) := by rw [List.foldl_append]
    _ = List.foldl step s2 (v :: post) := by rw [hs2_eq]
    _ = List.foldl step (step s2 v) post := h_foldl_step
    _ = List.foldl step (dfsVisit G n v (s2.setParent v u)) post := by rw [h_step]

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

section ReachabilityInvariants

/-! ## DFS reachability invariants

For any prefix of a full DFS, the set of black vertices is closed under
reachability: if a vertex is black, every vertex reachable from it is also
black.  This lets us argue that a path to a still-white vertex stays entirely
white at the moment of discovery. -/

/-- A `dfsVisit` from a white source blackens exactly the vertices that were
already black together with the white-reachable set from the source. -/
theorem dfsVisit_black_set {fuel : Nat} {u : V} {s : DFSState V}
    (hfuel : fuel ≥ (whiteReachableSet G s u).card + 1) (hwhite : s.color u = Color.white)
    (hu : u ∈ G.vertices)
    (hng : ∀ v, s.color v = Color.white ∨ s.color v = Color.black) :
    ∀ v, (dfsVisit G fuel u s).color v = Color.black ↔
      s.color v = Color.black ∨ v ∈ whiteReachableSet G s u := by
  intro v
  by_cases hblack : s.color v = Color.black
  · have hout : (dfsVisit G fuel u s).color v = Color.black := dfsVisit_preserves_black G hblack
    simp [hout, hblack]
  · have hwhite_v : s.color v = Color.white := by cases hng v <;> tauto
    have hiff := dfsVisit_blackens_iff_whiteReachable G hwhite hu hwhite_v hfuel
    simp [hblack, hiff]

/-- If `z` reaches a white vertex `p` and every vertex reachable from `z` and
from which `p` is reachable is white, then `p` is white-reachable from `z`. -/
theorem WhiteReachable.of_reachable_closed {s : DFSState V} {z p : V}
    (hwhite_p : s.color p = Color.white)
    (hreach : G.Reachable z p)
    (hwhite_inter : ∀ b, G.Reachable z b → G.Reachable b p → s.color b = Color.white) :
    WhiteReachable G s z p := by
  induction hreach with
  | refl =>
      exact whiteReachable_refl G s z
  | @tail x y hzx hadj ih =>
      have hx_white := hwhite_inter x hzx
        (G.reachable_trans (G.reachable_adj hadj) (G.reachable_refl y))
      have hzx' := ih hx_white (fun b hzb hbp => hwhite_inter b hzb (G.reachable_trans hbp (G.reachable_adj hadj)))
      exact whiteReachable_step G hzx' hadj hwhite_p

/-- After any prefix of a full DFS, black vertices are closed under reachability. -/
theorem dfsFromList_black_reachable_closed {fuel : Nat} {s0 : DFSState V} {vs : List V}
    (hfuel : 0 < fuel)
    (hfuel_bound : fuel ≥ G.vertices.card + 1)
    (hng : ∀ v, s0.color v = Color.white ∨ s0.color v = Color.black)
    (hclosed : ∀ z p, s0.color z = Color.black → G.Reachable z p → s0.color p = Color.black)
    (hvs : ∀ v ∈ vs, v ∈ G.vertices) :
    ∀ z p, (dfsFromList G fuel vs s0).color z = Color.black → G.Reachable z p →
      (dfsFromList G fuel vs s0).color p = Color.black := by
  induction vs generalizing s0 hng hclosed with
  | nil => simpa [dfsFromList]
  | cons u us ih =>
      by_cases hwhite : s0.color u = Color.white
      · -- u is white: the visit blackens the white-reachable set
        simp [dfsFromList, hwhite]
        let s1 := dfsVisit G fuel u s0
        have hng1 : ∀ v, s1.color v = Color.white ∨ s1.color v = Color.black := by
          apply dfsVisit_output_no_gray
          intro v; cases hng v <;> simp [*]
        have hcard : fuel ≥ (whiteReachableSet G s0 u).card + 1 := by
          have hsub : whiteReachableSet G s0 u ⊆ G.vertices :=
            whiteReachableSet_subset_vertices G s0 u (hvs u (by simp))
          have hcard : (whiteReachableSet G s0 u).card ≤ G.vertices.card :=
            Finset.card_le_card hsub
          omega
        have hblack_set := dfsVisit_black_set G hcard hwhite (hvs u (by simp)) hng
        have hclosed1 : ∀ z p, s1.color z = Color.black → G.Reachable z p → s1.color p = Color.black := by
          intro z p hz hp
          rw [hblack_set z] at hz
          rcases hz with (hz0 | hzwr)
          · -- z was already black in s0; closure forces p to be black in s0
            by_cases hp0 : s0.color p = Color.black
            · exact dfsVisit_preserves_black G hp0
            · have hpw : s0.color p = Color.white := by cases hng p <;> tauto
              have hp_black := hclosed z p hz0 hp
              contradiction
          · -- z is white-reachable from u; extend the white path to p
            by_cases hp0 : s0.color p = Color.black
            · exact dfsVisit_preserves_black G hp0
            · have hpw : s0.color p = Color.white := by cases hng p <;> tauto
              have hpwr : p ∈ whiteReachableSet G s0 u := by
                have hwr_z := whiteReachableIter_to_WhiteReachable G hzwr
                have hwr_p := WhiteReachable.of_reachable_closed G hpw hp (fun b _ hbp => by
                  by_contra hb
                  push_neg at hb
                  have hb_black : s0.color b = Color.black := by cases hng b <;> tauto
                  have hp_black := hclosed b p hb_black hbp
                  contradiction)
                have hwr_up := whiteReachable_trans G hwr_z hwr_p
                exact WhiteReachable.mem_set G (hvs u (by simp)) hwr_up
              rw [hblack_set p]
              right; exact hpwr
        exact ih (s0 := s1) hng1 hclosed1 (fun v hv => hvs v (List.mem_cons_of_mem u hv))
      · -- u is not white: the state is unchanged on this step
        have hunchanged : dfsVisit G fuel u s0 = s0 := by
          have hne : s0.color u ≠ Color.white := by simpa using hwhite
          induction fuel with
          | zero => simp [dfsVisit]
          | succ n _ => simp [dfsVisit, hne]
        simp [dfsFromList, hwhite]
        exact ih (s0 := s0) hng hclosed (fun v hv => hvs v (List.mem_cons_of_mem u hv))

/-- Finish times of black vertices are preserved by any further `dfsFromList`. -/
theorem dfsFromList_preserves_f_of_black {fuel : Nat} {s0 : DFSState V} {vs : List V}
    (hfuel : 0 < fuel) {x : V}
    (hblack : s0.color x = Color.black) :
    (dfsFromList G fuel vs s0).f x = s0.f x := by
  induction vs generalizing s0 with
  | nil => simp [dfsFromList]
  | cons u us ih =>
      simp [dfsFromList]
      split_ifs with hwhite
      · have hblack' : (dfsVisit G fuel u s0).color x = Color.black :=
          dfsVisit_preserves_black G hblack
        have hf : (dfsVisit G fuel u s0).f x = s0.f x := by
          by_cases hxu : x = u
          · rw [hxu] at hblack
            have : s0.color u ≠ Color.white := by simp [hblack]
            contradiction
          · have hnw : s0.color x ≠ Color.white := by simp [hblack]
            exact dfsVisit_preserves_f_of_not_white G hxu hnw
        have h1 := ih (s0 := dfsVisit G fuel u s0) hblack'
        rw [h1, hf]
      · exact ih hblack

/-- `dfsFromList` never moves the global clock backwards. -/
theorem dfsFromList_time_ge {fuel : Nat} {s0 : DFSState V} {vs : List V} :
    (dfsFromList G fuel vs s0).time ≥ s0.time := by
  induction vs generalizing s0 with
  | nil => simp [dfsFromList]
  | cons u us ih =>
      simp [dfsFromList]
      split_ifs with hwhite
      · have h1 := G.dfsVisit_time_ge (fuel := fuel) (u := u) (s := s0)
        have h2 := ih (s0 := dfsVisit G fuel u s0)
        linarith
      · exact ih

end ReachabilityInvariants

section Intervals

/-! ## DFS timestamps, intervals and ancestor relation

The parenthesis theorem compares the closed intervals
`[d[u], f[u]]` defined by the discovery/finish timestamps of a full DFS.
It is the key to edge classification and to the finish-time ordering of
strongly connected components. -/

/-- {lit}`u` finishes strictly before {lit}`v` is discovered. -/
def finishesBeforeDiscovered (s : DFSState V) (u v : V) : Prop :=
  finishTime s u < discoveryTime s v

/-- {lit}`v`'s interval is strictly nested inside {lit}`u`'s interval. -/
def intervalNestedInside (s : DFSState V) (u v : V) : Prop :=
  discoveryTime s u < discoveryTime s v ∧ finishTime s v < finishTime s u

/-- {lit}`u` is an ancestor of {lit}`v` in the DFS parent forest
(reflexive-transitive closure of the parent relation). -/
def IsDFSAncestor (s : DFSState V) (u v : V) : Prop :=
  Relation.ReflTransGen (fun x y => s.parent y = some x) u v

/-- {lit}`v` is a descendant of {lit}`u` in the DFS parent forest; this is the
same relation as {name}`IsDFSAncestor`. -/
def IsDFSDescendant (s : DFSState V) (u v : V) : Prop := IsDFSAncestor s u v

@[simp]
theorem IsDFSAncestor.refl (s : DFSState V) (u : V) : IsDFSAncestor s u u :=
  Relation.ReflTransGen.refl

/-- The source of a DFS visit is discovered at the input state's clock value. -/
theorem dfsVisit_discovery_source {fuel : Nat} {u : V} {s : DFSState V}
    (hfuel : 0 < fuel) (hwhite : s.color u = Color.white) :
    discoveryTime (dfsVisit G fuel u s) u = s.time := by
  cases fuel with
  | zero => linarith
  | succ n =>
      let s1 := s.setColor u Color.gray |>.setDiscovery u
      let s2 := List.foldl (fun (s' : DFSState V) (v : V) =>
          if s'.color v = Color.white then dfsVisit G n v (s'.setParent v u) else s') s1 (G.adj u).toList
      let s3 := s2.setColor u Color.black |>.setFinish u
      have heq_state : dfsVisit G (n + 1) u s = s3 := by
        simp [s3, s2, s1, dfsVisit, hwhite]
      rw [heq_state]
      have hs2 : s2.d u = s1.d u := by
        apply G.dfsVisit_fold_preserves_d_of_not_white
        simpa [s1]
      simp [s3, s1, discoveryTime, hs2]

/-- Stronger version: the source's `d` field equals `some (s.time)`. -/
theorem dfsVisit_discovery_source_d_eq {fuel : Nat} {u : V} {s : DFSState V}
    (hfuel : 0 < fuel) (hwhite : s.color u = Color.white) :
    (dfsVisit G fuel u s).d u = some (s.time) := by
  cases fuel with
  | zero => omega
  | succ n =>
      let s1 := s.setColor u Color.gray |>.setDiscovery u
      let s2 := List.foldl (fun (s' : DFSState V) (v : V) =>
          if s'.color v = Color.white then dfsVisit G n v (s'.setParent v u) else s') s1 (G.adj u).toList
      let s3 := s2.setColor u Color.black |>.setFinish u
      have heq_state : dfsVisit G (n + 1) u s = s3 := by
        simp [s3, s2, s1, dfsVisit, hwhite]
      rw [heq_state]
      have h_set : s1.d u = some (s.time) := by simp [s1]
      have hnw : s1.color u ≠ Color.white := by simp [s1]
      have h_fold : s2.d u = s1.d u :=
        dfsVisit_fold_preserves_d_of_not_white G (u := u) (v := u) s1 (l := (G.adj u).toList) hnw
      have h_finish : s3.d u = s2.d u := by simp [s3]
      simp [h_set, h_fold, h_finish]

/-- The source of a DFS visit is finished exactly one time unit before the
output state's clock. -/
theorem dfsVisit_finishTime_source_eq_pred_time {fuel : Nat} {u : V} {s : DFSState V}
    (hfuel : 0 < fuel) (hwhite : s.color u = Color.white) :
    finishTime (dfsVisit G fuel u s) u = (dfsVisit G fuel u s).time - 1 := by
  cases fuel with
  | zero => linarith
  | succ n =>
      let s1 := s.setColor u Color.gray |>.setDiscovery u
      let s2 := List.foldl (fun (s' : DFSState V) (v : V) =>
          if s'.color v = Color.white then dfsVisit G n v (s'.setParent v u) else s') s1 (G.adj u).toList
      let s3 := s2.setColor u Color.black |>.setFinish u
      have heq_state : dfsVisit G (n + 1) u s = s3 := by
        simp [s3, s2, s1, dfsVisit, hwhite]
      rw [heq_state]
      have hs2 : s2.f u = s1.f u := by
        apply G.dfsVisit_fold_preserves_f_of_not_white s1
        simpa [s1]
      simp [s3, s1, finishTime, hs2]
      <;> omega

/-- In a DFS visit from a white source `u`, every vertex blackened during the
visit finishes no later than `u`. -/
theorem dfsVisit_finish_le_source {fuel : Nat} {u v : V} {s : DFSState V}
    (hfuel : 0 < fuel) (hwhite : s.color u = Color.white)
    (hinv : ∀ w, s.color w = Color.black → finishTime s w < s.time)
    (hblack : (dfsVisit G fuel u s).color v = Color.black) :
    finishTime (dfsVisit G fuel u s) v ≤ finishTime (dfsVisit G fuel u s) u := by
  by_cases hvu : v = u
  · subst v; rfl
  · have h1 : finishTime (dfsVisit G fuel u s) u = (dfsVisit G fuel u s).time - 1 :=
      dfsVisit_finishTime_source_eq_pred_time G hfuel hwhite
    have h2 : finishTime (dfsVisit G fuel u s) v < (dfsVisit G fuel u s).time := by
      apply dfsVisit_black_finish_lt_time G hfuel hwhite hinv
      exact hblack
    have htime_pos : (dfsVisit G fuel u s).time > 0 := by
      have : finishTime (dfsVisit G fuel u s) v ≥ 0 := Nat.zero_le _
      omega
    omega

/-- Any non-source vertex discovered during a DFS visit is discovered at a time
strictly later than the input state's clock. -/
theorem dfsVisit_discovery_ge_input_time {fuel : Nat} {u v : V} {s : DFSState V}
    (hfuel : 0 < fuel) (hwhite : s.color u = Color.white)
    (hwhite_v : s.color v = Color.white)
    (hblack : (dfsVisit G fuel u s).color v = Color.black) (hne : v ≠ u) :
    discoveryTime (dfsVisit G fuel u s) v ≥ s.time + 1 := by
  induction fuel generalizing u s with
  | zero =>
      simp [dfsVisit] at hblack
      rw [hwhite_v] at hblack
      contradiction
  | succ n ih =>
      let s1 := s.setColor u Color.gray |>.setDiscovery u
      let step := fun (s' : DFSState V) (w : V) =>
        if s'.color w = Color.white then dfsVisit G n w (s'.setParent w u) else s'
      let s2 := List.foldl step s1 (G.adj u).toList
      let s3 := s2.setColor u Color.black |>.setFinish u
      have heq_state : dfsVisit G (n + 1) u s = s3 := by
        simp [s3, s2, s1, step, dfsVisit, hwhite]
      have heq_color : (dfsVisit G (n + 1) u s).color v = s3.color v := by
        rw [heq_state]
      have heq_d : (dfsVisit G (n + 1) u s).d v = s3.d v := by
        rw [heq_state]
      rw [heq_color] at hblack
      have hwhite_v1 : s1.color v = Color.white := by
        simp [s1, hne, hwhite_v]
      have hfold_black : (List.foldl step s1 (G.adj u).toList).color v = Color.black := by
        simp [s3, hne] at hblack
        simpa using hblack
      have hdisc_fold : discoveryTime s2 v ≥ s1.time := by
        have hgen : ∀ (l : List V) (s' : DFSState V),
            s'.color v = Color.white →
            (List.foldl step s' l).color v = Color.black →
            discoveryTime (List.foldl step s' l) v ≥ s'.time := by
          intro l s' hwhite_s' hblack_s'
          induction l generalizing s' with
          | nil =>
              rw [List.foldl_nil] at hblack_s'
              rw [hwhite_s'] at hblack_s'
              contradiction
          | cons w ws ih' =>
              rw [List.foldl_cons] at hblack_s' ⊢
              by_cases hw : s'.color w = Color.white
              · let s_rec := dfsVisit G n w (s'.setParent w u)
                have hstep : step s' w = s_rec := by
                  simp [step, s_rec, hw]
                rw [hstep]
                by_cases hblack_rec : s_rec.color v = Color.black
                · have hn_pos : 0 < n := by
                    by_contra h
                    have : n = 0 := by omega
                    subst n
                    simp [s_rec, dfsVisit] at hblack_rec
                    rw [hwhite_s'] at hblack_rec
                    cases hblack_rec
                  have hdisc_rec : discoveryTime s_rec v ≥ (s'.setParent w u).time := by
                    by_cases hvw : v = w
                    · rw [hvw]
                      rw [dfsVisit_discovery_source G hn_pos (by simpa using hw)]
                    · have h1 := ih (u := w) (s := s'.setParent w u) hn_pos (by simpa using hw) (by simpa [hvw] using hwhite_s') hblack_rec hvw
                      linarith
                  have htime_eq : (s'.setParent w u).time = s'.time := by simp
                  have hdisc_rec' : discoveryTime s_rec v ≥ s'.time := by linarith [hdisc_rec, htime_eq]
                  have hpres : discoveryTime (List.foldl step s_rec ws) v = discoveryTime s_rec v := by
                    have hblack' : s_rec.color v = Color.black := hblack_rec
                    have h4 : (List.foldl step s_rec ws).d v = s_rec.d v :=
                      G.dfsVisit_fold_preserves_d_of_black (s1 := s_rec) (l := ws) hblack'
                    simp [discoveryTime, h4]
                  linarith [hpres, hdisc_rec']
                · have hwhite_rec : s_rec.color v = Color.white := by
                    have hspv : (s'.setParent w u).color v = Color.white := by simpa using hwhite_s'
                    have hng : s_rec.color v ≠ Color.gray := by
                      intro h
                      have := dfsVisit_no_new_gray G v h
                      rw [hspv] at this
                      contradiction
                    cases hcolor : s_rec.color v with
                    | white => rfl
                    | gray => contradiction
                    | black => contradiction
                  rw [hstep] at hblack_s'
                  have htime_ge : s_rec.time ≥ s'.time := by
                    have h1 := G.dfsVisit_time_ge (fuel := n) (u := w) (s := s'.setParent w u)
                    have h2 : (s'.setParent w u).time = s'.time := by simp
                    linarith
                  have hsub : discoveryTime (List.foldl step s_rec ws) v ≥ s_rec.time :=
                    ih' s_rec hwhite_rec hblack_s'
                  linarith [hsub, htime_ge]
              · have hstep : step s' w = s' := by
                  simp [step, hw]
                  all_goals tauto
                rw [hstep]
                rw [hstep] at hblack_s'
                exact ih' s' hwhite_s' hblack_s'
        exact hgen (G.adj u).toList s1 hwhite_v1 hfold_black
      have htime_s1 : s1.time = s.time + 1 := by
        simp [s1]
      have hdisc_top : discoveryTime (dfsVisit G (n + 1) u s) v = discoveryTime s2 v := by
        have h4 : (dfsVisit G (n + 1) u s).d v = s2.d v := by
          rw [heq_d]
          simp [s3]
        simp [discoveryTime, h4]
      linarith [hdisc_fold, htime_s1, hdisc_top]

/-- Every non-white vertex of a DFS state was discovered strictly before the
state's current clock.  This invariant holds for all well-formed intermediate
states produced by DFS. -/
def DiscoveryTimeInvariant (s : DFSState V) : Prop :=
  ∀ v, s.color v ≠ Color.white → discoveryTime s v < s.time

/-- A DFS visit from a white source strictly advances the global clock. -/
theorem dfsVisit_time_gt_of_white {fuel : Nat} {u : V} {s : DFSState V}
    (hfuel : 0 < fuel) (hwhite : s.color u = Color.white) :
    (dfsVisit G fuel u s).time > s.time := by
  cases fuel with
  | zero => linarith
  | succ n =>
      let s1 := s.setColor u Color.gray |>.setDiscovery u
      let s2 := List.foldl (fun (s' : DFSState V) (v : V) =>
          if s'.color v = Color.white then dfsVisit G n v (s'.setParent v u) else s') s1 (G.adj u).toList
      let s3 := s2.setColor u Color.black |>.setFinish u
      have heq : dfsVisit G (n + 1) u s = s3 := by
        simp [dfsVisit, hwhite, s1, s2, s3]
      rw [heq]
      have hs1 : s1.time = s.time + 1 := by simp [s1]
      have hs2 : s2.time ≥ s1.time := G.dfsVisit_fold_time_ge s1
      have hs3 : s3.time = s2.time + 1 := by simp [s3]
      linarith [hs1, hs2, hs3]

/-- A DFS visit from a white source preserves the discovery-time invariant for
all non-white vertices, including intermediate gray vertices on the recursion
stack. -/
theorem dfsVisit_preserves_discoveryTimeInvariant {fuel : Nat} {u : V} {s : DFSState V}
    (hfuel : 0 < fuel) (hwhite : s.color u = Color.white)
    (hdt : DiscoveryTimeInvariant s)
    (hbf : ∀ v, s.color v = Color.black → finishTime s v < s.time)
    (hdf : DiscoveryFinishInvariant s) :
    DiscoveryTimeInvariant (dfsVisit G fuel u s) := by
  intro v hv
  by_cases hgray_out : (dfsVisit G fuel u s).color v = Color.gray
  · -- `v` stays gray; it was already gray in `s`, so its discovery time is
    -- preserved while the clock advanced.
    have hgray_in : s.color v = Color.gray := dfsVisit_no_new_gray G v hgray_out
    have hne : v ≠ u := by
      intro heq
      rw [heq] at hgray_in
      simp [hwhite] at hgray_in
    have hd_eq : discoveryTime (dfsVisit G fuel u s) v = discoveryTime s v := by
      have h2 : (dfsVisit G fuel u s).d v = s.d v :=
        dfsVisit_preserves_d_of_not_white G hne (by simp [hgray_in])
      simp [discoveryTime, h2]
    rw [hd_eq]
    have h1 : discoveryTime s v < s.time := hdt v (by simp [hgray_in])
    have h2 : (dfsVisit G fuel u s).time > s.time :=
      dfsVisit_time_gt_of_white G hfuel hwhite
    linarith
  · -- `v` is not gray; since it is not white either, it is black.
    have hblack : (dfsVisit G fuel u s).color v = Color.black := by
      have h1 : (dfsVisit G fuel u s).color v ≠ Color.white := hv
      have h2 : (dfsVisit G fuel u s).color v ≠ Color.gray := by
        intro h'; simp [h'] at hgray_out
      cases hcolor : (dfsVisit G fuel u s).color v with
      | white => exfalso; exact h1 hcolor
      | gray => exfalso; exact h2 hcolor
      | black => rfl
    by_cases hwhite_v : s.color v = Color.white
    · -- `v` was white and was blackened during the visit
      have hdu : discoveryTime (dfsVisit G fuel u s) v < finishTime (dfsVisit G fuel u s) v := by
        have hdf_out : DiscoveryFinishInvariant (dfsVisit G fuel u s) :=
          dfsVisit_discovery_lt_finish G hfuel hwhite hdf
        exact hdf_out v hblack
      have hft : finishTime (dfsVisit G fuel u s) v < (dfsVisit G fuel u s).time := by
        exact dfsVisit_black_finish_lt_time G hfuel hwhite hbf v hblack
      linarith
    · -- `v` was already non-white in `s`
      have hne : v ≠ u := by
        intro heq
        rw [heq] at hwhite_v
        simp [hwhite] at hwhite_v
      have hd_eq : discoveryTime (dfsVisit G fuel u s) v = discoveryTime s v := by
        have h2 : (dfsVisit G fuel u s).d v = s.d v :=
          dfsVisit_preserves_d_of_not_white G hne (by simp [hwhite_v])
        simp [discoveryTime, h2]
      rw [hd_eq]
      have h1 : discoveryTime s v < s.time := hdt v (by simp [hwhite_v])
      have h2 : (dfsVisit G fuel u s).time > s.time :=
        dfsVisit_time_gt_of_white G hfuel hwhite
      linarith

/-- Recursive DFS over a list preserves the discovery-time invariant. -/
theorem dfsFromList_preserves_discoveryTimeInvariant {fuel : Nat} {s0 : DFSState V} {vs : List V}
    (hfuel : 0 < fuel)
    (hdt : DiscoveryTimeInvariant s0)
    (hbf : ∀ v, s0.color v = Color.black → finishTime s0 v < s0.time)
    (hdf : DiscoveryFinishInvariant s0)
    (hng : ∀ v, s0.color v = Color.white ∨ s0.color v = Color.black)
    (hvs : ∀ v ∈ vs, v ∈ G.vertices) :
    DiscoveryTimeInvariant (dfsFromList G fuel vs s0) := by
  induction vs generalizing s0 with
  | nil => simpa [dfsFromList]
  | cons u us ih =>
      simp [dfsFromList]
      split_ifs with hwhite
      · let s1 := dfsVisit G fuel u s0
        have hdt1 : DiscoveryTimeInvariant s1 :=
          dfsVisit_preserves_discoveryTimeInvariant G hfuel hwhite hdt hbf hdf
        have hbf1 : ∀ v, s1.color v = Color.black → finishTime s1 v < s1.time :=
          dfsVisit_black_finish_lt_time G hfuel hwhite hbf
        have hdf1 : DiscoveryFinishInvariant s1 :=
          dfsVisit_discovery_lt_finish G hfuel hwhite hdf
        have hng1 : ∀ v, s1.color v = Color.white ∨ s1.color v = Color.black :=
          dfsVisit_output_no_gray G hng
        exact ih (s0 := s1) hdt1 hbf1 hdf1 hng1 (fun v hv => hvs v (by simp [hv]))
      · exact ih (s0 := s0) hdt hbf hdf hng (fun v hv => hvs v (by simp [hv]))

section DiscoveryState

/-! ## Existence of the discovery state

For any vertex discovered during a DFS visit, there is a state just before the
recursive call that first discovers it.  This state satisfies the black-vertex
finish-time invariant and has the discovered vertex white. -/

/-- The neighbor-processing fold of a DFS visit preserves the discovery-time,
black-finish, and discovery<finish invariants. -/
theorem dfsVisit_fold_preserves_invariants {n : Nat} {u : V} {s1 : DFSState V} {l : List V}
    (hdt : DiscoveryTimeInvariant s1)
    (hbf : ∀ v, s1.color v = Color.black → finishTime s1 v < s1.time)
    (hdf : DiscoveryFinishInvariant s1) :
    DiscoveryTimeInvariant (List.foldl (fun (s' : DFSState V) (w : V) =>
        if s'.color w = Color.white then dfsVisit G n w (s'.setParent w u) else s') s1 l) ∧
      (∀ v, (List.foldl (fun (s' : DFSState V) (w : V) =>
          if s'.color w = Color.white then dfsVisit G n w (s'.setParent w u) else s') s1 l).color v = Color.black →
        finishTime (List.foldl (fun (s' : DFSState V) (w : V) =>
          if s'.color w = Color.white then dfsVisit G n w (s'.setParent w u) else s') s1 l) v <
        (List.foldl (fun (s' : DFSState V) (w : V) =>
          if s'.color w = Color.white then dfsVisit G n w (s'.setParent w u) else s') s1 l).time) ∧
      DiscoveryFinishInvariant (List.foldl (fun (s' : DFSState V) (w : V) =>
          if s'.color w = Color.white then dfsVisit G n w (s'.setParent w u) else s') s1 l) := by
  induction l generalizing s1 with
  | nil => exact ⟨hdt, hbf, hdf⟩
  | cons w ws ih =>
      simp only [List.foldl_cons]
      split_ifs with hw
      · let s0 := s1.setParent w u
        let s_rec := dfsVisit G n w s0
        have hdt0 : DiscoveryTimeInvariant s0 := by
          intro z hz
          have hz1 : s1.color z ≠ Color.white := by simpa [s0] using hz
          have h1 : discoveryTime s0 z = discoveryTime s1 z := by simp [discoveryTime, s0]
          have h2 : s0.time = s1.time := by simp [s0]
          rw [h1, h2]
          exact hdt z hz1
        have hbf0 : ∀ v, s0.color v = Color.black → finishTime s0 v < s0.time := by
          intro z hz
          have hz1 : s1.color z = Color.black := by simpa [s0] using hz
          have h1 : finishTime s0 z = finishTime s1 z := by simp [finishTime, s0]
          have h2 : s0.time = s1.time := by simp [s0]
          rw [h1, h2]
          exact hbf z hz1
        have hdf0 : DiscoveryFinishInvariant s0 := by
          intro z hz
          have hz1 : s1.color z = Color.black := by simpa [s0] using hz
          have hd : discoveryTime s0 z = discoveryTime s1 z := by simp [discoveryTime, s0]
          have hf : finishTime s0 z = finishTime s1 z := by simp [finishTime, s0]
          rw [hd, hf]
          exact hdf z hz1
        have hdt_rec : DiscoveryTimeInvariant s_rec := by
          by_cases hn0 : n = 0
          · -- n = 0: the recursive call returns s0 unchanged
            have h_eq : s_rec = s0 := by
              simp [s_rec, s0, hn0, dfsVisit]
            rw [h_eq]
            exact hdt0
          · exact dfsVisit_preserves_discoveryTimeInvariant G (by omega) (by simpa [s0] using hw) hdt0 hbf0 hdf0
        have hbf_rec : ∀ v, s_rec.color v = Color.black → finishTime s_rec v < s_rec.time := by
          by_cases hn0 : n = 0
          · -- n = 0: the recursive call returns s0 unchanged
            have h_eq : s_rec = s0 := by
              simp [s_rec, s0, hn0, dfsVisit]
            rw [h_eq]
            exact hbf0
          · exact dfsVisit_black_finish_lt_time G (by omega) (by simpa [s0] using hw) hbf0
        have hdf_rec : DiscoveryFinishInvariant s_rec := by
          by_cases hn0 : n = 0
          · -- n = 0: the recursive call returns s0 unchanged
            have h_eq : s_rec = s0 := by
              simp [s_rec, s0, hn0, dfsVisit]
            rw [h_eq]
            exact hdf0
          · exact dfsVisit_discovery_lt_finish G (by omega) (by simpa [s0] using hw) hdf0
        exact ih hdt_rec hbf_rec hdf_rec
      · exact ih hdt hbf hdf

/-- Variant of {name}`dfsVisit_fold_blackens_loc_prefix` that also guarantees
the accumulator satisfies the discovery-time invariant. -/
theorem dfsVisit_fold_blackens_loc_prefix_full {n : Nat} {u v : V} {s1 : DFSState V}
    (hinv : ∀ v, s1.color v = Color.black → finishTime s1 v < s1.time)
    (hdt : DiscoveryTimeInvariant s1)
    (hdf : DiscoveryFinishInvariant s1)
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
      (∀ z, s2.color z = Color.black → finishTime s2 z < s2.time) ∧
      DiscoveryTimeInvariant s2 := by
  rcases dfsVisit_fold_blackens_loc_prefix G hinv hwhite_v1 hfold_black
    with ⟨pre, post, w, s2, heq, hs2, h2w, h2v, h2b, h2mono, h2inv⟩
  have hdt2 : DiscoveryTimeInvariant s2 := by
    rw [hs2]
    exact (dfsVisit_fold_preserves_invariants G hdt hinv hdf).1
  exact ⟨pre, post, w, s2, heq, hs2, h2w, h2v, h2b, h2mono, h2inv, hdt2⟩

/-- Discovery times of black vertices are preserved by any further `dfsFromList`. -/
theorem dfsFromList_preserves_d_of_black {fuel : Nat} {s0 : DFSState V} {vs : List V}
    (hfuel : 0 < fuel) {x : V}
    (hblack : s0.color x = Color.black) :
    (dfsFromList G fuel vs s0).d x = s0.d x := by
  induction vs generalizing s0 with
  | nil => simp [dfsFromList]
  | cons u us ih =>
      simp [dfsFromList]
      split_ifs with hwhite
      · have hne : x ≠ u := by
          intro h
          rw [h] at hblack
          simp [hblack] at hwhite
        have hblack' : (dfsVisit G fuel u s0).color x = Color.black :=
          dfsVisit_preserves_black G hblack
        have hd : (dfsVisit G fuel u s0).d x = s0.d x := by
          have hnw : s0.color x ≠ Color.white := by simp [hblack]
          exact dfsVisit_preserves_d_of_not_white G hne hnw
        have h1 := ih (s0 := dfsVisit G fuel u s0) hblack'
        rw [h1, hd]
      · exact ih hblack

/-- If a vertex is white at the beginning of a `dfsFromList` prefix and black at
its end, then its discovery time in the final state is at least the initial
clock value. -/
theorem dfsFromList_discovery_ge_of_white {fuel : Nat} {s0 : DFSState V} {vs : List V} {c : V}
    (hfuel : 0 < fuel)
    (hwhite : s0.color c = Color.white)
    (hblack : (dfsFromList G fuel vs s0).color c = Color.black) :
    discoveryTime (dfsFromList G fuel vs s0) c ≥ s0.time := by
  induction vs generalizing s0 with
  | nil =>
      simp [dfsFromList] at hblack
      rw [hwhite] at hblack
      contradiction
  | cons u us ih =>
      simp [dfsFromList] at hblack ⊢
      by_cases hwhite_u : s0.color u = Color.white
      · simp [hwhite_u] at hblack ⊢
        let s1 := dfsVisit G fuel u s0
        by_cases hc : s1.color c = Color.black
        · -- `c` is discovered during the visit from `u`
          have hdisc_s1 : discoveryTime s1 c ≥ s0.time := by
            by_cases hcu : c = u
            · rw [hcu]
              have heq := dfsVisit_discovery_source G hfuel hwhite_u
              simp [s1] at heq ⊢
              linarith
            · have hge : discoveryTime s1 c ≥ s0.time + 1 :=
                dfsVisit_discovery_ge_input_time G hfuel hwhite_u hwhite hc hcu
              linarith
          have hdisc_final : discoveryTime (dfsFromList G fuel us s1) c = discoveryTime s1 c := by
            have h1 : (dfsFromList G fuel us s1).d c = s1.d c :=
              dfsFromList_preserves_d_of_black G hfuel hc
            simp [discoveryTime, h1]
          linarith [hdisc_final, hdisc_s1]
        · -- `c` stays white through the visit from `u`
          have hwhite' : s1.color c = Color.white :=
            dfsVisit_white_stays_white_or_black G hwhite hc
          have h1 := ih (s0 := s1) hwhite' hblack
          have h2 : s1.time ≥ s0.time := G.dfsVisit_time_ge (fuel := fuel) (u := u) (s := s0)
          linarith
      · simp [hwhite_u] at hblack ⊢
        exact ih hwhite hblack

/-- The set of vertices that are white in a DFS state. -/
noncomputable def whiteVertices (s : DFSState V) : Finset V :=
  G.vertices.filter (fun w => s.color w = Color.white)

/-- A non-trivial white-reachable path stays inside the vertex set. -/
theorem whiteReachable_source_mem_vertices {u v : V} {s : DFSState V}
    (hr : WhiteReachable G s u v) (hne : v ≠ u) : u ∈ G.vertices := by
  have h : u = v ∨ u ∈ G.vertices := by
    induction hr using Relation.ReflTransGen.head_induction_on with
    | refl =>
        left
        rfl
    | head h' _ _ =>
        right
        exact G.adj_mem_left h'.1
  cases h with
  | inl h_eq => exfalso; exact hne h_eq.symm
  | inr h_mem => exact h_mem

/-- Inside a `dfsVisit` from a white source `u`, any white-reachable vertex `v`
has a discovery state: a state just before a recursive call on `v` in which `v`
is white, the black-vertex finish-time invariant holds, and every gray vertex
reaches `v` (they are ancestors on the recursion stack). -/
theorem dfsVisit_discovery_state {fuel : Nat} {u v : V} {s : DFSState V}
    (hfuel : 0 < fuel) (hwhite : s.color u = Color.white)
    (hinv : ∀ v, s.color v = Color.black → finishTime s v < s.time)
    (hb : (dfsVisit G fuel u s).color v = Color.black)
    (hw : WhiteReachable G s u v) (hv : s.color v = Color.white)
    (hgray : ∀ w, s.color w = Color.gray → G.Reachable w u) :
    ∃ (s' : DFSState V) (fuel' : Nat),
      s'.color v = Color.white ∧
      (dfsVisit G fuel' v s').color v = Color.black ∧
      (∀ w, s'.color w = Color.black → finishTime s' w < s'.time) ∧
      (∀ w, s'.color w = Color.gray → G.Reachable w v) := by
  by_cases hvu : v = u
  · -- `v` is the source itself; the current state is already the discovery state
    subst v
    exact ⟨s, fuel, hwhite, hb, hinv, hgray⟩
  generalize hk : (whiteVertices G s).card = k
  have hgoal : ∃ (s' : DFSState V) (fuel' : Nat),
      s'.color v = Color.white ∧
      (dfsVisit G fuel' v s').color v = Color.black ∧
      (∀ w, s'.color w = Color.black → finishTime s' w < s'.time) ∧
      (∀ w, s'.color w = Color.gray → G.Reachable w v) := by
    have hP : ∀ (k : Nat) (fuel : Nat) (u v : V) (s : DFSState V),
        (whiteVertices G s).card = k →
        0 < fuel → s.color u = Color.white →
        (∀ v, s.color v = Color.black → finishTime s v < s.time) →
        (dfsVisit G fuel u s).color v = Color.black →
        WhiteReachable G s u v → s.color v = Color.white →
        (∀ w, s.color w = Color.gray → G.Reachable w u) →
        ∃ (s' : DFSState V) (fuel' : Nat),
          s'.color v = Color.white ∧
          (dfsVisit G fuel' v s').color v = Color.black ∧
          (∀ w, s'.color w = Color.black → finishTime s' w < s'.time) ∧
          (∀ w, s'.color w = Color.gray → G.Reachable w v) := by
      intro k
      induction k using Nat.strongRecOn with
      | ind k ih =>
        intro fuel u v s hk hfuel hwhite hinv hb hw hv hgray
        cases fuel with
        | zero => linarith
        | succ n =>
            by_cases h' : v = u
            · -- `v` is the source itself; the current state is already the discovery state
              subst v
              exact ⟨s, n + 1, hwhite, hb, hinv, hgray⟩
            · -- `v` is a proper descendant, so it is blackened inside the fold
              let s1 := s.setColor u Color.gray |>.setDiscovery u
              let step := fun (s' : DFSState V) (w : V) =>
                if s'.color w = Color.white then dfsVisit G n w (s'.setParent w u) else s'
              let s2 := List.foldl step s1 (G.adj u).toList
              let s3 := s2.setColor u Color.black |>.setFinish u
              have heq_state : dfsVisit G (n + 1) u s = s3 := by
                simp [s3, s2, s1, step, dfsVisit, hwhite]
              have hv_s3 : s3.color v = Color.black := by
                rw [← heq_state]
                exact hb
              have hfold_black : s2.color v = Color.black := by
                simp [s3] at hv_s3
                exact hv_s3 h'
              have hwhite_v_s1 : s1.color v = Color.white := by
                simp [s1]
                rw [if_neg h']
                exact hv
              have hinv_s1 : ∀ z, s1.color z = Color.black → finishTime s1 z < s1.time := by
                intro z hz
                have hne_zu : z ≠ u := by
                  intro h
                  subst z
                  simp [s1] at hz
                have h1 : finishTime s1 z = finishTime s z := by
                  simp [finishTime, s1]
                have h2 : s1.time = s.time + 1 := by
                  simp [s1]
                have h3 : finishTime s z < s.time := hinv z (by simpa [s1, hne_zu] using hz)
                rw [h1, h2]
                linarith
              have hloc := dfsVisit_fold_blackens_loc_prefix G hinv_s1 hwhite_v_s1 hfold_black
              rcases hloc with ⟨pre, post, w, s2', heq, hs2, hwhite_w, hwhite_v, hblack_v, hmono, hinv_s2'⟩
              let s_input := s2'.setParent w u
              have hwhite_w_input : s_input.color w = Color.white := by
                simp [s_input, hwhite_w]
              have hwhite_v_input : s_input.color v = Color.white := by
                simp [s_input, hwhite_v]
              have hblack_v_input : (dfsVisit G n w s_input).color v = Color.black := by
                simpa [s_input] using hblack_v
              have hn_pos : 0 < n := by
                by_contra h
                have : n = 0 := by omega
                subst n
                simp [dfsVisit] at hblack_v_input
                rw [hwhite_v_input] at hblack_v_input
                contradiction
              have hwreach : WhiteReachable G s_input w v := by
                apply dfsVisit_blackens_implies_whiteReachable
                · exact hwhite_w_input
                · exact hn_pos
                · exact hwhite_v_input
                · exact hblack_v_input
              have hinv_input : ∀ z, s_input.color z = Color.black → finishTime s_input z < s_input.time := by
                intro z hz
                have hz2 : s2'.color z = Color.black := by
                  simpa [s_input] using hz
                have h1 := hinv_s2' z hz2
                simp [s_input] at h1 ⊢
                exact h1
              have hgray_input : ∀ z, s_input.color z = Color.gray → G.Reachable z w := by
                intro z hz
                have hz2 : s2'.color z = Color.gray := by
                  simpa [s_input] using hz
                have hz1 : s1.color z = Color.gray := by
                  rw [hs2] at hz2
                  exact dfsVisit_fold_no_new_gray G s1 hz2
                have h1 : z = u ∨ s.color z = Color.gray := by
                  by_cases hzu : z = u
                  · left; exact hzu
                  · right
                    simp [s1, hzu] at hz1
                    exact hz1
                rcases h1 with (hzu | hz_gray)
                · subst z
                  have hadj_uw : G.Adj u w := by
                    have hwmem : w ∈ (G.adj u).toList := by
                      rw [heq]
                      simp
                    simp [Finset.mem_toList] at hwmem
                    exact hwmem
                  exact Relation.ReflTransGen.single hadj_uw
                · have hzu : G.Reachable z u := hgray z hz_gray
                  have hadj_uw : G.Adj u w := by
                    have hwmem : w ∈ (G.adj u).toList := by
                      rw [heq]
                      simp
                    simp [Finset.mem_toList] at hwmem
                    exact hwmem
                  exact Relation.ReflTransGen.trans hzu (Relation.ReflTransGen.single hadj_uw)
              have hcard : (whiteVertices G s_input).card < k := by
                have hk' : k = (whiteVertices G s).card := by rw [hk]
                have hsub : whiteVertices G s_input ⊆ whiteVertices G s := by
                  intro x hx
                  simp [whiteVertices] at hx ⊢
                  constructor
                  · exact hx.1
                  · have h1 : s_input.color x = Color.white := hx.2
                    have h2 : s2'.color x = Color.white := by
                      simpa [s_input] using h1
                    have h3 : s2'.color x = Color.white → s1.color x = Color.white := hmono x
                    have h4 : s1.color x = Color.white := h3 h2
                    have hxu : x ≠ u := by
                      intro h
                      subst x
                      have : s_input.color u = Color.white := h1
                      simp [s_input] at this
                      have : s2'.color u = Color.white := by
                        simpa [s_input] using this
                      have : s1.color u = Color.white := hmono u this
                      simp [s1] at this
                    simp [s1, hxu] at h4
                    exact h4
                have hu_notin : u ∉ whiteVertices G s_input := by
                  simp [whiteVertices, s_input]
                  intro hmem hwhite_u
                  have : s2'.color u = Color.white := by
                    simpa [s_input] using hwhite_u
                  have : s1.color u = Color.white := hmono u this
                  simp [s1] at this
                have hu_mem : u ∈ G.vertices := whiteReachable_source_mem_vertices G hw h'
                have hu_in : u ∈ whiteVertices G s := by
                  simp [whiteVertices, hwhite, hu_mem]
                have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => hu_notin (heq ▸ hu_in)⟩)
                linarith
              exact ih (whiteVertices G s_input).card hcard n w v s_input (by rfl) hn_pos hwhite_w_input hinv_input hblack_v_input hwreach hwhite_v_input hgray_input
    exact hP k fuel u v s hk hfuel hwhite hinv hb hw hv hgray
  exact hgoal

/-- Variant of {name}`dfsVisit_discovery_state` that also guarantees the
recursive fuel is large enough to blacken the whole white-reachable set of the
discovered vertex. -/
theorem dfsVisit_discovery_state_with_fuel {fuel : Nat} {u v : V} {s : DFSState V}
    (hfuel : fuel ≥ (whiteReachableSet G s u).card + 1)
    (hwhite : s.color u = Color.white)
    (hinv : ∀ v, s.color v = Color.black → finishTime s v < s.time)
    (hb : (dfsVisit G fuel u s).color v = Color.black)
    (hw : WhiteReachable G s u v) (hv : s.color v = Color.white)
    (hgray : ∀ w, s.color w = Color.gray → G.Reachable w u) :
    ∃ (s' : DFSState V) (fuel' : Nat),
      s'.color v = Color.white ∧
      (dfsVisit G fuel' v s').color v = Color.black ∧
      (∀ w, s'.color w = Color.black → finishTime s' w < s'.time) ∧
      (∀ w, s'.color w = Color.gray → G.Reachable w v) ∧
      fuel' ≥ (whiteReachableSet G s' v).card + 1 := by
  by_cases hvu : v = u
  · -- `v` is the source itself; the current state is already the discovery state
    subst v
    exact ⟨s, fuel, hwhite, hb, hinv, hgray, hfuel⟩
  generalize hk : (whiteVertices G s).card = k
  have hgoal : ∃ (s' : DFSState V) (fuel' : Nat),
      s'.color v = Color.white ∧
      (dfsVisit G fuel' v s').color v = Color.black ∧
      (∀ w, s'.color w = Color.black → finishTime s' w < s'.time) ∧
      (∀ w, s'.color w = Color.gray → G.Reachable w v) ∧
      fuel' ≥ (whiteReachableSet G s' v).card + 1 := by
    have hP : ∀ (k : Nat) (fuel : Nat) (u v : V) (s : DFSState V),
        (whiteVertices G s).card = k →
        fuel ≥ (whiteReachableSet G s u).card + 1 →
        s.color u = Color.white →
        (∀ v, s.color v = Color.black → finishTime s v < s.time) →
        (dfsVisit G fuel u s).color v = Color.black →
        WhiteReachable G s u v → s.color v = Color.white →
        (∀ w, s.color w = Color.gray → G.Reachable w u) →
        ∃ (s' : DFSState V) (fuel' : Nat),
          s'.color v = Color.white ∧
          (dfsVisit G fuel' v s').color v = Color.black ∧
          (∀ w, s'.color w = Color.black → finishTime s' w < s'.time) ∧
          (∀ w, s'.color w = Color.gray → G.Reachable w v) ∧
          fuel' ≥ (whiteReachableSet G s' v).card + 1 := by
      intro k
      induction k using Nat.strongRecOn with
      | ind k ih =>
        intro fuel u v s hk hfuel_bound hwhite hinv hb hw hv hgray
        cases fuel with
        | zero => linarith
        | succ n =>
            by_cases h' : v = u
            · -- `v` is the source itself; the current state is already the discovery state
              subst v
              exact ⟨s, n + 1, hwhite, hb, hinv, hgray, hfuel_bound⟩
            · -- `v` is a proper descendant, so it is blackened inside the fold
              let s1 := s.setColor u Color.gray |>.setDiscovery u
              let step := fun (s' : DFSState V) (w : V) =>
                if s'.color w = Color.white then dfsVisit G n w (s'.setParent w u) else s'
              let s2 := List.foldl step s1 (G.adj u).toList
              let s3 := s2.setColor u Color.black |>.setFinish u
              have heq_state : dfsVisit G (n + 1) u s = s3 := by
                simp [s3, s2, s1, step, dfsVisit, hwhite]
              have hv_s3 : s3.color v = Color.black := by
                rw [← heq_state]
                exact hb
              have hfold_black : s2.color v = Color.black := by
                simp [s3] at hv_s3
                exact hv_s3 h'
              have hwhite_v_s1 : s1.color v = Color.white := by
                simp [s1]
                rw [if_neg h']
                exact hv
              have hinv_s1 : ∀ z, s1.color z = Color.black → finishTime s1 z < s1.time := by
                intro z hz
                have hne_zu : z ≠ u := by
                  intro h
                  subst z
                  simp [s1] at hz
                have h1 : finishTime s1 z = finishTime s z := by
                  simp [finishTime, s1]
                have h2 : s1.time = s.time + 1 := by
                  simp [s1]
                have h3 : finishTime s z < s.time := hinv z (by simpa [s1, hne_zu] using hz)
                rw [h1, h2]
                linarith
              have hloc := dfsVisit_fold_blackens_loc_prefix G hinv_s1 hwhite_v_s1 hfold_black
              rcases hloc with ⟨pre, post, w, s2', heq, hs2, hwhite_w, hwhite_v, hblack_v, hmono, hinv_s2'⟩
              let s_input := s2'.setParent w u
              have hwhite_w_input : s_input.color w = Color.white := by
                simp [s_input, hwhite_w]
              have hwhite_v_input : s_input.color v = Color.white := by
                simp [s_input, hwhite_v]
              have hblack_v_input : (dfsVisit G n w s_input).color v = Color.black := by
                simpa [s_input] using hblack_v
              have hn_pos : 0 < n := by
                by_contra h
                have : n = 0 := by omega
                subst n
                simp [dfsVisit] at hblack_v_input
                rw [hwhite_v_input] at hblack_v_input
                contradiction
              have hwreach : WhiteReachable G s_input w v := by
                apply dfsVisit_blackens_implies_whiteReachable
                · exact hwhite_w_input
                · exact hn_pos
                · exact hwhite_v_input
                · exact hblack_v_input
              have hinv_input : ∀ z, s_input.color z = Color.black → finishTime s_input z < s_input.time := by
                intro z hz
                have hz2 : s2'.color z = Color.black := by
                  simpa [s_input] using hz
                have h1 := hinv_s2' z hz2
                simp [s_input] at h1 ⊢
                exact h1
              have hgray_input : ∀ z, s_input.color z = Color.gray → G.Reachable z w := by
                intro z hz
                have hz2 : s2'.color z = Color.gray := by
                  simpa [s_input] using hz
                have hz1 : s1.color z = Color.gray := by
                  rw [hs2] at hz2
                  exact dfsVisit_fold_no_new_gray G s1 hz2
                have h1 : z = u ∨ s.color z = Color.gray := by
                  by_cases hzu : z = u
                  · left; exact hzu
                  · right
                    simp [s1, hzu] at hz1
                    exact hz1
                rcases h1 with (hzu | hz_gray)
                · subst z
                  have hadj_uw : G.Adj u w := by
                    have hwmem : w ∈ (G.adj u).toList := by
                      rw [heq]
                      simp
                    simp [Finset.mem_toList] at hwmem
                    exact hwmem
                  exact Relation.ReflTransGen.single hadj_uw
                · have hzu : G.Reachable z u := hgray z hz_gray
                  have hadj_uw : G.Adj u w := by
                    have hwmem : w ∈ (G.adj u).toList := by
                      rw [heq]
                      simp
                    simp [Finset.mem_toList] at hwmem
                    exact hwmem
                  exact Relation.ReflTransGen.trans hzu (Relation.ReflTransGen.single hadj_uw)
              have hcard : (whiteVertices G s_input).card < k := by
                have hk' : k = (whiteVertices G s).card := by rw [hk]
                have hsub : whiteVertices G s_input ⊆ whiteVertices G s := by
                  intro x hx
                  simp [whiteVertices] at hx ⊢
                  constructor
                  · exact hx.1
                  · have h1 : s_input.color x = Color.white := hx.2
                    have h2 : s2'.color x = Color.white := by
                      simpa [s_input] using h1
                    have h3 : s2'.color x = Color.white → s1.color x = Color.white := hmono x
                    have h4 : s1.color x = Color.white := h3 h2
                    have hxu : x ≠ u := by
                      intro h
                      subst x
                      have : s_input.color u = Color.white := h1
                      simp [s_input] at this
                      have : s2'.color u = Color.white := by
                        simpa [s_input] using this
                      have : s1.color u = Color.white := hmono u this
                      simp [s1] at this
                    simp [s1, hxu] at h4
                    exact h4
                have hu_notin : u ∉ whiteVertices G s_input := by
                  simp [whiteVertices, s_input]
                  intro hmem hwhite_u
                  have : s2'.color u = Color.white := by
                    simpa [s_input] using hwhite_u
                  have : s1.color u = Color.white := hmono u this
                  simp [s1] at this
                have hu_mem : u ∈ G.vertices := whiteReachable_source_mem_vertices G hw h'
                have hu_in : u ∈ whiteVertices G s := by
                  simp [whiteVertices, hwhite, hu_mem]
                have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => hu_notin (heq ▸ hu_in)⟩)
                linarith
              have hwV : w ∈ G.vertices := by
                have hadj_w : G.Adj u w := by
                  have hwmem : w ∈ (G.adj u).toList := by
                    rw [heq]
                    simp
                  simp [Finset.mem_toList] at hwmem
                  exact hwmem
                exact G.adj_mem_right hadj_w
              have hfuel_input : n ≥ (whiteReachableSet G s_input w).card + 1 := by
                have hsub : whiteReachableSet G s_input w ⊆ whiteReachableSet G s u := by
                  intro x hx
                  have hxw : WhiteReachable G s_input w x := (mem_whiteReachableSet_iff G hwV).mp hx
                  have hxu : WhiteReachable G s u x := by
                    have hwu : WhiteReachable G s u w := by
                      have hadj_uw : G.Adj u w := by
                        have hwmem : w ∈ (G.adj u).toList := by
                          rw [heq]
                          simp
                        simp [Finset.mem_toList] at hwmem
                        exact hwmem
                      have hwhite_w_s : s.color w = Color.white := by
                        have h1 : s1.color w = Color.white := hmono w hwhite_w
                        have hwu : w ≠ u := by
                          intro heq
                          rw [heq] at h1
                          simp [s1] at h1
                        simp [s1, hwu] at h1
                        exact h1
                      exact whiteReachable_step G (whiteReachable_refl G s u) hadj_uw hwhite_w_s
                    have hwx : WhiteReachable G s_input w x := hxw
                    have hwx' : WhiteReachable G s w x := by
                      have hcolors : ∀ x, s_input.color x = Color.white → s.color x = Color.white := by
                        intro x hx
                        have h1 : s2'.color x = Color.white := by
                          have : s_input.color x = Color.white := hx
                          simpa [s_input] using this
                        have h2 : s1.color x = Color.white := hmono x h1
                        have hxu : x ≠ u := by
                          intro heq
                          rw [heq] at h2
                          simp [s1] at h2
                        simp [s1, hxu] at h2
                        exact h2
                      apply whiteReachable_mono_of_color_superset G hcolors hwx
                    exact whiteReachable_trans G hwu hwx'
                  exact (mem_whiteReachableSet_iff G (whiteReachable_source_mem_vertices G hw h')).mpr hxu
                have hne : u ∉ whiteReachableSet G s_input w := by
                  intro hu_in
                  have hwhite_u : WhiteReachable G s_input w u := (mem_whiteReachableSet_iff G hwV).mp hu_in
                  have hcolor_u : s_input.color u = Color.white := whiteReachable_target_white G hwhite_w_input hwhite_u
                  have hs2'_gray_u : s2'.color u = Color.gray := by
                    rw [hs2]
                    let step := fun (s' : DFSState V) (v : V) =>
                      if s'.color v = Color.white then dfsVisit G n v (s'.setParent v u) else s'
                    have hfold : ∀ (pre : List V) (s' : DFSState V),
                        s'.color u = Color.gray →
                        (List.foldl step s' pre).color u = Color.gray := by
                      intro pre s' hs'
                      induction pre generalizing s' with
                      | nil => simpa
                      | cons v vs ih' =>
                          simp [step]
                          by_cases hv : s'.color v = Color.white
                          · simp [hv]
                            apply ih' (dfsVisit G n v (s'.setParent v u))
                            have hsp : (s'.setParent v u).color u = Color.gray := by simp [hs']
                            have hne : u ≠ v := by
                              intro heq
                              rw [← heq] at hv
                              have hcontra : Color.gray = Color.white := by
                                rw [← hs', hv]
                              cases hcontra
                            exact dfsVisit_preserves_gray G hsp hne
                          · simp [hv]
                            exact ih' s' hs'
                    exact hfold pre s1 (by simp [s1])
                  have hgray_u : s_input.color u = Color.gray := by
                    have h1 : s2'.color u = Color.gray := hs2'_gray_u
                    simp [s_input, h1]
                  rw [hgray_u] at hcolor_u
                  exact Color.noConfusion hcolor_u
                have hcard1 : (whiteReachableSet G s_input w).card ≤ (whiteReachableSet G s u).card - 1 := by
                  have hfin : (whiteReachableSet G s_input w).card < (whiteReachableSet G s u).card := by
                    apply Finset.card_lt_card
                    apply Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => hne (heq ▸ by
                      have : u ∈ whiteReachableSet G s u := by
                        apply (mem_whiteReachableSet_iff G (whiteReachable_source_mem_vertices G hw h')).mpr
                        exact whiteReachable_refl G s u
                      exact this)⟩
                  omega
                have hcard2 : (whiteReachableSet G s u).card ≤ n := by
                  omega
                omega
              exact ih (whiteVertices G s_input).card hcard n w v s_input (by rfl) hfuel_input hwhite_w_input hinv_input hblack_v_input hwreach hwhite_v_input hgray_input
    exact hP k fuel u v s hk hfuel hwhite hinv hb hw hv hgray
  exact hgoal

/-- A fuel-aware version of the discovery-state theorem for `dfsFromList`: it
also guarantees that the recursive fuel chosen for the discovered vertex is
large enough to blacken its whole white-reachable set. -/
theorem dfsFromList_discovery_state_with_fuel {fuel : Nat} {s0 : DFSState V} {vs : List V} {v : V}
    (hfuel : fuel ≥ G.vertices.card + 1)
    (hvs : ∀ x ∈ vs, x ∈ G.vertices)
    (hinv0 : ∀ w, s0.color w = Color.black → finishTime s0 w < s0.time)
    (hwhite0 : s0.color v = Color.white)
    (hblack : (dfsFromList G fuel vs s0).color v = Color.black)
    (hng0 : ∀ w, s0.color w = Color.gray → False) :
    ∃ (s' : DFSState V) (fuel' : Nat),
      s'.color v = Color.white ∧
      (dfsVisit G fuel' v s').color v = Color.black ∧
      (∀ w, s'.color w = Color.black → finishTime s' w < s'.time) ∧
      (∀ w, s'.color w = Color.gray → G.Reachable w v) ∧
      fuel' ≥ (whiteReachableSet G s' v).card + 1 := by
  induction vs generalizing s0 with
  | nil =>
      simp [dfsFromList] at hblack
      rw [hwhite0] at hblack
      contradiction
  | cons u us ih =>
      have hfuel_pos : 0 < fuel := by omega
      simp [dfsFromList] at hblack
      by_cases hwhite_u : s0.color u = Color.white
      · simp [hwhite_u] at hblack
        let s1 := dfsVisit G fuel u s0
        by_cases hc : s1.color v = Color.black
        · -- `v` is discovered during the visit from `u`
          have hwr : WhiteReachable G s0 u v := by
            apply dfsVisit_blackens_implies_whiteReachable
            · exact hwhite_u
            · exact hfuel_pos
            · exact hwhite0
            · exact hc
          have hgray_u : ∀ w, s0.color w = Color.gray → G.Reachable w u := by
            intro w hw
            exfalso
            exact hng0 w hw
          have hfuel_visit : fuel ≥ (whiteReachableSet G s0 u).card + 1 := by
            have hsub : whiteReachableSet G s0 u ⊆ G.vertices :=
              whiteReachableSet_subset_vertices G s0 u (hvs u (by simp))
            have hcard : (whiteReachableSet G s0 u).card ≤ G.vertices.card :=
              Finset.card_le_card hsub
            omega
          exact dfsVisit_discovery_state_with_fuel G hfuel_visit hwhite_u hinv0 hc hwr hwhite0 hgray_u
        · -- `v` stays white through the visit from `u`
          have hwhite' : s1.color v = Color.white :=
            dfsVisit_white_stays_white_or_black G hwhite0 hc
          have hinv1 : ∀ w, s1.color w = Color.black → finishTime s1 w < s1.time := by
            apply dfsVisit_black_finish_lt_time G hfuel_pos hwhite_u hinv0
          have hng1 : ∀ w, s1.color w = Color.gray → False := by
            have hno_gray : ∀ w, s1.color w = Color.white ∨ s1.color w = Color.black := by
              apply dfsVisit_output_no_gray
              intro w
              have h : s0.color w = Color.white ∨ s0.color w = Color.black := by
                by_cases hg : s0.color w = Color.gray
                · exfalso; exact hng0 w hg
                · cases hcol : s0.color w with
                  | white => simp
                  | gray => contradiction
                  | black => simp
              cases h <;> simp [*]
            intro w hw
            have := hno_gray w
            simp [hw] at this
          have hvs' : ∀ x ∈ us, x ∈ G.vertices := by
            intro x hx
            exact hvs x (by simp [hx])
          exact ih (s0 := s1) hvs' hinv1 hwhite' hblack hng1
      · simp [hwhite_u] at hblack
        have hvs' : ∀ x ∈ us, x ∈ G.vertices := by
          intro x hx
          exact hvs x (by simp [hx])
        exact ih hvs' hinv0 hwhite0 hblack hng0

end DiscoveryState

theorem IsDFSAncestor.trans {s : DFSState V} {u v w : V}
    (huv : IsDFSAncestor s u v) (hvw : IsDFSAncestor s v w) :
    IsDFSAncestor s u w :=
  Relation.ReflTransGen.trans huv hvw

theorem IsDFSAncestor.single {s : DFSState V} {u v : V}
    (hparent : s.parent v = some u) : IsDFSAncestor s u v :=
  Relation.ReflTransGen.single hparent

/-- A parent edge recorded by any DFS computation is always a graph edge. -/
theorem dfsFromList_preserves_parent_edge {fuel : Nat} {s0 : DFSState V} {vs : List V}
    (hfuel : 0 < fuel)
    (hinv : ∀ u v, s0.parent v = some u → s0.color v ≠ Color.white → G.Adj u v) :
    ∀ u v, (dfsFromList G fuel vs s0).parent v = some u →
      (dfsFromList G fuel vs s0).color v ≠ Color.white → G.Adj u v := by
  sorry

/-- Every DFS ancestor in the full DFS forest is reachable in the graph. -/
theorem IsDFSAncestor_reachable {u v : V}
    (h : IsDFSAncestor (G.dfs) u v) : G.Reachable u v := by
  sorry

end Intervals

section WhitePathTheorem

/-! ## White-path theorem

The white-path theorem characterises DFS descendants by the existence of a
monochromatic (white) path at the moment the ancestor is discovered.
-/

/-- A DFS visit preserves the parent of a vertex that is not white and not the
source. -/
theorem dfsVisit_preserves_parent_of_not_white {fuel : Nat} {u x : V} {s : DFSState V}
    (hne : x ≠ u) (hnw : s.color x ≠ Color.white) :
    (dfsVisit G fuel u s).parent x = s.parent x := by
  induction fuel generalizing u s with
  | zero => simp [dfsVisit]
  | succ n ih =>
      by_cases hwhite : s.color u = Color.white
      · -- u is white: process it and its neighbors
        let s1 := s.setColor u Color.gray |>.setDiscovery u
        let s2 := List.foldl (fun (s' : DFSState V) (w : V) =>
            if s'.color w = Color.white then dfsVisit G n w (s'.setParent w u) else s') s1 (G.adj u).toList
        let s3 := s2.setColor u Color.black |>.setFinish u
        have h_eq : (dfsVisit G (n + 1) u s).parent x = s3.parent x := by
          simp [dfsVisit, hwhite, s1, s2, s3]
        rw [h_eq]
        have h1 : s1.parent x = s.parent x := by simp [s1]
        have h2 : s2.parent x = s1.parent x := by
          have hfold : ∀ (l : List V) (s' : DFSState V),
              s'.parent x = s1.parent x ∧ s'.color x ≠ Color.white →
              (List.foldl (fun (s'' : DFSState V) (w : V) =>
                  if s''.color w = Color.white then dfsVisit G n w (s''.setParent w u) else s'') s' l).parent x = s1.parent x := by
            intro l s' hs'
            induction l generalizing s' with
            | nil => simpa using hs'.1
            | cons w ws ih' =>
                simp
                by_cases hw : s'.color w = Color.white
                · simp [hw]
                  apply ih'
                  constructor
                  · have hne' : x ≠ w := by
                      by_contra h
                      rw [h] at hs'
                      exact hs'.2 hw
                    have hsp : (s'.setParent w u).parent x = s'.parent x := by
                      simp [hne']
                    have hnw' : (s'.setParent w u).color x ≠ Color.white := by simpa using hs'.2
                    have hrec : (dfsVisit G n w (s'.setParent w u)).parent x = (s'.setParent w u).parent x :=
                      ih (u := w) (s := s'.setParent w u) hne' hnw'
                    rw [hrec, hsp]
                    exact hs'.1
                  · have hne' : x ≠ w := by
                      by_contra h
                      rw [h] at hs'
                      exact hs'.2 hw
                    have hnw' : (s'.setParent w u).color x ≠ Color.white := by simpa using hs'.2
                    exact dfsVisit_preserves_not_white (fuel := n) G hne' hnw'
                · simp [hw]
                  exact ih' s' hs'
          have hs1 : s1.parent x = s1.parent x ∧ s1.color x ≠ Color.white := by
            constructor
            · rfl
            · simpa [s1, hne] using hnw
          exact hfold (G.adj u).toList s1 hs1
        have h3 : s3.parent x = s2.parent x := by
          simp [s3]
        rw [h3, h2, h1]
      · -- u is not white: state unchanged
        simp [dfsVisit, hwhite]

/-- The inner fold of a DFS visit preserves the parent of any already-black
vertex. -/
theorem dfsVisit_fold_preserves_parent_of_black {n : Nat} {u x : V} (s1 : DFSState V) {l : List V}
    (hb : s1.color x = Color.black) :
    (List.foldl (fun (s' : DFSState V) (w : V) =>
        if s'.color w = Color.white then dfsVisit G n w (s'.setParent w u) else s') s1 l).parent x = s1.parent x := by
  induction l generalizing s1 with
  | nil => simp
  | cons w ws ih =>
      simp
      by_cases hw : s1.color w = Color.white
      · simp [hw]
        have hne : x ≠ w := by
          intro h
          rw [h] at hb
          simp [hw] at hb
        have hblack' : (s1.setParent w u).color x = Color.black := by simp [hb]
        have hrec_black : (dfsVisit G n w (s1.setParent w u)).color x = Color.black :=
          dfsVisit_preserves_black G hblack'
        have hsp : (s1.setParent w u).parent x = s1.parent x := by
          simp [hne]
        have hrec_parent : (dfsVisit G n w (s1.setParent w u)).parent x = (s1.setParent w u).parent x :=
          dfsVisit_preserves_parent_of_not_white G hne (by rw [hblack']; decide)
        have hfold := ih (dfsVisit G n w (s1.setParent w u)) hrec_black
        rw [hfold, hrec_parent, hsp]
      · simp [hw]
        exact ih s1 hb

/-- Recursive DFS over a list preserves the parent of any already-black
vertex. -/
theorem dfsFromList_preserves_parent_of_black {fuel : Nat} {s0 : DFSState V} {vs : List V} {x : V}
    (hfuel : 0 < fuel)
    (hblack : s0.color x = Color.black) :
    (dfsFromList G fuel vs s0).parent x = s0.parent x := by
  induction vs generalizing s0 with
  | nil => simp [dfsFromList]
  | cons u us ih =>
      simp [dfsFromList]
      split_ifs with hwhite
      · have hne : x ≠ u := by
          intro h
          rw [h] at hblack
          simp [hblack] at hwhite
        have hblack' : (dfsVisit G fuel u s0).color x = Color.black :=
          dfsVisit_preserves_black G hblack
        have hp : (dfsVisit G fuel u s0).parent x = s0.parent x := by
          have hnw : s0.color x ≠ Color.white := by simp [hblack]
          exact dfsVisit_preserves_parent_of_not_white G hne hnw
        have h1 := ih (s0 := dfsVisit G fuel u s0) hblack'
        rw [h1, hp]
      · exact ih hblack

end WhitePathTheorem

section SCCFinishOrdering

/-! ## Finish-time ordering of SCCs

For a full DFS of {lit}`G`, if SCC {lit}`C` has an edge to a different SCC
{lit}`D`, then the maximum finish time in {lit}`C` is strictly larger than the
maximum finish time in {lit}`D`.  This is Lemma 22.14 of CLRS and is the key
property used by Kosaraju's second pass. -/

open Classical in
/-- The maximum finish time of a vertex set {lit}`C` after a full DFS. -/
noncomputable def maxFinish (s : DFSState V) (C : Set V) : Nat :=
  Finset.sup (@Finset.filter V (fun v => v ∈ C) (Classical.decPred (fun v => v ∈ C)) G.vertices)
    (fun v => finishTime s v)

/-- The maximum finish time is attained at some vertex of {lit}`C`. -/
theorem maxFinish_exists {s : DFSState V} {C : Set V} (hC : C.Nonempty) (hsub : C ⊆ G.vertices) :
    ∃ v ∈ C, maxFinish G s C = finishTime s v := by
  rw [maxFinish]
  let sC := @Finset.filter V (fun v => v ∈ C) (Classical.decPred (fun v => v ∈ C)) G.vertices
  have hfin : sC.Nonempty := by
    rcases hC with ⟨v, hvC⟩
    have hvV : v ∈ G.vertices := hsub hvC
    refine ⟨v, ?_⟩
    simp [sC, hvV, hvC]
  rcases Finset.exists_mem_eq_sup sC hfin (fun v => finishTime s v) with ⟨v, hv, heq⟩
  use v
  constructor
  · simp [sC] at hv
    exact hv.2
  · exact heq

/-- If {lit}`v ∈ C` then its finish time is at most the maximum finish time of
{lit}`C`. -/
theorem finish_le_maxFinish {s : DFSState V} {C : Set V} {v : V}
    (hsub : C ⊆ G.vertices) (hv : v ∈ C) : finishTime s v ≤ maxFinish G s C := by
  rw [maxFinish]
  let sC := @Finset.filter V (fun x => x ∈ C) (Classical.decPred (fun x => x ∈ C)) G.vertices
  have hV : v ∈ G.vertices := hsub hv
  have hmem : v ∈ sC := by
    simp [sC, hV, hv]
  exact Finset.le_sup (s := sC) (f := fun x => finishTime s x) hmem

/-! ## First-discovered vertex -/

/-- For a nonempty subset `C` of vertices, there exists a vertex in `C` whose
discovery time is minimal among all vertices in `C`. -/
theorem exists_firstDiscovered {s : DFSState V} {C : Set V}
    (hC : C.Nonempty) (hsub : C ⊆ G.vertices) :
    ∃ r, r ∈ C ∧ ∀ v ∈ C, discoveryTime s r ≤ discoveryTime s v := by
  let sC := @Finset.filter V (fun v => v ∈ C) (Classical.decPred (fun v => v ∈ C)) G.vertices
  have h_sC : sC.Nonempty := by
    rcases hC with ⟨v, hv⟩
    have hvV : v ∈ G.vertices := hsub hv
    refine ⟨v, ?_⟩
    simp [sC, hvV, hv]
  -- Image of discovery times on sC (a nonempty Finset of ℕ)
  let times := Finset.image (fun v => discoveryTime s v) sC
  have h_times : times.Nonempty := by
    rcases h_sC with ⟨v, hv⟩
    exact ⟨discoveryTime s v, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩
  let m := times.min' h_times
  have hm_mem : m ∈ times := Finset.min'_mem times h_times
  rcases Finset.mem_image.mp hm_mem with ⟨r, hr_sC, hm⟩
  have hrC : r ∈ C := by
    simp [sC] at hr_sC; exact hr_sC.2
  refine ⟨r, hrC, ?_⟩
  intro v hv
  have hvV : v ∈ G.vertices := hsub hv
  have hv_sC : v ∈ sC := by
    simp [sC, hvV, hv]
  have : discoveryTime s v ∈ times := Finset.mem_image.mpr ⟨v, hv_sC, rfl⟩
  have hm_le : m ≤ discoveryTime s v := Finset.min'_le times (discoveryTime s v) this
  rw [hm]
  exact hm_le

open Classical in
/-- The vertex in `C` with minimum discovery time.  Requires `C` to be nonempty
and a subset of `G.vertices` so the choice is well-defined. -/
noncomputable def firstDiscoveredVertex (s : DFSState V) (C : Set V)
    (hC : C.Nonempty) (hsub : C ⊆ G.vertices) : V :=
  Classical.choose (exists_firstDiscovered G (s := s) (C := C) hC hsub)

/-- The first-discovered vertex of `C` belongs to `C`. -/
theorem firstDiscoveredVertex_mem {s : DFSState V} {C : Set V}
    (hC : C.Nonempty) (hsub : C ⊆ G.vertices) :
    firstDiscoveredVertex G s C hC hsub ∈ C :=
  (Classical.choose_spec (exists_firstDiscovered G (s := s) (C := C) hC hsub)).1

/-- Every vertex in `C` has discovery time at least that of the first-discovered
vertex. -/
theorem firstDiscoveredVertex_min {s : DFSState V} {C : Set V} {v : V}
    (hC : C.Nonempty) (hsub : C ⊆ G.vertices) (hv : v ∈ C) :
    discoveryTime s (firstDiscoveredVertex G s C hC hsub) ≤ discoveryTime s v :=
  (Classical.choose_spec (exists_firstDiscovered G (s := s) (C := C) hC hsub)).2 v hv

/-! ## Discovery state of a vertex

For the SCC finish-time proof we need access to the *discovery state* of a
vertex `v` — the state just before `dfsVisit` is called with `v` white.  At this
state the clock equals `d[v]` in the final DFS.  The lemma walks through the
`dfsFromList` computation, handling both top-level discovery (outer-loop
`dfsVisit`) and nested discovery (recursive `dfsVisit` inside a fold). -/

/-- For a vertex `v` that is black in `G.dfs`, there exists a state `s` and
fuel `f` such that `s` is the input to the `dfsVisit` call that discovers `v`:
`v` is white in `s`, the call blackens it, and `discoveryTime (G.dfs) v = s.time`.
Moreover, `s` satisfies `DiscoveryTimeInvariant` and the black-finish invariant. -/
theorem exists_discovery_state (v : V) (hv : v ∈ G.vertices) :
    ∃ (s : DFSState V) (f : Nat),
      s.color v = Color.white ∧
      (dfsVisit G f v s).color v = Color.black ∧
      discoveryTime (G.dfs) v = s.time ∧
      (∀ w, s.color w ≠ Color.white → discoveryTime (G.dfs) w < s.time) ∧
      (∀ w, s.color w = Color.black → finishTime s w < s.time) := by
  set n := G.vertices.card + 1 with hn
  have hn_pos : 0 < n := by
    have hcard := Finset.card_pos.mpr ⟨v, hv⟩
    omega
  have h_dfs : G.dfs = dfsFromList G n G.vertices.toList dfsInit := rfl
  -- We walk through the `dfsFromList` computation, carrying three invariants:
  --   (ng) no gray vertices:  ∀ w, s0.color w = Color.white ∨ s0.color w = Color.black
  --   (bf) black-finish:      ∀ w, s0.color w = Color.black → finishTime s0 w < s0.time
  --   (disc) discovery-time:  DiscoveryTimeInvariant (G := G) s0  (not needed directly)
  -- All three hold for `dfsInit` and are preserved by `dfsVisit`.
  have h_ind : ∀ (vs : List V) (s0 : DFSState V),
      (∀ w, s0.color w = Color.white ∨ s0.color w = Color.black) →
      (∀ w, s0.color w = Color.black → finishTime s0 w < s0.time) →
      DiscoveryFinishInvariant s0 →
      (s0.color v = Color.white) →
      ((dfsFromList G n vs s0).color v = Color.black) →
      ∃ (s : DFSState V) (f : Nat),
        s.color v = Color.white ∧
        (dfsVisit G f v s).color v = Color.black ∧
        discoveryTime (dfsFromList G n vs s0) v = s.time ∧
        (∀ w, s.color w ≠ Color.white → discoveryTime (dfsFromList G n vs s0) w < s.time) ∧
        (∀ w, s.color w = Color.black → finishTime s w < s.time) := by
    intro vs s0 h_ng h_bf h_df hwhite_s0 hblack_result
    induction vs generalizing s0 with
    | nil =>
        simp [dfsFromList, hwhite_s0] at hblack_result
    | cons u us ih =>
        simp [dfsFromList] at hblack_result
        by_cases hu_white : s0.color u = Color.white
        · rw [if_pos hu_white] at hblack_result
          set s1 := dfsVisit G n u s0 with hs1
          -- Invariants are preserved through dfsVisit
          have h_ng_s1 : ∀ w, s1.color w = Color.white ∨ s1.color w = Color.black :=
            dfsVisit_output_no_gray (G := G) (fuel := n) (u := u) (s := s0) h_ng
          have h_bf_s1 : ∀ w, s1.color w = Color.black → finishTime s1 w < s1.time :=
            dfsVisit_black_finish_lt_time (G := G) (fuel := n) (u := u) (s := s0) hn_pos hu_white h_bf
          have h_df_s1 : DiscoveryFinishInvariant s1 :=
            dfsVisit_discovery_lt_finish (G := G) (fuel := n) (u := u) (s := s0) hn_pos hu_white h_df
          by_cases hv_white_s1 : s1.color v = Color.white
          · -- v stayed white; continue with the rest
            rcases ih s1 h_ng_s1 h_bf_s1 h_df_s1 hv_white_s1 hblack_result with
              ⟨s, f, hs, hf, hdisc, h_nonwhite_ih, h_bf_s_ih⟩
            have h_nonwhite' : ∀ w, s.color w ≠ Color.white →
                discoveryTime (dfsFromList G n (u :: us) s0) w < s.time := by
              intro w hnw
              have h := h_nonwhite_ih w hnw
              simpa [dfsFromList, hu_white] using h
            refine ⟨s, f, hs, hf, ?_, h_nonwhite', h_bf_s_ih⟩
            dsimp [dfsFromList]; rw [if_pos hu_white]; exact hdisc
          · -- v turned non-white during dfsVisit from u
            by_cases hvu : v = u
            · -- v = u: the accumulator s0 is the discovery state
              subst v
              have h_black_u : s1.color u = Color.black :=
                dfsVisit_blackens_u_pos (G := G) hn_pos hu_white
              have h_disc_src : discoveryTime s1 u = s0.time :=
                dfsVisit_discovery_source G hn_pos hu_white
              -- d[u] is preserved through the rest of dfsFromList
              have hd_preserved : (dfsFromList G n us s1).d u = s1.d u :=
                dfsFromList_preserves_d_of_black G hn_pos (x := u) h_black_u
              -- h_nonwhite for s0: non-white w in s0 → d_final[w] < s0.time
              have h_nonwhite_s0 : ∀ w, s0.color w ≠ Color.white →
                  discoveryTime (dfsFromList G n (u :: us) s0) w < s0.time := by
                intro w hnw
                have h_black_w : s0.color w = Color.black := by
                  rcases h_ng w with (hw | hb)
                  · exact (hnw hw).elim
                  · exact hb
                have hne_wu : w ≠ u := by
                  intro heq; subst w; apply hnw; exact hu_white
                have h_disc_lt_fin : discoveryTime s0 w < finishTime s0 w := h_df w h_black_w
                have h_fin_lt_time : finishTime s0 w < s0.time := h_bf w h_black_w
                -- d-preservation from s0 through dfsVisit u and dfsFromList us
                have h_d_s1_eq : s1.d w = s0.d w :=
                  @dfsVisit_preserves_d_of_not_white V _ G n u w s0 hne_wu hnw
                have h_black_s1 : s1.color w = Color.black :=
                  @dfsVisit_preserves_black V _ G n u w s0 h_black_w
                have h_d_result_eq : (dfsFromList G n us s1).d w = s1.d w :=
                  dfsFromList_preserves_d_of_black G hn_pos (x := w) h_black_s1
                have h_disc_result : discoveryTime (dfsFromList G n us s1) w = discoveryTime s0 w := by
                  dsimp [discoveryTime]; rw [h_d_result_eq, h_d_s1_eq]
                -- Now: discoveryTime (dfsFromList (u::us) s0) w
                --   = discoveryTime (dfsFromList us s1) w (since hu_white)
                --   = discoveryTime s0 w (by h_disc_result)
                --   < finishTime s0 w (by h_disc_lt_fin)
                --   < s0.time (by h_fin_lt_time)
                dsimp [dfsFromList]
                rw [if_pos hu_white, h_disc_result]
                omega
              refine ⟨s0, n, hu_white, h_black_u, ?_, h_nonwhite_s0, h_bf⟩
              dsimp [dfsFromList]
              rw [if_pos hu_white, discoveryTime, hd_preserved, ← discoveryTime]
              exact h_disc_src
            · -- v ≠ u: v discovered inside dfsVisit from u
              have hv_black_s1 : s1.color v = Color.black := by
                rcases h_ng_s1 v with (hw | hb)
                · exact (hv_white_s1 hw).elim
                · exact hb
              -- Name the step function to avoid lambda-matching issues
              let step : DFSState V → V → DFSState V := fun s' x =>
                if s'.color x = Color.white then dfsVisit G (n-1) x (s'.setParent x u) else s'
              -- Use dfsVisit_fold_blackens_loc_prefix to find v in the outer fold
              set s_init := s0.setColor u Color.gray |>.setDiscovery u with hs_init
              have hwhite_v_init : s_init.color v = Color.white := by simp [s_init, hvu, hwhite_s0]
              have h_bf_init : ∀ z, s_init.color z = Color.black →
                  finishTime s_init z < s_init.time := by
                intro z hz
                have hz0 : s0.color z = Color.black := by
                  simp [s_init] at hz
                  by_cases hzu : z = u; · subst z; simp [s_init, hu_white] at hz
                  · simpa [hzu] using hz
                have h_fin : finishTime s_init z = finishTime s0 z := by simp [s_init, finishTime]
                have h_time : s_init.time = s0.time + 1 := by simp [s_init]
                rw [h_fin, h_time]; have h := h_bf z hz0; omega
              have hcolor : (List.foldl step s_init (G.adj u).toList).color v = s1.color v := by
                rw [hs1, dfsVisit, hu_white]
                -- Goal: foldl.color v = (foldl.setColor u black |>.setFinish u).color v
                -- Both setColor and setFinish don't change color for v ≠ u
                have h_simplify : ((List.foldl step s_init (G.adj u).toList).setColor u Color.black |>.setFinish u).color v =
                    (List.foldl step s_init (G.adj u).toList).color v := by
                  simp [hvu]
                apply h_simplify.symm
              have hfold_black : (List.foldl step s_init (G.adj u).toList).color v = Color.black := by
                rw [hcolor, hv_black_s1]
              rcases dfsVisit_fold_blackens_loc_prefix G h_bf_init hwhite_v_init hfold_black
                with ⟨pre, post, w, s2, hadj_eq, hs2_eq, hw_white, hv_white_s2, hw_disc_v, _, _⟩
              by_cases hw_eq_v : w = v
              · -- w = v: v is directly discovered as u's neighbor.
                -- Sub-problem 2: prove s1.d v = some (s2.time)
                subst w
                let s' := s2.setParent v u
                have hs'_white : s'.color v = Color.white := by simp [s', hv_white_s2]
                have hs'_time : s'.time = s2.time := by simp [s']
                have hf'_black : (dfsVisit G (n-1) v s').color v = Color.black := hw_disc_v
                have hfuel' : 0 < n-1 := by
                  have hcard : 1 ≤ G.vertices.card := Finset.card_pos.mpr ⟨v, hv⟩
                  dsimp [n]; omega
                -- Step 1: d[v] in recursive call = some (s2.time)
                have h_rec_d : (dfsVisit G (n-1) v s').d v = some (s2.time) := by
                  rw [← hs'_time]
                  exact dfsVisit_discovery_source_d_eq G hfuel' hs'_white
                -- Step 2: d[v] preserved through rest of outer fold (post)
                have h_fold_d : (List.foldl (fun s' x =>
                    if s'.color x = Color.white then dfsVisit G (n-1) x (s'.setParent x u) else s')
                    (dfsVisit G (n-1) v s') post).d v = (dfsVisit G (n-1) v s').d v :=
                  dfsVisit_fold_preserves_d_of_black G
                    (s1 := dfsVisit G (n-1) v s') (l := post) hf'_black
                -- Step 3: s1.d v = some (s2.time) using the fold decomposition lemma
                have h_s1_d : s1.d v = some (s2.time) := by
                  rw [hs1, dfsVisit, hu_white]
                  -- Goal: (foldl step s_init adj |>.setColor u black |>.setFinish u).d v = some (s2.time)
                  -- setColor/setFinish don't change d[v]
                  simp only [DFSState.setColor_d, DFSState.setFinish_d]
                  -- Goal: (foldl step s_init (G.adj u).toList).d v = some (s2.time)
                  have h_fold_split := dfsVisit_fold_split_at_white_neighbor G
                    s_init pre post s2 hadj_eq hs2_eq hv_white_s2
                  -- From h_fold_split: full_fold = foldl step (dfsVisit ...) post
                  -- Take .d v on both sides, then chain with h_fold_d and h_rec_d
                  calc
                    (List.foldl step s_init (G.adj u).toList).d v
                        = (List.foldl step (dfsVisit G (n-1) v (s2.setParent v u)) post).d v := by
                          simpa using congrArg (fun f => f.d v) h_fold_split
                    _ = (List.foldl step (dfsVisit G (n-1) v s') post).d v := by simp [s']
                    _ = (dfsVisit G (n-1) v s').d v := by rw [h_fold_d]
                    _ = some (s2.time) := h_rec_d
                -- Step 4: d preserved through dfsFromList
                have h_result_d : (dfsFromList G n us s1).d v = s1.d v :=
                  dfsFromList_preserves_d_of_black G hn_pos (x := v) hv_black_s1
                -- h_nonwhite for s' (fold accumulator): follows from fold invariants
                have h_nonwhite_s' : ∀ w, s'.color w ≠ Color.white →
                    discoveryTime (dfsFromList G n (u :: us) s0) w < s'.time := by
                  sorry
                have h_bf_s' : ∀ w, s'.color w = Color.black → finishTime s' w < s'.time := by
                  -- s' = s2.setParent v u.  The fold accumulator s2 satisfies h_bf.
                  -- setParent doesn't change color or time or finishTime.
                  sorry
                refine ⟨s', n-1, hs'_white, hf'_black, ?_, h_nonwhite_s', h_bf_s'⟩
                dsimp [discoveryTime, dfsFromList]
                rw [if_pos hu_white, h_result_d, h_s1_d, hs'_time]; simp
              · -- w ≠ v: v is discovered inside dfsVisit on w.  Use induction on
                -- the white-vertex count (same as dfsVisit_discovery_state).
                sorry
        · -- u not white; skip
          rw [if_neg hu_white] at hblack_result
          rcases ih s0 h_ng h_bf h_df hwhite_s0 hblack_result with
            ⟨s, f, hs, hf, hdisc, h_nonwhite_ih, h_bf_s_ih⟩
          have h_nonwhite' : ∀ w, s.color w ≠ Color.white →
              discoveryTime (dfsFromList G n (u :: us) s0) w < s.time := by
            intro w hnw; have h := h_nonwhite_ih w hnw
            simpa [dfsFromList, hu_white] using h
          refine ⟨s, f, hs, hf, ?_, h_nonwhite', h_bf_s_ih⟩
          dsimp [dfsFromList]; rw [if_neg hu_white]; exact hdisc
  -- Start from dfsInit
  have hwhite_init : (dfsInit (V := V)).color v = Color.white := rfl
  have h_ng_init : ∀ (w : V), (dfsInit (V := V)).color w = Color.white ∨ (dfsInit (V := V)).color w = Color.black :=
    λ (w : V) => Or.inl rfl
  have h_bf_init : ∀ (w : V), (dfsInit (V := V)).color w = Color.black → finishTime (dfsInit (V := V)) w < (dfsInit (V := V)).time := by
    intro w h; dsimp [dfsInit] at h; nomatch h
  have h_df_init : DiscoveryFinishInvariant (dfsInit (V := V)) := by
    intro w h; dsimp [dfsInit] at h; nomatch h
  have hblack_final : (dfsFromList G n G.vertices.toList dfsInit).color v = Color.black := by
    rw [← h_dfs]; exact G.dfs_all_black hv
  rcases h_ind G.vertices.toList dfsInit h_ng_init h_bf_init h_df_init hwhite_init hblack_final with
    ⟨s, f, hs, hf, hdisc, h_nonwhite_s, h_bf_s⟩
  refine ⟨s, f, hs, hf, ?_, ?_, h_bf_s⟩
  · rw [h_dfs]; exact hdisc
  · intro w hnw
    have h := h_nonwhite_s w hnw
    simpa [h_dfs] using h

end SCCFinishOrdering

end Graph
end Chapter22
end CLRS

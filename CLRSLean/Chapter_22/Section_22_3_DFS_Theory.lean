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

end Graph
end Chapter22
end CLRS

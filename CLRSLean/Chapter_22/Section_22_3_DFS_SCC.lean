import Mathlib
import CLRSLean.Chapter_22.Section_22_1_Representing_Graphs
import CLRSLean.Chapter_22.Section_22_3_DFS
import CLRSLean.Chapter_22.Section_22_3_DFS_Intervals

/-! # DFS theory: finish-time ordering of SCCs

This file proves the key lemma connecting DFS timestamps to SCC
finish-time ordering, and provides the discovery-state existence lemma.
-/

namespace CLRS
namespace Chapter22
namespace Graph

variable {V : Type} [DecidableEq V] (G : Graph V)

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
      (∀ w, s.color w = Color.black → finishTime s w < s.time) ∧
      (∀ w, s.color w = Color.white ∨ s.color w = Color.black) ∧
      (∀ w, (dfsVisit G f v s).color w = Color.black →
        finishTime (G.dfs) w = finishTime (dfsVisit G f v s) w) ∧
      (f ≥ (whiteReachableSet G s v).card + 1) := by
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
        (∀ w, s.color w = Color.black → finishTime s w < s.time) ∧
        (∀ w, s.color w = Color.white ∨ s.color w = Color.black) ∧
        (∀ w, (dfsVisit G f v s).color w = Color.black →
          finishTime (dfsFromList G n vs s0) w = finishTime (dfsVisit G f v s) w) ∧
        (f ≥ (whiteReachableSet G s v).card + 1) := by
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
              ⟨s, f, hs, hf, hdisc, h_nonwhite_ih, h_bf_s_ih, h_ng_s_ih, h_f_pres_ih, h_fuel_ih⟩
            have h_nonwhite' : ∀ w, s.color w ≠ Color.white →
                discoveryTime (dfsFromList G n (u :: us) s0) w < s.time := by
              intro w hnw
              have h := h_nonwhite_ih w hnw
              simpa [dfsFromList, hu_white] using h
            have h_f_pres' : ∀ w, (dfsVisit G f v s).color w = Color.black →
                finishTime (dfsFromList G n (u :: us) s0) w = finishTime (dfsVisit G f v s) w := by
              intro w hblack
              have h := h_f_pres_ih w hblack
              simpa [dfsFromList, hu_white] using h
            refine ⟨s, f, hs, hf, ?_, h_nonwhite', h_bf_s_ih, h_ng_s_ih, h_f_pres', h_fuel_ih⟩
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
              have h_f_preserved : ∀ w, s1.color w = Color.black →
                  finishTime (dfsFromList G n (u :: us) s0) w = finishTime s1 w := by
                intro w hblack
                dsimp [dfsFromList]; rw [if_pos hu_white]
                have h := dfsFromList_preserves_f_of_black (G := G) (vs := us) hn_pos (x := w) hblack
                rw [finishTime, finishTime, h]
              have h_fuel_bound : n ≥ (whiteReachableSet G s0 u).card + 1 := by
                have hcard : (whiteReachableSet G s0 u).card ≤ G.vertices.card :=
                  Finset.card_le_card (whiteReachableSet_subset_vertices G s0 u hv)
                dsimp [n]; omega
              refine ⟨s0, n, hu_white, h_black_u, ?_, h_nonwhite_s0, h_bf, h_ng, h_f_preserved, h_fuel_bound⟩
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
                have h_f_pres_s' : ∀ w, (dfsVisit G (n-1) v s').color w = Color.black →
                    finishTime (dfsFromList G n (u :: us) s0) w = finishTime (dfsVisit G (n-1) v s') w := by
                  sorry
                have h_fuel_s' : (n-1) ≥ (whiteReachableSet G s' v).card + 1 := by
                  sorry
                have h_ng_s' : ∀ w, s'.color w = Color.white ∨ s'.color w = Color.black := by
                  sorry
                refine ⟨s', n-1, hs'_white, hf'_black, ?_, h_nonwhite_s', h_bf_s', h_ng_s', h_f_pres_s', h_fuel_s'⟩
                dsimp [discoveryTime, dfsFromList]
                rw [if_pos hu_white, h_result_d, h_s1_d, hs'_time]; simp
              · -- w ≠ v: v is discovered inside dfsVisit on w.  Use induction on
                -- the white-vertex count (same as dfsVisit_discovery_state).
                sorry
        · -- u not white; skip
          rw [if_neg hu_white] at hblack_result
          rcases ih s0 h_ng h_bf h_df hwhite_s0 hblack_result with
            ⟨s, f, hs, hf, hdisc, h_nonwhite_ih, h_bf_s_ih, h_ng_s_ih, h_f_pres_ih, h_fuel_ih⟩
          have h_nonwhite' : ∀ w, s.color w ≠ Color.white →
              discoveryTime (dfsFromList G n (u :: us) s0) w < s.time := by
            intro w hnw; have h := h_nonwhite_ih w hnw
            simpa [dfsFromList, hu_white] using h
          have h_f_pres' : ∀ w, (dfsVisit G f v s).color w = Color.black →
              finishTime (dfsFromList G n (u :: us) s0) w = finishTime (dfsVisit G f v s) w := by
            intro w hblack; have h := h_f_pres_ih w hblack
            simpa [dfsFromList, hu_white] using h
          refine ⟨s, f, hs, hf, ?_, h_nonwhite', h_bf_s_ih, h_ng_s_ih, h_f_pres', h_fuel_ih⟩
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
    ⟨s, f, hs, hf, hdisc, h_nonwhite_s, h_bf_s, h_ng_s, h_f_pres, h_fuel⟩
  refine ⟨s, f, hs, hf, ?_, ?_, h_bf_s, h_ng_s, ?_, h_fuel⟩
  · rw [h_dfs]; exact hdisc
  · intro w hnw
    have h := h_nonwhite_s w hnw
    simpa [h_dfs] using h
  · intro w hblack
    have h := h_f_pres w hblack
    simpa [h_dfs] using h

end SCCFinishOrdering

end Graph
end Chapter22
end CLRS

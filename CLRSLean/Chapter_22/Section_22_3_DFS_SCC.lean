import Mathlib
import CLRSLean.Chapter_22.Section_22_1_Representing_Graphs
import CLRSLean.Chapter_22.Section_22_3_DFS
import CLRSLean.Chapter_22.Section_22_3_DFS_Intervals
import CLRSLean.Chapter_22.Section_22_3_DFS_Bridge

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

/-- If {lit}`c` witnesses the maximum finish time of {lit}`C`, then every member
of {lit}`C` finishes no later than {lit}`c`. -/
theorem finish_le_maxFinish_witness {s : DFSState V} {C : Set V} {r c : V}
    (hsub : C ⊆ G.vertices) (hr : r ∈ C)
    (hc_max : maxFinish G s C = finishTime s c) :
    finishTime s r ≤ finishTime s c := by
  have h := finish_le_maxFinish G (s := s) (C := C) hsub hr
  rw [hc_max] at h
  exact h

/-! ## First-discovered vertex -/

/-- For a nonempty subset {lit}`C` of vertices, there exists a vertex in
{lit}`C` whose discovery time is minimal among all vertices in {lit}`C`. -/
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
/-- The vertex in {lit}`C` with minimum discovery time.  Requires {lit}`C` to
be nonempty and a subset of {lit}`G.vertices` so the choice is well-defined. -/
noncomputable def firstDiscoveredVertex (s : DFSState V) (C : Set V)
    (hC : C.Nonempty) (hsub : C ⊆ G.vertices) : V :=
  Classical.choose (exists_firstDiscovered G (s := s) (C := C) hC hsub)

/-- The first-discovered vertex of {lit}`C` belongs to {lit}`C`. -/
theorem firstDiscoveredVertex_mem {s : DFSState V} {C : Set V}
    (hC : C.Nonempty) (hsub : C ⊆ G.vertices) :
    firstDiscoveredVertex G s C hC hsub ∈ C :=
  (Classical.choose_spec (exists_firstDiscovered G (s := s) (C := C) hC hsub)).1

/-- Every vertex in {lit}`C` has discovery time at least that of the
first-discovered vertex. -/
theorem firstDiscoveredVertex_min {s : DFSState V} {C : Set V} {v : V}
    (hC : C.Nonempty) (hsub : C ⊆ G.vertices) (hv : v ∈ C) :
    discoveryTime s (firstDiscoveredVertex G s C hC hsub) ≤ discoveryTime s v :=
  (Classical.choose_spec (exists_firstDiscovered G (s := s) (C := C) hC hsub)).2 v hv

/-- Bundled membership and minimality facts for {name}`Graph.firstDiscoveredVertex`. -/
theorem firstDiscoveredVertex_mem_min {s : DFSState V} {C : Set V}
    (hC : C.Nonempty) (hsub : C ⊆ G.vertices) :
    let r := firstDiscoveredVertex G s C hC hsub
    r ∈ C ∧ ∀ v ∈ C, discoveryTime s r ≤ discoveryTime s v := by
  intro r
  exact ⟨firstDiscoveredVertex_mem G (s := s) (C := C) hC hsub,
    fun v hv => firstDiscoveredVertex_min G (s := s) (C := C) hC hsub hv⟩

/-! ## Discovery state of a vertex

For the SCC finish-time proof we need access to the *discovery state* of a
vertex {lit}`v`: the state just before {name}`dfsVisit` is called with
{lit}`v` white.  At this state the clock equals {lit}`d[v]` in the final DFS.
The lemma walks through the {name}`dfsFromList` computation, handling both
top-level discovery (outer-loop {name}`dfsVisit`) and nested discovery
(recursive {name}`dfsVisit` inside a fold). -/

/-- For a vertex {lit}`v` that is black in {lit}`G.dfs`, there exists a state
{lit}`s` and fuel {lit}`f` such that {lit}`s` is the input to the
{name}`dfsVisit` call that discovers {lit}`v`: {lit}`v` is white in {lit}`s`,
the call blackens it, and {lit}`discoveryTime (G.dfs) v = s.time`.
Moreover, {lit}`s` satisfies {name}`DiscoveryTimeInvariant` and the
black-finish invariant. -/
theorem exists_discovery_state (v : V) (hv : v ∈ G.vertices) :
    ∃ (s : DFSState V) (f : Nat),
      s.color v = Color.white ∧
      (dfsVisit G f v s).color v = Color.black ∧
      discoveryTime (G.dfs) v = s.time ∧
      (∀ w, s.color w ≠ Color.white → discoveryTime (G.dfs) w < s.time) ∧
      (∀ w, s.color w = Color.black → finishTime s w < s.time) ∧
      (∀ w, s.color w = Color.gray → G.Reachable w v) ∧
      (∀ w, (dfsVisit G f v s).color w = Color.black →
        finishTime (G.dfs) w = finishTime (dfsVisit G f v s) w) ∧
      (f ≥ (whiteReachableSet G s v).card + 1) ∧
      (∀ w, (dfsVisit G f v s).color w = Color.white →
        (G.dfs).color w ≠ Color.white →
        (dfsVisit G f v s).time ≤ discoveryTime (G.dfs) w) := by
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
      DiscoveryTimeInvariant s0 →
      DiscoveryFinishInvariant s0 →
      (s0.color v = Color.white) →
      ((dfsFromList G n vs s0).color v = Color.black) →
      ∃ (s : DFSState V) (f : Nat),
        s.color v = Color.white ∧
        (dfsVisit G f v s).color v = Color.black ∧
        discoveryTime (dfsFromList G n vs s0) v = s.time ∧
        (∀ w, s.color w ≠ Color.white → discoveryTime (dfsFromList G n vs s0) w < s.time) ∧
        (∀ w, s.color w = Color.black → finishTime s w < s.time) ∧
        (∀ w, s.color w = Color.gray → G.Reachable w v) ∧
        (∀ w, (dfsVisit G f v s).color w = Color.black →
          finishTime (dfsFromList G n vs s0) w = finishTime (dfsVisit G f v s) w) ∧
        (f ≥ (whiteReachableSet G s v).card + 1) ∧
        (∀ w, (dfsVisit G f v s).color w = Color.white →
          (dfsFromList G n vs s0).color w ≠ Color.white →
          (dfsVisit G f v s).time ≤ discoveryTime (dfsFromList G n vs s0) w) := by
    intro vs s0 h_ng h_bf hdt h_df hwhite_s0 hblack_result
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
          have hdt_s1 : DiscoveryTimeInvariant s1 :=
            dfsVisit_preserves_discoveryTimeInvariant (G := G) (fuel := n) (u := u) (s := s0)
              hn_pos hu_white hdt h_bf h_df
          have h_df_s1 : DiscoveryFinishInvariant s1 :=
            dfsVisit_discovery_lt_finish (G := G) (fuel := n) (u := u) (s := s0) hn_pos hu_white h_df
          by_cases hv_white_s1 : s1.color v = Color.white
          · -- v stayed white; continue with the rest
            rcases ih s1 h_ng_s1 h_bf_s1 hdt_s1 h_df_s1 hv_white_s1 hblack_result with
              ⟨s, f, hs, hf, hdisc, h_nonwhite_ih, h_bf_s_ih, h_gray_s_ih, h_f_pres_ih, h_fuel_ih, h_later_ih⟩
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
            have h_later' : ∀ w, (dfsVisit G f v s).color w = Color.white →
                (dfsFromList G n (u :: us) s0).color w ≠ Color.white →
                (dfsVisit G f v s).time ≤ discoveryTime (dfsFromList G n (u :: us) s0) w := by
              intro w hw hfinal
              have h := h_later_ih w hw (by simpa [dfsFromList, hu_white] using hfinal)
              simpa [dfsFromList, hu_white] using h
            refine ⟨s, f, hs, hf, ?_, h_nonwhite', h_bf_s_ih, h_gray_s_ih, h_f_pres', h_fuel_ih, h_later'⟩
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
              have h_gray_s0 : ∀ w, s0.color w = Color.gray → G.Reachable w u := by
                intro w hgray
                rcases h_ng w with (hw | hb)
                · rw [hw] at hgray; contradiction
                · rw [hb] at hgray; contradiction
              have h_fuel_bound : n ≥ (whiteReachableSet G s0 u).card + 1 := by
                have hcard : (whiteReachableSet G s0 u).card ≤ G.vertices.card :=
                  Finset.card_le_card (whiteReachableSet_subset_vertices G s0 u hv)
                dsimp [n]; omega
              have h_later_s0 : ∀ w, s1.color w = Color.white →
                  (dfsFromList G n (u :: us) s0).color w ≠ Color.white →
                  s1.time ≤ discoveryTime (dfsFromList G n (u :: us) s0) w := by
                intro w hwhite_w hfinal
                dsimp [dfsFromList] at hfinal ⊢
                rw [if_pos hu_white] at hfinal ⊢
                exact dfsFromList_white_to_nonwhite_disc_ge_time G hn_pos h_bf_s1 hwhite_w hfinal
              refine ⟨s0, n, hu_white, h_black_u, ?_, h_nonwhite_s0, h_bf, h_gray_s0, h_f_preserved, h_fuel_bound, h_later_s0⟩
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
                  by_cases hzu : z = u; · subst z; simp at hz
                  · simpa [hzu] using hz
                have h_fin : finishTime s_init z = finishTime s0 z := by simp [s_init, finishTime]
                have h_time : s_init.time = s0.time + 1 := by simp [s_init]
                rw [h_fin, h_time]; have h := h_bf z hz0; omega
              have hdt_init : DiscoveryTimeInvariant s_init := by
                intro z hnw
                by_cases hzu : z = u
                · subst z
                  simp [s_init, discoveryTime]
                · have hnw0 : s0.color z ≠ Color.white := by
                    simpa [s_init, hzu] using hnw
                  have hblack0 : s0.color z = Color.black := by
                    rcases h_ng z with (hw | hb)
                    · exact False.elim (hnw0 hw)
                    · exact hb
                  have hd_eq : discoveryTime s_init z = discoveryTime s0 z := by
                    simp [s_init, discoveryTime, hzu]
                  have htime : s_init.time = s0.time + 1 := by simp [s_init]
                  have hdisc_lt_fin : discoveryTime s0 z < finishTime s0 z := h_df z hblack0
                  have hfin_lt_time : finishTime s0 z < s0.time := h_bf z hblack0
                  rw [hd_eq, htime]
                  omega
              have hdf_init : DiscoveryFinishInvariant s_init := by
                intro z hblack
                have hzu : z ≠ u := by
                  intro h
                  subst z
                  simp [s_init] at hblack
                have hblack0 : s0.color z = Color.black := by
                  simpa [s_init, hzu] using hblack
                have hd_eq : discoveryTime s_init z = discoveryTime s0 z := by
                  simp [s_init, discoveryTime, hzu]
                have hf_eq : finishTime s_init z = finishTime s0 z := by
                  simp [s_init, finishTime]
                rw [hd_eq, hf_eq]
                exact h_df z hblack0
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
              rcases dfsVisit_fold_blackens_loc_prefix_full G h_bf_init hdt_init hdf_init hwhite_v_init hfold_black
                with ⟨pre, post, w, s2, hadj_eq, hs2_eq, hw_white, hv_white_s2, hw_disc_v, hmono_s2, hbf_s2, hdt_s2⟩
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
                  simp
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
                  intro x hnw
                  have hnw_s2 : s2.color x ≠ Color.white := by
                    simpa [s'] using hnw
                  have hlt_s2 : discoveryTime s2 x < s2.time := hdt_s2 x hnw_s2
                  have hx_ne_v : x ≠ v := by
                    intro hxv
                    subst x
                    exact hnw hs'_white
                  have hd_visit : (dfsVisit G (n - 1) v s').d x = s'.d x :=
                    dfsVisit_preserves_d_of_not_white G hx_ne_v hnw
                  have hnw_visit : (dfsVisit G (n - 1) v s').color x ≠ Color.white :=
                    dfsVisit_preserves_not_white G hx_ne_v hnw
                  have h_full_fold : List.foldl step s_init (G.adj u).toList =
                      List.foldl step (dfsVisit G (n - 1) v s') post := by
                    have h := dfsVisit_fold_split_at_white_neighbor G
                      s_init pre post s2 hadj_eq hs2_eq hv_white_s2
                    simpa [s'] using h
                  have h_post_d : (List.foldl step (dfsVisit G (n - 1) v s') post).d x =
                      (dfsVisit G (n - 1) v s').d x :=
                    dfsVisit_fold_preserves_d_of_not_white G
                      (u := u) (v := x) (s1 := dfsVisit G (n - 1) v s') (l := post) hnw_visit
                  have h_s1_d_x : s1.d x = s2.d x := by
                    rw [hs1, dfsVisit, hu_white]
                    simp
                    calc
                      (List.foldl step s_init (G.adj u).toList).d x
                          = (List.foldl step (dfsVisit G (n - 1) v s') post).d x := by
                            simpa using congrArg (fun st => st.d x) h_full_fold
                      _ = (dfsVisit G (n - 1) v s').d x := h_post_d
                      _ = s'.d x := hd_visit
                      _ = s2.d x := by simp [s']
                  have hnw_s1 : s1.color x ≠ Color.white := by
                    by_cases hxu : x = u
                    · subst x
                      have hblack_u : s1.color u = Color.black := by
                        have h := dfsVisit_blackens_u_pos (G := G) hn_pos hu_white
                        simpa [hs1] using h
                      rw [hblack_u]
                      decide
                    · have hnw_post :
                          (List.foldl step (dfsVisit G (n - 1) v s') post).color x ≠ Color.white :=
                        dfsVisit_fold_preserves_not_white G
                          (u := u) (v := x) (s1 := dfsVisit G (n - 1) v s') (l := post)
                          hxu hnw_visit
                      intro hwhite_s1
                      have hwhite_full : (List.foldl step s_init (G.adj u).toList).color x = Color.white := by
                        rw [hs1, dfsVisit, hu_white] at hwhite_s1
                        simpa [step, s_init, hn, hxu] using hwhite_s1
                      rw [h_full_fold] at hwhite_full
                      exact hnw_post hwhite_full
                  have hblack_s1_x : s1.color x = Color.black := by
                    rcases h_ng_s1 x with (hw | hb)
                    · exact False.elim (hnw_s1 hw)
                    · exact hb
                  have h_final_d : (dfsFromList G n (u :: us) s0).d x = s2.d x := by
                    dsimp [dfsFromList]
                    rw [if_pos hu_white]
                    calc
                      (dfsFromList G n us s1).d x = s1.d x :=
                        dfsFromList_preserves_d_of_black G hn_pos (x := x) hblack_s1_x
                      _ = s2.d x := h_s1_d_x
                  dsimp [discoveryTime] at hlt_s2 ⊢
                  rw [h_final_d]
                  simpa [s'] using hlt_s2
                have h_bf_s' : ∀ w, s'.color w = Color.black → finishTime s' w < s'.time := by
                  intro w hblack
                  have hblack_s2 : s2.color w = Color.black := by
                    simpa [s'] using hblack
                  have h_lt : finishTime s2 w < s2.time := hbf_s2 w hblack_s2
                  simpa [s', finishTime] using h_lt
                have hs2_gray_u : s2.color u = Color.gray := by
                  rw [hs2_eq]
                  have hfold : ∀ (l : List V) (t : DFSState V),
                      t.color u = Color.gray →
                      (List.foldl step t l).color u = Color.gray := by
                    intro l
                    induction l with
                    | nil =>
                        intro t ht
                        simpa using ht
                    | cons x xs ihxs =>
                        intro t ht
                        simp [step]
                        by_cases hx : t.color x = Color.white
                        · simp [hx]
                          apply ihxs
                          have hsp : (t.setParent x u).color u = Color.gray := by
                            simp [ht]
                          have hne : u ≠ x := by
                            intro hux
                            subst x
                            rw [ht] at hx
                            contradiction
                          exact dfsVisit_preserves_gray G hsp hne
                        · simp [hx]
                          exact ihxs t ht
                  exact hfold pre s_init (by simp [s_init])
                have hs'_u_gray : s'.color u = Color.gray := by
                  simp [s', hs2_gray_u]
                have h_f_pres_s' : ∀ w, (dfsVisit G (n-1) v s').color w = Color.black →
                    finishTime (dfsFromList G n (u :: us) s0) w = finishTime (dfsVisit G (n-1) v s') w := by
                  intro w hblack_w
                  dsimp [dfsFromList]; rw [if_pos hu_white]
                  -- Goal: finishTime (dfsFromList G n us s1) w = finishTime (dfsVisit ... v s') w
                  -- Step 1: through dfsFromList us (w black in s1 → f preserved)
                  have hblack_s1 : s1.color w = Color.black := by
                    have h_full_fold : List.foldl step s_init (G.adj u).toList =
                        List.foldl step (dfsVisit G (n - 1) v s') post := by
                      have h := dfsVisit_fold_split_at_white_neighbor G
                        s_init pre post s2 hadj_eq hs2_eq hv_white_s2
                      simpa [s'] using h
                    have hpost_black :
                        (List.foldl step (dfsVisit G (n - 1) v s') post).color w = Color.black :=
                      dfsVisit_fold_preserves_black G
                        (u := u) (x := w) (s1 := dfsVisit G (n - 1) v s') (l := post) hblack_w
                    rw [hs1, dfsVisit, hu_white]
                    by_cases hwu : w = u
                    · subst w
                      simp
                    · have hfull_black : (List.foldl step s_init (G.adj u).toList).color w = Color.black := by
                        rw [h_full_fold]
                        exact hpost_black
                      simpa [hwu, hfull_black]
                  have h_f1 : finishTime (dfsFromList G n us s1) w = finishTime s1 w := by
                    have h := dfsFromList_preserves_f_of_black (G := G) (vs := us) hn_pos (x := w) hblack_s1
                    rw [finishTime, finishTime, h]
                  -- Step 2: s1.w = ... = s_rec.w (through outer fold and setFinish)
                  -- s1 = s_fold.setColor u black |>.setFinish u
                  -- where s_fold = foldl step s_init (G.adj u).toList
                  -- Using the fold decomposition: s_fold's f[w] = s_rec's f[w] (by fold f-preservation)
                  have h_f2 : finishTime s1 w = finishTime (dfsVisit G (n-1) v s') w := by
                    have hwu : w ≠ u := by
                      intro h
                      subst w
                      have hu_gray_out : (dfsVisit G (n - 1) v s').color u = Color.gray := by
                        have huv : u ≠ v := by
                          intro huv
                          exact hvu huv.symm
                        exact dfsVisit_preserves_gray G hs'_u_gray huv
                      rw [hu_gray_out] at hblack_w
                      contradiction
                    have h_full_fold : List.foldl step s_init (G.adj u).toList =
                        List.foldl step (dfsVisit G (n - 1) v s') post := by
                      have h := dfsVisit_fold_split_at_white_neighbor G
                        s_init pre post s2 hadj_eq hs2_eq hv_white_s2
                      simpa [s'] using h
                    have hpost_f : (List.foldl step (dfsVisit G (n - 1) v s') post).f w =
                        (dfsVisit G (n - 1) v s').f w :=
                      dfsVisit_fold_preserves_f_of_black G
                        (u := u) (v := w) (s1 := dfsVisit G (n - 1) v s') (l := post) hblack_w
                    have hs1_f_full : s1.f w = (List.foldl step s_init (G.adj u).toList).f w := by
                      rw [hs1, dfsVisit, hu_white]
                      simp [step, s_init, hn, hwu]
                    have hs1_f : s1.f w =
                        (List.foldl step (dfsVisit G (n - 1) v s') post).f w := by
                      rw [hs1_f_full, h_full_fold]
                    rw [finishTime, finishTime, hs1_f, hpost_f]
                  rw [h_f1, h_f2]
                have h_fuel_s' : (n-1) ≥ (whiteReachableSet G s' v).card + 1 := by
                  have hnot_u : u ∉ whiteReachableSet G s' v := by
                    intro huin
                    have hwr : WhiteReachable G s' v u :=
                      (mem_whiteReachableSet_iff G hv).mp huin
                    have hu_white : s'.color u = Color.white :=
                      whiteReachable_target_white G hs'_white hwr
                    rw [hs'_u_gray] at hu_white
                    contradiction
                  have hsub_vertices : whiteReachableSet G s' v ⊆ G.vertices :=
                    whiteReachableSet_subset_vertices G s' v hv
                  have hu_vertices : u ∈ G.vertices := by
                    have hv_mem : v ∈ (G.adj u).toList := by
                      rw [hadj_eq]
                      simp
                    have hadj_uv : G.Adj u v := by
                      simpa [Graph.Adj, Finset.mem_toList] using hv_mem
                    exact G.adj_mem_left hadj_uv
                  have hcard_le : (whiteReachableSet G s' v).card ≤ (G.vertices.erase u).card := by
                    apply Finset.card_le_card
                    intro x hx
                    have hxV : x ∈ G.vertices := hsub_vertices hx
                    have hxu : x ≠ u := by
                      intro h
                      subst x
                      exact hnot_u hx
                    simp [hxV, hxu]
                  have herase : (G.vertices.erase u).card = G.vertices.card - 1 :=
                    Finset.card_erase_of_mem hu_vertices
                  dsimp [n]
                  omega
                have h_gray_s' : ∀ w, s'.color w = Color.gray → G.Reachable w v := by
                  intro z hz
                  have hz2 : s2.color z = Color.gray := by
                    simpa [s'] using hz
                  have hz_init : s_init.color z = Color.gray := by
                    rw [hs2_eq] at hz2
                    exact dfsVisit_fold_no_new_gray G s_init hz2
                  have hzu : z = u := by
                    by_cases hzu : z = u
                    · exact hzu
                    · have hz0 : s0.color z = Color.gray := by
                        simp [s_init, hzu] at hz_init
                        exact hz_init
                      rcases h_ng z with (hw | hb)
                      · rw [hw] at hz0; contradiction
                      · rw [hb] at hz0; contradiction
                  subst z
                  have hadj_uv : G.Adj u v := by
                    have hv_mem : v ∈ (G.adj u).toList := by
                      rw [hadj_eq]
                      simp
                    simpa [Graph.Adj, Finset.mem_toList] using hv_mem
                  exact Relation.ReflTransGen.single hadj_uv
                have h_later_s' : ∀ w, (dfsVisit G (n - 1) v s').color w = Color.white →
                    (dfsFromList G n (u :: us) s0).color w ≠ Color.white →
                    (dfsVisit G (n - 1) v s').time ≤
                      discoveryTime (dfsFromList G n (u :: us) s0) w := by
                  intro x hwhite_rec hfinal
                  dsimp [dfsFromList] at hfinal ⊢
                  rw [if_pos hu_white] at hfinal ⊢
                  have h_full_fold : List.foldl step s_init (G.adj u).toList =
                      List.foldl step (dfsVisit G (n - 1) v s') post := by
                    have h := dfsVisit_fold_split_at_white_neighbor G
                      s_init pre post s2 hadj_eq hs2_eq hv_white_s2
                    simpa [s'] using h
                  have h_full_fold_time :
                      (List.foldl (fun s' x =>
                        if s'.color x = Color.white then dfsVisit G G.vertices.card x (s'.setParent x u) else s')
                        ((s0.setColor u Color.gray).setDiscovery u) (G.adj u).toList).time =
                        (List.foldl step (dfsVisit G (n - 1) v s') post).time := by
                    simpa [step, s_init, hn] using congrArg (fun st => st.time) h_full_fold
                  have htime_to_s1 : (dfsVisit G (n - 1) v s').time ≤ s1.time := by
                    have htime_post : (dfsVisit G (n - 1) v s').time ≤
                        (List.foldl step (dfsVisit G (n - 1) v s') post).time := by
                      simpa using dfsVisit_fold_time_ge G
                        (u := u) (s1 := dfsVisit G (n - 1) v s') (l := post)
                    have htime_s1 : s1.time =
                        (List.foldl step (dfsVisit G (n - 1) v s') post).time + 1 := by
                      rw [hs1, dfsVisit, hu_white]
                      simp [h_full_fold_time]
                    omega
                  by_cases hwhite_s1_x : s1.color x = Color.white
                  · have h_disc_ge :=
                      dfsFromList_white_to_nonwhite_disc_ge_time G hn_pos h_bf_s1 hwhite_s1_x hfinal
                    exact le_trans htime_to_s1 h_disc_ge
                  · have hxu : x ≠ u := by
                      intro h
                      subst x
                      have huv : u ≠ v := by
                        intro huv
                        exact hvu huv.symm
                      have hu_gray_rec : (dfsVisit G (n - 1) v s').color u = Color.gray :=
                        dfsVisit_preserves_gray G hs'_u_gray huv
                      rw [hu_gray_rec] at hwhite_rec
                      contradiction
                    have h_s1_color : s1.color x =
                        (List.foldl step (dfsVisit G (n - 1) v s') post).color x := by
                      have h_full_fold_color :
                          (List.foldl (fun s' y =>
                            if s'.color y = Color.white then dfsVisit G G.vertices.card y (s'.setParent y u) else s')
                            ((s0.setColor u Color.gray).setDiscovery u) (G.adj u).toList).color x =
                            (List.foldl step (dfsVisit G (n - 1) v s') post).color x := by
                        simpa [step, s_init, hn] using congrArg (fun st => st.color x) h_full_fold
                      rw [hs1, dfsVisit, hu_white]
                      simp [hxu, h_full_fold_color]
                    have h_nonwhite_post :
                        (List.foldl step (dfsVisit G (n - 1) v s') post).color x ≠ Color.white := by
                      intro hpost
                      apply hwhite_s1_x
                      rw [h_s1_color, hpost]
                    have h_bf_rec : ∀ z, (dfsVisit G (n - 1) v s').color z = Color.black →
                        finishTime (dfsVisit G (n - 1) v s') z <
                          (dfsVisit G (n - 1) v s').time :=
                      dfsVisit_black_finish_lt_time G hfuel' hs'_white h_bf_s'
                    have h_disc_ge_post :
                        (dfsVisit G (n - 1) v s').time ≤
                          discoveryTime (List.foldl step (dfsVisit G (n - 1) v s') post) x :=
                      dfsVisit_fold_white_to_nonwhite_disc_ge_time G hfuel' h_bf_rec hwhite_rec h_nonwhite_post
                    have h_s1_d : s1.d x =
                        (List.foldl step (dfsVisit G (n - 1) v s') post).d x := by
                      have h_full_fold_d :
                          (List.foldl (fun s' y =>
                            if s'.color y = Color.white then dfsVisit G G.vertices.card y (s'.setParent y u) else s')
                            ((s0.setColor u Color.gray).setDiscovery u) (G.adj u).toList).d x =
                            (List.foldl step (dfsVisit G (n - 1) v s') post).d x := by
                        simpa [step, s_init, hn] using congrArg (fun st => st.d x) h_full_fold
                      rw [hs1, dfsVisit, hu_white]
                      simp [h_full_fold_d]
                    have hblack_s1_x : s1.color x = Color.black := by
                      rcases h_ng_s1 x with (hw | hb)
                      · exact False.elim (hwhite_s1_x hw)
                      · exact hb
                    have h_final_d : (dfsFromList G n us s1).d x = s1.d x :=
                      dfsFromList_preserves_d_of_black G hn_pos (x := x) hblack_s1_x
                    dsimp [discoveryTime] at h_disc_ge_post ⊢
                    rw [h_final_d, h_s1_d]
                    exact h_disc_ge_post
                refine ⟨s', n-1, hs'_white, hf'_black, ?_, h_nonwhite_s', h_bf_s', h_gray_s', h_f_pres_s', h_fuel_s', h_later_s'⟩
                dsimp [discoveryTime, dfsFromList]
                rw [if_pos hu_white, h_result_d, h_s1_d, hs'_time]; simp
              · -- w ≠ v: v is discovered inside dfsVisit on w.  Use induction on
                -- the white-vertex count (same as dfsVisit_discovery_state).
                let s_input := s2.setParent w u
                have hwhite_w_input : s_input.color w = Color.white := by
                  simp [s_input, hw_white]
                have hwhite_v_input : s_input.color v = Color.white := by
                  simp [s_input, hv_white_s2]
                have hblack_v_input : (dfsVisit G (n - 1) w s_input).color v = Color.black := by
                  simpa [s_input] using hw_disc_v
                have hfuel_rec_pos : 0 < n - 1 := by
                  have hcard : 1 ≤ G.vertices.card := Finset.card_pos.mpr ⟨v, hv⟩
                  dsimp [n]
                  omega
                have hadj_uw : G.Adj u w := by
                  have hw_mem : w ∈ (G.adj u).toList := by
                    rw [hadj_eq]
                    simp
                  simpa [Graph.Adj, Finset.mem_toList] using hw_mem
                have hu_vertices : u ∈ G.vertices := G.adj_mem_left hadj_uw
                have hw_vertices : w ∈ G.vertices := G.adj_mem_right hadj_uw
                have hs2_gray_u : s2.color u = Color.gray := by
                  rw [hs2_eq]
                  have hfold : ∀ (l : List V) (t : DFSState V),
                      t.color u = Color.gray →
                      (List.foldl step t l).color u = Color.gray := by
                    intro l
                    induction l with
                    | nil =>
                        intro t ht
                        simpa using ht
                    | cons x xs ihxs =>
                        intro t ht
                        simp [step]
                        by_cases hx : t.color x = Color.white
                        · simp [hx]
                          apply ihxs
                          have hsp : (t.setParent x u).color u = Color.gray := by
                            simp [ht]
                          have hne : u ≠ x := by
                            intro hux
                            subst x
                            rw [ht] at hx
                            contradiction
                          exact dfsVisit_preserves_gray G hsp hne
                        · simp [hx]
                          exact ihxs t ht
                  exact hfold pre s_init (by simp [s_init])
                have hinput_u_gray : s_input.color u = Color.gray := by
                  simp [s_input, hs2_gray_u]
                have huw : u ≠ w := by
                  intro h
                  subst w
                  rw [hs2_gray_u] at hw_white
                  contradiction
                have h_fuel_input : (n - 1) ≥ (whiteReachableSet G s_input w).card + 1 := by
                  have hnot_u : u ∉ whiteReachableSet G s_input w := by
                    intro huin
                    have hwr : WhiteReachable G s_input w u :=
                      (mem_whiteReachableSet_iff G hw_vertices).mp huin
                    have hu_white : s_input.color u = Color.white :=
                      whiteReachable_target_white G hwhite_w_input hwr
                    rw [hinput_u_gray] at hu_white
                    contradiction
                  have hsub_vertices : whiteReachableSet G s_input w ⊆ G.vertices :=
                    whiteReachableSet_subset_vertices G s_input w hw_vertices
                  have hcard_le : (whiteReachableSet G s_input w).card ≤ (G.vertices.erase u).card := by
                    apply Finset.card_le_card
                    intro x hx
                    have hxV : x ∈ G.vertices := hsub_vertices hx
                    have hxu : x ≠ u := by
                      intro h
                      subst x
                      exact hnot_u hx
                    simp [hxV, hxu]
                  have herase : (G.vertices.erase u).card = G.vertices.card - 1 :=
                    Finset.card_erase_of_mem hu_vertices
                  dsimp [n]
                  omega
                have hdt_input : DiscoveryTimeInvariant s_input := by
                  intro z hnw
                  have hnw2 : s2.color z ≠ Color.white := by
                    simpa [s_input] using hnw
                  have hlt := hdt_s2 z hnw2
                  simpa [s_input, discoveryTime] using hlt
                have hdf_s2 : DiscoveryFinishInvariant s2 := by
                  rw [hs2_eq]
                  exact dfsVisit_fold_preserves_discoveryFinishInvariant (G := G) (n := n - 1)
                    (u := u) (s1 := s_init) (l := pre) hdt_init h_bf_init hdf_init
                have hdf_input : DiscoveryFinishInvariant s_input := by
                  intro z hblack
                  have hblack2 : s2.color z = Color.black := by
                    simpa [s_input] using hblack
                  have h := hdf_s2 z hblack2
                  simpa [s_input, discoveryTime, finishTime] using h
                have h_bf_input : ∀ z, s_input.color z = Color.black → finishTime s_input z < s_input.time := by
                  intro z hblack
                  have hblack2 : s2.color z = Color.black := by
                    simpa [s_input] using hblack
                  have h := hbf_s2 z hblack2
                  simpa [s_input, finishTime] using h
                have hgray_input : ∀ z, s_input.color z = Color.gray → G.Reachable z w := by
                  intro z hz
                  have hz2 : s2.color z = Color.gray := by
                    simpa [s_input] using hz
                  have hz_init : s_init.color z = Color.gray := by
                    rw [hs2_eq] at hz2
                    exact dfsVisit_fold_no_new_gray G s_init hz2
                  have hzu : z = u := by
                    by_cases hzu : z = u
                    · exact hzu
                    · have hz0 : s0.color z = Color.gray := by
                        simp [s_init, hzu] at hz_init
                        exact hz_init
                      rcases h_ng z with (hw0 | hb0)
                      · rw [hw0] at hz0; contradiction
                      · rw [hb0] at hz0; contradiction
                  subst z
                  exact Relation.ReflTransGen.single hadj_uw
                have hwreach : WhiteReachable G s_input w v :=
                  dfsVisit_blackens_implies_whiteReachable G hwhite_w_input hfuel_rec_pos
                    hwhite_v_input hblack_v_input
                rcases dfsVisit_discovery_bridge G h_fuel_input hwhite_w_input
                    hdt_input h_bf_input hdf_input hblack_v_input hwreach hwhite_v_input hgray_input with
                  ⟨s_rec, f_rec, hs_rec_white, hf_rec_black, hdisc_rec, h_nonwhite_rec,
                    h_bf_rec_state, h_gray_rec, h_nonwhite_pres_rec, h_f_pres_rec,
                    h_fuel_rec, h_later_rec⟩
                have h_full_fold : List.foldl step s_init (G.adj u).toList =
                    List.foldl step (dfsVisit G (n - 1) w s_input) post := by
                  have h := dfsVisit_fold_split_at_white_neighbor G
                    s_init pre post s2 hadj_eq hs2_eq hw_white
                  simpa [s_input] using h
                have h_s1_d_of_rec_not_white : ∀ x,
                    (dfsVisit G (n - 1) w s_input).color x ≠ Color.white →
                    s1.d x = (dfsVisit G (n - 1) w s_input).d x := by
                  intro x hnw_rec
                  have h_post_d : (List.foldl step (dfsVisit G (n - 1) w s_input) post).d x =
                      (dfsVisit G (n - 1) w s_input).d x :=
                    dfsVisit_fold_preserves_d_of_not_white G
                      (u := u) (v := x) (s1 := dfsVisit G (n - 1) w s_input) (l := post) hnw_rec
                  rw [hs1, dfsVisit, hu_white]
                  simp
                  calc
                    (List.foldl step s_init (G.adj u).toList).d x
                        = (List.foldl step (dfsVisit G (n - 1) w s_input) post).d x := by
                          simpa using congrArg (fun st => st.d x) h_full_fold
                    _ = (dfsVisit G (n - 1) w s_input).d x := h_post_d
                have h_s1_nonwhite_of_rec : ∀ x,
                    (dfsVisit G (n - 1) w s_input).color x ≠ Color.white →
                    s1.color x ≠ Color.white := by
                  intro x hnw_rec
                  rw [hs1, dfsVisit, hu_white]
                  by_cases hxu : x = u
                  · subst x
                    simp
                  · have hpost_nw :
                        (List.foldl step (dfsVisit G (n - 1) w s_input) post).color x ≠ Color.white :=
                      dfsVisit_fold_preserves_not_white G
                        (u := u) (v := x) (s1 := dfsVisit G (n - 1) w s_input) (l := post)
                        hxu hnw_rec
                    have h_full_fold_color :
                        (List.foldl (fun s' y =>
                          if s'.color y = Color.white then dfsVisit G G.vertices.card y (s'.setParent y u) else s')
                          ((s0.setColor u Color.gray).setDiscovery u) (G.adj u).toList).color x =
                          (List.foldl step (dfsVisit G (n - 1) w s_input) post).color x := by
                      simpa [step, s_init, hn] using congrArg (fun st => st.color x) h_full_fold
                    simpa [hxu, h_full_fold_color] using hpost_nw
                have h_s1_f_of_rec_black : ∀ x,
                    (dfsVisit G (n - 1) w s_input).color x = Color.black →
                    finishTime s1 x = finishTime (dfsVisit G (n - 1) w s_input) x := by
                  intro x hblack_rec
                  have hxu : x ≠ u := by
                    intro h
                    subst x
                    have hrec_u_gray : (dfsVisit G (n - 1) w s_input).color u = Color.gray :=
                      dfsVisit_preserves_gray G hinput_u_gray huw
                    rw [hrec_u_gray] at hblack_rec
                    contradiction
                  have hpost_f : (List.foldl step (dfsVisit G (n - 1) w s_input) post).f x =
                      (dfsVisit G (n - 1) w s_input).f x :=
                    dfsVisit_fold_preserves_f_of_black G
                      (u := u) (v := x) (s1 := dfsVisit G (n - 1) w s_input) (l := post) hblack_rec
                  have h_full_fold_f :
                      (List.foldl (fun s' y =>
                        if s'.color y = Color.white then dfsVisit G G.vertices.card y (s'.setParent y u) else s')
                        ((s0.setColor u Color.gray).setDiscovery u) (G.adj u).toList).f x =
                        (List.foldl step (dfsVisit G (n - 1) w s_input) post).f x := by
                    simpa [step, s_init, hn] using congrArg (fun st => st.f x) h_full_fold
                  rw [hs1, dfsVisit, hu_white]
                  simp [finishTime, hxu, h_full_fold_f, hpost_f]
                have h_sub_time_le_rec : (dfsVisit G f_rec v s_rec).time ≤
                    (dfsVisit G (n - 1) w s_input).time := by
                  have hf_rec_pos : 0 < f_rec := by
                    omega
                  have hfinish_src :
                      finishTime (dfsVisit G f_rec v s_rec) v =
                        (dfsVisit G f_rec v s_rec).time - 1 :=
                    dfsVisit_finishTime_source_eq_pred_time G hf_rec_pos hs_rec_white
                  have hlocal_v := h_f_pres_rec v hf_rec_black
                  have hfinish_lt :
                      finishTime (dfsVisit G (n - 1) w s_input) v <
                        (dfsVisit G (n - 1) w s_input).time :=
                    dfsVisit_black_finish_lt_time G hfuel_rec_pos hwhite_w_input h_bf_input
                      v hlocal_v.1
                  rw [hlocal_v.2, hfinish_src] at hfinish_lt
                  have htime_pos : (dfsVisit G f_rec v s_rec).time > 0 := by
                    have hgt := dfsVisit_time_gt_of_white G hf_rec_pos hs_rec_white
                    exact lt_of_le_of_lt (Nat.zero_le s_rec.time) hgt
                  omega
                have h_rec_time_le_s1 : (dfsVisit G (n - 1) w s_input).time ≤ s1.time := by
                  have htime_post : (dfsVisit G (n - 1) w s_input).time ≤
                      (List.foldl step (dfsVisit G (n - 1) w s_input) post).time :=
                    dfsVisit_fold_time_ge G
                      (u := u) (s1 := dfsVisit G (n - 1) w s_input) (l := post)
                  have h_full_fold_time :
                      (List.foldl (fun s' x =>
                        if s'.color x = Color.white then dfsVisit G G.vertices.card x (s'.setParent x u) else s')
                        ((s0.setColor u Color.gray).setDiscovery u) (G.adj u).toList).time =
                        (List.foldl step (dfsVisit G (n - 1) w s_input) post).time := by
                    simpa [step, s_init, hn] using congrArg (fun st => st.time) h_full_fold
                  have htime_s1 : s1.time =
                      (List.foldl step (dfsVisit G (n - 1) w s_input) post).time + 1 := by
                    rw [hs1, dfsVisit, hu_white]
                    simp [h_full_fold_time]
                  omega
                have h_sub_time_le_s1 : (dfsVisit G f_rec v s_rec).time ≤ s1.time :=
                  le_trans h_sub_time_le_rec h_rec_time_le_s1
                have h_nonwhite_s_rec : ∀ x, s_rec.color x ≠ Color.white →
                    discoveryTime (dfsFromList G n (u :: us) s0) x < s_rec.time := by
                  intro x hnw
                  have hlt_rec := h_nonwhite_rec x hnw
                  have hnw_rec := h_nonwhite_pres_rec x hnw
                  have h_s1_d_x := h_s1_d_of_rec_not_white x hnw_rec
                  have hnw_s1 := h_s1_nonwhite_of_rec x hnw_rec
                  have hblack_s1_x : s1.color x = Color.black := by
                    rcases h_ng_s1 x with (hw0 | hb0)
                    · exact False.elim (hnw_s1 hw0)
                    · exact hb0
                  have h_final_d : (dfsFromList G n us s1).d x = s1.d x :=
                    dfsFromList_preserves_d_of_black G hn_pos (x := x) hblack_s1_x
                  dsimp [dfsFromList]
                  rw [if_pos hu_white]
                  change discoveryTime (dfsFromList G n us s1) x < s_rec.time
                  dsimp [discoveryTime] at hlt_rec ⊢
                  rw [h_final_d, h_s1_d_x]
                  exact hlt_rec
                have h_f_pres_s_rec : ∀ x, (dfsVisit G f_rec v s_rec).color x = Color.black →
                    finishTime (dfsFromList G n (u :: us) s0) x =
                      finishTime (dfsVisit G f_rec v s_rec) x := by
                  intro x hblack_sub
                  have hlocal := h_f_pres_rec x hblack_sub
                  have hnw_s1 : s1.color x ≠ Color.white :=
                    h_s1_nonwhite_of_rec x (by rw [hlocal.1]; decide)
                  have hblack_s1_x : s1.color x = Color.black := by
                    rcases h_ng_s1 x with (hw0 | hb0)
                    · exact False.elim (hnw_s1 hw0)
                    · exact hb0
                  have h_f_rest : finishTime (dfsFromList G n us s1) x = finishTime s1 x := by
                    have h := dfsFromList_preserves_f_of_black (G := G) (vs := us) hn_pos
                      (x := x) hblack_s1_x
                    rw [finishTime, finishTime, h]
                  dsimp [dfsFromList]
                  rw [if_pos hu_white]
                  calc
                    finishTime (dfsFromList G n us s1) x = finishTime s1 x := h_f_rest
                    _ = finishTime (dfsVisit G (n - 1) w s_input) x :=
                      h_s1_f_of_rec_black x hlocal.1
                    _ = finishTime (dfsVisit G f_rec v s_rec) x := hlocal.2
                have h_later_s_rec : ∀ x, (dfsVisit G f_rec v s_rec).color x = Color.white →
                    (dfsFromList G n (u :: us) s0).color x ≠ Color.white →
                    (dfsVisit G f_rec v s_rec).time ≤
                      discoveryTime (dfsFromList G n (u :: us) s0) x := by
                  intro x hwhite_sub hfinal
                  dsimp [dfsFromList] at hfinal ⊢
                  rw [if_pos hu_white] at hfinal ⊢
                  by_cases hwhite_s1_x : s1.color x = Color.white
                  · have h_disc_ge :=
                      dfsFromList_white_to_nonwhite_disc_ge_time G hn_pos h_bf_s1 hwhite_s1_x hfinal
                    exact le_trans h_sub_time_le_s1 h_disc_ge
                  · have hblack_s1_x : s1.color x = Color.black := by
                      rcases h_ng_s1 x with (hw0 | hb0)
                      · exact False.elim (hwhite_s1_x hw0)
                      · exact hb0
                    by_cases hwhite_rec_x :
                        (dfsVisit G (n - 1) w s_input).color x = Color.white
                    · have hxu : x ≠ u := by
                        intro h
                        subst x
                        have hrec_u_gray : (dfsVisit G (n - 1) w s_input).color u = Color.gray :=
                          dfsVisit_preserves_gray G hinput_u_gray huw
                        rw [hrec_u_gray] at hwhite_rec_x
                        contradiction
                      have h_s1_color_x : s1.color x =
                          (List.foldl step (dfsVisit G (n - 1) w s_input) post).color x := by
                        have h_full_fold_color :
                            (List.foldl (fun s' y =>
                              if s'.color y = Color.white then dfsVisit G G.vertices.card y (s'.setParent y u) else s')
                              ((s0.setColor u Color.gray).setDiscovery u) (G.adj u).toList).color x =
                              (List.foldl step (dfsVisit G (n - 1) w s_input) post).color x := by
                          simpa [step, s_init, hn] using congrArg (fun st => st.color x) h_full_fold
                        rw [hs1, dfsVisit, hu_white]
                        simpa [hxu] using h_full_fold_color
                      have h_nonwhite_post :
                          (List.foldl step (dfsVisit G (n - 1) w s_input) post).color x ≠
                            Color.white := by
                        intro hpost
                        apply hwhite_s1_x
                        rw [h_s1_color_x, hpost]
                      have h_bf_rec_out : ∀ z,
                          (dfsVisit G (n - 1) w s_input).color z = Color.black →
                          finishTime (dfsVisit G (n - 1) w s_input) z <
                            (dfsVisit G (n - 1) w s_input).time :=
                        dfsVisit_black_finish_lt_time G hfuel_rec_pos hwhite_w_input h_bf_input
                      have h_disc_ge_post :
                          (dfsVisit G (n - 1) w s_input).time ≤
                            discoveryTime (List.foldl step (dfsVisit G (n - 1) w s_input) post) x :=
                        dfsVisit_fold_white_to_nonwhite_disc_ge_time G hfuel_rec_pos
                          h_bf_rec_out hwhite_rec_x h_nonwhite_post
                      have h_s1_d_fold_x : s1.d x =
                          (List.foldl step (dfsVisit G (n - 1) w s_input) post).d x := by
                        have h_full_fold_d :
                            (List.foldl (fun s' y =>
                              if s'.color y = Color.white then dfsVisit G G.vertices.card y (s'.setParent y u) else s')
                              ((s0.setColor u Color.gray).setDiscovery u) (G.adj u).toList).d x =
                              (List.foldl step (dfsVisit G (n - 1) w s_input) post).d x := by
                          simpa [step, s_init, hn] using congrArg (fun st => st.d x) h_full_fold
                        rw [hs1, dfsVisit, hu_white]
                        simp
                        exact h_full_fold_d
                      have h_final_d : (dfsFromList G n us s1).d x = s1.d x :=
                        dfsFromList_preserves_d_of_black G hn_pos (x := x) hblack_s1_x
                      dsimp [discoveryTime] at h_disc_ge_post ⊢
                      rw [h_final_d, h_s1_d_fold_x]
                      exact le_trans h_sub_time_le_rec h_disc_ge_post
                    · have h_later_rec_x := h_later_rec x hwhite_sub hwhite_rec_x
                      have h_s1_d_x := h_s1_d_of_rec_not_white x hwhite_rec_x
                      have h_final_d : (dfsFromList G n us s1).d x = s1.d x :=
                        dfsFromList_preserves_d_of_black G hn_pos (x := x) hblack_s1_x
                      dsimp [discoveryTime] at h_later_rec_x ⊢
                      rw [h_final_d, h_s1_d_x]
                      exact h_later_rec_x
                refine ⟨s_rec, f_rec, hs_rec_white, hf_rec_black, ?_,
                  h_nonwhite_s_rec, h_bf_rec_state, h_gray_rec, ?_, h_fuel_rec, h_later_s_rec⟩
                have h_rec_nonwhite_v : (dfsVisit G (n - 1) w s_input).color v ≠ Color.white := by
                  rw [hblack_v_input]
                  decide
                have h_s1_d_v := h_s1_d_of_rec_not_white v h_rec_nonwhite_v
                have h_result_d : (dfsFromList G n us s1).d v = s1.d v :=
                  dfsFromList_preserves_d_of_black G hn_pos (x := v) hv_black_s1
                · dsimp [dfsFromList]
                  rw [if_pos hu_white]
                  change discoveryTime (dfsFromList G n us s1) v = s_rec.time
                  dsimp [discoveryTime] at hdisc_rec ⊢
                  rw [h_result_d, h_s1_d_v]
                  exact hdisc_rec
                · intro x hblack_sub
                  exact h_f_pres_s_rec x hblack_sub
        · -- u not white; skip
          rw [if_neg hu_white] at hblack_result
          rcases ih s0 h_ng h_bf hdt h_df hwhite_s0 hblack_result with
            ⟨s, f, hs, hf, hdisc, h_nonwhite_ih, h_bf_s_ih, h_gray_s_ih, h_f_pres_ih, h_fuel_ih, h_later_ih⟩
          have h_nonwhite' : ∀ w, s.color w ≠ Color.white →
              discoveryTime (dfsFromList G n (u :: us) s0) w < s.time := by
            intro w hnw; have h := h_nonwhite_ih w hnw
            simpa [dfsFromList, hu_white] using h
          have h_f_pres' : ∀ w, (dfsVisit G f v s).color w = Color.black →
              finishTime (dfsFromList G n (u :: us) s0) w = finishTime (dfsVisit G f v s) w := by
            intro w hblack; have h := h_f_pres_ih w hblack
            simpa [dfsFromList, hu_white] using h
          have h_later' : ∀ w, (dfsVisit G f v s).color w = Color.white →
              (dfsFromList G n (u :: us) s0).color w ≠ Color.white →
              (dfsVisit G f v s).time ≤ discoveryTime (dfsFromList G n (u :: us) s0) w := by
            intro w hw hfinal
            have h := h_later_ih w hw (by simpa [dfsFromList, hu_white] using hfinal)
            simpa [dfsFromList, hu_white] using h
          refine ⟨s, f, hs, hf, ?_, h_nonwhite', h_bf_s_ih, h_gray_s_ih, h_f_pres', h_fuel_ih, h_later'⟩
          dsimp [dfsFromList]; rw [if_neg hu_white]; exact hdisc
  -- Start from dfsInit
  have hwhite_init : (dfsInit (V := V)).color v = Color.white := rfl
  have h_ng_init : ∀ (w : V), (dfsInit (V := V)).color w = Color.white ∨ (dfsInit (V := V)).color w = Color.black :=
    λ (w : V) => Or.inl rfl
  have h_bf_init : ∀ (w : V), (dfsInit (V := V)).color w = Color.black → finishTime (dfsInit (V := V)) w < (dfsInit (V := V)).time := by
    intro w h; dsimp [dfsInit] at h; nomatch h
  have hdt_init : DiscoveryTimeInvariant (dfsInit (V := V)) := by
    intro w h; dsimp [dfsInit] at h; nomatch h
  have h_df_init : DiscoveryFinishInvariant (dfsInit (V := V)) := by
    intro w h; dsimp [dfsInit] at h; nomatch h
  have hblack_final : (dfsFromList G n G.vertices.toList dfsInit).color v = Color.black := by
    rw [← h_dfs]; exact G.dfs_all_black hv
  rcases h_ind G.vertices.toList dfsInit h_ng_init h_bf_init hdt_init h_df_init hwhite_init hblack_final with
    ⟨s, f, hs, hf, hdisc, h_nonwhite_s, h_bf_s, h_gray_s, h_f_pres, h_fuel, h_later⟩
  refine ⟨s, f, hs, hf, ?_, ?_, h_bf_s, h_gray_s, ?_, h_fuel, ?_⟩
  · rw [h_dfs]; exact hdisc
  · intro w hnw
    have h := h_nonwhite_s w hnw
    simpa [h_dfs] using h
  · intro w hblack
    have h := h_f_pres w hblack
    simpa [h_dfs] using h
  · intro w hw hfinal
    have h := h_later w hw (by simpa [h_dfs] using hfinal)
    simpa [h_dfs] using h

end SCCFinishOrdering

end Graph
end Chapter22
end CLRS

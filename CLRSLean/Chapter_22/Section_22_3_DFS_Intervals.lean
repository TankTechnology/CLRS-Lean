import Mathlib
import CLRSLean.Chapter_22.Section_22_1_Representing_Graphs
import CLRSLean.Chapter_22.Section_22_3_DFS
import CLRSLean.Chapter_22.Section_22_3_DFS_WhitePath

/-! # DFS theory: parenthesis theorem and ancestor relations

This file extends the white-path theory with DFS timestamp intervals,
the ancestor/descendant relations, and the discovery-state theorem.
-/

namespace CLRS
namespace Chapter22
namespace Graph

variable {V : Type} [DecidableEq V] (G : Graph V)

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
    (hinv : ∀ u v, s0.parent v = some u → G.Adj u v) :
    ∀ u v, (dfsFromList G fuel vs s0).parent v = some u →
      G.Adj u v := by
  induction vs generalizing s0 with
  | nil =>
      intro u v hparent
      simpa [dfsFromList] using hinv u v hparent
  | cons u us ih =>
      intro x y hparent
      simp [dfsFromList] at hparent
      by_cases hwhite : s0.color u = Color.white
      · rw [if_pos hwhite] at hparent
        have hinv' : ∀ x y, (dfsVisit G fuel u s0).parent y = some x → G.Adj x y :=
          dfsVisit_preserves_parent_edge G hinv
        exact ih hinv' x y hparent
      · rw [if_neg hwhite] at hparent
        exact ih hinv x y hparent

/-- Every DFS ancestor in the full DFS forest is reachable in the graph. -/
theorem IsDFSAncestor_reachable {u v : V}
    (h : IsDFSAncestor (G.dfs) u v) : G.Reachable u v := by
  have hparent_edge : ∀ x y, (G.dfs).parent y = some x → G.Adj x y := by
    have hinv_init : ∀ x y, (dfsInit (V := V)).parent y = some x → G.Adj x y := by
      intro x y hparent
      simp [dfsInit] at hparent
    simpa [dfs] using
      (dfsFromList_preserves_parent_edge (G := G) (fuel := G.vertices.card + 1)
        (s0 := dfsInit) (vs := G.vertices.toList) hinv_init)
  induction h with
  | refl =>
      exact G.reachable_refl u
  | tail hxy hyz ih =>
      exact G.reachable_trans ih (G.reachable_adj (hparent_edge _ _ hyz))

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

end Graph
end Chapter22
end CLRS

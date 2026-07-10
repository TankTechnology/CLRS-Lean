import Mathlib
import CLRSLean.Chapter_22.Section_22_1_Representing_Graphs
import CLRSLean.Chapter_22.Section_22_3_DFS
import CLRSLean.Chapter_22.Section_22_3_DFS.WhitePath
import CLRSLean.Chapter_22.Section_22_3_DFS.Intervals

/-! # Bridge lemma: white→nonwhite during dfsVisit → discovery time ≥ input clock

The single key lemma needed for Case 2 of {lit}`scc_finish_time_order`.  The
proof uses **induction on {lit}`fuel`**.  Case {lit}`v = u`:
{lit}`setDiscovery` sets {lit}`d[u] = s.time`.  Case {lit}`v ≠ u`:
{lit}`dfsVisit_fold_blackens_loc_prefix` finds the exact fold position; the
recursive call has smaller fuel, so the induction hypothesis applies.  The
returned {lit}`hbf_s2` and {lit}`hmono_s2` provide the needed fold-accumulator
invariants, eliminating the need for separate fold-level analysis.
-/

namespace CLRS
namespace Chapter22
namespace Graph

variable {V : Type} [DecidableEq V] (G : Graph V)

/-- If {lit}`v` turns from white to non-white during
{lit}`dfsVisit G fuel u s`, then {name}`discoveryTime` in the output is at
least {lit}`s.time`.

Uses {lit}`h_bf : ∀ w, s.color w = Color.black → finishTime s w < s.time` to
satisfy {name}`dfsVisit_fold_blackens_loc_prefix`'s {lit}`hinv` hypothesis.
For the outer-loop accumulator states used in the SCC proof, {lit}`h_bf` is
available from {lit}`exists_discovery_state`. -/
theorem dfsVisit_white_to_nonwhite_disc_ge_time {fuel : Nat} {u v : V} {s : DFSState V}
    (hfuel : 0 < fuel)
    (h_bf : ∀ w, s.color w = Color.black → finishTime s w < s.time)
    (hwhite_v : s.color v = Color.white)
    (h_nonwhite_result : (dfsVisit G fuel u s).color v ≠ Color.white) :
    discoveryTime (dfsVisit G fuel u s) v ≥ s.time := by
  induction fuel generalizing u s with
  | zero =>
      simp [dfsVisit] at h_nonwhite_result
      rw [hwhite_v] at h_nonwhite_result
      contradiction
  | succ k ih =>
      by_cases hu_white : s.color u = Color.white
      · -- expand dfsVisit; h_eq captures the full expansion
        -- dfsVisit expands: s1 = setDiscovery u, s2 = fold, s3 = setFinish u
        let s1 := s.setColor u Color.gray |>.setDiscovery u
        let step := fun (s' : DFSState V) (w : V) =>
          if s'.color w = Color.white then dfsVisit G k w (s'.setParent w u) else s'
        let s2 := List.foldl step s1 (G.adj u).toList
        let s3 := s2.setColor u Color.black |>.setFinish u
        have h_eq : dfsVisit G (k+1) u s = s3 := by
          simp [s3, s2, s1, step, dfsVisit, hu_white]
        rw [h_eq] at h_nonwhite_result ⊢
        by_cases hvu : v = u
        · -- v = u: discovered at setDiscovery, d[u] = s.time
          subst v
          have h_s3_d : s3.d u = some (s.time) := by
            have h_s1 : s1.d u = some (s.time) := by simp [s1]
            have h_s2 : s2.d u = s1.d u :=
              dfsVisit_fold_preserves_d_of_not_white G (u := u) (v := u) s1
                (l := (G.adj u).toList) (by simp [s1])
            simp [s3, h_s1, h_s2]
          simp [discoveryTime, h_s3_d]
        · -- v ≠ u: v turned non-white during the fold
          have hwhite_v_s1 : s1.color v = Color.white := by simp [s1, hvu, hwhite_v]
          -- s3.color v = s2.color v (setFinish doesn't change v, v ≠ u)
          have h_nonwhite_s2 : s2.color v ≠ Color.white := by
            intro hw; apply h_nonwhite_result; simp [s3, hvu, hw]
          -- s2.color v is black: not white (above) and not gray (fold_no_new_gray)
          have h_black_s2 : s2.color v = Color.black := by
            have h_no_gray : s2.color v ≠ Color.gray := by
              intro hg
              have h_s1_gray : s1.color v = Color.gray :=
                dfsVisit_fold_no_new_gray G s1 (by simpa [s2, step] using hg)
              rw [hwhite_v_s1] at h_s1_gray
              simp at h_s1_gray
            cases hcolor : s2.color v with
            | white => exact (h_nonwhite_s2 hcolor).elim
            | gray => exact (h_no_gray hcolor).elim
            | black => rfl
          -- Build h_bf_init for s1 (from h_bf for s)
          have h_bf_init : ∀ z, s1.color z = Color.black → finishTime s1 z < s1.time := by
            intro z hblack
            have hz_ne_u : z ≠ u := by intro heq; subst z; simp [s1] at hblack
            have hblack_s : s.color z = Color.black := by simpa [s1, hz_ne_u] using hblack
            have h_fin_s : finishTime s z < s.time := h_bf z hblack_s
            have h_fin_s1 : finishTime s1 z = finishTime s z := by simp [s1, finishTime]
            have h_time_s1 : s1.time = s.time + 1 := by simp [s1]
            rw [h_fin_s1, h_time_s1]; omega
          -- Apply dfsVisit_fold_blackens_loc_prefix to find fold position
          rcases dfsVisit_fold_blackens_loc_prefix G h_bf_init hwhite_v_s1 h_black_s2
            with ⟨pre, post, w, s2_acc, hadj_eq, hs2_eq, hw_white, hv_white_s2_acc,
                  hw_disc_v, hmono_s2, hbf_s2⟩
          -- s2_acc is the accumulator just before processing w.
          -- The recursive call dfsVisit G k w (s2_acc.setParent w u) discovers v.
          by_cases hw_eq_v : w = v
          · -- w = v: the recursive call directly discovers v
            subst w
            let s_rec_in := s2_acc.setParent v u
            have hwhite_rec_in : s_rec_in.color v = Color.white := by
              simp [s_rec_in, hv_white_s2_acc]
            have h_nonwhite_rec_out : (dfsVisit G k v s_rec_in).color v ≠ Color.white := by
              rw [hw_disc_v]; decide
            have h_bf_rec : ∀ z, s_rec_in.color z = Color.black →
                finishTime s_rec_in z < s_rec_in.time := by
              intro z hblack
              have hblack_s2_acc : s2_acc.color z = Color.black := by
                simpa [s_rec_in] using hblack
              have h_lt := hbf_s2 z hblack_s2_acc
              simpa [s_rec_in, finishTime] using h_lt
            -- Apply IH at smaller fuel k
            have hk_pos_v : 0 < k := by
              by_cases hz : k = 0
              · subst hz
                have h_eq : dfsVisit G 0 v s_rec_in = s_rec_in := by simp [dfsVisit]
                rw [h_eq] at h_nonwhite_rec_out
                rw [hwhite_rec_in] at h_nonwhite_rec_out
                simp at h_nonwhite_rec_out
              · omega
            have h_disc_ge := ih (u := v) (s := s_rec_in) hk_pos_v h_bf_rec hwhite_rec_in h_nonwhite_rec_out
            -- h_disc_ge: discoveryTime (dfsVisit G k v s_rec_in) v ≥ s_rec_in.time = s2_acc.time
            have h_time_acc : s_rec_in.time = s2_acc.time := by simp [s_rec_in]
            rw [h_time_acc] at h_disc_ge
            -- d[v] preserved through rest of fold (post) and setFinish
            have h_d_post : (List.foldl step (dfsVisit G k v s_rec_in) post).d v =
                (dfsVisit G k v s_rec_in).d v :=
              dfsVisit_fold_preserves_d_of_black G
                (s1 := dfsVisit G k v s_rec_in) (l := post) hw_disc_v
            -- Decompose the full fold using hadj_eq and hs2_eq
            have h_full_fold : s2 = List.foldl step (dfsVisit G k v s_rec_in) post := by
              -- s2 = foldl step s1 (G.adj u).toList
              --    = foldl step s1 (pre ++ v :: post)          [hadj_eq]
              --    = foldl step (foldl step s1 pre) (v :: post) [List.foldl_append]
              --    = foldl step s2_acc (v :: post)             [hs2_eq]
              --    = foldl step (step s2_acc v) post           [List.foldl]
              --    = foldl step (dfsVisit G k v (s2_acc.setParent v u)) post [...]
              calc
                s2 = List.foldl step s1 (G.adj u).toList := rfl
                _ = List.foldl step s1 (pre ++ v :: post) := by rw [hadj_eq]
                _ = List.foldl step (List.foldl step s1 pre) (v :: post) := by rw [List.foldl_append]
                _ = List.foldl step s2_acc (v :: post) := by rw [hs2_eq]
                _ = List.foldl step (step s2_acc v) post := rfl
                _ = List.foldl step (dfsVisit G k v (s2_acc.setParent v u)) post := by
                  simp [step, hw_white]
                _ = List.foldl step (dfsVisit G k v s_rec_in) post := rfl
            have h_s3_d : s3.d v = (dfsVisit G k v s_rec_in).d v := by
              simp [s3, h_full_fold, h_d_post]
            dsimp [discoveryTime] at h_disc_ge ⊢
            rw [h_s3_d]
            -- h_disc_ge says: (dfsVisit ...).d v .getD 0 ≥ s2_acc.time
            -- Need: (dfsVisit ...).d v .getD 0 ≥ s.time
            -- Since s2_acc is a fold accumulator from s1, s2_acc.time ≥ s1.time ≥ s.time
            have h_time_ge : s2_acc.time ≥ s1.time := by
              -- s2_acc = foldl step s1 pre; dfsVisit_fold_time_ge gives clock monotonicity
              rw [hs2_eq]
              simpa [step] using @dfsVisit_fold_time_ge V _ G k u s1 pre
            have h_s1_time : s1.time = s.time + 1 := by simp [s1]
            have h_s2_acc_ge_s_time : s2_acc.time ≥ s.time := by omega
            exact le_trans h_s2_acc_ge_s_time h_disc_ge
          · -- w ≠ v: v is discovered inside the recursive call on w.
            -- By IH (fuel k) on that call, d[v] ≥ s2_acc.time.
            -- Then d-preservation through post and setFinish.
            let s_rec_in := s2_acc.setParent w u
            have hwhite_rec_in : s_rec_in.color v = Color.white := by
              simp [s_rec_in, hv_white_s2_acc]
            have h_bf_rec : ∀ z, s_rec_in.color z = Color.black →
                finishTime s_rec_in z < s_rec_in.time := by
              intro z hblack
              have hblack_s2_acc : s2_acc.color z = Color.black := by
                simpa [s_rec_in] using hblack
              have h_lt := hbf_s2 z hblack_s2_acc
              simpa [s_rec_in, finishTime] using h_lt
            have hk_pos_w : 0 < k := by
              by_cases hz : k = 0
              · subst hz
                have h_eq : dfsVisit G 0 w s_rec_in = s_rec_in := by simp [dfsVisit]
                rw [h_eq] at hw_disc_v
                rw [hwhite_rec_in] at hw_disc_v
                simp at hw_disc_v
              · omega
            have h_nonwhite_w : (dfsVisit G k w s_rec_in).color v ≠ Color.white := by
              rw [hw_disc_v]; decide
            have h_disc_ge := ih (u := w) (s := s_rec_in) hk_pos_w h_bf_rec hwhite_rec_in h_nonwhite_w
            -- hw_disc_v: (dfsVisit G k w s_rec_in).color v = Color.black ≠ white
            -- So h_disc_ge: discoveryTime (dfsVisit G k w s_rec_in) v ≥ s_rec_in.time
            have h_time_rec : s_rec_in.time = s2_acc.time := by simp [s_rec_in]
            rw [h_time_rec] at h_disc_ge
            -- d[v] preserved through rest of fold (post) and setFinish
            have h_d_post : (List.foldl step (dfsVisit G k w s_rec_in) post).d v =
                (dfsVisit G k w s_rec_in).d v :=
              dfsVisit_fold_preserves_d_of_black G
                (s1 := dfsVisit G k w s_rec_in) (l := post) hw_disc_v
            -- Decompose the full fold
            have h_full_fold : s2 = List.foldl step (dfsVisit G k w s_rec_in) post := by
              calc
                s2 = List.foldl step s1 (G.adj u).toList := rfl
                _ = List.foldl step s1 (pre ++ w :: post) := by rw [hadj_eq]
                _ = List.foldl step (List.foldl step s1 pre) (w :: post) := by rw [List.foldl_append]
                _ = List.foldl step s2_acc (w :: post) := by rw [hs2_eq]
                _ = List.foldl step (step s2_acc w) post := rfl
                _ = List.foldl step (dfsVisit G k w s_rec_in) post := by
                  simp [step, hw_white, s_rec_in]
            have h_s3_d : s3.d v = (dfsVisit G k w s_rec_in).d v := by
              simp [s3, h_full_fold, h_d_post]
            dsimp [discoveryTime] at h_disc_ge ⊢
            rw [h_s3_d]
            -- h_disc_ge: discoveryTime (dfsVisit ...) v ≥ s2_acc.time ≥ s.time
            have h_s2_acc_ge_s_time : s2_acc.time ≥ s.time := by
              rw [hs2_eq]
              have h_ge : (List.foldl step s1 pre).time ≥ s1.time := by
                simpa [step] using @dfsVisit_fold_time_ge V _ G k u s1 pre
              have h_s1_ge_s : s1.time ≥ s.time := by
                have : s1.time = s.time + 1 := by simp [s1]
                omega
              exact le_trans h_s1_ge_s h_ge
            exact le_trans h_s2_acc_ge_s_time h_disc_ge

      · -- u is not white: dfsVisit returns s unchanged
        simp [dfsVisit, hu_white] at h_nonwhite_result ⊢
        exact (h_nonwhite_result hwhite_v).elim

/-! ## Corollary: {name}`dfsFromList` version

The lemma lifts to {name}`dfsFromList` by induction on the vertex list. -/

/-- If {lit}`v` turns from white to non-white during the neighbor-processing fold
inside a DFS visit, then its discovery time in the fold output is at least the
input state's clock. -/
theorem dfsVisit_fold_white_to_nonwhite_disc_ge_time {n : Nat} {u : V} {l : List V}
    {s0 : DFSState V} {v : V}
    (hfuel : 0 < n)
    (h_bf_s0 : ∀ w, s0.color w = Color.black → finishTime s0 w < s0.time)
    (hwhite_s0 : s0.color v = Color.white)
    (h_nonwhite_result : (List.foldl (fun (s' : DFSState V) (w : V) =>
        if s'.color w = Color.white then dfsVisit G n w (s'.setParent w u) else s') s0 l).color v ≠
      Color.white) :
    discoveryTime (List.foldl (fun (s' : DFSState V) (w : V) =>
        if s'.color w = Color.white then dfsVisit G n w (s'.setParent w u) else s') s0 l) v ≥
      s0.time := by
  induction l generalizing s0 with
  | nil =>
      simp at h_nonwhite_result
      rw [hwhite_s0] at h_nonwhite_result
      contradiction
  | cons w ws ih =>
      simp at h_nonwhite_result ⊢
      by_cases hw_white : s0.color w = Color.white
      · simp [hw_white] at h_nonwhite_result ⊢
        let s_parent := s0.setParent w u
        let s1 := dfsVisit G n w s_parent
        have h_bf_parent : ∀ z, s_parent.color z = Color.black →
            finishTime s_parent z < s_parent.time := by
          intro z hz
          have hz0 : s0.color z = Color.black := by
            simpa [s_parent] using hz
          have hlt := h_bf_s0 z hz0
          simpa [s_parent, finishTime] using hlt
        by_cases hv_white_s1 : s1.color v = Color.white
        · have h_bf_s1 : ∀ z, s1.color z = Color.black → finishTime s1 z < s1.time := by
            exact dfsVisit_black_finish_lt_time G hfuel (by simpa [s_parent] using hw_white) h_bf_parent
          have htime_ge : s1.time ≥ s0.time := by
            have h := G.dfsVisit_time_ge (fuel := n) (u := w) (s := s_parent)
            simpa [s1, s_parent] using h
          have h_ih := ih (s0 := s1) h_bf_s1 hv_white_s1 h_nonwhite_result
          exact le_trans htime_ge h_ih
        · have hwhite_parent : s_parent.color v = Color.white := by
            simpa [s_parent] using hwhite_s0
          have h_disc_ge_s1 : discoveryTime s1 v ≥ s0.time := by
            have h := dfsVisit_white_to_nonwhite_disc_ge_time G hfuel h_bf_parent
              hwhite_parent hv_white_s1
            simpa [s1, s_parent] using h
          have hblack_s1 : s1.color v = Color.black := by
            have h_no_gray : s1.color v ≠ Color.gray := by
              intro hg
              have h_input_gray : s_parent.color v = Color.gray := dfsVisit_no_new_gray G v hg
              rw [hwhite_parent] at h_input_gray
              contradiction
            cases hcolor : s1.color v with
            | white => exact (hv_white_s1 hcolor).elim
            | gray => exact (h_no_gray hcolor).elim
            | black => rfl
          have h_d_rest :
              (List.foldl (fun (s' : DFSState V) (w : V) =>
                if s'.color w = Color.white then dfsVisit G n w (s'.setParent w u) else s') s1 ws).d v =
                s1.d v :=
            dfsVisit_fold_preserves_d_of_black G (u := u) (v := v) (s1 := s1) (l := ws) hblack_s1
          dsimp [discoveryTime] at h_disc_ge_s1 ⊢
          rw [h_d_rest]
          exact h_disc_ge_s1
      · simp [hw_white] at h_nonwhite_result ⊢
        exact ih h_bf_s0 hwhite_s0 h_nonwhite_result

/-- Named predicate for the bridge facts produced by a local discovery-state
argument.

The {lit}`state` argument is the input state to the recursive {name}`dfsVisit`
that discovers {lit}`v`; {lit}`outer` is the enclosing DFS state in which the
discovery is observed.  Keeping this witness in {lean}`Prop` lets the proof use ordinary
existential elimination over fold-location lemmas. -/
def DFSDiscoveryBridge (G : Graph V) (outer : DFSState V) (v : V)
    (state : DFSState V) (fuel : Nat) : Prop :=
  state.color v = Color.white ∧
  (dfsVisit G fuel v state).color v = Color.black ∧
  discoveryTime outer v = state.time ∧
  (∀ w, state.color w ≠ Color.white → discoveryTime outer w < state.time) ∧
  (∀ w, state.color w = Color.black → finishTime state w < state.time) ∧
  (∀ w, state.color w = Color.gray → G.Reachable w v) ∧
  (∀ w, state.color w ≠ Color.white → outer.color w ≠ Color.white) ∧
  (∀ w, (dfsVisit G fuel v state).color w = Color.black →
    outer.color w = Color.black ∧
    finishTime outer w = finishTime (dfsVisit G fuel v state) w) ∧
  fuel ≥ (whiteReachableSet G state v).card + 1 ∧
  (∀ w, (dfsVisit G fuel v state).color w = Color.white →
    outer.color w ≠ Color.white →
    (dfsVisit G fuel v state).time ≤ discoveryTime outer w)

/-- Local discovery-state theorem for a single {name}`dfsVisit`.

If a sufficiently-fuelled visit from {lit}`u` discovers a white vertex
{lit}`v`, this returns the actual state immediately before the recursive call on
{lit}`v`, packaged as a {name}`DFSDiscoveryBridge`. -/
theorem dfsVisit_discovery_bridge {fuel : Nat} {u v : V} {s : DFSState V}
    (hfuel : fuel ≥ (whiteReachableSet G s u).card + 1)
    (hwhite : s.color u = Color.white)
    (hdt : DiscoveryTimeInvariant s)
    (hbf : ∀ w, s.color w = Color.black → finishTime s w < s.time)
    (hdf : DiscoveryFinishInvariant s)
    (hb : (dfsVisit G fuel u s).color v = Color.black)
    (hw : WhiteReachable G s u v)
    (hv : s.color v = Color.white)
    (hgray : ∀ w, s.color w = Color.gray → G.Reachable w u) :
    ∃ (s' : DFSState V) (fuel' : Nat),
      DFSDiscoveryBridge G (dfsVisit G fuel u s) v s' fuel' := by
  induction fuel generalizing u s with
  | zero =>
      simp [dfsVisit] at hb
      rw [hv] at hb
      contradiction
  | succ n ih =>
      by_cases hvu : v = u
      · subst v
        have hfuel_pos : 0 < n + 1 := by omega
        have hdisc : discoveryTime (dfsVisit G (n + 1) u s) u = s.time :=
          dfsVisit_discovery_source G hfuel_pos hwhite
        have h_nonwhite : ∀ x, s.color x ≠ Color.white →
            discoveryTime (dfsVisit G (n + 1) u s) x < s.time := by
          intro x hnw
          have hxu : x ≠ u := by
            intro h
            subst x
            exact hnw hwhite
          have hd : (dfsVisit G (n + 1) u s).d x = s.d x :=
            dfsVisit_preserves_d_of_not_white G hxu hnw
          have hlt := hdt x hnw
          dsimp [discoveryTime] at hlt ⊢
          rw [hd]
          exact hlt
        have h_nonwhite_pres : ∀ x, s.color x ≠ Color.white →
            (dfsVisit G (n + 1) u s).color x ≠ Color.white := by
          intro x hnw
          have hxu : x ≠ u := by
            intro h
            subst x
            exact hnw hwhite
          exact dfsVisit_preserves_not_white G hxu hnw
        have h_f_pres : ∀ x, (dfsVisit G (n + 1) u s).color x = Color.black →
            (dfsVisit G (n + 1) u s).color x = Color.black ∧
            finishTime (dfsVisit G (n + 1) u s) x = finishTime (dfsVisit G (n + 1) u s) x := by
          intro x hblack
          exact ⟨hblack, rfl⟩
        have h_later : ∀ x, (dfsVisit G (n + 1) u s).color x = Color.white →
            (dfsVisit G (n + 1) u s).color x ≠ Color.white →
            (dfsVisit G (n + 1) u s).time ≤ discoveryTime (dfsVisit G (n + 1) u s) x := by
          intro x hw hnw
          exact False.elim (hnw hw)
        exact ⟨s, n + 1, hwhite, hb, hdisc, h_nonwhite, hbf, hgray,
          h_nonwhite_pres, h_f_pres, hfuel, h_later⟩
      · let s1 := s.setColor u Color.gray |>.setDiscovery u
        let step : DFSState V → V → DFSState V := fun s' x =>
          if s'.color x = Color.white then dfsVisit G n x (s'.setParent x u) else s'
        let s2 := List.foldl step s1 (G.adj u).toList
        let s3 := s2.setColor u Color.black |>.setFinish u
        have heq_state : dfsVisit G (n + 1) u s = s3 := by
          simp [s3, s2, s1, step, dfsVisit, hwhite]
        have hv_s3 : s3.color v = Color.black := by
          rw [← heq_state]
          exact hb
        have hfold_black : s2.color v = Color.black := by
          simp [s3] at hv_s3
          exact hv_s3 hvu
        have hwhite_v_s1 : s1.color v = Color.white := by
          simp [s1, hvu, hv]
        have hbf_s1 : ∀ z, s1.color z = Color.black → finishTime s1 z < s1.time := by
          intro z hz
          have hzu : z ≠ u := by
            intro h
            subst z
            simp [s1] at hz
          have hz0 : s.color z = Color.black := by
            simpa [s1, hzu] using hz
          have hlt := hbf z hz0
          have hf_eq : finishTime s1 z = finishTime s z := by simp [s1, finishTime]
          have ht_eq : s1.time = s.time + 1 := by simp [s1]
          rw [hf_eq, ht_eq]
          omega
        have hdt_s1 : DiscoveryTimeInvariant s1 := by
          intro z hnw
          by_cases hzu : z = u
          · subst z
            simp [s1, discoveryTime]
          · have hnw0 : s.color z ≠ Color.white := by
              simpa [s1, hzu] using hnw
            have hlt := hdt z hnw0
            have hd_eq : discoveryTime s1 z = discoveryTime s z := by
              simp [s1, discoveryTime, hzu]
            have ht_eq : s1.time = s.time + 1 := by simp [s1]
            rw [hd_eq, ht_eq]
            omega
        have hdf_s1 : DiscoveryFinishInvariant s1 := by
          intro z hblack
          have hzu : z ≠ u := by
            intro h
            subst z
            simp [s1] at hblack
          have hblack0 : s.color z = Color.black := by
            simpa [s1, hzu] using hblack
          have hd_eq : discoveryTime s1 z = discoveryTime s z := by
            simp [s1, discoveryTime, hzu]
          have hf_eq : finishTime s1 z = finishTime s z := by
            simp [s1, finishTime]
          rw [hd_eq, hf_eq]
          exact hdf z hblack0
        rcases dfsVisit_fold_blackens_loc_prefix_full G hbf_s1 hdt_s1 hdf_s1 hwhite_v_s1 hfold_black with
          ⟨pre, post, w, s2_acc, hadj_eq, hs2_eq, hw_white, hv_white_s2,
            hw_disc_v, hmono_s2, hbf_s2, hdt_s2⟩
        let s_input := s2_acc.setParent w u
        have hwhite_w_input : s_input.color w = Color.white := by
          simp [s_input, hw_white]
        have hwhite_v_input : s_input.color v = Color.white := by
          simp [s_input, hv_white_s2]
        have hblack_v_input : (dfsVisit G n w s_input).color v = Color.black := by
          simpa [s_input] using hw_disc_v
        have hn_pos : 0 < n := by
          by_contra h
          have hn0 : n = 0 := by omega
          subst n
          simp [dfsVisit] at hblack_v_input
          rw [hwhite_v_input] at hblack_v_input
          contradiction
        have hadj_uw : G.Adj u w := by
          have hw_mem : w ∈ (G.adj u).toList := by
            rw [hadj_eq]
            simp
          simpa [Graph.Adj, Finset.mem_toList] using hw_mem
        have hu_vertices : u ∈ G.vertices := G.adj_mem_left hadj_uw
        have hw_vertices : w ∈ G.vertices := G.adj_mem_right hadj_uw
        have hs2_gray_u : s2_acc.color u = Color.gray := by
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
          exact hfold pre s1 (by simp [s1])
        have hinput_u_gray : s_input.color u = Color.gray := by
          simp [s_input, hs2_gray_u]
        have huw : u ≠ w := by
          intro h
          subst w
          rw [hs2_gray_u] at hw_white
          contradiction
        have h_fuel_input : n ≥ (whiteReachableSet G s_input w).card + 1 := by
          have hnot_u : u ∉ whiteReachableSet G s_input w := by
            intro huin
            have hwr : WhiteReachable G s_input w u :=
              (mem_whiteReachableSet_iff G hw_vertices).mp huin
            have hu_white : s_input.color u = Color.white :=
              whiteReachable_target_white G hwhite_w_input hwr
            rw [hinput_u_gray] at hu_white
            contradiction
          have hsub : whiteReachableSet G s_input w ⊆ whiteReachableSet G s u := by
            intro x hx
            have hxw : WhiteReachable G s_input w x :=
              (mem_whiteReachableSet_iff G hw_vertices).mp hx
            have hwu : WhiteReachable G s u w := by
              have hwhite_w_s : s.color w = Color.white := by
                have h1 : s1.color w = Color.white := hmono_s2 w hw_white
                have hwu_ne : w ≠ u := by exact fun h => huw h.symm
                simpa [s1, hwu_ne] using h1
              exact whiteReachable_step G (whiteReachable_refl G s u) hadj_uw hwhite_w_s
            have hwx_s : WhiteReachable G s w x := by
              have hcolors : ∀ y, s_input.color y = Color.white → s.color y = Color.white := by
                intro y hy
                have hy2 : s2_acc.color y = Color.white := by
                  simpa [s_input] using hy
                have hy1 : s1.color y = Color.white := hmono_s2 y hy2
                have hyu : y ≠ u := by
                  intro h
                  subst y
                  simp [s1] at hy1
                simpa [s1, hyu] using hy1
              exact whiteReachable_mono_of_color_superset G hcolors hxw
            exact (mem_whiteReachableSet_iff G hu_vertices).mpr
              (whiteReachable_trans G hwu hwx_s)
          have hcard_lt : (whiteReachableSet G s_input w).card < (whiteReachableSet G s u).card := by
            apply Finset.card_lt_card
            apply Finset.ssubset_iff_subset_ne.mpr
            refine ⟨hsub, ?_⟩
            intro heq
            have hu_in : u ∈ whiteReachableSet G s u := by
              exact (mem_whiteReachableSet_iff G hu_vertices).mpr (whiteReachable_refl G s u)
            exact hnot_u (heq ▸ hu_in)
          have hcard_le : (whiteReachableSet G s_input w).card + 1 ≤
              (whiteReachableSet G s u).card := by
            omega
          omega
        have hdt_input : DiscoveryTimeInvariant s_input := by
          intro z hnw
          have hnw2 : s2_acc.color z ≠ Color.white := by
            simpa [s_input] using hnw
          have hlt := hdt_s2 z hnw2
          simpa [s_input, discoveryTime] using hlt
        have hdf_s2 : DiscoveryFinishInvariant s2_acc := by
          rw [hs2_eq]
          exact dfsVisit_fold_preserves_discoveryFinishInvariant (G := G) (n := n) (u := u)
            (s1 := s1) (l := pre) hdt_s1 hbf_s1 hdf_s1
        have hdf_input : DiscoveryFinishInvariant s_input := by
          intro z hblack
          have hblack2 : s2_acc.color z = Color.black := by
            simpa [s_input] using hblack
          have h := hdf_s2 z hblack2
          simpa [s_input, discoveryTime, finishTime] using h
        have hbf_input : ∀ z, s_input.color z = Color.black → finishTime s_input z < s_input.time := by
          intro z hblack
          have hblack2 : s2_acc.color z = Color.black := by
            simpa [s_input] using hblack
          have h := hbf_s2 z hblack2
          simpa [s_input, finishTime] using h
        have hgray_input : ∀ z, s_input.color z = Color.gray → G.Reachable z w := by
          intro z hz
          have hz2 : s2_acc.color z = Color.gray := by
            simpa [s_input] using hz
          have hz1 : s1.color z = Color.gray := by
            rw [hs2_eq] at hz2
            exact dfsVisit_fold_no_new_gray G s1 hz2
          have hzu_or : z = u ∨ s.color z = Color.gray := by
            by_cases hzu : z = u
            · exact Or.inl hzu
            · right
              simpa [s1, hzu] using hz1
          rcases hzu_or with (hzu | hz_gray)
          · subst z
            exact Relation.ReflTransGen.single hadj_uw
          · exact Relation.ReflTransGen.trans (hgray z hz_gray)
              (Relation.ReflTransGen.single hadj_uw)
        have hwreach : WhiteReachable G s_input w v :=
          dfsVisit_blackens_implies_whiteReachable G hwhite_w_input hn_pos
            hwhite_v_input hblack_v_input
        rcases ih (u := w) (s := s_input) h_fuel_input hwhite_w_input hdt_input
            hbf_input hdf_input hblack_v_input hwreach hwhite_v_input hgray_input with
          ⟨s_rec, f_rec, hs_rec_white, hf_rec_black, hdisc_rec, h_nonwhite_rec,
            hbf_rec_state, h_gray_rec, h_nonwhite_pres_rec, h_f_pres_rec,
            h_fuel_rec, h_later_rec⟩
        have h_full_fold : List.foldl step s1 (G.adj u).toList =
            List.foldl step (dfsVisit G n w s_input) post := by
          have h := dfsVisit_fold_split_at_white_neighbor G
            s1 pre post s2_acc hadj_eq hs2_eq hw_white
          simpa [s_input] using h
        have h_s3_d_of_rec_not_white : ∀ x,
            (dfsVisit G n w s_input).color x ≠ Color.white →
            s3.d x = (dfsVisit G n w s_input).d x := by
          intro x hnw_rec
          have h_post_d : (List.foldl step (dfsVisit G n w s_input) post).d x =
              (dfsVisit G n w s_input).d x :=
            dfsVisit_fold_preserves_d_of_not_white G
              (u := u) (v := x) (s1 := dfsVisit G n w s_input) (l := post) hnw_rec
          simp [s3, s2]
          calc
            (List.foldl step s1 (G.adj u).toList).d x
                = (List.foldl step (dfsVisit G n w s_input) post).d x := by
                  simpa using congrArg (fun st => st.d x) h_full_fold
            _ = (dfsVisit G n w s_input).d x := h_post_d
        have h_s3_nonwhite_of_rec : ∀ x,
            (dfsVisit G n w s_input).color x ≠ Color.white →
            s3.color x ≠ Color.white := by
          intro x hnw_rec
          by_cases hxu : x = u
          · subst x
            simp [s3]
          · have hpost_nw :
                (List.foldl step (dfsVisit G n w s_input) post).color x ≠ Color.white :=
              dfsVisit_fold_preserves_not_white G
                (u := u) (v := x) (s1 := dfsVisit G n w s_input) (l := post) hxu hnw_rec
            simpa [s3, s2, hxu, h_full_fold] using hpost_nw
        have h_s3_black_f_of_rec_black : ∀ x,
            (dfsVisit G n w s_input).color x = Color.black →
            s3.color x = Color.black ∧
              finishTime s3 x = finishTime (dfsVisit G n w s_input) x := by
          intro x hblack_rec
          have hxu : x ≠ u := by
            intro h
            subst x
            have hrec_u_gray : (dfsVisit G n w s_input).color u = Color.gray :=
              dfsVisit_preserves_gray G hinput_u_gray huw
            rw [hrec_u_gray] at hblack_rec
            contradiction
          have hpost_black : (List.foldl step (dfsVisit G n w s_input) post).color x = Color.black :=
            dfsVisit_fold_preserves_black G
              (u := u) (x := x) (s1 := dfsVisit G n w s_input) (l := post) hblack_rec
          have hpost_f : (List.foldl step (dfsVisit G n w s_input) post).f x =
              (dfsVisit G n w s_input).f x :=
            dfsVisit_fold_preserves_f_of_black G
              (u := u) (v := x) (s1 := dfsVisit G n w s_input) (l := post) hblack_rec
          constructor
          · simp [s3, s2, hxu, h_full_fold, hpost_black]
          · simp [s3, s2, finishTime, hxu, h_full_fold, hpost_f]
        have h_sub_time_le_rec : (dfsVisit G f_rec v s_rec).time ≤
            (dfsVisit G n w s_input).time := by
          have hf_rec_pos : 0 < f_rec := by omega
          have hfinish_src :
              finishTime (dfsVisit G f_rec v s_rec) v =
                (dfsVisit G f_rec v s_rec).time - 1 :=
            dfsVisit_finishTime_source_eq_pred_time G hf_rec_pos hs_rec_white
          have hlocal_v := h_f_pres_rec v hf_rec_black
          have hfinish_lt :
              finishTime (dfsVisit G n w s_input) v <
                (dfsVisit G n w s_input).time :=
            dfsVisit_black_finish_lt_time G hn_pos hwhite_w_input hbf_input v hlocal_v.1
          rw [hlocal_v.2, hfinish_src] at hfinish_lt
          have htime_pos : (dfsVisit G f_rec v s_rec).time > 0 := by
            have hgt := dfsVisit_time_gt_of_white G hf_rec_pos hs_rec_white
            exact lt_of_le_of_lt (Nat.zero_le s_rec.time) hgt
          omega
        have h_rec_time_le_s3 : (dfsVisit G n w s_input).time ≤ s3.time := by
          have htime_post : (dfsVisit G n w s_input).time ≤
              (List.foldl step (dfsVisit G n w s_input) post).time :=
            dfsVisit_fold_time_ge G (u := u) (s1 := dfsVisit G n w s_input) (l := post)
          have htime_s3 : s3.time =
              (List.foldl step (dfsVisit G n w s_input) post).time + 1 := by
            simp [s3, s2, h_full_fold]
          omega
        have h_sub_time_le_s3 : (dfsVisit G f_rec v s_rec).time ≤ s3.time :=
          le_trans h_sub_time_le_rec h_rec_time_le_s3
        have h_nonwhite : ∀ x, s_rec.color x ≠ Color.white →
            discoveryTime (dfsVisit G (n + 1) u s) x < s_rec.time := by
          intro x hnw
          have hlt_rec := h_nonwhite_rec x hnw
          have hnw_rec := h_nonwhite_pres_rec x hnw
          have h_s3_d_x := h_s3_d_of_rec_not_white x hnw_rec
          rw [heq_state]
          dsimp [discoveryTime] at hlt_rec ⊢
          rw [h_s3_d_x]
          exact hlt_rec
        have h_nonwhite_pres : ∀ x, s_rec.color x ≠ Color.white →
            (dfsVisit G (n + 1) u s).color x ≠ Color.white := by
          intro x hnw
          have hnw_rec := h_nonwhite_pres_rec x hnw
          rw [heq_state]
          exact h_s3_nonwhite_of_rec x hnw_rec
        have h_f_pres : ∀ x, (dfsVisit G f_rec v s_rec).color x = Color.black →
            (dfsVisit G (n + 1) u s).color x = Color.black ∧
              finishTime (dfsVisit G (n + 1) u s) x = finishTime (dfsVisit G f_rec v s_rec) x := by
          intro x hblack_sub
          have hlocal := h_f_pres_rec x hblack_sub
          have hs3 := h_s3_black_f_of_rec_black x hlocal.1
          rw [heq_state]
          exact ⟨hs3.1, by rw [hs3.2, hlocal.2]⟩
        have h_later : ∀ x, (dfsVisit G f_rec v s_rec).color x = Color.white →
            (dfsVisit G (n + 1) u s).color x ≠ Color.white →
            (dfsVisit G f_rec v s_rec).time ≤ discoveryTime (dfsVisit G (n + 1) u s) x := by
          intro x hwhite_sub hfinal
          rw [heq_state] at hfinal ⊢
          by_cases hwhite_rec_x : (dfsVisit G n w s_input).color x = Color.white
          · have hxu : x ≠ u := by
              intro h
              subst x
              have hrec_u_gray : (dfsVisit G n w s_input).color u = Color.gray :=
                dfsVisit_preserves_gray G hinput_u_gray huw
              rw [hrec_u_gray] at hwhite_rec_x
              contradiction
            have h_s3_color_x : s3.color x =
                (List.foldl step (dfsVisit G n w s_input) post).color x := by
              simp [s3, s2, hxu, h_full_fold]
            have h_nonwhite_post :
                (List.foldl step (dfsVisit G n w s_input) post).color x ≠ Color.white := by
              intro hpost
              apply hfinal
              rw [h_s3_color_x, hpost]
            have h_bf_rec_out : ∀ z, (dfsVisit G n w s_input).color z = Color.black →
                finishTime (dfsVisit G n w s_input) z < (dfsVisit G n w s_input).time :=
              dfsVisit_black_finish_lt_time G hn_pos hwhite_w_input hbf_input
            have h_disc_ge_post :
                (dfsVisit G n w s_input).time ≤
                  discoveryTime (List.foldl step (dfsVisit G n w s_input) post) x :=
              dfsVisit_fold_white_to_nonwhite_disc_ge_time G hn_pos h_bf_rec_out
                hwhite_rec_x h_nonwhite_post
            have h_s3_d_fold_x : s3.d x =
                (List.foldl step (dfsVisit G n w s_input) post).d x := by
              simp [s3, s2, h_full_fold]
            dsimp [discoveryTime] at h_disc_ge_post ⊢
            rw [h_s3_d_fold_x]
            exact le_trans h_sub_time_le_rec h_disc_ge_post
          · have h_later_rec_x := h_later_rec x hwhite_sub hwhite_rec_x
            have h_s3_d_x := h_s3_d_of_rec_not_white x hwhite_rec_x
            dsimp [discoveryTime] at h_later_rec_x ⊢
            rw [h_s3_d_x]
            exact h_later_rec_x
        refine ⟨s_rec, f_rec, hs_rec_white, hf_rec_black, ?_, h_nonwhite,
          hbf_rec_state, h_gray_rec, h_nonwhite_pres, h_f_pres, h_fuel_rec, h_later⟩
        have h_rec_nonwhite_v : (dfsVisit G n w s_input).color v ≠ Color.white := by
          rw [hblack_v_input]
          decide
        have h_s3_d_v := h_s3_d_of_rec_not_white v h_rec_nonwhite_v
        rw [heq_state]
        dsimp [discoveryTime] at hdisc_rec ⊢
        rw [h_s3_d_v]
        exact hdisc_rec

/-- Compatibility wrapper for callers that still destructure the bridge as an
existential/conjunction package. -/
theorem dfsVisit_discovery_state_with_bridges {fuel : Nat} {u v : V} {s : DFSState V}
    (hfuel : fuel ≥ (whiteReachableSet G s u).card + 1)
    (hwhite : s.color u = Color.white)
    (hdt : DiscoveryTimeInvariant s)
    (hbf : ∀ w, s.color w = Color.black → finishTime s w < s.time)
    (hdf : DiscoveryFinishInvariant s)
    (hb : (dfsVisit G fuel u s).color v = Color.black)
    (hw : WhiteReachable G s u v)
    (hv : s.color v = Color.white)
    (hgray : ∀ w, s.color w = Color.gray → G.Reachable w u) :
    ∃ (s' : DFSState V) (fuel' : Nat),
      s'.color v = Color.white ∧
      (dfsVisit G fuel' v s').color v = Color.black ∧
      discoveryTime (dfsVisit G fuel u s) v = s'.time ∧
      (∀ w, s'.color w ≠ Color.white →
        discoveryTime (dfsVisit G fuel u s) w < s'.time) ∧
      (∀ w, s'.color w = Color.black → finishTime s' w < s'.time) ∧
      (∀ w, s'.color w = Color.gray → G.Reachable w v) ∧
      (∀ w, s'.color w ≠ Color.white →
        (dfsVisit G fuel u s).color w ≠ Color.white) ∧
      (∀ w, (dfsVisit G fuel' v s').color w = Color.black →
        (dfsVisit G fuel u s).color w = Color.black ∧
        finishTime (dfsVisit G fuel u s) w = finishTime (dfsVisit G fuel' v s') w) ∧
      fuel' ≥ (whiteReachableSet G s' v).card + 1 ∧
      (∀ w, (dfsVisit G fuel' v s').color w = Color.white →
        (dfsVisit G fuel u s).color w ≠ Color.white →
        (dfsVisit G fuel' v s').time ≤ discoveryTime (dfsVisit G fuel u s) w) := by
  simpa [DFSDiscoveryBridge] using
    (dfsVisit_discovery_bridge G hfuel hwhite hdt hbf hdf hb hw hv hgray)

/-- If {lit}`v` turns from white to non-white during {name}`dfsFromList`, then
{name}`discoveryTime` in the result is at least {lit}`s0.time`. -/
theorem dfsFromList_white_to_nonwhite_disc_ge_time {fuel : Nat} {vs : List V}
    {s0 : DFSState V} {v : V}
    (hfuel : 0 < fuel)
    (h_bf_s0 : ∀ w, s0.color w = Color.black → finishTime s0 w < s0.time)
    (hwhite_s0 : s0.color v = Color.white)
    (h_nonwhite_result : (dfsFromList G fuel vs s0).color v ≠ Color.white) :
    discoveryTime (dfsFromList G fuel vs s0) v ≥ s0.time := by
  induction vs generalizing s0 with
  | nil =>
      simp [dfsFromList] at h_nonwhite_result
      rw [hwhite_s0] at h_nonwhite_result
      contradiction
  | cons u us ih =>
      simp [dfsFromList] at h_nonwhite_result ⊢
      by_cases hu_white : s0.color u = Color.white
      · rw [if_pos hu_white] at h_nonwhite_result ⊢
        let s1 := dfsVisit G fuel u s0
        by_cases hv_white_s1 : s1.color v = Color.white
        · -- v stayed white; apply IH on rest
          have h_bf_s1 : ∀ w, s1.color w = Color.black → finishTime s1 w < s1.time := by
            simpa [s1] using
              dfsVisit_black_finish_lt_time (G := G) (fuel := fuel) (u := u) (s := s0) hfuel hu_white h_bf_s0
          have h_time_ge_s1 : s1.time ≥ s0.time := G.dfsVisit_time_ge (fuel := fuel) (u := u) (s := s0)
          have h_ih := ih (s0 := s1) h_bf_s1 hv_white_s1 h_nonwhite_result
          exact le_trans h_time_ge_s1 h_ih
        · -- v turned non-white during dfsVisit from u
          have h_disc_ge : discoveryTime s1 v ≥ s0.time :=
            dfsVisit_white_to_nonwhite_disc_ge_time G hfuel h_bf_s0 hwhite_s0 hv_white_s1
          -- d[v] preserved through dfsFromList on rest
          have h_black_s1 : s1.color v = Color.black := by
            -- dfsVisit output has no gray for v ≠ u; v is non-white, so it's black
            by_cases hvu : v = u
            · subst v; exact dfsVisit_blackens_u_pos (G := G) hfuel hu_white
            · have h_no_gray : s1.color v ≠ Color.gray := by
                intro hg
                have h_input_gray : s0.color v = Color.gray := dfsVisit_no_new_gray G v hg
                rw [hwhite_s0] at h_input_gray; contradiction
              cases hcolor : s1.color v with
              | white => exact (hv_white_s1 hcolor).elim
              | gray => exact (h_no_gray hcolor).elim
              | black => rfl
          have hd_preserved : (dfsFromList G fuel us s1).d v = s1.d v :=
            dfsFromList_preserves_d_of_black G hfuel (x := v) h_black_s1
          dsimp [discoveryTime] at h_disc_ge ⊢
          rw [hd_preserved]
          simpa [discoveryTime] using h_disc_ge
      · rw [if_neg hu_white] at h_nonwhite_result ⊢
        exact ih (s0 := s0) h_bf_s0 hwhite_s0 h_nonwhite_result

end Graph
end Chapter22
end CLRS

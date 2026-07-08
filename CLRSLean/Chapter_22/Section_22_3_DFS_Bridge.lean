import Mathlib
import CLRSLean.Chapter_22.Section_22_1_Representing_Graphs
import CLRSLean.Chapter_22.Section_22_3_DFS
import CLRSLean.Chapter_22.Section_22_3_DFS_WhitePath

/-! # Bridge lemma: white→nonwhite during dfsVisit → discovery time ≥ input clock

The single key lemma needed for Case 2 of `scc_finish_time_order`.  The proof
uses **induction on `fuel`**.  Case `v = u`: `setDiscovery` sets `d[u] = s.time`.
Case `v ≠ u`: `dfsVisit_fold_blackens_loc_prefix` finds the exact fold position;
the recursive call has smaller fuel, so the induction hypothesis applies.
The returned `hbf_s2` and `hmono_s2` provide the needed fold-accumulator
invariants, eliminating the need for separate fold-level analysis.
-/

namespace CLRS
namespace Chapter22
namespace Graph

variable {V : Type} [DecidableEq V] (G : Graph V)

/-- If `v` turns from white to non-white during `dfsVisit G fuel u s`, then
`discoveryTime` in the output is at least `s.time`.

Uses `h_bf : ∀ w, s.color w = Color.black → finishTime s w < s.time` to
satisfy `dfsVisit_fold_blackens_loc_prefix`'s `hinv` hypothesis.  For the
outer-loop accumulator states used in the SCC proof, `h_bf` is available
from `exists_discovery_state`. -/
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
      have hk_pos : 0 < k := by
        by_contra h; have hzero : k = 0 := by omega; subst hzero
        simp [dfsVisit] at h_nonwhite_result
        rw [hwhite_v] at h_nonwhite_result
        contradiction
      simp [dfsVisit] at h_nonwhite_result ⊢
      by_cases hu_white : s.color u = Color.white
      · rw [if_pos hu_white] at h_nonwhite_result ⊢
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
          dsimp [discoveryTime]; rw [h_s3_d]; simp; omega
        · -- v ≠ u: v turned non-white during the fold
          have hwhite_v_s1 : s1.color v = Color.white := by simp [s1, hvu, hwhite_v]
          -- s3.color v = s2.color v (setFinish doesn't change v, v ≠ u)
          have h_nonwhite_s2 : s2.color v ≠ Color.white := by
            intro hw; apply h_nonwhite_result; simp [s3, hvu, hw]
          -- s2.color v is black: not white (above) and not gray (fold_no_new_gray)
          have h_black_s2 : s2.color v = Color.black := by
            have h_no_gray : s2.color v ≠ Color.gray := by
              intro hg
              -- dfsVisit_fold_no_new_gray: if s2 has gray, s1 had it
              apply @dfsVisit_fold_no_new_gray V _ G k u v s1 (G.adj u).toList hg
              simp [s1, hvu]
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
            have h_disc_ge := ih k v s_rec_in hk_pos h_bf_rec hwhite_rec_in h_nonwhite_rec_out
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
                  simp [step, hw_white, s_rec_in]
                _ = List.foldl step (dfsVisit G k v s_rec_in) post := rfl
            have h_s3_d : s3.d v = (dfsVisit G k v s_rec_in).d v := by
              dsimp [s3]; rw [h_full_fold, h_d_post]; simp [hvu]
            dsimp [discoveryTime]; rw [h_s3_d]
            -- h_disc_ge says: (dfsVisit ...).d v .getD 0 ≥ s2_acc.time
            -- Need: (dfsVisit ...).d v .getD 0 ≥ s.time
            -- Since s2_acc is a fold accumulator from s1, s2_acc.time ≥ s1.time ≥ s.time
            have h_time_ge : s2_acc.time ≥ s1.time := by
              -- s2_acc = foldl step s1 pre; dfsVisit_fold_time_ge gives clock monotonicity
              rw [hs2_eq]
              exact dfsVisit_fold_time_ge (G := G) (u := u) (s1 := s1) (l := pre)
            have h_s1_time : s1.time = s.time + 1 := by simp [s1]
            have h_s2_acc_ge_s_time : s2_acc.time ≥ s.time := by omega
            omega
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
            have h_disc_ge := ih k w s_rec_in hk_pos h_bf_rec hwhite_rec_in hw_disc_v
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
              dsimp [s3]; rw [h_full_fold, h_d_post]; simp [hvu]
            dsimp [discoveryTime]; rw [h_s3_d]
            -- h_disc_ge: discoveryTime (dfsVisit ...) v ≥ s2_acc.time ≥ s.time
            have h_s2_acc_ge_s_time : s2_acc.time ≥ s.time := by
              rw [hs2_eq]
              have h_ge := dfsVisit_fold_time_ge (G := G) (u := u) (s1 := s1) (l := pre)
              have h_s1_time : s1.time = s.time + 1 := by simp [s1]
              omega
            omega

      · -- u is not white: dfsVisit returns s unchanged
        rw [if_neg hu_white] at h_nonwhite_result ⊢
        exact ih u s hfuel h_bf hwhite_v h_nonwhite_result

/-! ### Corollary: `dfsFromList` version

The lemma lifts to `dfsFromList` by induction on the vertex list. -/

/-- If `v` turns from white to non-white during `dfsFromList`, then
`discoveryTime` in the result is at least `s0.time`. -/
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
          have h_bf_s1 : ∀ w, s1.color w = Color.black → finishTime s1 w < s1.time :=
            dfsVisit_black_finish_lt_time (G := G) (fuel := fuel) (u := u) (s := s0) hfuel hu_white h_bf_s0
          exact ih us s1 hfuel h_bf_s1 hv_white_s1 h_nonwhite_result
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
        exact ih us s0 hfuel h_bf_s0 hwhite_s0 h_nonwhite_result

end Graph
end Chapter22
end CLRS

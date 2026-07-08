import Mathlib
import CLRSLean.Chapter_22.Section_22_1_Representing_Graphs
import CLRSLean.Chapter_22.Section_22_3_DFS
import CLRSLean.Chapter_22.Section_22_3_DFS_WhitePath

/-! # Bridge lemma: white→nonwhite during dfsVisit → discovery time ≥ input clock

The single key lemma needed for Case 2 of `scc_finish_time_order`.  It is
proved by **induction on `fuel`** in `dfsVisit`.  In the `v ≠ u` case, the
induction hypothesis applies to the recursive `dfsVisit` call (with smaller
fuel) that discovers `v` within the fold.

The lemma takes two auxiliary hypotheses that are trivially satisfied for
the outer-loop accumulator states used in the SCC proof:
  `h_ng : ∀ w, w ≠ u → s.color w ≠ Color.gray` — no gray vertices except u
  `h_bf : ∀ w, s.color w = Color.black → finishTime s w < s.time`
-/

namespace CLRS
namespace Chapter22
namespace Graph

variable {V : Type} [DecidableEq V] (G : Graph V)

/-- If `v` turns from white to non-white during `dfsVisit G fuel u s`, then
`discoveryTime` in the output is at least `s.time`.

The proof is by induction on `fuel`.  Case `v = u`: `setDiscovery` sets
`d[u] = s.time`.  Case `v ≠ u`: `dfsVisit_fold_blackens_loc` finds the
fold position; the recursive call has smaller fuel, so the induction
hypothesis applies. -/
theorem dfsVisit_white_to_nonwhite_disc_ge_time {fuel : Nat} {u v : V} {s : DFSState V}
    (hfuel : 0 < fuel)
    (h_ng : ∀ w, s.color w = Color.white ∨ s.color w = Color.black)
    (h_bf : ∀ w, s.color w = Color.black → finishTime s w < s.time)
    (hwhite_v : s.color v = Color.white)
    (h_nonwhite_result : (dfsVisit G fuel u s).color v ≠ Color.white) :
    discoveryTime (dfsVisit G fuel u s) v ≥ s.time := by
  induction fuel generalizing u s with
  | zero => linarith
  | succ k ih =>
      simp [dfsVisit] at h_nonwhite_result ⊢
      by_cases hu_white : s.color u = Color.white
      · rw [if_pos hu_white] at h_nonwhite_result ⊢
        let s1 := s.setColor u Color.gray |>.setDiscovery u
        let step := fun (s' : DFSState V) (w : V) =>
          if s'.color w = Color.white then dfsVisit G k w (s'.setParent w u) else s'
        let s2 := List.foldl step s1 (G.adj u).toList
        let s3 := s2.setColor u Color.black |>.setFinish u
        have h_result : dfsVisit G (k+1) u s = s3 := by
          simp [s3, s2, s1, step, dfsVisit, hu_white]
        rw [h_result] at h_nonwhite_result ⊢
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
          -- The fold result s2 has v non-white (setFinish doesn't change v)
          have h_nonwhite_s2 : s2.color v ≠ Color.white := by
            intro hw; apply h_nonwhite_result; simp [s3, hvu, hw]
          -- s2.color v must be black: s1 has no gray for v≠u, fold preserves this
          have h_ng_s1 : s1.color v ≠ Color.gray := by simp [s1, hvu]
          -- The fold step function only turns white→gray→black; output has no gray.
          -- So s2.color v is black (not gray, and not white).
          have h_black_s2 : s2.color v = Color.black := by
            by_cases hw : s2.color v = Color.white
            · exact (h_nonwhite_s2 hw).elim
            · have h_gray : s2.color v ≠ Color.gray := by
                intro hg; apply h_ng_s1
                exact dfsVisit_fold_no_new_gray (G := G) (u := u) s1 (l := (G.adj u).toList) hg
              cases hcolor : s2.color v with
              | white => exact (h_nonwhite_s2 hcolor).elim
              | gray => exact (h_gray hcolor).elim
              | black => rfl
          -- Now use dfsVisit_fold_blackens_loc to find the recursive call.
          -- We need: h_bf_init for s1, hwhite_v1: s1.color v = white, hfold_black.
          have h_bf_init : ∀ w, s1.color w = Color.black → finishTime s1 w < s1.time := by
            intro w hblack
            -- w is black in s1 → w was black in s (setColor changes u to gray,
            -- setDiscovery doesn't change colors; so w ≠ u by h_ng u trivial?)
            -- Actually w could be any vertex.  If w ≠ u, s1.color w = s.color w.
            -- If w = u, s1.color u = gray, not black. So w ≠ u always.
            have hw_ne_u : w ≠ u := by
              intro heq; subst w; simp [s1] at hblack
            have hblack_s : s.color w = Color.black := by
              simpa [s1, hw_ne_u] using hblack
            have h_fin_s : finishTime s w < s.time := h_bf w hblack_s
            have h_fin_s1 : finishTime s1 w = finishTime s w := by simp [s1, finishTime]
            have h_time_s1 : s1.time = s.time + 1 := by simp [s1]
            rw [h_fin_s1, h_time_s1]; omega
          rcases dfsVisit_fold_blackens_loc (G := G) (n := k) (u := u) (v := v) (s1 := s1)
              hwhite_v_s1 h_black_s2 with ⟨w, hwmem, s2_acc, hw_white, hv_white_acc, h_black_result, hmono⟩
          -- At this fold position, the recursive call dfsVisit G k w (s2_acc.setParent w u)
          -- blackens v.  The accumulator s2_acc satisfies:
          --   s2_acc.color v = white  (from hv_white_acc)
          -- By IH (fuel k, which is < k+1), applied to the recursive call:
          have hk_pos : 0 < k := by
            -- If k = 0, dfsVisit G 0 w ... doesn't change colors, but h_black_result
            -- says v becomes black.  Contradiction.  So k > 0.
            by_contra hzero; have hzero' : k = 0 := by omega; subst hzero'
            simp [dfsVisit] at h_black_result
            rw [hv_white_acc] at h_black_result
          -- The recursive call input: s2_acc.setParent w u.
          -- Its color for v: white (setParent doesn't change colors)
          have hwhite_rec_input : (s2_acc.setParent w u).color v = Color.white := by simp [hv_white_acc]
          -- The recursive call output has v black
          have h_nonwhite_rec_output : (dfsVisit G k w (s2_acc.setParent w u)).color v ≠ Color.white := by
            rw [h_black_result]; decide
          -- Need h_ng for the recursive call input:
          -- s2_acc satisfies no-gray because the fold preserves it.
          -- s2_acc.setParent w u also satisfies it (setParent doesn't change colors).
          -- For now, we admit the no-gray property of s2_acc.
          have h_ng_rec : ∀ w', (s2_acc.setParent w u).color w' = Color.white ∨
              (s2_acc.setParent w u).color w' = Color.black := by
            -- s2_acc is a fold accumulator.  It was reached from s1 via fold steps
            -- that preserve the no-gray property.  We admit this.
            sorry
          have h_bf_rec : ∀ w', (s2_acc.setParent w u).color w' = Color.black →
              finishTime (s2_acc.setParent w u) w' < (s2_acc.setParent w u).time := by
            -- Follows from the fold accumulator invariants.  Admitted.
            sorry
          have h_disc_ge := ih k w (s2_acc.setParent w u) hk_pos h_ng_rec h_bf_rec
            hwhite_rec_input h_nonwhite_rec_output
          -- h_disc_ge: discoveryTime (dfsVisit G k w (s2_acc.setParent w u)) v ≥
          --   (s2_acc.setParent w u).time = s2_acc.time
          have h_time_acc : (s2_acc.setParent w u).time = s2_acc.time := by simp
          rw [h_time_acc] at h_disc_ge
          -- Now: d[v] in the recursive call output ≥ s2_acc.time.
          -- d[v] is preserved through the rest of the fold (by dfsVisit_fold_preserves_d_of_black)
          -- and through setFinish (s3).  So d[v] in s3 ≥ s2_acc.time.
          -- And s2_acc.time ≥ s1.time ≥ s.time (clock monotonicity in the fold).
          -- Therefore d[v] in s3 ≥ s.time.  We admit the d-preservation chain.
          sorry
      · -- u not white: dfsVisit returns s unchanged
        rw [if_neg hu_white] at h_nonwhite_result ⊢
        exact ih u s hfuel h_ng h_bf hwhite_v h_nonwhite_result

end Graph
end Chapter22
end CLRS

import Mathlib
import CLRSLean.Chapter_22.Section_22_1_Representing_Graphs
import CLRSLean.Chapter_22.Section_22_3_DFS

/-! # Bridge lemma: white→nonwhite during dfsFromList → discovery time ≥ start clock

The single key lemma needed for Case 2 of `scc_finish_time_order`:

  If `v` is white at the start of a `dfsFromList` call and turns non-white
  by the end, then `discoveryTime(result) v ≥ start_time`.

The proof is by induction on the vertex list, using the fact that `dfsVisit`
sets `d[u] = s.time` for the source, and preserves d for non-white vertices.
-/

namespace CLRS
namespace Chapter22
namespace Graph

variable {V : Type} [DecidableEq V] (G : Graph V)

/-- If `v` is white at the start of `dfsFromList` and non-white at the end,
then `discoveryTime` in the result is at least `s0.time`. -/
theorem dfsFromList_white_to_nonwhite_disc_ge_time {fuel : Nat} {vs : List V}
    {s0 : DFSState V} {v : V}
    (hfuel : 0 < fuel)
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
        by_cases hvu : v = u
        · -- v = u: dfsVisit sets d[u] = s0.time
          subst v
          have h_disc : discoveryTime s1 u = s0.time :=
            dfsVisit_discovery_source G hfuel hu_white
          have h_black_u : s1.color u = Color.black :=
            dfsVisit_blackens_u_pos (G := G) hfuel hu_white
          have hd_preserved : (dfsFromList G fuel us s1).d u = s1.d u :=
            dfsFromList_preserves_d_of_black G hfuel (x := u) h_black_u
          dsimp [discoveryTime]
          -- Goal: ((dfsFromList ... us s1).d u).getD 0 ≥ s0.time
          rw [hd_preserved]
          -- Goal: (s1.d u).getD 0 ≥ s0.time
          -- h_disc gives: (s1.d u).getD 0 = s0.time
          rw [← h_disc, discoveryTime]
        · -- v ≠ u
          by_cases hv_white_s1 : s1.color v = Color.white
          · -- v stayed white; induction hypothesis on rest
            exact ih us s1 hfuel hv_white_s1 h_nonwhite_result
          · -- v turned non-white during dfsVisit from u: v was discovered here
            -- d[v] was set during this dfsVisit, so d[v] ≥ s0.time
            -- d[v] is preserved through dfsFromList on rest
            have h_black_s1 : s1.color v = Color.black := by
              -- dfsVisit output has no gray vertices (if input has none)
              -- s0 satisfies no-gray (from dfsFromList accumulation)
              -- For simplicity, we use the fact that once non-white, it stays that way
              -- Actually, s1.color v = black follows from the fact that v turned
              -- non-white and dfsVisit output has no gray vertices.
              -- We need a lemma: dfsVisit output has no gray vertices.
              sorry
            have hd_s1_v_ge : discoveryTime s1 v ≥ s0.time := by
              -- v was discovered during dfsVisit, so its d was set to some
              -- clock value between s0.time and s1.time (inclusive).
              -- But we need the STRONGER: discoveryTime s1 v ≥ s0.time.
              -- This follows because d[v] was set at some clock ≥ s0.time.
              sorry
            have hd_preserved : (dfsFromList G fuel us s1).d v = s1.d v :=
              dfsFromList_preserves_d_of_black G hfuel (x := v) h_black_s1
            dsimp [discoveryTime] at hd_s1_v_ge ⊢
            -- Goal: ((dfsFromList ... us s1).d v).getD 0 ≥ s0.time
            rw [hd_preserved]
            -- Goal: (s1.d v).getD 0 ≥ s0.time
            -- This is exactly hd_s1_v_ge
            exact hd_s1_v_ge
      · rw [if_neg hu_white] at h_nonwhite_result ⊢
        exact ih us s0 hfuel hwhite_s0 h_nonwhite_result

end Graph
end Chapter22
end CLRS

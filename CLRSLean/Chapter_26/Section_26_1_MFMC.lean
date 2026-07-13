import Mathlib
import CLRSLean.Chapter_26.Section_26_1_Flow_Networks

/-!
# 26.1. Max-Flow Min-Cut Theorem

This file proves the full Max-Flow Min-Cut Theorem (CLRS Theorem 26.6).

**Status**: complete.
-/

set_option autoImplicit true

namespace CLRS
namespace Chapter26

open Finset Classical

/-- Every consecutive pair from a `List.IsChain` chain satisfies the relation. -/
lemma forall_zip_edges_of_isChain {V : Type*} {r : V → V → Prop} {a : V} {l : List V}
    (h : List.IsChain r (a :: l)) : ∀ (u v : V), (u, v) ∈ List.zip (a :: l) l → r u v := by
  have h_eq : l = [] ∨ ∃ (b : V) (l' : List V), l = b :: l' := by
    cases l
    · left; rfl
    · right; refine ⟨_, _, rfl⟩
  rcases h_eq with (hl | ⟨b, l', hl⟩)
  · subst hl; cases h <;> simp
  · subst hl
    have h_cons_cons := (List.isChain_cons_cons (a := a) (b := b) (l := l')).mp h
    rcases h_cons_cons with ⟨h_rel, h_chain⟩
    intro u v h_mem
    have h_zip : List.zip (a :: b :: l') (b :: l') = (a, b) :: List.zip (b :: l') l' := by simp
    simp [h_zip] at h_mem
    rcases h_mem with (⟨rfl, rfl⟩ | h_rest)
    · exact h_rel
    · exact forall_zip_edges_of_isChain h_chain u v h_rest

/-- Auxiliary lemma: removing the last element doesn't change counts of non-last elements. -/
lemma count_dropLast_eq_count_of_not_last {V : Type*} [DecidableEq V] {l : List V} {u : V}
    (hne : l ≠ []) (h_not_last : u ≠ l.getLast hne) : l.dropLast.count u = l.count u := by
  induction' l with x xs ih generalizing u
  · exact (hne rfl).elim
  · simp
    by_cases hx : u = x
    · subst hx; simp
      by_cases hxs : xs = []
      · subst hxs; simp
      · have hx_ne_xs_last : x ≠ xs.getLast hxs := by
          intro h_eq; apply h_not_last; simp [hxs, h_eq]
        -- In this branch, we need to show (x :: xs).dropLast.count x = (x :: xs).count x
        -- which simplifies to 1 + xs.dropLast.count x = 1 + xs.count x
        -- This follows from ih hxs hx_ne_xs_last
        have ih_val := ih hxs hx_ne_xs_last
        simp [hxs, ih_val]
    · simp [hx, ih (by intro hxs; exact hne (by simp [hxs])) (by
        intro h_eq; apply h_not_last; simp [h_eq])]

/-- A flow with an augmenting path is not maximal. -/
theorem Flow.not_isMaximal_of_hasAugmentingPath {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (φ : Flow V G) (hAug : Flow.hasAugmentingPath φ) : ¬ Flow.isMaximal φ := by
  rcases List.exists_isChain_cons_of_relationReflTransGen hAug with ⟨l, hl_chain, hl_last⟩
  have hlast_t : (G.s :: l).getLast (by simp) = G.t := hl_last
  have hne_st : G.s ≠ G.t := G.hs_ne_t
  have hl_nonempty : l ≠ [] := by
    intro hl
    have hlast_s : (G.s :: l).getLast (by simp) = G.s := by simp [hl]
    have : G.t = G.s := by
      calc G.t = (G.s :: l).getLast (by simp) := by symm; exact hlast_t
           _ = G.s := hlast_s
    exact hne_st this.symm

  let edgeList := List.zip (G.s :: l) l
  have h_edge_nonempty : edgeList ≠ [] := by
    intro hc
    apply hl_nonempty
    have hlen : (List.zip (G.s :: l) l).length = 0 := by simpa [hc] using rfl
    have : l.length = 0 := by
      simpa [List.length_zip] using hlen
    omega

  -- Each edge has positive residual capacity
  have h_edge_pos : ∀ (u v : V), (u, v) ∈ edgeList → Flow.residualCapacity φ u v > 0 :=
    forall_zip_edges_of_isChain hl_chain

  -- Minimum residual capacity along the path edges
  let edgeFinset : Finset (V × V) := edgeList.toFinset
  have h_edgeFinset_nonempty : edgeFinset.Nonempty := by
    have hmem : edgeList.head h_edge_nonempty ∈ edgeFinset :=
      List.mem_toFinset.mpr (List.head_mem h_edge_nonempty)
    exact ⟨_, hmem⟩
  let caps : Finset ℝ := edgeFinset.image (λ (uv : V × V) => Flow.residualCapacity φ uv.1 uv.2)
  have h_caps_nonempty : caps.Nonempty := by
    rcases h_edgeFinset_nonempty with ⟨x, hx⟩
    refine ⟨Flow.residualCapacity φ x.1 x.2, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
  let cf_min := caps.min' h_caps_nonempty
  have h_cf_min_pos : cf_min > 0 := by
    have h_mem : cf_min ∈ caps := Finset.min'_mem _ h_caps_nonempty
    rcases Finset.mem_image.mp h_mem with ⟨⟨u, v⟩, huv_mem, rfl⟩
    have h_in_edgeList : (u, v) ∈ edgeList := by simpa [edgeFinset] using huv_mem
    exact h_edge_pos u v h_in_edgeList

  let N := edgeList.length
  have hN_pos : N > 0 := by
    by_contra! hz
    have hlen : edgeList.length = 0 := by omega
    have : edgeList = [] := List.eq_nil_of_length_eq_zero hlen
    exact h_edge_nonempty this

  let δ := cf_min / (N : ℝ)
  have hδ_pos : δ > 0 := div_pos h_cf_min_pos (by exact_mod_cast hN_pos)

  -- Count forward/backward traversals of each edge
  let countFwd (u v : V) : ℕ := (edgeList.filter (λ (x, y) => x = u ∧ y = v)).length
  let net (u v : V) : ℝ := ((countFwd u v : ℤ) - (countFwd v u : ℤ) : ℝ)

  have h_net_skew (u v : V) : net u v = -net v u := by
    unfold net; ring

  -- |net(u,v)| ≤ N
  have h_net_le_N (u v : V) : (net u v : ℝ) ≤ (N : ℝ) := by
    unfold net
    have h_fwd_le_N : (countFwd u v : ℝ) ≤ (N : ℝ) := by
      have : countFwd u v ≤ edgeList.length :=
        (List.length_filter_le (λ (x : V × V) => x.1 = u ∧ x.2 = v) edgeList).trans (le_refl _)
      exact_mod_cast this
    have h_bwd_nonneg : 0 ≤ (countFwd v u : ℝ) := by exact_mod_cast Nat.zero_le _
    push_cast
    have : (countFwd u v : ℤ) ≤ (N : ℤ) := by exact_mod_cast h_fwd_le_N
    have h_sub_nonpos : (countFwd v u : ℤ) - (countFwd u v : ℤ) ≤ (countFwd u v : ℤ) := by
      omega
    omega

  have h_net_ge_negN (u v : V) : -(N : ℝ) ≤ (net u v : ℝ) := by
    have h := h_net_le_N v u
    rw [h_net_skew v u] at h; linarith

  -- Capacity constraint
  have h_capacity : ∀ (u v : V), φ.f u v + δ * net u v ≤ G.c u v := by
    intro u v
    have hcap_φ : φ.f u v ≤ G.c u v := φ.hcapacity u v
    by_cases h_net_nonpos : net u v ≤ 0
    · have : δ * net u v ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) h_net_nonpos
      linarith
    · have h_net_pos : net u v > 0 := by linarith
      have h_cf_mem : Flow.residualCapacity φ u v ∈ caps := by
        have h_nat_pos : countFwd u v > 0 := by
          by_contra! hz
          have hzero : countFwd u v = 0 := by omega
          have : (net u v : ℝ) ≤ 0 := by
            unfold net; push_cast
            have : (countFwd u v : ℤ) = 0 := by exact_mod_cast hzero
            rw [this]; simp
          linarith
        have h_mem_edgeList : (u, v) ∈ edgeList := by
          have h_filter_nonempty : (edgeList.filter (λ (x, y) => x = u ∧ y = v)) ≠ [] := by
            intro hc; apply h_nat_pos; simpa [countFwd, hc] using rfl
          have h_head_mem : (edgeList.filter (λ (x, y) => x = u ∧ y = v)).head h_filter_nonempty ∈
              edgeList.filter (λ (x, y) => x = u ∧ y = v) :=
            List.head_mem h_filter_nonempty
          let z := (edgeList.filter (λ (x, y) => x = u ∧ y = v)).head h_filter_nonempty
          have hz : z ∈ edgeList.filter (λ (x, y) => x = u ∧ y = v) := h_head_mem
          have hz_eq : z = (u, v) := by
            simpa using hz
          have hz_eq : z = (u, v) := by simpa using hz
          subst hz_eq
          exact List.mem_of_mem_filter hz
        apply Finset.mem_image.mpr
        refine ⟨(u, v), ?_, rfl⟩
        simp [edgeFinset, h_mem_edgeList]
      have h_cf_min_le : cf_min ≤ Flow.residualCapacity φ u v := Finset.min'_le _ _ h_cf_mem
      calc
        φ.f u v + δ * net u v = φ.f u v + (cf_min / (N : ℝ)) * net u v := rfl
        _ ≤ φ.f u v + (cf_min / (N : ℝ)) * (N : ℝ) := by
          have h_net_nonneg : 0 ≤ net u v := by linarith
          have h_div_nonneg : 0 ≤ cf_min / (N : ℝ) := by positivity
          exact mul_le_mul_of_nonneg_left (h_net_le_N u v) h_div_nonneg
        _ = φ.f u v + cf_min := by field_simp; ring
        _ ≤ φ.f u v + Flow.residualCapacity φ u v := by linarith
        _ = G.c u v := by unfold Flow.residualCapacity; linarith

  -- The map of edgeList's first components
  have h_map_fst : (edgeList.map Prod.fst) = (G.s :: l).take (l.length) := by simp
  have h_map_snd : (edgeList.map Prod.snd) = l.take ((G.s :: l).length) := by simp
  have h_snd_full : l.take ((G.s :: l).length) = l := by
    have hlen : l.length < (G.s :: l).length := by simp
    simp

  -- Lemma: sum of countFwd over all v equals count of u in first components
  have h_sum_fwd (u : V) : Finset.sum (Finset.univ : Finset V) (fun v => (countFwd u v : ℝ)) =
      ((edgeList.map Prod.fst).count u : ℝ) := by
    induction' edgeList with x xs ih generalizing u
    · simp [countFwd]
    · simp [countFwd]
      by_cases hx1 : x.1 = u
      · simp [hx1, ih]
      · simp [hx1, ih]

  -- Lemma: sum of countFwd over all u (reversed) equals count of u in second components
  have h_sum_bwd (u : V) : Finset.sum (Finset.univ : Finset V) (fun v => (countFwd v u : ℝ)) =
      ((edgeList.map Prod.snd).count u : ℝ) := by
    induction' edgeList with x xs ih generalizing u
    · simp [countFwd]
    · simp [countFwd]
      by_cases hx2 : x.2 = u
      · simp [hx2, ih]
      · simp [hx2, ih]

  -- Flow value at source: sum over v of net(s,v) = 1
  have h_source_net_sum_one : Finset.sum (Finset.univ : Finset V) (fun v => net G.s v) = 1 := by
    unfold net
    rw [h_sum_fwd G.s, h_sum_bwd G.s, h_map_fst, h_map_snd, h_snd_full]
    have h_take : (G.s :: l).take (l.length) = G.s :: (l.take (l.length - 1)) := by simp
    rw [h_take]
    simp
    have h_count_eq : l.count G.s = (l.take (l.length - 1)).count G.s := by
      have h_last_l_not_s : l.getLast hl_nonempty ≠ G.s := by
        intro h_eq; apply hne_st
        calc
          G.t = (G.s :: l).getLast (by simp) := by symm; exact hlast_t
          _ = l.getLast hl_nonempty := by simp
          _ = G.s := h_eq
      have h_dropLast_eq : l.dropLast = l.take (l.length - 1) := by simp
      rw [← h_dropLast_eq]
      exact count_dropLast_eq_count_of_not_last hl_nonempty h_last_l_not_s
    rw [h_count_eq]; ring

  -- Conservation at u ≠ s,t: Σ_v net(u,v) = 0
  have h_net_sum_zero (u : V) (hu_s : u ≠ G.s) (hu_t : u ≠ G.t) :
      Finset.sum (Finset.univ : Finset V) (fun v => net u v) = 0 := by
    unfold net
    rw [h_sum_fwd u, h_sum_bwd u, h_map_fst, h_map_snd, h_snd_full]
    have h_count_eq : ((G.s :: l).take (l.length)).count u = l.count u := by
      have h_take : (G.s :: l).take (l.length) = G.s :: (l.take (l.length - 1)) := by simp
      rw [h_take]
      simp [hu_s]
      have h_count_dropLast : (l.take (l.length - 1)).count u = l.count u := by
        have h_last_l_not_u : l.getLast hl_nonempty ≠ u := by
          intro h_eq; apply hu_t
          calc
            G.t = (G.s :: l).getLast (by simp) := by symm; exact hlast_t
            _ = l.getLast hl_nonempty := by simp
            _ = u := h_eq
        have h_dropLast_eq : l.dropLast = l.take (l.length - 1) := by simp
        rw [← h_dropLast_eq]
        exact count_dropLast_eq_count_of_not_last hl_nonempty h_last_l_not_u
      rw [h_count_dropLast]
    rw [h_count_eq]; ring

  -- The augmented flow ψ
  let ψ : Flow V G :=
    { f := λ u v => φ.f u v + δ * net u v
      hcapacity := h_capacity
      hskew_symm := by
        intro u v
        calc
          φ.f u v + δ * net u v = -φ.f v u + δ * net u v := by rw [φ.hskew_symm u v]
          _ = -(φ.f v u + δ * net v u) := by rw [h_net_skew u v]; ring
      hconservation := by
        intro u hu_s hu_t
        calc
          Finset.sum (Finset.univ : Finset V) (fun v => φ.f u v + δ * net u v) =
            Finset.sum (Finset.univ : Finset V) (fun v => φ.f u v) +
            δ * Finset.sum (Finset.univ : Finset V) (fun v => net u v) := by
            simp [Finset.sum_add_distrib, Finset.mul_sum]
          _ = 0 + δ * 0 := by rw [φ.hconservation u hu_s hu_t, h_net_sum_zero u hu_s hu_t]
          _ = 0 := by simp
    }

  -- ψ has strictly larger value
  have h_val_gt : ψ.value > φ.value := by
    unfold ψ Flow.value
    calc
      Finset.sum (Finset.univ : Finset V) (fun v => φ.f G.s v + δ * net G.s v) =
        Finset.sum (Finset.univ : Finset V) (fun v => φ.f G.s v) +
        δ * Finset.sum (Finset.univ : Finset V) (fun v => net G.s v) := by
        simp [Finset.sum_add_distrib, Finset.mul_sum]
      _ = φ.value + δ * 1 := by simp [Flow.value, h_source_net_sum_one]
      _ = φ.value + δ := by ring
      _ > φ.value := by linarith

  intro hMax
  have : ψ.value ≤ φ.value := hMax ψ
  linarith

/-! ## Main theorems -/

theorem Flow.maximal_iff_noAugmentingPath {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (φ : Flow V G) : Flow.isMaximal φ ↔ ¬ Flow.hasAugmentingPath φ := by
  constructor
  · intro hMax; by_contra! hAug; exact Flow.not_isMaximal_of_hasAugmentingPath φ hAug hMax
  · exact Flow.maximal_of_noAugmentingPath φ

theorem Flow.maximal_iff_eq_cutCapacity {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (φ : Flow V G) : Flow.isMaximal φ ↔
    ∃ (S : Finset V), G.s ∈ S ∧ G.t ∉ S ∧ φ.value = Finset.sum S (fun u => Finset.sum (Sᶜ) (fun v => G.c u v)) := by
  constructor
  · intro hMax
    have hNoPath : ¬ Flow.hasAugmentingPath φ := (Flow.maximal_iff_noAugmentingPath.mp hMax)
    let S : Finset V := Finset.filter (fun v => Flow.augmentingPathReachable φ G.s v) Finset.univ
    have hs_S : G.s ∈ S := by
      apply Finset.mem_filter.mpr; exact ⟨Finset.mem_univ _, Relation.ReflTransGen.refl⟩
    have ht_not_S : G.t ∉ S := by
      intro h; have h_reach : Flow.hasAugmentingPath φ := (Finset.mem_filter.mp h).2; exact hNoPath h_reach
    have h_saturated : ∀ u, u ∈ S → ∀ v, v ∉ S → φ.f u v = G.c u v := by
      intro u hu v hv
      have h_reach_u : Flow.augmentingPathReachable φ G.s u := (Finset.mem_filter.mp hu).2
      by_contra! h_lt
      have h_cf_pos : Flow.residualCapacity φ u v > 0 := by unfold Flow.residualCapacity; linarith
      have h_edge : Flow.residualEdge φ u v := h_cf_pos
      have h_reach_v : Flow.augmentingPathReachable φ G.s v := Relation.ReflTransGen.tail h_reach_u h_edge
      apply hv; apply Finset.mem_filter.mpr; exact ⟨Finset.mem_univ _, h_reach_v⟩
    have h_value_eq_cut : φ.value = Finset.sum S (fun u => Finset.sum (Sᶜ) (fun v => G.c u v)) := by
      calc
        φ.value = φ.netFlowAcrossCut S := (φ.netFlow_eq_value S hs_S ht_not_S).symm
        _ = Finset.sum S (fun u => Finset.sum (Sᶜ) (fun v => φ.f u v)) := rfl
        _ = Finset.sum S (fun u => Finset.sum (Sᶜ) (fun v => G.c u v)) := by
          refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => ?_
          rw [h_saturated u hu v (by simpa using hv)]
    exact ⟨S, hs_S, ht_not_S, h_value_eq_cut⟩
  · intro ⟨S, hs, ht, h_eq⟩
    intro ψ
    have hψ_le : ψ.value ≤ Finset.sum S (fun u => Finset.sum (Sᶜ) (fun v => G.c u v)) :=
      Flow.value_le_cut_capacity φ ψ S hs ht
    linarith

theorem Flow.maxFlow_eq_minCut {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (φ : Flow V G) (hMax : Flow.isMaximal φ) :
    ∃ (S : Finset V), G.s ∈ S ∧ G.t ∉ S ∧ φ.value = Finset.sum S (fun u => Finset.sum (Sᶜ) (fun v => G.c u v)) :=
  (Flow.maximal_iff_eq_cutCapacity.mp hMax)

end Chapter26
end CLRS

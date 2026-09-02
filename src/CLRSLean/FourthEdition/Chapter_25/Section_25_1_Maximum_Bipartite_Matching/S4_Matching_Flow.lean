import CLRSLean.Chapter_26.Section_26_3_Bipartite_Matching
import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching.S1_Matching_API

/-!
# S4. Residual edges of the matching flow

Computation of the residual-capacity structure of the §26.3 matching flow:
the flow values on source, left, right, and sink arcs, and the exact
residual-edge characterisations used by the reachability translation.

Main results:

- `matchingToFlow_f_source` / `matchingToFlow_f_right`: unit flow exactly on
  matched vertices
- `matchingToFlow_residualEdge_source` / `matchingToFlow_residualEdge_right`:
  residual edges out of the source and into the sink
- `matchingToFlow_residualEdge_inl_inl`: residual edges inside the vertex
  set are non-matching graph edges forward and matching edges backward
-/
namespace CLRS

open Finset Classical

namespace Matchings

open Chapter26

variable {V : Type*} [Fintype V] [DecidableEq V] {G : BipartiteGraph V}
/-! ## Residual edges of the matching flow -/

/-- The flow out of the source into a left vertex is `1` exactly when the
vertex is matched. -/
lemma matchingToFlow_f_source (M : Matching V G) (l : V) :
    (matchingToFlow M).f (Sum.inr true) (Sum.inl l) =
      if M.IsMatchedLeft l then (1 : ℝ) else 0 := by
  have h1 : (matchingToFlow M).f (Sum.inr true) (Sum.inl l) =
      ((M.edges.filter fun e => e.1 = l).card : ℝ) := by
    simp only [matchingToFlow, matchingFlowFun, matchingFlowFunSummand]
    rw [← Finset.sum_filter]
    simp
  rw [h1]
  by_cases h : M.IsMatchedLeft l
  · simp only [h, ↓reduceIte]
    obtain ⟨r, hr⟩ := h
    have hcard : (M.edges.filter fun e => e.1 = l).card = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨(l, r), Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩⟩
      · simp [hr]
      · intro e he
        simp only [Finset.mem_filter] at he
        exact Prod.ext he.2 (M.h_unique_left l e.2 r (by rw [← he.2, Prod.mk.eta]; exact he.1) hr)
    rw [hcard]
    simp
  · simp only [h, ↓reduceIte]
    have hempty : (M.edges.filter fun e => e.1 = l) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro e he
      intro he1
      exact h ⟨e.2, by rwa [← he1]⟩
    rw [hempty]
    simp

/-- The flow out of a right vertex into the sink is `1` exactly when the
vertex is matched. -/
lemma matchingToFlow_f_right (M : Matching V G) (r : V) :
    (matchingToFlow M).f (Sum.inl r) (Sum.inr false) =
      if M.IsMatchedRight r then (1 : ℝ) else 0 := by
  have h1 : (matchingToFlow M).f (Sum.inl r) (Sum.inr false) =
      ((M.edges.filter fun e => e.2 = r).card : ℝ) := by
    simp only [matchingToFlow, matchingFlowFun, matchingFlowFunSummand]
    rw [← Finset.sum_filter]
    simp
  rw [h1]
  by_cases h : M.IsMatchedRight r
  · simp only [h, ↓reduceIte]
    obtain ⟨l, hl⟩ := h
    have hcard : (M.edges.filter fun e => e.2 = r).card = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨(l, r), Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩⟩
      · simp [hl]
      · intro e he
        simp only [Finset.mem_filter] at he
        exact Prod.ext (M.h_unique_right e.1 l r (by rw [← he.2, Prod.mk.eta]; exact he.1) hl) he.2
    rw [hcard]
    simp
  · simp only [h, ↓reduceIte]
    have hempty : (M.edges.filter fun e => e.2 = r) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro e he
      intro he2
      exact h ⟨e.1, by rwa [← he2]⟩
    rw [hempty]
    simp

/-- The flow across an `L→R` pair is `1` on matching edges, `-1` on reversed
matching edges, and `0` elsewhere. -/
lemma matchingToFlow_f_lr (M : Matching V G) (l r : V) :
    (matchingToFlow M).f (Sum.inl l) (Sum.inl r) =
      (if (l, r) ∈ M.edges then (1 : ℝ) else 0) +
      (if (r, l) ∈ M.edges then (-1 : ℝ) else 0) := by
  simp only [matchingToFlow, matchingFlowFun, matchingFlowFunSummand]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']

/-- A residual edge out of the source reaches exactly the unmatched left
vertices. -/
lemma matchingToFlow_residualEdge_source (M : Matching V G) (l : V) :
    Flow.residualEdge (matchingToFlow M) (Sum.inr true) (Sum.inl l) ↔
      l ∈ G.L ∧ M.IsUnmatchedLeft l := by
  unfold Flow.residualEdge Flow.residualCapacity
  have hc : (toFlowNetwork V G).c (Sum.inr true) (Sum.inl l) =
      if l ∈ G.L then (1 : ℝ) else 0 := by simp [toFlowNetwork, capFunc]
  rw [hc, matchingToFlow_f_source]
  by_cases hl : l ∈ G.L
  · by_cases hm : M.IsMatchedLeft l
    · obtain ⟨r, hr⟩ := hm
      have hm' : M.IsMatchedLeft l := ⟨r, hr⟩
      have hnot : ¬ M.IsUnmatchedLeft l := fun hu => hu r hr
      simp [hl, hm', hnot]
    · simp [hm, Matching.IsMatchedLeft] at hm ⊢
      constructor
      · intro _
        exact ⟨hl, hm⟩
      · intro _
        by_cases hc : ∃ r, (l, r) ∈ M.edges
        · rcases hc with ⟨r', hr'⟩
          exact False.elim (hm r' hr')
        · simp [hc, hl]
  · have hnm : ¬ M.IsMatchedLeft l := fun h => hl (M.mem_L_of_isMatchedLeft h)
    simp [hl, hnm]

/-- The source has no residual edges into the extra vertices. -/
lemma matchingToFlow_not_residualEdge_source_inr (M : Matching V G) (b : Bool) :
    ¬ Flow.residualEdge (matchingToFlow M) (Sum.inr true) (Sum.inr b) := by
  unfold Flow.residualEdge Flow.residualCapacity
  have hc : (toFlowNetwork V G).c (Sum.inr true) (Sum.inr b) = 0 := by
    simp [toFlowNetwork, capFunc]
  have hf : (matchingToFlow M).f (Sum.inr true) (Sum.inr b) = 0 := by
    simp [matchingToFlow, matchingFlowFun, matchingFlowFunSummand]
  rw [hc, hf]
  norm_num

/-- Residual edges inside the vertex set are exactly the non-matching graph
edges in the forward direction and the matching edges in the backward
direction. -/
lemma matchingToFlow_residualEdge_inl_inl (M : Matching V G) (u v : V) :
    Flow.residualEdge (matchingToFlow M) (Sum.inl u) (Sum.inl v) ↔
      ((u, v) ∈ G.E ∧ (u, v) ∉ M.edges) ∨ (v, u) ∈ M.edges := by
  unfold Flow.residualEdge Flow.residualCapacity
  have hc : (toFlowNetwork V G).c (Sum.inl u) (Sum.inl v) =
      if (u, v) ∈ G.E then (1 : ℝ) else 0 := by simp [toFlowNetwork, capFunc]
  rw [hc, matchingToFlow_f_lr]
  by_cases huv : (u, v) ∈ M.edges
  · have hnv : (v, u) ∉ M.edges := fun hcon =>
      G.not_mem_L_of_mem_R (G.hE_subset _ (M.h_subset huv)).2 (G.hE_subset _ (M.h_subset hcon)).1
    have hE : (u, v) ∈ G.E := M.h_subset huv
    simp [huv, hnv, hE]
  · by_cases hvu : (v, u) ∈ M.edges
    · have hE : (u, v) ∉ G.E := fun hcon =>
        G.not_mem_L_of_mem_R (G.hE_subset _ hcon).2 (G.hE_subset _ (M.h_subset hvu)).1
      simp [huv, hvu, hE]
    · by_cases hE : (u, v) ∈ G.E
      · simp [huv, hvu, hE]
      · simp [huv, hvu, hE]

/-- A residual edge into the sink leaves exactly the unmatched right
vertices. -/
lemma matchingToFlow_residualEdge_right (M : Matching V G) (r : V) :
    Flow.residualEdge (matchingToFlow M) (Sum.inl r) (Sum.inr false) ↔
      r ∈ G.R ∧ M.IsUnmatchedRight r := by
  unfold Flow.residualEdge Flow.residualCapacity
  have hc : (toFlowNetwork V G).c (Sum.inl r) (Sum.inr false) =
      if r ∈ G.R then (1 : ℝ) else 0 := by simp [toFlowNetwork, capFunc]
  rw [hc, matchingToFlow_f_right]
  by_cases hr : r ∈ G.R
  · by_cases hm : M.IsMatchedRight r
    · obtain ⟨l, hl⟩ := hm
      have hm' : M.IsMatchedRight r := ⟨l, hl⟩
      have hnot : ¬ M.IsUnmatchedRight r := fun hu => hu l hl
      simp [hr, hm', hnot]
    · simp [hm, Matching.IsMatchedRight] at hm ⊢
      constructor
      · intro _
        exact ⟨hr, hm⟩
      · intro _
        by_cases hc : ∃ l, (l, r) ∈ M.edges
        · rcases hc with ⟨l', hl'⟩
          exact False.elim (hm l' hl')
        · simp [hc, hr]
  · have hnm : ¬ M.IsMatchedRight r := fun h => hr (M.mem_R_of_isMatchedRight h)
    simp [hr, hnm]

/-- Left vertices have no residual edge into the sink. -/
lemma matchingToFlow_not_residualEdge_left_sink (M : Matching V G) {l : V}
    (hl : l ∈ G.L) :
    ¬ Flow.residualEdge (matchingToFlow M) (Sum.inl l) (Sum.inr false) := by
  unfold Flow.residualEdge Flow.residualCapacity
  have hnr : l ∉ G.R := G.not_mem_R_of_mem_L hl
  have hc : (toFlowNetwork V G).c (Sum.inl l) (Sum.inr false) = 0 := by
    simp [toFlowNetwork, capFunc, hnr]
  have hf : (matchingToFlow M).f (Sum.inl l) (Sum.inr false) = 0 := by
    have h1 : (matchingToFlow M).f (Sum.inl l) (Sum.inr false) =
        ((M.edges.filter fun e => e.2 = l).card : ℝ) := by
      simp only [matchingToFlow, matchingFlowFun, matchingFlowFunSummand]
      rw [← Finset.sum_filter]
      simp
    have hempty : (M.edges.filter fun e => e.2 = l) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro e he he2
      have := M.right_mem_R he
      rw [he2] at this
      exact hnr this
    rw [h1, hempty]
    simp
  rw [hc, hf]
  norm_num

/-- Right vertices have no residual edge into the source. -/
lemma matchingToFlow_not_residualEdge_right_source (M : Matching V G) {r : V}
    (hr : r ∈ G.R) :
    ¬ Flow.residualEdge (matchingToFlow M) (Sum.inl r) (Sum.inr true) := by
  unfold Flow.residualEdge Flow.residualCapacity
  have hnl : r ∉ G.L := G.not_mem_L_of_mem_R hr
  have hc : (toFlowNetwork V G).c (Sum.inl r) (Sum.inr true) = 0 := by
    simp [toFlowNetwork, capFunc]
  have hf : (matchingToFlow M).f (Sum.inl r) (Sum.inr true) = 0 := by
    have hskew := (matchingToFlow M).hskew_symm (Sum.inl r) (Sum.inr true)
    rw [matchingToFlow_f_source] at hskew
    have hnm : ¬ M.IsMatchedLeft r := fun h => hnl (M.mem_L_of_isMatchedLeft h)
    simp [hnm] at hskew
    linarith
  rw [hc, hf]
  norm_num

end Matchings

end CLRS

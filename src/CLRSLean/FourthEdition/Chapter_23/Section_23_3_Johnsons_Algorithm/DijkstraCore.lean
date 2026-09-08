import CLRSLean.FourthEdition.Chapter_23.Section_23_3_Johnsons_Algorithm

/-!
# Dijkstra settlement with an explicit minimum

This proof isolates the standard invariant update from the native classical
minimum selector. A counted queue may supply any actual unsettled minimum,
including its own deterministic tie choice.
-/

namespace CLRS.Chapter24.WeightedGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : WeightedGraph V)

/-- Settle the chosen vertex and relax every outgoing edge. -/
noncomputable def dijkstraSettle (st : DijkstraState V) (u : V) : DijkstraState V :=
  { S := insert u st.S
    d := fun v => if (u, v) ∈ G.edges then min (st.d v) (st.d u + (G.w u v : WithTop ℝ)) else st.d v }

/-- Any unsettled minimum preserves the native Dijkstra invariant. -/
theorem dijkstraSettle_invariant (hnn : G.Nonneg) (s : V) (δ : V → WithTop ℝ)
    (hδ : ∀ v, G.IsShortestDist s v (δ v))
    (st : DijkstraState V) (h_inv : DijkstraInvariant G hnn s δ hδ st)
    (u : V) (hu_notin_S : u ∉ st.S) (hu_min_all : ∀ y, y ∉ st.S → st.d u ≤ st.d y) :
    DijkstraInvariant G hnn s δ hδ (G.dijkstraSettle st u) := by
  have h_du_eq_δu : st.d u = δ u :=
    G.extractMin_correct_of_invariant hnn s δ hδ st h_inv u hu_notin_S hu_min_all
  let S' := insert u st.S
  let d' := fun v => if (u, v) ∈ G.edges then min (st.d v) (st.d u + (G.w u v : WithTop ℝ)) else st.d v
  have h_s_S' : s ∈ S' := Finset.mem_insert_of_mem h_inv.hsS
  have h_settled' : ∀ x ∈ S', d' x = δ x := by
    intro x hx
    rcases Finset.mem_insert.1 hx with (he | hx_S)
    · subst x
      -- x = u
      dsimp [d']
      by_cases h_edge_uu : (u, u) ∈ G.edges
      · have h_nonneg_w : 0 ≤ G.w u u := hnn u u h_edge_uu
        have h_add : st.d u ≤ st.d u + (G.w u u : WithTop ℝ) := by
          have h_nonneg_w' : (0 : WithTop ℝ) ≤ (G.w u u : WithTop ℝ) := by exact_mod_cast h_nonneg_w
          exact le_add_of_nonneg_right h_nonneg_w'
        simp [h_edge_uu]
        have h_min_eq : min (st.d u) (st.d u + (G.w u u : WithTop ℝ)) = st.d u :=
          min_eq_left h_add
        rw [h_min_eq, h_du_eq_δu]
      · simp [h_edge_uu, h_du_eq_δu]
    · -- x ∈ st.S
      have h_dx_eq_δx : st.d x = δ x := h_inv.hsettled x hx_S
      dsimp [d']
      by_cases h_edge_ux : (u, x) ∈ G.edges
      · have h_ineq : δ x ≤ δ u + (G.w u x : WithTop ℝ) :=
          G.delta_le_delta_add_edge hnn s δ hδ u x h_edge_ux
        have h_add : st.d x ≤ st.d u + (G.w u x : WithTop ℝ) := by
          rw [h_dx_eq_δx, h_du_eq_δu]
          exact h_ineq
        simp [h_edge_ux]
        have h_min_eq : min (st.d x) (st.d u + (G.w u x : WithTop ℝ)) = st.d x :=
          min_eq_left h_add
        rw [h_min_eq, h_dx_eq_δx]
      · simp [h_edge_ux, h_dx_eq_δx]
  have h_htent' : ∀ y ∉ S', ∀ x ∈ S', (x, y) ∈ G.edges → d' y ≤ δ x + (G.w x y : WithTop ℝ) := by
    intro y hy_S' x hx_S' h_edge
    have hy_notin_S : y ∉ st.S := by
      intro hy_S; apply hy_S'; simp [S', hy_S]
    rcases Finset.mem_insert.1 hx_S' with (he | hx_S)
    · subst x
      -- x = u
      dsimp [d']
      have h_edge_uy : (u, y) ∈ G.edges := h_edge
      calc
        (if (u, y) ∈ G.edges then min (st.d y) (st.d u + (G.w u y : WithTop ℝ)) else st.d y)
            = min (st.d y) (st.d u + (G.w u y : WithTop ℝ)) := by simp [h_edge_uy]
        _ ≤ st.d u + (G.w u y : WithTop ℝ) := min_le_right _ _
        _ = δ u + (G.w u y : WithTop ℝ) := by rw [h_du_eq_δu]
    · -- x ∈ st.S
      have h_old_htent : st.d y ≤ δ x + (G.w x y : WithTop ℝ) :=
        h_inv.htent y hy_notin_S x hx_S h_edge
      dsimp [d']
      by_cases h_edge_uy : (u, y) ∈ G.edges
      · calc
          (if (u, y) ∈ G.edges then min (st.d y) (st.d u + (G.w u y : WithTop ℝ)) else st.d y)
              = min (st.d y) (st.d u + (G.w u y : WithTop ℝ)) := by simp [h_edge_uy]
          _ ≤ st.d y := min_le_left _ _
          _ ≤ δ x + (G.w x y : WithTop ℝ) := h_old_htent
      · simp [h_edge_uy, h_old_htent]
  have h_valid' : ∀ y ∉ S', δ y ≤ d' y := by
    intro y hy_S'
    have hy_notin_S : y ∉ st.S := by
      intro hy_S; apply hy_S'; simp [S', hy_S]
    have h_old_valid : δ y ≤ st.d y := h_inv.hvalid y hy_notin_S
    by_cases h_edge_uy : (u, y) ∈ G.edges
    · have h_ineq : δ y ≤ δ u + (G.w u y : WithTop ℝ) :=
        G.delta_le_delta_add_edge hnn s δ hδ u y h_edge_uy
      have h_hvalid_via_add : δ y ≤ st.d u + (G.w u y : WithTop ℝ) := by
        rw [h_du_eq_δu]
        exact h_ineq
      simpa [d', h_edge_uy] using le_min_iff.mpr ⟨h_old_valid, h_hvalid_via_add⟩
    · simpa [d', h_edge_uy] using h_old_valid
  exact ⟨h_s_S', h_settled', h_htent', h_valid'⟩

end CLRS.Chapter24.WeightedGraph

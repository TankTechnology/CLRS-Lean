import CLRSLean.Chapter_26.Section_26_3_Bipartite_Matching
import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching.S2_Alternating_Paths
import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching.S3_Simple_Paths
import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching.S4_Matching_Flow

/-!
# S5. From residual reachability to graph augmenting paths

The translation from §26.3 residual reachability to explicit §25.1
augmenting paths: the well-founded `translation_inner` walk-to-path
construction and the headline `augmentingPath_of_hasAugmentingPath`.

Main results:

- `translation_inner`: a vertex-simple residual walk from an embedded left
  vertex to the sink induces an alternating path
- `augmentingPath_of_hasAugmentingPath`: a residual augmenting path of the
  matching flow induces a graph augmenting path
-/
namespace CLRS

open Finset Classical

namespace Matchings

open Chapter26

variable {V : Type*} [Fintype V] [DecidableEq V] {G : BipartiteGraph V}
/-! ## From residual reachability to graph augmenting paths -/

/-- **Translation lemma** (auxiliary, well-founded on the walk length): a
vertex-simple residual walk from an `inl`-embedded left vertex to the sink
induces an alternating path in the bipartite graph.  The conclusion lists
exactly the `IsAugmentingPath` fields except the (unneeded here) start
unmatched condition, plus a membership tracker used for the no-repeat
arguments. -/
theorem translation_inner (M : Matching V G) (l : V) (hl : l ∈ G.L) :
    ∀ (w : List (V ⊕ Bool)), w.IsChain (Flow.residualEdge (matchingToFlow M)) →
      w.Nodup → w[0]? = some (Sum.inl l) → w[w.length - 1]? = some (Sum.inr false) →
      Sum.inr true ∉ w →
      ∃ p : List V, p.Nodup ∧ Even p.length ∧ 2 ≤ p.length ∧ p.head? = some l ∧
        (∀ r₂ : V, p.getLast? = some r₂ → r₂ ∈ G.R ∧ M.IsUnmatchedRight r₂) ∧
        (∀ e ∈ (altEdges p).1, e ∈ G.E ∧ e ∉ M.edges) ∧
        (∀ e ∈ (altEdges p).2, e ∈ M.edges) ∧
        (∀ v ∈ p, Sum.inl v ∈ w) := by
  suffices aux : ∀ (n : ℕ) (l : V) (hl : l ∈ G.L) (w : List (V ⊕ Bool)),
      w.length ≤ n → w.IsChain (Flow.residualEdge (matchingToFlow M)) →
      w.Nodup → w[0]? = some (Sum.inl l) → w[w.length - 1]? = some (Sum.inr false) →
      Sum.inr true ∉ w →
      ∃ p : List V, p.Nodup ∧ Even p.length ∧ 2 ≤ p.length ∧ p.head? = some l ∧
        (∀ r₂ : V, p.getLast? = some r₂ → r₂ ∈ G.R ∧ M.IsUnmatchedRight r₂) ∧
        (∀ e ∈ (altEdges p).1, e ∈ G.E ∧ e ∉ M.edges) ∧
        (∀ e ∈ (altEdges p).2, e ∈ M.edges) ∧
        (∀ v ∈ p, Sum.inl v ∈ w) from
    fun w hw hnd h0 hlst hns => aux w.length l hl w le_rfl hw hnd h0 hlst hns
  intro n
  induction n with
  | zero =>
    intro l hl w hlen hw hnd h0 hlst hns
    simp at hlen
    subst hlen
    simp at h0
  | succ n ih =>
    intro l hl w hlen hw hnd h0 hlst hns
    cases w with
    | nil => simp at h0
    | cons x rest =>
      simp only [List.length_cons, List.getElem?_cons_zero, Option.some.injEq] at h0
      subst h0
      cases rest with
      | nil =>
        simp only [List.length_cons, List.length_nil, Nat.add_zero, Nat.sub_self,
          List.getElem?_cons_zero] at hlst
        simp at hlst
      | cons y rest' =>
        have hstep0 : Flow.residualEdge (matchingToFlow M) (Sum.inl l) y := by
          have hc := (List.isChain_iff_getElem.mp hw) 0 (by simp)
          simpa using hc
        cases y with
        | inl r =>
          have hiff := (matchingToFlow_residualEdge_inl_inl M l r).mp hstep0
          rcases hiff with ⟨hE, hnotM⟩ | hcon
          · have hr : r ∈ G.R := (G.hE_subset _ hE).2
            cases rest' with
            | nil =>
              simp only [List.length_cons, List.length_nil] at hlst
              norm_num at hlst
              simp at hlst
            | cons z rest'' =>
              have hstep1 : Flow.residualEdge (matchingToFlow M) (Sum.inl r) z := by
                have hc := (List.isChain_iff_getElem.mp hw) 1 (by simp)
                simpa using hc
              cases z with
              | inl l₂ =>
                have hiff1 := (matchingToFlow_residualEdge_inl_inl M r l₂).mp hstep1
                rcases hiff1 with ⟨hE1, -⟩ | hback
                · exact (G.not_mem_L_of_mem_R hr (G.hE_subset _ hE1).1).elim
                · have hl₂ : l₂ ∈ G.L := (G.hE_subset _ (M.h_subset hback)).1
                  -- recurse on the tail `inl l₂ :: rest''`
                  have hw₂len : (Sum.inl l₂ :: rest'').length ≤ n := by
                    have hlen' : (Sum.inl l :: Sum.inl r :: Sum.inl l₂ :: rest'').length =
                        (Sum.inl l₂ :: rest'').length + 2 := by simp
                    rw [hlen'] at hlen
                    omega
                  have hw₂chain : (Sum.inl l₂ :: rest'').IsChain
                      (Flow.residualEdge (matchingToFlow M)) := by
                    rw [List.isChain_iff_getElem] at hw ⊢
                    intro i hi
                    have := hw (i + 2) (by simp at hi ⊢; omega)
                    simpa using this
                  have hw₂nodup : (Sum.inl l₂ :: rest'').Nodup := by
                    have h1 := hnd
                    rw [List.nodup_cons] at h1
                    exact h1.2.of_cons
                  have hw₂0 : (Sum.inl l₂ :: rest'')[0]? = some (Sum.inl l₂) := rfl
                  have hw₂last : (Sum.inl l₂ :: rest'')[(Sum.inl l₂ :: rest'').length - 1]? =
                      some (Sum.inr false) := by
                    have h1 : (Sum.inl l :: Sum.inl r :: Sum.inl l₂ :: rest'').length =
                        (Sum.inl l₂ :: rest'').length + 2 := by simp
                    have h2 : (Sum.inl l :: Sum.inl r :: Sum.inl l₂ :: rest'')[
                        (Sum.inl l :: Sum.inl r :: Sum.inl l₂ :: rest'').length - 1]? =
                        (Sum.inl l₂ :: rest'')[(Sum.inl l₂ :: rest'').length - 1]? := by
                      rw [h1]
                      simp [List.getElem?_cons_succ, Nat.add_sub_cancel]
                    rw [h2] at hlst
                    exact hlst
                  have hw₂ns : Sum.inr true ∉ Sum.inl l₂ :: rest'' := by
                    intro hcon
                    exact hns (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hcon))
                  obtain ⟨p', hp'n, hp'e, hp'ge, hp'head, hp'last, hp'fw, hp'bw, hp'mem⟩ :=
                    ih l₂ hl₂ (Sum.inl l₂ :: rest'') hw₂len hw₂chain hw₂nodup hw₂0 hw₂last hw₂ns
                  -- assemble `l :: r :: p'`
                  have hp'ne : p' ≠ [] := fun h => by simp [h] at hp'ge
                  obtain ⟨l₃, p'', hp'⟩ := List.exists_cons_of_ne_nil hp'ne
                  have hl₃ : l₃ = l₂ := by
                    rw [hp'] at hp'head
                    simp at hp'head
                    exact hp'head
                  subst l₃
                  subst p'
                  refine ⟨l :: r :: l₂ :: p'', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                  · have hlr : l ≠ r := fun h => G.not_mem_R_of_mem_L hl (h ▸ hr)
                    have hlnotin : l ∉ r :: l₂ :: p'' := by
                      intro hcon
                      simp only [List.mem_cons] at hcon
                      rcases hcon with hcon | hcon'
                      · exact hlr hcon
                      · rcases hcon' with hcon' | hcon'
                        · have h2 := hnd
                          rw [List.nodup_cons] at h2
                          exact h2.1 (by simpa [hcon'])
                        · have h1 := hp'mem l (List.mem_cons_of_mem l₂ hcon')
                          have h2 := hnd
                          rw [List.nodup_cons] at h2
                          exact h2.1 (List.mem_cons_of_mem _ h1)
                    have hrnotin : r ∉ l₂ :: p'' := by
                      intro hcon
                      simp only [List.mem_cons] at hcon
                      rcases hcon with hcon | hcon'
                      · exact G.not_mem_L_of_mem_R hr (hcon ▸ hl₂)
                      · have h1 := hp'mem r (List.mem_cons_of_mem l₂ hcon')
                        have h2 := hnd
                        rw [List.nodup_cons] at h2
                        obtain ⟨-, h2⟩ := h2
                        rw [List.nodup_cons] at h2
                        exact h2.1 h1
                    exact List.nodup_cons.mpr ⟨hlnotin,
                      List.nodup_cons.mpr ⟨hrnotin, hp'n⟩⟩
                  · simp at hp'e ⊢
                    exact hp'e.add (by norm_num : Even 2)
                  · simp [hp'ge]
                  · rfl
                  · intro r₂ hr₂
                    rw [List.getLast?_cons_cons, List.getLast?_cons_cons] at hr₂
                    exact hp'last r₂ hr₂
                  · intro e he
                    rw [altEdges.eq_def] at he
                    simp only [List.mem_cons] at he
                    rcases he with he | he
                    · rw [he]
                      exact ⟨hE, hnotM⟩
                    · exact hp'fw e he
                  · intro e he
                    rw [altEdges.eq_def] at he
                    simp only [List.mem_cons] at he
                    rcases he with he | he
                    · rw [he]
                      exact hback
                    · exact hp'bw e he
                  · intro v hv
                    simp only [List.mem_cons] at hv
                    rcases hv with rfl | rfl | hv
                    · exact List.mem_cons_self
                    · exact List.mem_cons_of_mem _ List.mem_cons_self
                    · rcases hv with rfl | hv
                      · exact List.mem_cons_of_mem _
                          (List.mem_cons_of_mem _ List.mem_cons_self)
                      · exact List.mem_cons_of_mem _
                          (List.mem_cons_of_mem _ (hp'mem v (List.mem_cons_of_mem _ hv)))
              | inr b =>
                cases b with
                | true => exact absurd (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) hns
                | false =>
                  have hr_un := (matchingToFlow_residualEdge_right M r).mp hstep1
                  -- the sink must be the last vertex: `rest'' = []`
                  have hrest'' : rest'' = [] := by
                    cases rest'' with
                    | nil => rfl
                    | cons u rest''' =>
                      have hlast' : (Sum.inl l :: Sum.inl r :: Sum.inr false :: u :: rest''')[
                          (Sum.inl l :: Sum.inl r :: Sum.inr false :: u :: rest''').length - 1]? =
                          some (Sum.inr false) := hlst
                      have hget : (Sum.inl l :: Sum.inl r :: Sum.inr false :: u :: rest''')[
                          (Sum.inl l :: Sum.inl r :: Sum.inr false :: u :: rest''').length - 1] =
                          Sum.inr false := by
                        rw [List.getElem?_eq_getElem (by simp)] at hlast'
                        exact Option.some.inj hlast'
                      have hdup' : (Sum.inl l :: Sum.inl r :: Sum.inr false :: u :: rest''')[2] =
                          Sum.inr false := by simp
                      have hinj := List.Nodup.getElem_inj_iff hnd (i := 2) (hi := by simp)
                        (j := (Sum.inl l :: Sum.inl r :: Sum.inr false :: u :: rest''').length - 1)
                        (hj := by simp)
                      rw [hdup', hget] at hinj
                      rw [show (2 = (Sum.inl l :: Sum.inl r :: Sum.inr false :: u :: rest''').length - 1) =
                          False by simp] at hinj
                      exact False.elim (hinj.mp rfl)
                  subst hrest''
                  refine ⟨[l, r], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                  · exact List.nodup_cons.mpr ⟨by
                      simp; exact fun h => G.not_mem_R_of_mem_L hl (h ▸ hr),
                      List.nodup_singleton _⟩
                  · norm_num
                  · norm_num
                  · rfl
                  · intro r₂ hr₂
                    rw [List.getLast?_cons_cons] at hr₂
                    simp at hr₂
                    subst hr₂
                    exact hr_un
                  · intro e he
                    simp [altEdges] at he
                    simpa [he] using ⟨hE, hnotM⟩
                  · intro e he
                    simp [altEdges] at he
                  · intro v hv
                    simp at hv
                    rcases hv with rfl | rfl
                    · exact List.mem_cons_self
                    · exact List.mem_cons_of_mem _ List.mem_cons_self
          · exact (G.not_mem_R_of_mem_L hl (G.hE_subset _ (M.h_subset hcon)).2).elim
        | inr b =>
          cases b with
          | true => exact absurd (List.mem_cons_of_mem _ List.mem_cons_self) hns
          | false => exact absurd hstep0 (matchingToFlow_not_residualEdge_left_sink M hl)

/-- **Translation lemma**: a residual augmenting path in the §26.3 flow
network of a bipartite graph induces an augmenting path for the matching in
the graph itself. -/
theorem augmentingPath_of_hasAugmentingPath (M : Matching V G)
    (hpath : (matchingToFlow M).hasAugmentingPath) :
    ∃ p : List V, IsAugmentingPath G M p := by
  have hne : Sum.inr true ≠ (Sum.inr false : V ⊕ Bool) := by simp
  obtain ⟨q, hqchain, hqnodup, hqlen, hq0, hqend⟩ :=
    exists_nodup_path_of_reflTransGen hpath hne
  cases q with
  | nil => simp at hq0
  | cons x rest =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hq0
    subst hq0
    cases rest with
    | nil => simp at hqlen
    | cons y rest' =>
      have hstep0 : Flow.residualEdge (matchingToFlow M) (Sum.inr true) y := by
        have hc := (List.isChain_iff_getElem.mp hqchain) 0 (by simp)
        simpa [toFlowNetwork] using hc
      cases y with
      | inl l =>
        have ⟨hl, hlu⟩ := (matchingToFlow_residualEdge_source M l).mp hstep0
        have hw : (Sum.inl l :: rest').IsChain (Flow.residualEdge (matchingToFlow M)) := by
          rw [List.isChain_iff_getElem] at hqchain ⊢
          intro i hi
          have := hqchain (i + 1) (by simp at hi ⊢; omega)
          simpa [toFlowNetwork] using this
        have hwnd : (Sum.inl l :: rest').Nodup := hqnodup.of_cons
        have hw0 : (Sum.inl l :: rest')[0]? = some (Sum.inl l) := rfl
        have hwlast : (Sum.inl l :: rest')[(Sum.inl l :: rest').length - 1]? =
            some (Sum.inr false) := by
          have h1 : (Sum.inr true :: Sum.inl l :: rest')[(Sum.inr true :: Sum.inl l ::
              rest').length - 1]? = (Sum.inl l :: rest')[(Sum.inl l :: rest').length - 1]? := by
            simp [List.getElem?_cons_succ, List.length_cons]
          rw [show (toFlowNetwork V G).s = Sum.inr true by rfl,
            show (toFlowNetwork V G).t = Sum.inr false by rfl] at hqend
          rw [h1] at hqend
          exact hqend
        have hwns : Sum.inr true ∉ Sum.inl l :: rest' := by
          have h1 := hqnodup
          rw [List.nodup_cons] at h1
          exact h1.1
        obtain ⟨p, hpn, hpe, hpge, hphead, hplast, hpfw, hpbw, -⟩ :=
          translation_inner M l hl (Sum.inl l :: rest') hw hwnd hw0 hwlast hwns
        have hpne : p ≠ [] := fun h => by simp [h] at hpge
        refine ⟨p, hpn, hpe, hpge, ?_, ?_, ?_, ?_, hpfw, hpbw⟩
        · intro h
          have h1 : p.head h = l := by
            have h2 : p.head? = some (p.head h) := List.head?_eq_some_head _
            rw [hphead] at h2
            exact (Option.some.inj h2).symm
          rw [h1]
          exact hl
        · intro h r₂
          have h1 : p.head h = l := by
            have h2 : p.head? = some (p.head h) := List.head?_eq_some_head _
            rw [hphead] at h2
            exact (Option.some.inj h2).symm
          rw [h1]
          exact hlu r₂
        · intro h
          have h1 : p.getLast? = some (p.getLast h) := List.getLast?_eq_some_getLast hpne
          obtain ⟨hr, -⟩ := hplast _ h1
          exact hr
        · intro h l₂
          have h1 : p.getLast? = some (p.getLast h) := List.getLast?_eq_some_getLast hpne
          obtain ⟨-, hu⟩ := hplast _ h1
          exact hu l₂
      | inr b => exact absurd hstep0 (matchingToFlow_not_residualEdge_source_inr M b)

end Matchings

end CLRS

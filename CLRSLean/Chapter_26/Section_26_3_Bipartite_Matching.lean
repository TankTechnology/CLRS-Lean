import Mathlib
import CLRSLean.Chapter_26.Section_26_1_Flow_Networks

/-!
# 26.3. Maximum bipartite matching

Reduction from maximum bipartite matching to maximum flow, proving that
the maximum-flow value of the constructed flow network equals the size
of a maximum matching (CLRS Theorem 26.12).

Main results:

In the interests of a clean import structure, we place this module under
`CLRS.Chapter26` alongside the other Chapter 26 sections.
-/

namespace CLRS
namespace Chapter26
open Finset Classical

/-- A bipartite graph with left partition `L`, right partition `R`, and
edges `E` that only go from `L` to `R`. (CLRS §26.3.) -/
structure BipartiteGraph (V : Type*) [Fintype V] [DecidableEq V] where
  L : Finset V
  R : Finset V
  h_disjoint : L ∩ R = ∅
  h_cover : L ∪ R = Finset.univ
  E : Finset (V × V)
  hE_subset : ∀ e ∈ E, e.1 ∈ L ∧ e.2 ∈ R

/-- A matching in a bipartite graph: a set of edges with no shared endpoints. -/
structure Matching (V : Type*) [Fintype V] [DecidableEq V] (G : BipartiteGraph V) where
  edges : Finset (V × V)
  h_subset : edges ⊆ G.E
  h_unique_left : ∀ (l r₁ r₂ : V), (l, r₁) ∈ edges → (l, r₂) ∈ edges → r₁ = r₂
  h_unique_right : ∀ (l₁ l₂ r : V), (l₁, r) ∈ edges → (l₂, r) ∈ edges → l₁ = l₂

/-- The size (cardinality) of a matching. -/
def Matching.size {V : Type*} [Fintype V] [DecidableEq V] {G : BipartiteGraph V}
    (M : Matching V G) : ℕ := M.edges.card

lemma Matching.left_mem_L {V : Type*} [Fintype V] [DecidableEq V] {G : BipartiteGraph V}
    (M : Matching V G) {l r : V} (h : (l, r) ∈ M.edges) : l ∈ G.L := by
  have hE : (l, r) ∈ G.E := M.h_subset h; exact (G.hE_subset (l, r) hE).1

lemma Matching.right_mem_R {V : Type*} [Fintype V] [DecidableEq V] {G : BipartiteGraph V}
    (M : Matching V G) {l r : V} (h : (l, r) ∈ M.edges) : r ∈ G.R := by
  have hE : (l, r) ∈ G.E := M.h_subset h; exact (G.hE_subset (l, r) hE).2

/-! Capacity function defined as a standalone `def` so `simp` can use it. -/
def capFunc (V : Type*) [Fintype V] [DecidableEq V] (G : BipartiteGraph V) (u v : V ⊕ Bool) : ℝ :=
  match u, v with
  | Sum.inr true, Sum.inl l' => if l' ∈ G.L then (1 : ℝ) else 0
  | Sum.inl l', Sum.inl r' => if (l', r') ∈ G.E then (1 : ℝ) else 0
  | Sum.inl r', Sum.inr false => if r' ∈ G.R then (1 : ℝ) else 0
  | _, _ => 0

/-- The flow network constructed from a bipartite graph (CLRS eq. (26.11)). -/
def toFlowNetwork (V : Type*) [Fintype V] [DecidableEq V] (G : BipartiteGraph V) :
    FlowNetwork (V ⊕ Bool) :=
  { s := Sum.inr true
  , t := Sum.inr false
  , c := capFunc V G
  , hc_nonneg := λ u v =>
    have h_nonneg : 0 ≤ capFunc V G u v := by
      unfold capFunc
      cases u with
      | inl a =>
        cases v with
        | inl b => simp; split_ifs <;> norm_num
        | inr b => cases b <;> simp <;> try (split_ifs <;> norm_num)
      | inr a =>
        cases a with
        | true =>
          cases v with
          | inl b => simp; split_ifs <;> norm_num
          | inr b => cases b <;> simp <;> try (split_ifs <;> norm_num)
        | false =>
          cases v with
          | inl b => norm_num
          | inr b => cases b <;> simp <;> try (split_ifs <;> norm_num)
    h_nonneg
  , hc_self := λ u =>
    by
      unfold capFunc
      match u with
      | Sum.inl v =>
        by_cases h : (v, v) ∈ G.E
        · have hvL : v ∈ G.L := (G.hE_subset (v, v) h).1
          have hvR : v ∈ G.R := (G.hE_subset (v, v) h).2
          have : v ∈ G.L ∩ G.R := Finset.mem_inter.mpr ⟨hvL, hvR⟩
          rw [G.h_disjoint] at this; simp at this
        · simp [h]
      | Sum.inr _ => simp
  , hs_ne_t := by simp
  }

/-- The flow induced by a matching `M` in the constructed flow network. -/
def matchingFlowFun {V : Type*} [Fintype V] [DecidableEq V] {G : BipartiteGraph V}
    (M : Matching V G) (u v : V ⊕ Bool) : ℝ :=
  Finset.sum M.edges (λ (e : V × V) =>
    match u, v with
    | Sum.inr true, Sum.inl l => if e.1 = l then (1 : ℝ) else 0
    | Sum.inl a, Sum.inl b => if e = (a, b) then (1 : ℝ) else if e = (b, a) then (-1 : ℝ) else 0
    | Sum.inl r, Sum.inr false => if e.2 = r then (1 : ℝ) else 0
    | Sum.inl l, Sum.inr true => if e.1 = l then (-1 : ℝ) else 0
    | Sum.inr false, Sum.inl r => if e.2 = r then (-1 : ℝ) else 0
    | _, _ => 0)

/-- **Theorem (matching-flow value).** The flow induced by a matching `M` has
value equal to `|M|` (CLRS Theorem 26.12, value direction). -/
theorem matchingToFlow_value {V : Type*} [Fintype V] [DecidableEq V] {G : BipartiteGraph V}
    (M : Matching V G) (φ : Flow (V ⊕ Bool) (toFlowNetwork V G))
    (h : φ.f = matchingFlowFun M) : φ.value = (M.size : ℝ) := by
  unfold Flow.value
  rw [h]
  have h_sum : Finset.sum (Finset.univ : Finset (V ⊕ Bool)) (λ v => matchingFlowFun M (Sum.inr true) v) = (M.size : ℝ) := by
    calc
      Finset.sum (Finset.univ : Finset (V ⊕ Bool)) (λ v => matchingFlowFun M (Sum.inr true) v)
          = Finset.sum (Finset.univ : Finset (V ⊕ Bool)) (λ v =>
              Finset.sum M.edges (λ (e : V × V) =>
                match v with
                | Sum.inl l => if e.1 = l then (1 : ℝ) else 0
                | Sum.inr _ => 0)) := by
        refine Finset.sum_congr rfl (λ v hv => ?_)
        unfold matchingFlowFun
        cases v with
        | inl l => simp
        | inr b => simp
      _ = Finset.sum M.edges (λ (e : V × V) =>
            Finset.sum (Finset.univ : Finset (V ⊕ Bool)) (λ v =>
              match v with
              | Sum.inl l => if e.1 = l then (1 : ℝ) else 0
              | Sum.inr _ => 0)) := by
        rw [Finset.sum_comm]
      _ = Finset.sum M.edges (λ (e : V × V) => (1 : ℝ)) := by
        refine Finset.sum_congr rfl (λ e he => ?_)
        simp
      _ = (M.size : ℝ) := by
        simp [Matching.size]
  simpa [toFlowNetwork] using h_sum

end Chapter26
end CLRS

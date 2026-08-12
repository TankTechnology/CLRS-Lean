import Mathlib
import CLRSLean.FourthEdition.Chapter_24.Section_24_1_Flow_Networks
import CLRSLean.FourthEdition.Chapter_24.Section_24_2_Edmonds_Karp.Ford_Fulkerson_Augmentation

/-!
# 24.3. Maximum bipartite matching

This file formalizes the bipartite-to-flow-network reduction of CLRS §24.3
and proves Theorem 24.12: the maximum matching size equals the maximum flow
value in the unit-capacity network.  It constructs the feasible flow induced
by every matching, recovers a matching from every integral flow, iterates
augmentation from the zero flow to obtain an integral maximum flow, and
combines the two directions.

Main results:

- `BipartiteGraph`, `Matching`, and `Matching.size`
- `capFunc` and `toFlowNetwork`
- `matchingFlowFun` and `matchingFlowFunSummand`
- `matchingToFlow` and `matchingToFlow_value`: the feasible flow induced by a
  matching has value `|M|`
- `Flow.IsIntegral`, `matchingOfIntegralFlow`, and
  `matchingOfIntegralFlow_size`: an integral flow of value `v` yields a
  matching of size `v`
- `maxMatching_eq_maxFlow_value` (Theorem 24.12): the maximum matching size
  equals the value of a maximal flow
-/

namespace CLRS
namespace Chapter26
open Finset Classical

/-- A bipartite graph with left partition `L`, right partition `R`, and
edges `E` that only go from `L` to `R`. (CLRS §24.3.) -/
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

/-- The flow network constructed from a bipartite graph (CLRS eq. (24.11)). -/
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

/-! ## The flow induced by a matching -/

/-- The contribution of a single matched edge `e` to the matching-induced flow
on pair `(u,v)` (CLRS eq. (24.11)): `+1` along `s → e.1`, `e.1 → e.2`,
`e.2 → t`, `−1` on the reverse edges, and `0` elsewhere.

The `(e.1, e.2)` direction is written as the sum of two indicators so that the
forward and reverse contributions cancel on degenerate pairs, making the
summand skew-symmetric for every `e`. -/
def matchingFlowFunSummand {V : Type*} [DecidableEq V] (e : V × V) (u v : V ⊕ Bool) : ℝ :=
  match u, v with
  | Sum.inr true, Sum.inl l => if e.1 = l then (1 : ℝ) else 0
  | Sum.inl a, Sum.inl b =>
      (if e = (a, b) then (1 : ℝ) else 0) + (if e = (b, a) then (-1 : ℝ) else 0)
  | Sum.inl r, Sum.inr false => if e.2 = r then (1 : ℝ) else 0
  | Sum.inl l, Sum.inr true => if e.1 = l then (-1 : ℝ) else 0
  | Sum.inr false, Sum.inl r => if e.2 = r then (-1 : ℝ) else 0
  | _, _ => 0

/-- The flow induced by a matching `M` in the constructed flow network. -/
def matchingFlowFun {V : Type*} [Fintype V] [DecidableEq V] {G : BipartiteGraph V}
    (M : Matching V G) (u v : V ⊕ Bool) : ℝ :=
  Finset.sum M.edges (fun (e : V × V) => matchingFlowFunSummand e u v)

/-- A matching has at most one edge leaving a given left vertex. -/
lemma count_left_le_one {V : Type*} [Fintype V] [DecidableEq V] {G : BipartiteGraph V}
    (M : Matching V G) (l : V) :
    Finset.sum M.edges (fun (e : V × V) => if e.1 = l then (1 : ℝ) else 0) ≤ 1 := by
  have hcard : (M.edges.filter (fun e : V × V => e.1 = l)).card ≤ 1 := by
    refine Finset.card_le_one.mpr ?_
    intro e1 he1 e2 he2
    have he1' : e1 ∈ M.edges := (Finset.mem_filter.mp he1).1
    have he2' : e2 ∈ M.edges := (Finset.mem_filter.mp he2).1
    have h1 : e1.1 = e2.1 := (Finset.mem_filter.mp he1).2.trans (Finset.mem_filter.mp he2).2.symm
    have h2 : e1.2 = e2.2 := M.h_unique_left e1.1 e1.2 e2.2 he1' (by simpa [h1] using he2')
    exact Prod.ext h1 h2
  have hsum : Finset.sum M.edges (fun (e : V × V) => if e.1 = l then (1 : ℝ) else 0)
      = ((M.edges.filter (fun e : V × V => e.1 = l)).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp
  rw [hsum]
  exact_mod_cast hcard

/-- A matching has at most one edge entering a given right vertex. -/
lemma count_right_le_one {V : Type*} [Fintype V] [DecidableEq V] {G : BipartiteGraph V}
    (M : Matching V G) (r : V) :
    Finset.sum M.edges (fun (e : V × V) => if e.2 = r then (1 : ℝ) else 0) ≤ 1 := by
  have hcard : (M.edges.filter (fun e : V × V => e.2 = r)).card ≤ 1 := by
    refine Finset.card_le_one.mpr ?_
    intro e1 he1 e2 he2
    have he1' : e1 ∈ M.edges := (Finset.mem_filter.mp he1).1
    have he2' : e2 ∈ M.edges := (Finset.mem_filter.mp he2).1
    have h1 : e1.2 = e2.2 := (Finset.mem_filter.mp he1).2.trans (Finset.mem_filter.mp he2).2.symm
    have h2 : e1.1 = e2.1 := M.h_unique_right e1.1 e2.1 e1.2 he1' (by simpa [h1] using he2')
    exact Prod.ext h2 h1
  have hsum : Finset.sum M.edges (fun (e : V × V) => if e.2 = r then (1 : ℝ) else 0)
      = ((M.edges.filter (fun e : V × V => e.2 = r)).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp
  rw [hsum]
  exact_mod_cast hcard

/-- The single-edge summand is skew-symmetric: its value on `(u,v)` is the
negation of its value on `(v,u)`. -/
lemma matchingFlowFunSummand_skew {V : Type*} [DecidableEq V] (e : V × V) (u v : V ⊕ Bool) :
    matchingFlowFunSummand e u v = - matchingFlowFunSummand e v u := by
  unfold matchingFlowFunSummand
  cases u with
  | inl a =>
    cases v with
    | inl b =>
      by_cases h1 : e = (a, b)
      · by_cases h2 : e = (b, a)
        · have hab : a = b := by
            exact (congrArg Prod.fst h1).symm.trans (congrArg Prod.fst h2)
          simp [h1, hab]
        · have hab_ne : a ≠ b := by
            intro hab
            apply h2
            simp [h1, hab]
          simp [h1, hab_ne]
      · by_cases h2 : e = (b, a)
        · have hab_ne : a ≠ b := by
            intro hab
            apply h1
            simp [h2, hab]
          simp [h2, hab_ne]
        · simp [h1, h2]
    | inr b =>
      cases b with
      | true => by_cases h : e.1 = a <;> simp [h]
      | false => by_cases h : e.2 = a <;> simp [h]
  | inr b =>
    cases b with
    | true =>
      cases v with
      | inl l => by_cases h : e.1 = l <;> simp [h]
      | inr b' => cases b' <;> simp
    | false =>
      cases v with
      | inl r => by_cases h : e.2 = r <;> simp [h]
      | inr b' => cases b' <;> simp

/-- The flow induced by a matching is skew-symmetric. -/
lemma matchingFlowFun_skew_symm {V : Type*} [Fintype V] [DecidableEq V] {G : BipartiteGraph V}
    (M : Matching V G) (u v : V ⊕ Bool) : matchingFlowFun M u v = - matchingFlowFun M v u := by
  unfold matchingFlowFun
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  exact matchingFlowFunSummand_skew e u v

/-- For a fixed edge `e`, summing the `(inl a, inl b)` summand over all `b`
counts how many endpoints of `e` equal `a`. -/
lemma matchingFlowFunSummand_inl_inl_sum {V : Type*} [Fintype V] [DecidableEq V]
    (e : V × V) (a : V) :
    (∑ b : V, matchingFlowFunSummand e (Sum.inl a) (Sum.inl b)) =
      (if e.1 = a then (1 : ℝ) else 0) - (if e.2 = a then (1 : ℝ) else 0) := by
  have hS1 : (∑ b : V, if e = (a, b) then (1 : ℝ) else 0) = if e.1 = a then (1 : ℝ) else 0 := by
    by_cases h : e.1 = a
    · calc
        (∑ b : V, if e = (a, b) then (1 : ℝ) else 0) = if e = (a, e.2) then (1 : ℝ) else 0 := by
          refine Finset.sum_eq_single e.2 ?_ ?_
          · intro b _ hb
            have hNe : e ≠ (a, b) := by
              intro hEq
              exact hb (congrArg Prod.snd hEq).symm
            simp [hNe]
          · simp
      _ = if e.1 = a then 1 else 0 := by
        have hEq : e = (a, e.2) := Prod.ext h rfl
        rw [hEq]
        simp
    · have hsum : (∑ b : V, if e = (a, b) then (1 : ℝ) else 0) = 0 := by
        refine Finset.sum_eq_zero (fun b _ => ?_)
        have hNe : e ≠ (a, b) := by
          intro hEq
          exact h (congrArg Prod.fst hEq)
        simp [hNe]
      simpa [h] using hsum
  have hS2 : (∑ b : V, if e = (b, a) then (-1 : ℝ) else 0) = if e.2 = a then (-1 : ℝ) else 0 := by
    by_cases h : e.2 = a
    · calc
        (∑ b : V, if e = (b, a) then (-1 : ℝ) else 0) = if e = (e.1, a) then (-1 : ℝ) else 0 := by
          refine Finset.sum_eq_single e.1 ?_ ?_
          · intro b _ hb
            have hNe : e ≠ (b, a) := by
              intro hEq
              exact hb (congrArg Prod.fst hEq).symm
            simp [hNe]
          · simp
      _ = if e.2 = a then -1 else 0 := by
        have hEq : e = (e.1, a) := Prod.ext rfl h
        rw [hEq]
        simp
    · have hsum : (∑ b : V, if e = (b, a) then (-1 : ℝ) else 0) = 0 := by
        refine Finset.sum_eq_zero (fun b _ => ?_)
        have hNe : e ≠ (b, a) := by
          intro hEq
          exact h (congrArg Prod.snd hEq)
        simp [hNe]
      simpa [h] using hsum
  calc
    (∑ b : V, matchingFlowFunSummand e (Sum.inl a) (Sum.inl b))
        = (∑ b : V, ((if e = (a, b) then (1 : ℝ) else 0) + (if e = (b, a) then (-1 : ℝ) else 0))) := by
          rfl
    _ = (∑ b : V, if e = (a, b) then (1 : ℝ) else 0)
        + (∑ b : V, if e = (b, a) then (-1 : ℝ) else 0) := by
          rw [Finset.sum_add_distrib]
    _ = (if e.1 = a then (1 : ℝ) else 0) + (if e.2 = a then (-1 : ℝ) else 0) := by
          rw [hS1, hS2]
    _ = (if e.1 = a then (1 : ℝ) else 0) - (if e.2 = a then (1 : ℝ) else 0) := by
          by_cases h1 : e.1 = a <;> by_cases h2 : e.2 = a <;> simp [h1, h2]

/-- The flow induced by a matching satisfies flow conservation at every
non-source non-sink vertex. -/
lemma matchingFlowFun_conservation {V : Type*} [Fintype V] [DecidableEq V]
    {G : BipartiteGraph V} (M : Matching V G) (a : V) :
    (∑ v : V ⊕ Bool, matchingFlowFun M (Sum.inl a) v) = 0 := by
  have h1 : (∑ b : V, matchingFlowFun M (Sum.inl a) (Sum.inl b)) =
      Finset.sum M.edges (fun (e : V × V) =>
        (if e.1 = a then (1 : ℝ) else 0) - (if e.2 = a then (1 : ℝ) else 0)) := by
    unfold matchingFlowFun
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    exact matchingFlowFunSummand_inl_inl_sum e a
  have h2 : matchingFlowFun M (Sum.inl a) (Sum.inr false) =
      Finset.sum M.edges (fun (e : V × V) => if e.2 = a then (1 : ℝ) else 0) := by
    unfold matchingFlowFun
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rfl
  have h3 : matchingFlowFun M (Sum.inl a) (Sum.inr true) =
      -(Finset.sum M.edges (fun (e : V × V) => if e.1 = a then (1 : ℝ) else 0)) := by
    unfold matchingFlowFun
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    dsimp [matchingFlowFunSummand]
    by_cases h : e.1 = a <;> simp [h]
  calc
    (∑ v : V ⊕ Bool, matchingFlowFun M (Sum.inl a) v)
        = (∑ b : V, matchingFlowFun M (Sum.inl a) (Sum.inl b))
          + (matchingFlowFun M (Sum.inl a) (Sum.inr false) + matchingFlowFun M (Sum.inl a) (Sum.inr true)) := by
          rw [← Finset.univ_disjSum_univ (α := V) (β := Bool)]
          rw [Finset.sum_disjSum (Finset.univ : Finset V) (Finset.univ : Finset Bool)
            (fun v : V ⊕ Bool => matchingFlowFun M (Sum.inl a) v)]
          rw [Fintype.univ_bool]
          rw [Finset.sum_pair (by decide : true ≠ false)]
          ring
    _ = 0 := by
      rw [h1, h2, h3]
      rw [Finset.sum_sub_distrib]
      ring

/-- The flow induced by a matching satisfies the capacity constraint
`f(u,v) ≤ c(u,v)`. -/
lemma matchingFlowFun_capacity {V : Type*} [Fintype V] [DecidableEq V] {G : BipartiteGraph V}
    (M : Matching V G) (u v : V ⊕ Bool) : matchingFlowFun M u v ≤ capFunc V G u v := by
  cases u with
  | inl a =>
    cases v with
    | inr b =>
      cases b with
      | true =>
        have hflow : matchingFlowFun M (Sum.inl a) (Sum.inr true) ≤ 0 := by
          unfold matchingFlowFun
          exact Finset.sum_nonpos (fun e he => by
            dsimp [matchingFlowFunSummand]
            by_cases h : e.1 = a <;> simp [h])
        simpa [capFunc] using hflow
      | false =>
        by_cases hR : a ∈ G.R
        · have hflow : matchingFlowFun M (Sum.inl a) (Sum.inr false) ≤ 1 := by
            have hsum : matchingFlowFun M (Sum.inl a) (Sum.inr false) =
                Finset.sum M.edges (fun (e : V × V) => if e.2 = a then (1 : ℝ) else 0) := by
              unfold matchingFlowFun
              refine Finset.sum_congr rfl (fun e _ => ?_)
              rfl
            rw [hsum]
            exact count_right_le_one M a
          simpa [capFunc, hR] using hflow
        · have hflow : matchingFlowFun M (Sum.inl a) (Sum.inr false) ≤ 0 := by
            unfold matchingFlowFun
            exact Finset.sum_nonpos (fun e he => by
              have hNe : e.2 ≠ a := by
                intro hEq
                exact hR (by simpa [hEq] using M.right_mem_R he)
              dsimp [matchingFlowFunSummand]
              simp [hNe])
          simpa [capFunc, hR] using hflow
    | inl b =>
      by_cases hE : (a, b) ∈ G.E
      · have hflow : matchingFlowFun M (Sum.inl a) (Sum.inl b) ≤ 1 := by
          have hsum_le : Finset.sum M.edges (fun (e : V × V) => if e = (a, b) then (1 : ℝ) else 0) ≤ 1 := by
            rw [Finset.sum_ite_eq' M.edges (a, b) (fun _ => (1 : ℝ))]
            by_cases h : (a, b) ∈ M.edges <;> simp [h]
          have hflow_le : matchingFlowFun M (Sum.inl a) (Sum.inl b) ≤
              Finset.sum M.edges (fun (e : V × V) => if e = (a, b) then (1 : ℝ) else 0) := by
            unfold matchingFlowFun
            exact Finset.sum_le_sum (fun e he => by
              dsimp [matchingFlowFunSummand]
              by_cases h1 : e = (a, b)
              · by_cases h2 : e = (b, a)
                · have hab : a = b := by
                    exact (congrArg Prod.fst h1).symm.trans (congrArg Prod.fst h2)
                  simp [h1, hab]
                · have hab_ne : a ≠ b := by
                    intro hab
                    apply h2
                    simp [h1, hab]
                  simp [h1, hab_ne]
              · by_cases h2 : e = (b, a)
                · have hab_ne : a ≠ b := by
                    intro hab
                    apply h1
                    simp [h2, hab]
                  simp [h2, hab_ne]
                · simp [h1, h2])
          linarith
        simpa [capFunc, hE] using hflow
      · have hflow : matchingFlowFun M (Sum.inl a) (Sum.inl b) ≤ 0 := by
          unfold matchingFlowFun
          exact Finset.sum_nonpos (fun e he => by
            have hNe : e ≠ (a, b) := by
              intro hEq
              exact hE (by simpa [hEq] using M.h_subset he)
            dsimp [matchingFlowFunSummand]
            by_cases h2 : e = (b, a)
            · have hab_ne : a ≠ b := by
                intro hab
                exact hNe (by simp [h2, hab])
              simp [h2, hab_ne]
            · simp [hNe, h2])
        simpa [capFunc, hE] using hflow
  | inr b =>
    cases b with
    | true =>
      cases v with
      | inr b' => cases b' <;> dsimp [matchingFlowFun, matchingFlowFunSummand] <;> simp [capFunc]
      | inl l =>
        by_cases hL : l ∈ G.L
        · have hflow : matchingFlowFun M (Sum.inr true) (Sum.inl l) ≤ 1 := by
            have hsum : matchingFlowFun M (Sum.inr true) (Sum.inl l) =
                Finset.sum M.edges (fun (e : V × V) => if e.1 = l then (1 : ℝ) else 0) := by
              unfold matchingFlowFun
              refine Finset.sum_congr rfl (fun e _ => ?_)
              rfl
            rw [hsum]
            exact count_left_le_one M l
          simpa [capFunc, hL] using hflow
        · have hflow : matchingFlowFun M (Sum.inr true) (Sum.inl l) ≤ 0 := by
            unfold matchingFlowFun
            exact Finset.sum_nonpos (fun e he => by
              have hNe : e.1 ≠ l := by
                intro hEq
                exact hL (by simpa [hEq] using M.left_mem_L he)
              dsimp [matchingFlowFunSummand]
              simp [hNe])
          simpa [capFunc, hL] using hflow
    | false =>
      cases v with
      | inl r =>
        have hflow : matchingFlowFun M (Sum.inr false) (Sum.inl r) ≤ 0 := by
          unfold matchingFlowFun
          exact Finset.sum_nonpos (fun e he => by
            dsimp [matchingFlowFunSummand]
            by_cases h : e.2 = r <;> simp [h])
        simpa [capFunc] using hflow
      | inr b' => cases b' <;> dsimp [matchingFlowFun, matchingFlowFunSummand] <;> simp [capFunc]

/-- The feasible flow induced by a matching (CLRS §24.3).  The flow sends one
unit along `s → l`, `l → r`, `r → t` for every matched edge `(l, r)`, with
skew-symmetric reverse contributions. -/
noncomputable def matchingToFlow {V : Type*} [Fintype V] [DecidableEq V] {G : BipartiteGraph V}
    (M : Matching V G) : Flow (V ⊕ Bool) (toFlowNetwork V G) :=
  { f := matchingFlowFun M
  , hcapacity := matchingFlowFun_capacity M
  , hskew_symm := matchingFlowFun_skew_symm M
  , hconservation := by
      intro u hu hs
      cases u with
      | inl a => exact matchingFlowFun_conservation M a
      | inr b =>
          cases b with
          | true => simp [toFlowNetwork] at hu
          | false => simp [toFlowNetwork] at hs
  }

/-- The total flow out of the source equals the number of matched edges. -/
lemma matchingFlowFun_value_sum {V : Type*} [Fintype V] [DecidableEq V] {G : BipartiteGraph V}
    (M : Matching V G) :
    Finset.sum (Finset.univ : Finset (V ⊕ Bool)) (fun v => matchingFlowFun M (Sum.inr true) v)
      = (M.size : ℝ) := by
  calc
    Finset.sum (Finset.univ : Finset (V ⊕ Bool)) (fun v => matchingFlowFun M (Sum.inr true) v)
        = Finset.sum (Finset.univ : Finset (V ⊕ Bool)) (fun v =>
            Finset.sum M.edges (fun (e : V × V) =>
              match v with
              | Sum.inl l => if e.1 = l then (1 : ℝ) else 0
              | Sum.inr _ => 0)) := by
          refine Finset.sum_congr rfl (fun v hv => ?_)
          unfold matchingFlowFun
          cases v with
          | inl l => rfl
          | inr b => cases b <;> rfl
      _ = Finset.sum M.edges (fun (e : V × V) =>
            Finset.sum (Finset.univ : Finset (V ⊕ Bool)) (fun v =>
              match v with
              | Sum.inl l => if e.1 = l then (1 : ℝ) else 0
              | Sum.inr _ => 0)) := by
            rw [Finset.sum_comm]
      _ = Finset.sum M.edges (fun (e : V × V) => (1 : ℝ)) := by
            refine Finset.sum_congr rfl (fun e _ => ?_)
            simp
      _ = (M.size : ℝ) := by
            simp [Matching.size]

/-- **Theorem (matching-flow value).**  The flow induced by a matching `M` has
value equal to `|M|` (CLRS Theorem 24.12, value direction). -/
theorem matchingToFlow_value {V : Type*} [Fintype V] [DecidableEq V] {G : BipartiteGraph V}
    (M : Matching V G) : (matchingToFlow M).value = (M.size : ℝ) := by
  simp [Flow.value, matchingToFlow, toFlowNetwork, matchingFlowFun_value_sum M]

/-! ## Integral flows and the converse construction -/

/-- An integral flow takes only integer values on every edge.  Values may be
negative (reverse flow); the `{0,1}` recovery uses the capacity bounds to
force nonnegativity on the relevant pairs. -/
def Flow.IsIntegral {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Flow V G) : Prop :=
  ∀ u v, ∃ n : ℤ, φ.f u v = (n : ℝ)

/-- A real in `[0,1]` that is an integer is `0` or `1`. -/
lemma integral_of_unit_range {x : ℝ} (h01 : 0 ≤ x ∧ x ≤ 1) (hint : ∃ n : ℤ, x = (n : ℝ)) :
    x = 0 ∨ x = 1 := by
  rcases hint with ⟨n, hn⟩
  have hn_ge : 0 ≤ n := by
    have hx_ge : 0 ≤ x := h01.1
    rw [hn] at hx_ge
    exact_mod_cast hx_ge
  have hn_le : n ≤ 1 := by
    have hx_le : x ≤ 1 := h01.2
    rw [hn] at hx_le
    exact_mod_cast hx_le
  have hn_eq : n = 0 ∨ n = 1 := by omega
  rcases hn_eq with h | h <;> simp [hn, h]

/-- A vertex in `R` is not in `L` (the partitions are disjoint). -/
lemma BipartiteGraph.not_mem_L_of_mem_R {V : Type*} [Fintype V] [DecidableEq V]
    (G : BipartiteGraph V) {v : V} (h : v ∈ G.R) : v ∉ G.L := by
  intro hL
  have : v ∈ G.L ∩ G.R := Finset.mem_inter.mpr ⟨hL, h⟩
  rw [G.h_disjoint] at this
  simp at this

/-- A vertex in `L` is not in `R` (the partitions are disjoint). -/
lemma BipartiteGraph.not_mem_R_of_mem_L {V : Type*} [Fintype V] [DecidableEq V]
    (G : BipartiteGraph V) {v : V} (h : v ∈ G.L) : v ∉ G.R := by
  intro hR
  have : v ∈ G.L ∩ G.R := Finset.mem_inter.mpr ⟨h, hR⟩
  rw [G.h_disjoint] at this
  simp at this

/-- In the unit-capacity matching network, the flow on every `L→R` pair lies
in `[0, 1]`, and is zero when the edge is absent.  The reverse capacity is
zero because the graph has no anti-parallel edges: `(r, l) ∈ E` would put
`l` in both partitions. -/
lemma matchingFlow_lr_bounds {V : Type*} [Fintype V] [DecidableEq V] {G : BipartiteGraph V}
    (φ : Flow (V ⊕ Bool) (toFlowNetwork V G)) (l : V) (hl : l ∈ G.L) (r : V) :
    0 ≤ φ.f (Sum.inl l) (Sum.inl r) ∧
      φ.f (Sum.inl l) (Sum.inl r) ≤ (if (l, r) ∈ G.E then (1 : ℝ) else 0) := by
  have hrev : (toFlowNetwork V G).c (Sum.inl r) (Sum.inl l) = 0 := by
    simp [toFlowNetwork, capFunc]
    by_cases h : (r, l) ∈ G.E
    · exact False.elim (G.not_mem_R_of_mem_L hl (G.hE_subset (r, l) h).2)
    · simp [h]
  simpa [toFlowNetwork, capFunc] using (Flow.range_of_zero_reverse_cap φ (Sum.inl l) (Sum.inl r) hrev)

/-- In the matching network, the flow out of a left vertex equals its inflow
from the source (conservation at `l ∈ L`). -/
lemma matchingFlow_conservation_left {V : Type*} [Fintype V] [DecidableEq V]
    {G : BipartiteGraph V} (φ : Flow (V ⊕ Bool) (toFlowNetwork V G))
    (l : V) (hl : l ∈ G.L) :
    φ.f (Sum.inr true) (Sum.inl l) = ∑ r : V, φ.f (Sum.inl l) (Sum.inl r) := by
  have hcons : (∑ v : V ⊕ Bool, φ.f (Sum.inl l) v) = 0 :=
    φ.hconservation (Sum.inl l) (by simp [toFlowNetwork]) (by simp [toFlowNetwork])
  have hdecomp : (∑ v : V ⊕ Bool, φ.f (Sum.inl l) v) =
      (∑ r : V, φ.f (Sum.inl l) (Sum.inl r)) +
        (φ.f (Sum.inl l) (Sum.inr true) + φ.f (Sum.inl l) (Sum.inr false)) := by
    rw [← Finset.univ_disjSum_univ (α := V) (β := Bool)]
    rw [Finset.sum_disjSum (Finset.univ : Finset V) (Finset.univ : Finset Bool)
      (fun v : V ⊕ Bool => φ.f (Sum.inl l) v)]
    rw [Fintype.univ_bool]
    rw [Finset.sum_pair (by decide : true ≠ false)]
  have hlt : φ.f (Sum.inl l) (Sum.inr false) = 0 := by
    have hrev : (toFlowNetwork V G).c (Sum.inr false) (Sum.inl l) = 0 := by
      simp [toFlowNetwork, capFunc]
    have hr0 := Flow.range_of_zero_reverse_cap φ (Sum.inl l) (Sum.inr false) hrev
    have hcap : (toFlowNetwork V G).c (Sum.inl l) (Sum.inr false) = 0 := by
      simp [toFlowNetwork, capFunc]
      by_cases h : l ∈ G.R
      · exact False.elim (G.not_mem_R_of_mem_L hl h)
      · simp [h]
    linarith
  have hls : φ.f (Sum.inl l) (Sum.inr true) = -φ.f (Sum.inr true) (Sum.inl l) :=
    φ.hskew_symm (Sum.inl l) (Sum.inr true)
  rw [hdecomp, hlt, hls] at hcons
  linarith

/-- In the matching network, the flow into a right vertex equals its outflow
to the sink (conservation at `r ∈ R`). -/
lemma matchingFlow_conservation_right {V : Type*} [Fintype V] [DecidableEq V]
    {G : BipartiteGraph V} (φ : Flow (V ⊕ Bool) (toFlowNetwork V G))
    (r : V) (hr : r ∈ G.R) :
    φ.f (Sum.inl r) (Sum.inr false) = ∑ l : V, φ.f (Sum.inl l) (Sum.inl r) := by
  have hcons : (∑ v : V ⊕ Bool, φ.f (Sum.inl r) v) = 0 :=
    φ.hconservation (Sum.inl r) (by simp [toFlowNetwork]) (by simp [toFlowNetwork])
  have hdecomp : (∑ v : V ⊕ Bool, φ.f (Sum.inl r) v) =
      (∑ l : V, φ.f (Sum.inl r) (Sum.inl l)) +
        (φ.f (Sum.inl r) (Sum.inr true) + φ.f (Sum.inl r) (Sum.inr false)) := by
    rw [← Finset.univ_disjSum_univ (α := V) (β := Bool)]
    rw [Finset.sum_disjSum (Finset.univ : Finset V) (Finset.univ : Finset Bool)
      (fun v : V ⊕ Bool => φ.f (Sum.inl r) v)]
    rw [Fintype.univ_bool]
    rw [Finset.sum_pair (by decide : true ≠ false)]
  have hrs : φ.f (Sum.inl r) (Sum.inr true) = 0 := by
    have hrev : (toFlowNetwork V G).c (Sum.inr true) (Sum.inl r) = 0 := by
      simp [toFlowNetwork, capFunc]
      by_cases h : r ∈ G.L
      · exact False.elim (G.not_mem_L_of_mem_R hr h)
      · simp [h]
    have hr0 := Flow.range_of_zero_reverse_cap φ (Sum.inl r) (Sum.inr true) hrev
    have hcap : (toFlowNetwork V G).c (Sum.inl r) (Sum.inr true) = 0 := by
      simp [toFlowNetwork, capFunc]
    linarith
  have hlr_sum : (∑ l : V, φ.f (Sum.inl r) (Sum.inl l)) =
      -(∑ l : V, φ.f (Sum.inl l) (Sum.inl r)) := by
    calc
      (∑ l : V, φ.f (Sum.inl r) (Sum.inl l)) = ∑ l : V, -φ.f (Sum.inl l) (Sum.inl r) := by
        refine Finset.sum_congr rfl (fun l _ => ?_)
        exact φ.hskew_symm (Sum.inl r) (Sum.inl l)
      _ = -(∑ l : V, φ.f (Sum.inl l) (Sum.inl r)) := by
        rw [Finset.sum_neg_distrib]
  rw [hdecomp, hrs, hlr_sum] at hcons
  linarith

/-- Flow between two right vertices is zero (both directions have zero
capacity). -/
lemma matchingFlow_rr_zero {V : Type*} [Fintype V] [DecidableEq V] {G : BipartiteGraph V}
    (φ : Flow (V ⊕ Bool) (toFlowNetwork V G)) {r₁ r₂ : V}
    (hr₁ : r₁ ∈ G.R) (hr₂ : r₂ ∈ G.R) : φ.f (Sum.inl r₁) (Sum.inl r₂) = 0 := by
  have hcap : (toFlowNetwork V G).c (Sum.inl r₁) (Sum.inl r₂) = 0 := by
    simp [toFlowNetwork, capFunc]
    by_cases h : (r₁, r₂) ∈ G.E
    · exact False.elim (G.not_mem_L_of_mem_R hr₁ (G.hE_subset (r₁, r₂) h).1)
    · simp [h]
  have hrev : (toFlowNetwork V G).c (Sum.inl r₂) (Sum.inl r₁) = 0 := by
    simp [toFlowNetwork, capFunc]
    by_cases h : (r₂, r₁) ∈ G.E
    · exact False.elim (G.not_mem_L_of_mem_R hr₂ (G.hE_subset (r₂, r₁) h).1)
    · simp [h]
  have hle := Flow.nonpos_of_zero_cap φ (Sum.inl r₁) (Sum.inl r₂) hcap
  have hge := Flow.nonneg_of_zero_reverse_cap φ (Sum.inl r₁) (Sum.inl r₂) hrev
  linarith

/-- On the unit-capacity network an integral flow takes values in `{0, 1}`
on every `L→R` pair. -/
lemma integral_lr_unit {V : Type*} [Fintype V] [DecidableEq V] {G : BipartiteGraph V}
    (φ : Flow (V ⊕ Bool) (toFlowNetwork V G)) (hint : φ.IsIntegral)
    (l : V) (hl : l ∈ G.L) (r : V) :
    φ.f (Sum.inl l) (Sum.inl r) = 0 ∨ φ.f (Sum.inl l) (Sum.inl r) = 1 := by
  have hb := matchingFlow_lr_bounds φ l hl r
  have hle : φ.f (Sum.inl l) (Sum.inl r) ≤ 1 := by
    by_cases hE : (l, r) ∈ G.E
    · simpa [hE] using hb.2
    · simp [hE] at hb
      linarith
  exact integral_of_unit_range ⟨hb.1, hle⟩ (hint (Sum.inl l) (Sum.inl r))

/-- On the unit-capacity network an integral flow sends `0` or `1` units out
of the source to every left vertex. -/
lemma integral_source_unit {V : Type*} [Fintype V] [DecidableEq V] {G : BipartiteGraph V}
    (φ : Flow (V ⊕ Bool) (toFlowNetwork V G)) (hint : φ.IsIntegral)
    (l : V) (hl : l ∈ G.L) :
    φ.f (Sum.inr true) (Sum.inl l) = 0 ∨ φ.f (Sum.inr true) (Sum.inl l) = 1 := by
  have hrev : (toFlowNetwork V G).c (Sum.inl l) (Sum.inr true) = 0 := by
    simp [toFlowNetwork, capFunc]
  exact integral_of_unit_range
    (by simpa [toFlowNetwork, capFunc, hl] using
      (Flow.range_of_zero_reverse_cap φ (Sum.inr true) (Sum.inl l) hrev))
    (hint (Sum.inr true) (Sum.inl l))

/-- An edge carrying one unit of flow in the matching network belongs to
`G.E`. -/
lemma mem_edges_of_flow_one {V : Type*} [Fintype V] [DecidableEq V] {G : BipartiteGraph V}
    (φ : Flow (V ⊕ Bool) (toFlowNetwork V G)) {l r : V}
    (h : φ.f (Sum.inl l) (Sum.inl r) = 1) : (l, r) ∈ G.E := by
  have hle1 : 1 ≤ (toFlowNetwork V G).c (Sum.inl l) (Sum.inl r) := by
    linarith [φ.hcapacity (Sum.inl l) (Sum.inl r), h]
  by_cases hE : (l, r) ∈ G.E
  · exact hE
  · simp [toFlowNetwork, capFunc, hE] at hle1
    norm_num at hle1

/-- The indicator of a one-unit flow into a right vertex equals the flow
value: integral flows take `0` or `1` on `L→R` pairs and zero on `R→R`
pairs. -/
lemma flow_one_indicator_eq_of_right {V : Type*} [Fintype V] [DecidableEq V]
    {G : BipartiteGraph V} (φ : Flow (V ⊕ Bool) (toFlowNetwork V G)) (hint : φ.IsIntegral)
    {r : V} (hr : r ∈ G.R) (l : V) :
    (if φ.f (Sum.inl l) (Sum.inl r) = 1 then (1 : ℝ) else 0) = φ.f (Sum.inl l) (Sum.inl r) := by
  by_cases hl : l ∈ G.L
  · rcases integral_lr_unit φ hint l hl r with h | h <;> simp [h]
  · have hlR : l ∈ G.R := by
      have : l ∈ G.L ∪ G.R := by simp [G.h_cover]
      exact (Finset.mem_union.mp this).resolve_left hl
    have hz : φ.f (Sum.inl l) (Sum.inl r) = 0 := matchingFlow_rr_zero φ hlR hr
    simp [hz]

/-- The matching recovered from an integral flow: every `L→R` pair carrying
one unit of flow. -/
noncomputable def matchingOfIntegralFlow {V : Type*} [Fintype V] [DecidableEq V]
    {G : BipartiteGraph V} (φ : Flow (V ⊕ Bool) (toFlowNetwork V G)) (hint : φ.IsIntegral) :
    Matching V G :=
  { edges := (Finset.univ : Finset (V × V)).filter (fun e : V × V => φ.f (Sum.inl e.1) (Sum.inl e.2) = 1)
  , h_subset := by
      intro e he
      exact mem_edges_of_flow_one φ (Finset.mem_filter.mp he).2
  , h_unique_left := by
      intro l r₁ r₂ h1 h2
      have hf1 : φ.f (Sum.inl l) (Sum.inl r₁) = 1 := (Finset.mem_filter.mp h1).2
      have hl : l ∈ G.L := (G.hE_subset (l, r₁) (mem_edges_of_flow_one φ hf1)).1
      have hcount : φ.f (Sum.inr true) (Sum.inl l) =
          ((Finset.univ.filter (fun r : V => φ.f (Sum.inl l) (Sum.inl r) = 1)).card : ℝ) := by
        calc
          φ.f (Sum.inr true) (Sum.inl l) = ∑ r : V, φ.f (Sum.inl l) (Sum.inl r) :=
            matchingFlow_conservation_left φ l hl
          _ = ∑ r : V, (if φ.f (Sum.inl l) (Sum.inl r) = 1 then (1 : ℝ) else 0) := by
            refine Finset.sum_congr rfl (fun r _ => ?_)
            rcases integral_lr_unit φ hint l hl r with h | h <;> simp [h]
          _ = ((Finset.univ.filter (fun r : V => φ.f (Sum.inl l) (Sum.inl r) = 1)).card : ℝ) := by
            rw [← Finset.sum_filter]
            simp
      have hle : φ.f (Sum.inr true) (Sum.inl l) ≤ 1 := by
        rcases integral_source_unit φ hint l hl with h | h <;> simp [h]
      have hcard : (Finset.univ.filter (fun r : V => φ.f (Sum.inl l) (Sum.inl r) = 1)).card ≤ 1 := by
        have hℝ : (↑(Finset.univ.filter (fun r : V => φ.f (Sum.inl l) (Sum.inl r) = 1)).card : ℝ) ≤ 1 := by
          rw [← hcount]
          exact hle
        exact_mod_cast hℝ
      exact Finset.card_le_one.mp hcard r₁ (by simp [hf1]) r₂ (by simp [(Finset.mem_filter.mp h2).2])
  , h_unique_right := by
      intro l₁ l₂ r h1 h2
      have hf1 : φ.f (Sum.inl l₁) (Sum.inl r) = 1 := (Finset.mem_filter.mp h1).2
      have hr : r ∈ G.R := (G.hE_subset (l₁, r) (mem_edges_of_flow_one φ hf1)).2
      have hcount : φ.f (Sum.inl r) (Sum.inr false) =
          ((Finset.univ.filter (fun l : V => φ.f (Sum.inl l) (Sum.inl r) = 1)).card : ℝ) := by
        calc
          φ.f (Sum.inl r) (Sum.inr false) = ∑ l : V, φ.f (Sum.inl l) (Sum.inl r) :=
            matchingFlow_conservation_right φ r hr
          _ = ∑ l : V, (if φ.f (Sum.inl l) (Sum.inl r) = 1 then (1 : ℝ) else 0) := by
            refine Finset.sum_congr rfl (fun l _ => ?_)
            exact (flow_one_indicator_eq_of_right φ hint hr l).symm
          _ = ((Finset.univ.filter (fun l : V => φ.f (Sum.inl l) (Sum.inl r) = 1)).card : ℝ) := by
            rw [← Finset.sum_filter]
            simp
      have hr01 : 0 ≤ φ.f (Sum.inl r) (Sum.inr false) ∧ φ.f (Sum.inl r) (Sum.inr false) ≤ 1 := by
        have hrev : (toFlowNetwork V G).c (Sum.inr false) (Sum.inl r) = 0 := by
          simp [toFlowNetwork, capFunc]
        have hr0 := Flow.range_of_zero_reverse_cap φ (Sum.inl r) (Sum.inr false) hrev
        have hc : (toFlowNetwork V G).c (Sum.inl r) (Sum.inr false) = 1 := by
          simp [toFlowNetwork, capFunc, hr]
        exact ⟨hr0.1, by simpa [hc] using hr0.2⟩
      have hcard : (Finset.univ.filter (fun l : V => φ.f (Sum.inl l) (Sum.inl r) = 1)).card ≤ 1 := by
        have hℝ : (↑(Finset.univ.filter (fun l : V => φ.f (Sum.inl l) (Sum.inl r) = 1)).card : ℝ) ≤ 1 := by
          rw [← hcount]
          exact hr01.2
        exact_mod_cast hℝ
      exact Finset.card_le_one.mp hcard l₁ (by simp [hf1]) l₂ (by simp [(Finset.mem_filter.mp h2).2])
  }

/-- **Theorem (integral-flow converse).**  An integral flow of value `v` in
the matching network yields a matching of size `v` (CLRS Theorem 24.12,
converse direction). -/
theorem matchingOfIntegralFlow_size {V : Type*} [Fintype V] [DecidableEq V]
    {G : BipartiteGraph V} (φ : Flow (V ⊕ Bool) (toFlowNetwork V G)) (hint : φ.IsIntegral) :
    ((matchingOfIntegralFlow φ hint).size : ℝ) = φ.value := by
  have hcard : ((matchingOfIntegralFlow φ hint).edges.card : ℝ) =
      ∑ e : V × V, (if φ.f (Sum.inl e.1) (Sum.inl e.2) = 1 then (1 : ℝ) else 0) := by
    unfold matchingOfIntegralFlow
    rw [← Finset.sum_filter]
    simp
  have hval : φ.value = ∑ l : V, φ.f (Sum.inr true) (Sum.inl l) := by
    calc
      φ.value = (∑ l : V, φ.f (Sum.inr true) (Sum.inl l)) +
          (φ.f (Sum.inr true) (Sum.inr true) + φ.f (Sum.inr true) (Sum.inr false)) := by
        simp [Flow.value, toFlowNetwork]
      _ = ∑ l : V, φ.f (Sum.inr true) (Sum.inl l) := by
        have hss : φ.f (Sum.inr true) (Sum.inr true) = 0 := Flow.self_zero φ (Sum.inr true)
        have hst : φ.f (Sum.inr true) (Sum.inr false) = 0 := by
          have hrev : (toFlowNetwork V G).c (Sum.inr false) (Sum.inr true) = 0 := by
            simp [toFlowNetwork, capFunc]
          have hr0 := Flow.range_of_zero_reverse_cap φ (Sum.inr true) (Sum.inr false) hrev
          have hcap : (toFlowNetwork V G).c (Sum.inr true) (Sum.inr false) = 0 := by
            simp [toFlowNetwork, capFunc]
          linarith
        simp [hss, hst]
  calc
    ((matchingOfIntegralFlow φ hint).size : ℝ)
        = ∑ e : V × V, (if φ.f (Sum.inl e.1) (Sum.inl e.2) = 1 then (1 : ℝ) else 0) := by
          simp only [Matching.size]
          rw [hcard]
    _ = ∑ l : V, ∑ r : V, (if φ.f (Sum.inl l) (Sum.inl r) = 1 then (1 : ℝ) else 0) := by
          have huniv : (Finset.univ : Finset (V × V)) = Finset.univ.product Finset.univ := by
            ext e; simp
          rw [huniv]
          exact (Finset.sum_product Finset.univ Finset.univ
            (fun e : V × V => if φ.f (Sum.inl e.1) (Sum.inl e.2) = 1 then (1 : ℝ) else 0))
    _ = ∑ l : V, φ.f (Sum.inr true) (Sum.inl l) := by
          refine Finset.sum_congr rfl (fun l _ => ?_)
          by_cases hl : l ∈ G.L
          · calc
              ∑ r : V, (if φ.f (Sum.inl l) (Sum.inl r) = 1 then (1 : ℝ) else 0)
                  = ∑ r : V, φ.f (Sum.inl l) (Sum.inl r) := by
                    refine Finset.sum_congr rfl (fun r _ => ?_)
                    rcases integral_lr_unit φ hint l hl r with h | h <;> simp [h]
              _ = φ.f (Sum.inr true) (Sum.inl l) := (matchingFlow_conservation_left φ l hl).symm
          · have hlR : l ∈ G.R := by
              have : l ∈ G.L ∪ G.R := by simp [G.h_cover]
              exact (Finset.mem_union.mp this).resolve_left hl
            have hsum : ∑ r : V, (if φ.f (Sum.inl l) (Sum.inl r) = 1 then (1 : ℝ) else 0) = 0 := by
              refine Finset.sum_eq_zero (fun r _ => ?_)
              have hcap : (toFlowNetwork V G).c (Sum.inl l) (Sum.inl r) = 0 := by
                simp [toFlowNetwork, capFunc]
                by_cases h : (l, r) ∈ G.E
                · exact False.elim (hl (G.hE_subset (l, r) h).1)
                · simp [h]
              have hf : φ.f (Sum.inl l) (Sum.inl r) ≤ 0 :=
                Flow.nonpos_of_zero_cap φ (Sum.inl l) (Sum.inl r) hcap
              by_cases h : φ.f (Sum.inl l) (Sum.inl r) = 1
              · exfalso; linarith
              · simp [h]
            have hsrc : φ.f (Sum.inr true) (Sum.inl l) = 0 := by
              have hcap : (toFlowNetwork V G).c (Sum.inr true) (Sum.inl l) = 0 := by
                simp [toFlowNetwork, capFunc]
                by_cases h : l ∈ G.L
                · exact False.elim (hl h)
                · simp [h]
              have hrev : (toFlowNetwork V G).c (Sum.inl l) (Sum.inr true) = 0 := by
                simp [toFlowNetwork, capFunc]
              have hr0 := Flow.range_of_zero_reverse_cap φ (Sum.inr true) (Sum.inl l) hrev
              linarith
            rw [hsum, hsrc]
    _ = φ.value := hval.symm

/-! ## Integral maximum flow and Theorem 24.12 -/

/-- The zero flow on a network. -/
noncomputable def zeroFlow {V : Type*} [Fintype V] [DecidableEq V] (G : FlowNetwork V) : Flow V G :=
  { f := fun _ _ => 0
  , hcapacity := by intro u v; exact G.hc_nonneg u v
  , hskew_symm := by intro u v; simp
  , hconservation := by intro u hu ht; simp
  }

/-- The zero flow is integral. -/
lemma IsIntegral_zero {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V} :
    (zeroFlow G).IsIntegral := by
  intro u v
  exact ⟨0, by simp [zeroFlow]⟩

/-- The residual capacity of an integral flow on an integral-capacity network
is an integer. -/
lemma residualCapacity_integral {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Flow V G) (hint : φ.IsIntegral) (hc : ∀ u v, ∃ n : ℕ, G.c u v = (n : ℝ))
    (u v : V) : ∃ n : ℤ, φ.residualCapacity u v = (n : ℝ) := by
  rcases hc u v with ⟨m, hm⟩
  rcases hint u v with ⟨n, hn⟩
  unfold Flow.residualCapacity
  refine ⟨m - n, ?_⟩
  rw [hm, hn]
  push_cast
  ring

/-- The bottleneck of an augmenting path in an integral network is an
integer. -/
lemma bottleneck_integral {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Flow V G) (hint : φ.IsIntegral) (hc : ∀ u v, ∃ n : ℕ, G.c u v = (n : ℝ))
    (p : Flow.AugmentingPath φ) : ∃ n : ℤ, p.bottleneck = (n : ℝ) := by
  have hmem : p.bottleneck ∈ p.edges.toFinset.image (fun e => φ.residualCapacity e.1 e.2) := by
    unfold Flow.AugmentingPath.bottleneck
    exact Finset.min'_mem _ _
  rcases Finset.mem_image.mp hmem with ⟨e, he, hEq⟩
  rw [← hEq]
  exact residualCapacity_integral φ hint hc e.1 e.2

/-- The bottleneck of an augmenting path in an integral network is at least
`1`. -/
lemma bottleneck_ge_one {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Flow V G) (hint : φ.IsIntegral) (hc : ∀ u v, ∃ n : ℕ, G.c u v = (n : ℝ))
    (p : Flow.AugmentingPath φ) : 1 ≤ p.bottleneck := by
  unfold Flow.AugmentingPath.bottleneck
  rw [Finset.le_min'_iff]
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨e, he, rfl⟩
  have hpos : 0 < φ.residualCapacity e.1 e.2 :=
    p.residualEdge_of_mem_edges (by simpa using he)
  rcases residualCapacity_integral φ hint hc e.1 e.2 with ⟨n, hn⟩
  rw [hn]
  have hn_pos : 0 < n := by
    have h0 : 0 < (n : ℝ) := by simpa [hn] using hpos
    exact_mod_cast h0
  exact_mod_cast (by omega : 1 ≤ n)

/-- The single-edge update of an integral delta is integral. -/
lemma edgeDelta_integral {V : Type*} [DecidableEq V] {delta : ℝ}
    (hdelta : ∃ n : ℤ, delta = (n : ℝ)) (a b u v : V) :
    ∃ n : ℤ, Flow.edgeDelta delta a b u v = (n : ℝ) := by
  rcases hdelta with ⟨n, hn⟩
  by_cases h1 : u = a ∧ v = b
  · by_cases h2 : u = b ∧ v = a
    · have hab : a = b := h1.1.symm.trans h2.1
      exact ⟨0, by simp [Flow.edgeDelta, h1, hab, hn]⟩
    · have hab_ne : a ≠ b := by
        intro hab
        apply h2
        exact ⟨by simpa [hab] using h1.1, by simpa [hab] using h1.2⟩
      exact ⟨n, by simp [Flow.edgeDelta, h1, hab_ne, hn]⟩
  · by_cases h2 : u = b ∧ v = a
    · have hab_ne : a ≠ b := by
        intro hab
        apply h1
        exact ⟨by simpa [hab] using h2.1, by simpa [hab] using h2.2⟩
      exact ⟨-n, by simp [Flow.edgeDelta, h2, hab_ne, hn]⟩
    · exact ⟨0, by simp [Flow.edgeDelta, h1, h2]⟩

/-- The path update of an integral delta is integral. -/
lemma pathDelta_integral {V : Type*} [DecidableEq V] {delta : ℝ}
    (hdelta : ∃ n : ℤ, delta = (n : ℝ)) (xs : List V) (u v : V) :
    ∃ n : ℤ, Flow.pathDelta delta xs u v = (n : ℝ) := by
  induction xs with
  | nil => exact ⟨0, by simp [Flow.pathDelta]⟩
  | cons a xs ih =>
      cases xs with
      | nil => exact ⟨0, by simp [Flow.pathDelta]⟩
      | cons b xs =>
          rcases edgeDelta_integral hdelta a b u v with ⟨m, hm⟩
          rcases ih with ⟨k, hk⟩
          exact ⟨m + k, by
            simp only [Flow.pathDelta]
            rw [hm, hk]
            push_cast
            ring⟩

/-- Augmentation preserves integrality on an integral-capacity network. -/
lemma IsIntegral_augment {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Flow V G) (hint : φ.IsIntegral) (hc : ∀ u v, ∃ n : ℕ, G.c u v = (n : ℝ))
    (p : Flow.AugmentingPath φ) : (φ.augment p).IsIntegral := by
  intro u v
  have hb : ∃ n : ℤ, p.bottleneck = (n : ℝ) := bottleneck_integral φ hint hc p
  have hf : ∃ n : ℤ, φ.f u v = (n : ℝ) := hint u v
  have hp : ∃ n : ℤ, Flow.pathDelta p.bottleneck p.vertices u v = (n : ℝ) :=
    pathDelta_integral hb p.vertices u v
  rcases hf with ⟨n, hn⟩
  rcases hp with ⟨k, hk⟩
  exact ⟨n + k, by
    change φ.f u v + Flow.pathDelta p.bottleneck p.vertices u v = ((n + k : ℤ) : ℝ)
    rw [hn, hk]
    push_cast
    ring⟩

/-- Augmenting along a residual path increases the value by at least one on
an integral network. -/
lemma augment_value_ge_one {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Flow V G) (hint : φ.IsIntegral) (hc : ∀ u v, ∃ n : ℕ, G.c u v = (n : ℝ))
    (p : Flow.AugmentingPath φ) : φ.value + 1 ≤ (φ.augment p).value := by
  rw [φ.augment_value p]
  linarith [bottleneck_ge_one φ hint hc p]

/-- One augmentation step: augment along an arbitrary residual source-to-sink
path if one exists. -/
noncomputable def augmentOnce {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Flow V G) : Flow V G :=
  if h : φ.hasAugmentingPath then
    φ.augment (Classical.choice (Flow.hasAugmentingPath_iff_nonempty_augmentingPath.mp h))
  else φ

/-- `augmentOnce` preserves integrality. -/
lemma IsIntegral_augmentOnce {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Flow V G) (hint : φ.IsIntegral) (hc : ∀ u v, ∃ n : ℕ, G.c u v = (n : ℝ)) :
    (augmentOnce φ).IsIntegral := by
  unfold augmentOnce
  by_cases h : φ.hasAugmentingPath
  · simp [h]
    exact IsIntegral_augment φ hint hc
      (Classical.choice (Flow.hasAugmentingPath_iff_nonempty_augmentingPath.mp h))
  · simp [h]
    exact hint

/-- Repeatedly augment from a starting flow. -/
noncomputable def iterAugment {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Flow V G) : ℕ → Flow V G
  | 0 => φ
  | n + 1 => augmentOnce (iterAugment φ n)

/-- Every iterate of `iterAugment` is integral. -/
lemma IsIntegral_iterAugment {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Flow V G) (hint : φ.IsIntegral) (hc : ∀ u v, ∃ n : ℕ, G.c u v = (n : ℝ)) :
    ∀ n, (iterAugment φ n).IsIntegral := by
  intro n
  induction n with
  | zero => simpa [iterAugment] using hint
  | succ n ih =>
      simpa [iterAugment] using (IsIntegral_augmentOnce (iterAugment φ n) ih hc)

/-- Each augmentation step increases the value by at least one, unless the
flow is already free of augmenting paths. -/
lemma iterAugment_step_value {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Flow V G) (hint : φ.IsIntegral) (hc : ∀ u v, ∃ n : ℕ, G.c u v = (n : ℝ))
    (n : ℕ) :
    ¬(iterAugment φ n).hasAugmentingPath ∨
      (iterAugment φ n).value + 1 ≤ (iterAugment φ (n + 1)).value := by
  by_cases h : (iterAugment φ n).hasAugmentingPath
  · right
    simp [iterAugment, augmentOnce, h]
    exact augment_value_ge_one (iterAugment φ n) (IsIntegral_iterAugment φ hint hc n) hc
      (Classical.choice (Flow.hasAugmentingPath_iff_nonempty_augmentingPath.mp h))
  · left
    exact h

/-- Flow value is bounded by the total capacity out of the source. -/
lemma value_le_source_cut {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Flow V G) : φ.value ≤ Finset.sum (Finset.univ : Finset V) (fun v => G.c G.s v) := by
  unfold Flow.value
  exact Finset.sum_le_sum (fun v _ => φ.hcapacity G.s v)

/-- The total capacity out of the source is an integer on an integral
network. -/
lemma source_cut_integral {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (hc : ∀ u v, ∃ n : ℕ, G.c u v = (n : ℝ)) :
    ∃ n : ℕ, Finset.sum (Finset.univ : Finset V) (fun v => G.c G.s v) = (n : ℝ) := by
  classical
  choose nv hnv using (fun v => hc G.s v)
  refine ⟨Finset.sum (Finset.univ : Finset V) nv, ?_⟩
  rw [show (fun v : V => G.c G.s v) = fun v : V => (nv v : ℝ) by
    funext v
    exact hnv v]
  norm_cast

/-- While every step finds an augmenting path, the value after `n` steps is
at least `n`. -/
lemma iterAugment_value_ge {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (φ : Flow V G) (hint : φ.IsIntegral)
    (hc : ∀ u v, ∃ n : ℕ, G.c u v = (n : ℝ)) (hφ : 0 ≤ φ.value)
    (hsteps : ∀ n, (iterAugment φ n).hasAugmentingPath) :
    ∀ n : ℕ, (n : ℝ) ≤ (iterAugment φ n).value := by
  intro n
  induction n with
  | zero => simpa [iterAugment] using hφ
  | succ n ih =>
      have hinc := (iterAugment_step_value φ hint hc n).resolve_left (not_not_intro (hsteps n))
      push_cast
      linarith

/-- Repeated augmentation from an integral flow terminates at a flow without
augmenting paths: the value strictly increases by at least one each step and
is bounded by the (integral) source-side cut capacity. -/
lemma exists_noAugmentingPath_iter {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (φ : Flow V G) (hint : φ.IsIntegral)
    (hc : ∀ u v, ∃ n : ℕ, G.c u v = (n : ℝ)) (hφ : 0 ≤ φ.value) :
    ∃ n, ¬ (iterAugment φ n).hasAugmentingPath := by
  by_contra hnot
  have hsteps : ∀ n, (iterAugment φ n).hasAugmentingPath := by
    intro n
    by_contra h
    exact hnot ⟨n, h⟩
  rcases source_cut_integral hc with ⟨K, hK⟩
  have hge : ((K + 1 : ℕ) : ℝ) ≤ (iterAugment φ (K + 1)).value :=
    iterAugment_value_ge φ hint hc hφ hsteps (K + 1)
  have hle : (iterAugment φ (K + 1)).value ≤ (K : ℝ) := by
    rw [← hK]
    exact value_le_source_cut (iterAugment φ (K + 1))
  have hle' : ((K + 1 : ℕ) : ℝ) ≤ (K : ℝ) := le_trans hge hle
  norm_num at hle'

/-- The matching network has integral capacities (in fact `0` or `1`). -/
lemma toFlowNetwork_integral_capacity {V : Type*} [Fintype V] [DecidableEq V]
    {G : BipartiteGraph V} : ∀ u v, ∃ n : ℕ, (toFlowNetwork V G).c u v = (n : ℝ) := by
  intro u v
  cases u with
  | inl a =>
    cases v with
    | inl b =>
      change ∃ n : ℕ, (if (a, b) ∈ G.E then (1 : ℝ) else 0) = (n : ℝ)
      by_cases h : (a, b) ∈ G.E
      · exact ⟨1, by simp [h]⟩
      · exact ⟨0, by simp [h]⟩
    | inr b =>
      cases b with
      | true =>
        change ∃ n : ℕ, (0 : ℝ) = (n : ℝ)
        exact ⟨0, by norm_num⟩
      | false =>
        change ∃ n : ℕ, (if a ∈ G.R then (1 : ℝ) else 0) = (n : ℝ)
        by_cases h : a ∈ G.R
        · exact ⟨1, by simp [h]⟩
        · exact ⟨0, by simp [h]⟩
  | inr a =>
    cases a with
    | true =>
      cases v with
      | inl b =>
        change ∃ n : ℕ, (if b ∈ G.L then (1 : ℝ) else 0) = (n : ℝ)
        by_cases h : b ∈ G.L
        · exact ⟨1, by simp [h]⟩
        · exact ⟨0, by simp [h]⟩
      | inr b =>
        cases b <;> (change ∃ n : ℕ, (0 : ℝ) = (n : ℝ); exact ⟨0, by norm_num⟩)
    | false =>
      cases v with
      | inl b =>
        change ∃ n : ℕ, (0 : ℝ) = (n : ℝ)
        exact ⟨0, by norm_num⟩
      | inr b =>
        cases b <;> (change ∃ n : ℕ, (0 : ℝ) = (n : ℝ); exact ⟨0, by norm_num⟩)

/-- **Theorem 24.12 (CLRS).**  In the unit-capacity network of a bipartite
graph, the maximum matching size equals the maximum flow value: there is a
matching at least as large as every matching, and a maximal flow whose value
is exactly its size. -/
theorem maxMatching_eq_maxFlow_value {V : Type*} [Fintype V] [DecidableEq V]
    {G : BipartiteGraph V} :
    ∃ M : Matching V G, (∀ M' : Matching V G, M'.size ≤ M.size) ∧
      ∃ φ : Flow (V ⊕ Bool) (toFlowNetwork V G), φ.isMaximal ∧ φ.value = (M.size : ℝ) := by
  let N : FlowNetwork (V ⊕ Bool) := toFlowNetwork V G
  let zf : Flow (V ⊕ Bool) N := zeroFlow N
  have hc : ∀ u v, ∃ n : ℕ, N.c u v = (n : ℝ) := by
    intro u v
    exact toFlowNetwork_integral_capacity u v
  have hz : 0 ≤ zf.value := by
    unfold Flow.value
    simp [zf, zeroFlow]
  rcases exists_noAugmentingPath_iter zf (IsIntegral_zero (G := N)) hc hz with
    ⟨n, hn⟩
  let φ : Flow (V ⊕ Bool) N := iterAugment zf n
  have hintφ : φ.IsIntegral := IsIntegral_iterAugment zf (IsIntegral_zero (G := N)) hc n
  have hmax : φ.isMaximal := Flow.maximal_of_noAugmentingPath φ hn
  let M : Matching V G := matchingOfIntegralFlow φ hintφ
  refine ⟨M, ?_, φ, hmax, ?_⟩
  · intro M'
    have hvalφ : φ.value = (M.size : ℝ) := (matchingOfIntegralFlow_size φ hintφ).symm
    have hvalM : (matchingToFlow M').value = (M'.size : ℝ) := matchingToFlow_value M'
    have hle : (matchingToFlow M').value ≤ φ.value := hmax (matchingToFlow M')
    have hsize : (M'.size : ℝ) ≤ (M.size : ℝ) := by linarith
    exact_mod_cast hsize
  · exact (matchingOfIntegralFlow_size φ hintφ).symm

end Chapter26
end CLRS

import Mathlib
import CLRSLean.Chapter_22.Section_22_1_Representing_Graphs

open Classical

/-! # Section 24.0 — Weighted Graphs

Extends the finite-graph model from Section 22.1 with real-valued edge weights
and defines the shortest-path weight `δ(s,v)`.

Main definitions:

- `WeightedGraph V`: a finite directed graph with a real-valued edge-weight
  function `weight : V → V → ℝ`.
- `WeightedGraph.walkWeight`: sum of edge weights along a vertex list.
- `WeightedGraph.δ`: shortest-path weight from `s` to `v` — the infimum of all
  walk weights, represented as `WithTop ℝ` (`⊤` for unreachable; `some w`
  otherwise).

Results:
- `δ_le_walkWeight`: δ(s,v) ≤ walkWeight(p) for any walk p (nonneg weights).
- `δ_self`: δ(s,v) = 0 when s = v and weights are nonnegative.
- `δ_nonneg`: 0 ≤ δ(s,v) under nonnegative weights.
- `walkWeight_nonneg`: nonnegative edge weights imply nonnegative walk weights.
-/

namespace CLRS
namespace Chapter24

open Chapter22

/-- A weighted directed graph: a finite graph with real-valued edge weights. -/
structure WeightedGraph (V : Type) [DecidableEq V] extends Graph V where
  weight : V → V → ℝ

namespace WeightedGraph

variable {V : Type} [DecidableEq V] (G : WeightedGraph V)

/-! ## Walk weight -/

/-- Sum of edge weights along a vertex list. -/
def walkWeight : List V → ℝ
  | [] | [_] => 0
  | u :: v :: rest => G.weight u v + walkWeight (v :: rest)

@[simp] theorem walkWeight_nil : G.walkWeight [] = 0 := rfl
@[simp] theorem walkWeight_singleton (u : V) : G.walkWeight [u] = 0 := rfl

theorem walkWeight_pair (u v : V) : G.walkWeight [u, v] = G.weight u v := by
  simp [walkWeight]

theorem walkWeight_nonneg (h : ∀ u v, G.weight u v ≥ 0) (p : List V) :
    G.walkWeight p ≥ 0 := by
  induction' p with u p ih
  · simp [walkWeight]
  · cases' p with v rest
    · simp [walkWeight]
    · have hpos := h u v
      have ih' : G.walkWeight (v :: rest) ≥ 0 := ih
      simp [walkWeight]
      nlinarith

/-! ## Set of walk weights -/

/-- The set of all walk weights from `s` to `v`. -/
def walkWeightsSet (s v : V) : Set ℝ :=
  { w | ∃ (p : List V), (G.toGraph).IsWalkFromTo p s v ∧ G.walkWeight p = w }

/-! ## Shortest-path weight δ(s,v) -/

/-- Shortest-path weight `δ(s,v)`: the infimum of all walk weights from `s` to
`v`.  Returns `⊤` (top) when no walk from `s` to `v` exists. -/
noncomputable def δ (s v : V) : WithTop ℝ :=
  if h : (G.walkWeightsSet s v).Nonempty then
    some (sInf (G.walkWeightsSet s v))
  else
    ⊤

theorem δ_le_walkWeight (hnonneg : ∀ u v, G.weight u v ≥ 0)
    {s v : V} (p : List V) (hw : (G.toGraph).IsWalkFromTo p s v) :
    G.δ s v ≤ (G.walkWeight p : WithTop ℝ) := by
  unfold δ walkWeightsSet
  by_cases h : ({ w | ∃ (p : List V), (G.toGraph).IsWalkFromTo p s v ∧ G.walkWeight p = w }).Nonempty
  · have hbdd : BddBelow { w | ∃ (p : List V),
        (G.toGraph).IsWalkFromTo p s v ∧ G.walkWeight p = w } := by
      refine ⟨0, ?_⟩
      intro w hw'
      rcases hw' with ⟨p', _, hw_eq⟩
      rw [← hw_eq]
      exact G.walkWeight_nonneg hnonneg p'
    have hmem : G.walkWeight p ∈ { w | ∃ (p : List V),
        (G.toGraph).IsWalkFromTo p s v ∧ G.walkWeight p = w } :=
      ⟨p, hw, rfl⟩
    simp [h]
    exact WithTop.coe_le_coe.mpr (csInf_le hbdd hmem)
  · exfalso; exact h ⟨G.walkWeight p, p, hw, rfl⟩

theorem δ_self (s : V) (hs_vert : s ∈ G.vertices)
    (hnonneg : ∀ u v, G.weight u v ≥ 0) : G.δ s s = (0 : WithTop ℝ) := by
  have hwalk : (G.toGraph).IsWalkFromTo [s] s s := by
    refine ⟨(G.toGraph).isWalk_singleton hs_vert, ?_, ?_⟩
    · simp
    · simp
  have h_upper : G.δ s s ≤ (0 : WithTop ℝ) := by
    have h := G.δ_le_walkWeight hnonneg [s] hwalk
    simpa [walkWeight_singleton] using h
  have h_lower : (0 : WithTop ℝ) ≤ G.δ s s := by
    unfold δ walkWeightsSet
    by_cases hne : ({ w | ∃ (p : List V), (G.toGraph).IsWalkFromTo p s s ∧ G.walkWeight p = w }).Nonempty
    · have h_inf_nonneg : (0 : ℝ) ≤ sInf ({ w | ∃ (p : List V),
          (G.toGraph).IsWalkFromTo p s s ∧ G.walkWeight p = w } : Set ℝ) :=
        le_csInf hne (by
          intro w hw
          rcases hw with ⟨p', _, hw_eq⟩
          rw [← hw_eq]
          exact G.walkWeight_nonneg hnonneg p')
      simp [hne]
      exact WithTop.coe_nonneg.mpr h_inf_nonneg
    · exfalso; apply hne
      refine ⟨0, [s], ?_, by simp [walkWeight]⟩
      refine ⟨(G.toGraph).isWalk_singleton hs_vert, ?_, ?_⟩
      · simp
      · simp
  exact le_antisymm h_upper h_lower

theorem δ_nonneg (hnonneg : ∀ u v, G.weight u v ≥ 0) (s v : V) :
    (0 : WithTop ℝ) ≤ G.δ s v := by
  unfold δ walkWeightsSet
  by_cases hne : ({ w | ∃ (p : List V), (G.toGraph).IsWalkFromTo p s v ∧ G.walkWeight p = w }).Nonempty
  · have h_inf_nonneg : (0 : ℝ) ≤ sInf ({ w | ∃ (p : List V),
        (G.toGraph).IsWalkFromTo p s v ∧ G.walkWeight p = w } : Set ℝ) :=
      le_csInf hne (by
        intro w hw
        rcases hw with ⟨p', _, hw_eq⟩
        rw [← hw_eq]
        exact G.walkWeight_nonneg hnonneg p')
    simp [hne]
    exact WithTop.coe_nonneg.mpr h_inf_nonneg
  · simp [hne]

end WeightedGraph

end Chapter24
end CLRS

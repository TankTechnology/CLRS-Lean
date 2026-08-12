import CLRSLean.FourthEdition.Chapter_22.Section_22_4_Difference_Constraints

/-!
# 29.2: Shortest paths as a linear program

For a source {lit}`s` and target {lit}`t`, CLRS maximizes {lit}`d t`, subject to
{lit}`d s = 0` and {lit}`d v ≤ d u + w u v` on every edge.  Thus every feasible
{lit}`d t` is a lower bound on every {lit}`s`-to-{lit}`t` walk; an attained
bound is optimal.
-/

namespace CLRS
namespace Chapter29
namespace ShortestPathLP

open Chapter24

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Feasibility constraints of the CLRS shortest-path LP. -/
def IsFeasible (G : WeightedGraph V) (s : V) (d : V → ℝ) : Prop :=
  d s = 0 ∧ ∀ u v, (u, v) ∈ G.edges → d v ≤ d u + G.w u v

/-- Optimality for the maximization objective {lit}`d t`. -/
def IsOptimal (G : WeightedGraph V) (s t : V) (d : V → ℝ) : Prop :=
  IsFeasible G s d ∧ ∀ e, IsFeasible G s e → e t ≤ d t

/-- Every feasible potential is a lower bound on the weight of every walk from
the source.  This is the core correctness property of the formulation. -/
theorem feasible_le_walkWeight {G : WeightedGraph V} {s t : V} {d : V → ℝ}
    (hd : IsFeasible G s d) (p : List V) (hp : G.IsWalkFrom s t p) :
    d t ≤ Chapter24.WeightedGraph.walkWeight G.w p := by
  have h := Chapter24.WeightedGraph.le_add_walkWeight_of_potential G d hd.2 s t p hp
  simpa [hd.1] using h

/-- If a feasible potential is attained by an actual source-to-target walk,
then it solves the shortest-path LP. -/
theorem optimal_of_attained_walk {G : WeightedGraph V} {s t : V} {d : V → ℝ}
    (hd : IsFeasible G s d) (p : List V) (hp : G.IsWalkFrom s t p)
    (hweight : Chapter24.WeightedGraph.walkWeight G.w p = d t) : IsOptimal G s t d := by
  refine ⟨hd, ?_⟩
  intro e he
  calc
    e t ≤ Chapter24.WeightedGraph.walkWeight G.w p := feasible_le_walkWeight he p hp
    _ = d t := hweight

end ShortestPathLP
end Chapter29
end CLRS

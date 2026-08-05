import Mathlib

/-!
# 29.2: Common finite-network definitions

CLRS writes its flow linear programs with one nonnegative variable `f u v`
for every ordered pair of vertices.  A missing edge is represented by capacity
zero.  This file records that shared finite-network vocabulary.
-/

namespace CLRS
namespace Chapter29

open Finset

/-- A finite directed capacitated network.  Capacities are total; assigning
capacity zero to nonedges gives exactly the convention used in CLRS §29.2. -/
structure FlowNetwork (V : Type*) [Fintype V] where
  source : V
  sink : V
  source_ne_sink : source ≠ sink
  capacity : V → V → ℝ
  capacity_nonnegative : ∀ u v, 0 ≤ capacity u v

namespace FlowNetwork

variable {V : Type*} [Fintype V] (N : FlowNetwork V)

/-- Total flow leaving a vertex. -/
def outflow (f : V → V → ℝ) (u : V) : ℝ := ∑ v, f u v

/-- Total flow entering a vertex. -/
def inflow (f : V → V → ℝ) (u : V) : ℝ := ∑ v, f v u

/-- Net flow leaving a vertex. -/
def netOutflow (f : V → V → ℝ) (u : V) : ℝ := outflow f u - inflow f u

/-- Flow conservation at one vertex. -/
def ConservesAt (f : V → V → ℝ) (u : V) : Prop := inflow f u = outflow f u

/-- The nonnegativity and capacity inequalities shared by the flow LPs. -/
def IsCapacityFeasible (f : V → V → ℝ) : Prop :=
  (∀ u v, 0 ≤ f u v) ∧ ∀ u v, f u v ≤ N.capacity u v

/-- A feasible single-commodity flow: capacity constraints everywhere and
conservation away from the source and sink. -/
def IsFlow (f : V → V → ℝ) : Prop :=
  N.IsCapacityFeasible f ∧
    ∀ u, u ≠ N.source → u ≠ N.sink → ConservesAt f u

end FlowNetwork

end Chapter29
end CLRS

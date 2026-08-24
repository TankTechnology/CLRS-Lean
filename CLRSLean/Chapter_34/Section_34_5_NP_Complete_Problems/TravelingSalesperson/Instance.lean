import Mathlib

/-!
# Finite decision-TSP instances

This file gives the typed decision problem used by the textbook reduction from
HAM-CYCLE.  The complete weighted graph has `vertexCount` vertices, an explicit
budget, and a natural-number weight for every pair of in-range vertices.
-/

namespace CLRS.Chapter34

/-- A finite complete weighted graph together with a tour-cost budget. -/
structure TSPInstance where
  vertexCount : Nat
  budget : Nat
  weight : Fin vertexCount → Fin vertexCount → Nat

namespace TSPInstance

/-- Read an edge weight using natural-number vertex names.  Out-of-range names
receive weight zero; valid tour certificates never use that fallback. -/
def edgeWeight (I : TSPInstance) (u v : Nat) : Nat :=
  if hu : u < I.vertexCount then
    if hv : v < I.vertexCount then
      I.weight ⟨u, hu⟩ ⟨v, hv⟩
    else 0
  else 0

theorem edgeWeight_of_lt (I : TSPInstance) {u v : Nat}
    (hu : u < I.vertexCount) (hv : v < I.vertexCount) :
    I.edgeWeight u v = I.weight ⟨u, hu⟩ ⟨v, hv⟩ := by
  simp [edgeWeight, hu, hv]

/-- Last element of a nonempty list, without carrying a proof argument. -/
def lastFrom (current : Nat) : List Nat → Nat
  | [] => current
  | next :: rest => lastFrom next rest

theorem lastFrom_mem (current : Nat) (rest : List Nat) :
    lastFrom current rest ∈ current :: rest := by
  induction rest generalizing current with
  | nil => simp [lastFrom]
  | cons next rest ih =>
      simp only [lastFrom, List.mem_cons]
      exact Or.inr (by simpa only [List.mem_cons] using ih next)

/-- Cost of all consecutive edges in a vertex list. -/
def pathCost (I : TSPInstance) : List Nat → Nat
  | [] => 0
  | [_] => 0
  | u :: v :: rest => I.edgeWeight u v + I.pathCost (v :: rest)

/-- Cost of the cyclic tour obtained by adding the last-to-first edge. -/
def tourCost (I : TSPInstance) : List Nat → Nat
  | [] => 0
  | first :: rest =>
      I.pathCost (first :: rest) + I.edgeWeight (lastFrom first rest) first

/-- A decision-TSP certificate lists every vertex exactly once and has total
cyclic cost at most the instance budget. -/
def ListRepresentsTour (I : TSPInstance) (vertices : List Nat) : Prop :=
  3 ≤ I.vertexCount ∧
    vertices.Nodup ∧
    vertices.length = I.vertexCount ∧
    (∀ v ∈ vertices, v < I.vertexCount) ∧
    I.tourCost vertices ≤ I.budget

/-- The decision-TSP instance admits a tour within its budget. -/
def HasTour (I : TSPInstance) : Prop :=
  ∃ vertices, I.ListRepresentsTour vertices

instance decidableListRepresentsTour
    (I : TSPInstance) (vertices : List Nat) :
    Decidable (I.ListRepresentsTour vertices) := by
  unfold ListRepresentsTour
  infer_instance

end TSPInstance
end CLRS.Chapter34

import Mathlib

/-!
# General graph-plus-k CLIQUE instances

This module gives the mathematical model for the textbook CLIQUE decision
problem.  An undirected edge is stored once, with its smaller endpoint first.

Main definitions:

- `CliqueInstance.WellFormed`: canonical finite graph encoding invariants.
- `CliqueInstance.Adj`: symmetric adjacency induced by normalized edges.
- `CliqueInstance.HasClique`: a clique of exactly the requested size.
-/

namespace CLRS
namespace Chapter34

/-! ## Instances and graph semantics -/

/-- A finite undirected graph together with the requested clique size.
Edges use natural-number vertex names and are stored in normalized order. -/
structure CliqueInstance where
  vertexCount : Nat
  targetSize : Nat
  edges : List (Nat × Nat)
  deriving DecidableEq, Repr

namespace CliqueInstance

/-- A CLIQUE instance is well formed when the target fits in the vertex set
and its edge list is duplicate-free, normalized, and in range. -/
def WellFormed (I : CliqueInstance) : Prop :=
  I.targetSize ≤ I.vertexCount ∧
    I.edges.Nodup ∧
    ∀ e ∈ I.edges, e.1 < e.2 ∧ e.2 < I.vertexCount

/-- Symmetric adjacency induced by the normalized edge list. -/
def Adj (I : CliqueInstance) (u v : Nat) : Prop :=
  if u < v then (u, v) ∈ I.edges
  else if v < u then (v, u) ∈ I.edges
  else False

/-- The graph contains a clique with exactly the requested number of vertices. -/
def HasClique (I : CliqueInstance) : Prop :=
  ∃ vertices : Finset Nat,
    vertices.card = I.targetSize ∧
      (∀ v ∈ vertices, v < I.vertexCount) ∧
      ∀ u ∈ vertices, ∀ v ∈ vertices, u ≠ v → I.Adj u v

/-- Well-formedness is executable because every universal check is bounded by
the stored finite edge list. -/
instance decidableWellFormed (I : CliqueInstance) : Decidable I.WellFormed := by
  unfold WellFormed
  infer_instance

/-- Adjacency is decidable by the two normalized edge lookups. -/
instance decidableAdj (I : CliqueInstance) (u v : Nat) : Decidable (I.Adj u v) := by
  unfold Adj
  infer_instance

/-! ## Adjacency interface -/

/-- Below the diagonal, adjacency is exactly normalized edge membership. -/
theorem adj_iff_of_lt (I : CliqueInstance) {u v : Nat} (huv : u < v) :
    I.Adj u v ↔ (u, v) ∈ I.edges := by
  simp [Adj, huv]

/-- Above the diagonal, adjacency checks the reversed normalized edge. -/
theorem adj_iff_of_gt (I : CliqueInstance) {u v : Nat} (hvu : v < u) :
    I.Adj u v ↔ (v, u) ∈ I.edges := by
  simp [Adj, hvu, Nat.not_lt.mpr (Nat.le_of_lt hvu)]

/-- Adjacency has an order-independent normalized-edge characterization. -/
theorem adj_iff (I : CliqueInstance) (u v : Nat) :
    I.Adj u v ↔
      (u < v ∧ (u, v) ∈ I.edges) ∨ (v < u ∧ (v, u) ∈ I.edges) := by
  by_cases huv : u < v
  · simp [Adj, huv, Nat.not_lt.mpr (Nat.le_of_lt huv)]
  · by_cases hvu : v < u
    · simp [Adj, huv, hvu]
    · simp [Adj, huv, hvu]

/-- The induced undirected adjacency relation is symmetric. -/
theorem adj_comm (I : CliqueInstance) (u v : Nat) :
    I.Adj u v ↔ I.Adj v u := by
  rw [adj_iff, adj_iff]
  aesop

/-- Normalized edge membership introduces adjacency. -/
theorem adj_of_mem (I : CliqueInstance) {u v : Nat}
    (huv : u < v) (hedge : (u, v) ∈ I.edges) : I.Adj u v :=
  (I.adj_iff_of_lt huv).2 hedge

/-- No vertex is adjacent to itself. -/
theorem not_adj_self (I : CliqueInstance) (u : Nat) : ¬ I.Adj u u := by
  simp [Adj]

end CliqueInstance

end Chapter34
end CLRS

import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.Reduction.Construction

/-!
# Cost semantics of the HAM-CYCLE to TSP construction

The constructed tour cost is exactly the number of visited vertices plus the
number of source-graph cycle edges that are missing.  This identity is the
entire numerical core of both reduction directions.
-/

namespace CLRS.Chapter34.TSPReduction

/-- Number of consecutive path pairs that are nonedges of the source graph. -/
def missingPathEdges (G : HamiltonianCycleInstance) : List Nat → Nat
  | [] => 0
  | [_] => 0
  | u :: v :: rest =>
      (if G.Adj u v then 0 else 1) + missingPathEdges G (v :: rest)

/-- Number of nonedges in the cyclic closure.  The empty list is assigned one
missing edge so that zero characterizes `CycleAdjacent` without a side condition. -/
def missingCycleEdges (G : HamiltonianCycleInstance) : List Nat → Nat
  | [] => 1
  | first :: rest =>
      missingPathEdges G (first :: rest) +
        if G.Adj (TSPInstance.lastFrom first rest) first then 0 else 1

@[simp] theorem tsp_lastFrom_eq_hamiltonian_lastFrom
    (first : Nat) (rest : List Nat) :
    TSPInstance.lastFrom first rest = CliqueInstance.lastFrom first rest := by
  induction rest generalizing first with
  | nil => rfl
  | cons next rest ih =>
      simpa [TSPInstance.lastFrom, CliqueInstance.lastFrom] using ih next

theorem pathCost_hamiltonianToTSP
    (G : HamiltonianCycleInstance) (vertices : List Nat)
    (hbound : ∀ v ∈ vertices, v < G.vertexCount) :
    (hamiltonianToTSP G).pathCost vertices =
      (vertices.length - 1) + missingPathEdges G vertices := by
  induction vertices using List.twoStepInduction with
  | nil => simp [TSPInstance.pathCost, missingPathEdges]
  | singleton v => simp [TSPInstance.pathCost, missingPathEdges]
  | cons_cons u v rest _ ih =>
      have hu : u < G.vertexCount := hbound u (by simp)
      have hv : v < G.vertexCount := hbound v (by simp)
      have htail : ∀ w ∈ v :: rest, w < G.vertexCount := by
        intro w hw
        exact hbound w (by simp [hw])
      simp only [TSPInstance.pathCost, missingPathEdges, List.length_cons]
      rw [hamiltonianToTSP_edgeWeight_of_lt G hu hv, ih v htail]
      simp only [List.length_cons, Nat.add_sub_cancel]
      split <;> omega

theorem tourCost_hamiltonianToTSP
    (G : HamiltonianCycleInstance) (first : Nat) (rest : List Nat)
    (hbound : ∀ v ∈ first :: rest, v < G.vertexCount) :
    (hamiltonianToTSP G).tourCost (first :: rest) =
      (first :: rest).length + missingCycleEdges G (first :: rest) := by
  have hfirst : first < G.vertexCount := hbound first (by simp)
  have hlast : TSPInstance.lastFrom first rest < G.vertexCount :=
    hbound _ (TSPInstance.lastFrom_mem first rest)
  rw [TSPInstance.tourCost, pathCost_hamiltonianToTSP G (first :: rest) hbound,
    hamiltonianToTSP_edgeWeight_of_lt G hlast hfirst]
  simp only [missingCycleEdges, List.length_cons]
  split <;> omega

theorem missingPathEdges_eq_zero_iff
    (G : HamiltonianCycleInstance) (vertices : List Nat) :
    missingPathEdges G vertices = 0 ↔ G.PathAdjacent vertices := by
  induction vertices using List.twoStepInduction with
  | nil => simp [missingPathEdges, CliqueInstance.PathAdjacent]
  | singleton v => simp [missingPathEdges, CliqueInstance.PathAdjacent]
  | cons_cons u v rest _ ih =>
      simp [missingPathEdges, CliqueInstance.PathAdjacent, ih]

theorem missingCycleEdges_eq_zero_iff
    (G : HamiltonianCycleInstance) (vertices : List Nat) :
    missingCycleEdges G vertices = 0 ↔ G.CycleAdjacent vertices := by
  cases vertices with
  | nil => simp [missingCycleEdges, CliqueInstance.CycleAdjacent]
  | cons first rest =>
      simp [missingCycleEdges, CliqueInstance.CycleAdjacent,
        missingPathEdges_eq_zero_iff]

end CLRS.Chapter34.TSPReduction

import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.Reduction.CostSemantics

/-!
# Correctness of the HAM-CYCLE to decision-TSP reduction
-/

namespace CLRS.Chapter34.TSPReduction

theorem hamiltonianToTSP_complete (G : HamiltonianCycleInstance) :
    G.HasHamiltonianCycle → (hamiltonianToTSP G).HasTour := by
  rintro ⟨vertices, hthree, hnodup, hlength, hbound, hcycle⟩
  refine ⟨vertices, ?_⟩
  refine ⟨hthree, hnodup, hlength, hbound, ?_⟩
  cases vertices with
  | nil => simp [CliqueInstance.CycleAdjacent] at hcycle
  | cons first rest =>
      have hmissing : missingCycleEdges G (first :: rest) = 0 :=
        (missingCycleEdges_eq_zero_iff G (first :: rest)).2 hcycle
      rw [tourCost_hamiltonianToTSP G first rest hbound,
        hmissing, hlength]
      simp

theorem hamiltonianToTSP_sound (G : HamiltonianCycleInstance) :
    (hamiltonianToTSP G).HasTour → G.HasHamiltonianCycle := by
  rintro ⟨vertices, hthree, hnodup, hlength, hbound, hcost⟩
  refine ⟨vertices, hthree, hnodup, hlength, hbound, ?_⟩
  cases vertices with
  | nil =>
      change 3 ≤ G.vertexCount at hthree
      change [].length = G.vertexCount at hlength
      simp at hlength
      omega
  | cons first rest =>
      have hcostIdentity :=
        tourCost_hamiltonianToTSP G first rest hbound
      change (first :: rest).length = G.vertexCount at hlength
      change (hamiltonianToTSP G).tourCost (first :: rest) ≤
        G.vertexCount at hcost
      have hcostIdentity' :
          (hamiltonianToTSP G).tourCost (first :: rest) =
            G.vertexCount + missingCycleEdges G (first :: rest) := by
        rw [hcostIdentity, hlength]
      have hbudget : G.vertexCount + missingCycleEdges G (first :: rest) ≤
          G.vertexCount := by
        calc
          G.vertexCount + missingCycleEdges G (first :: rest) =
              (hamiltonianToTSP G).tourCost (first :: rest) := hcostIdentity'.symm
          _ ≤ G.vertexCount := hcost
      have hmissing : missingCycleEdges G (first :: rest) = 0 := by omega
      exact (missingCycleEdges_eq_zero_iff G (first :: rest)).1 hmissing

/-- The typed textbook HAM-CYCLE-to-decision-TSP equivalence. -/
theorem hamiltonianToTSP_correct (G : HamiltonianCycleInstance) :
    G.HasHamiltonianCycle ↔ (hamiltonianToTSP G).HasTour :=
  ⟨hamiltonianToTSP_complete G, hamiltonianToTSP_sound G⟩

end CLRS.Chapter34.TSPReduction

import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.VerifierMachine.CyclePairStream

/-! # Simple-cycle properties of TSP certificate edge streams -/

namespace CLRS.Chapter34.Turing.TSPVerifier.CostSemantics

open HamiltonianCycle.VerifierMachine.CyclePairs
open GeneralCliqueVerifier.QueryNormalizer

private theorem normalizeQuery_eq_iff (left right : Nat × Nat) :
    normalizeQuery left = normalizeQuery right ↔
      left = right ∨ left = (right.2, right.1) := by
  rcases left with ⟨a, b⟩
  rcases right with ⟨c, d⟩
  by_cases hab : a ≤ b <;> by_cases hcd : c ≤ d <;>
    simp [normalizeQuery, hab, hcd, Prod.ext_iff] <;> omega

theorem pathPairsFrom_endpoints_mem {previous : Nat} {rest : List Nat}
    {pair : Nat × Nat} (hpair : pair ∈ pathPairsFrom previous rest) :
    pair.1 ∈ previous :: rest ∧ pair.2 ∈ previous :: rest := by
  induction rest generalizing previous with
  | nil => simp [pathPairsFrom] at hpair
  | cons current rest ih =>
      rw [pathPairsFrom] at hpair
      rcases List.mem_cons.mp hpair with rfl | htail
      · simp
      · have hendpoints := ih htail
        exact ⟨by simp [hendpoints.1], by simp [hendpoints.2]⟩

private theorem lastFrom_eq (current : Nat) (rest : List Nat) :
    CliqueInstance.lastFrom current rest =
      TSPInstance.lastFrom current rest := by
  induction rest generalizing current with
  | nil => rfl
  | cons next rest ih =>
      simp only [CliqueInstance.lastFrom, TSPInstance.lastFrom]
      exact ih next

theorem cyclePairs_endpoints_mem {vertices : List Nat}
    {pair : Nat × Nat} (hpair : pair ∈ cyclePairs vertices) :
    pair.1 ∈ vertices ∧ pair.2 ∈ vertices := by
  cases vertices with
  | nil => simp [cyclePairs] at hpair
  | cons first rest =>
      rw [cyclePairs, List.mem_append] at hpair
      rcases hpair with hpath | hclosing
      · exact pathPairsFrom_endpoints_mem hpath
      · have hpairEq := List.mem_singleton.mp hclosing
        subst pair
        constructor
        · rw [lastFrom_eq]
          exact TSPInstance.lastFrom_mem first rest
        · exact List.mem_cons_self

private theorem normalizedPathPairs_nodup (previous : Nat)
    (rest : List Nat) (hnodup : (previous :: rest).Nodup) :
    ((pathPairsFrom previous rest).map normalizeQuery).Nodup := by
  induction rest generalizing previous with
  | nil => simp [pathPairsFrom]
  | cons current rest ih =>
      rw [pathPairsFrom, List.map_cons, List.nodup_cons]
      have hprevious : previous ∉ current :: rest :=
        (List.nodup_cons.mp hnodup).1
      refine ⟨?_, ih current (List.nodup_cons.mp hnodup).2⟩
      intro hmem
      rcases List.mem_map.mp hmem with ⟨pair, hpair, heq⟩
      have horientation := (normalizeQuery_eq_iff _ _).mp heq.symm
      have hendpoints := pathPairsFrom_endpoints_mem hpair
      rcases horientation with horientation | horientation
      · have hfirst := congrArg Prod.fst horientation
        simp only at hfirst
        apply hprevious
        rw [hfirst]
        exact hendpoints.1
      · have hfirst := congrArg Prod.fst horientation
        simp only at hfirst
        apply hprevious
        rw [hfirst]
        exact hendpoints.2

private theorem lastFrom_mem_tail (current next : Nat) (rest : List Nat) :
    CliqueInstance.lastFrom current (next :: rest) ∈ next :: rest := by
  rw [lastFrom_eq]
  simpa [TSPInstance.lastFrom] using
    TSPInstance.lastFrom_mem next rest

private theorem pathPairsFrom_endpoints_ne (previous : Nat)
    (rest : List Nat) (hnodup : (previous :: rest).Nodup)
    {pair : Nat × Nat} (hpair : pair ∈ pathPairsFrom previous rest) :
    pair.1 ≠ pair.2 := by
  induction rest generalizing previous pair with
  | nil => simp [pathPairsFrom] at hpair
  | cons current rest ih =>
      rw [pathPairsFrom] at hpair
      rcases List.mem_cons.mp hpair with rfl | htail
      · intro heq
        simp only at heq
        exact (List.nodup_cons.mp hnodup).1
          (List.mem_cons.mpr (Or.inl heq))
      · exact ih current (List.nodup_cons.mp hnodup).2 htail

theorem cyclePairs_endpoints_ne {vertices : List Nat}
    (hthree : 3 ≤ vertices.length) (hnodup : vertices.Nodup)
    {pair : Nat × Nat} (hpair : pair ∈ cyclePairs vertices) :
    pair.1 ≠ pair.2 := by
  cases vertices with
  | nil => simp at hthree
  | cons first rest =>
      cases rest with
      | nil => simp at hthree
      | cons second rest =>
          rw [cyclePairs, List.mem_append] at hpair
          rcases hpair with hpath | hclosing
          · exact pathPairsFrom_endpoints_ne first (second :: rest)
              hnodup hpath
          · have hpairEq := List.mem_singleton.mp hclosing
            subst pair
            intro heq
            simp only at heq
            have hlastMem : CliqueInstance.lastFrom first (second :: rest) ∈
                second :: rest := lastFrom_mem_tail first second rest
            rw [heq] at hlastMem
            exact (List.nodup_cons.mp hnodup).1 hlastMem

/-- A certificate with at least three distinct vertices yields distinct
undirected cyclic edges after endpoint normalization. -/
theorem normalizedCyclePairs_nodup (vertices : List Nat)
    (hthree : 3 ≤ vertices.length) (hnodup : vertices.Nodup) :
    ((cyclePairs vertices).map normalizeQuery).Nodup := by
  cases vertices with
  | nil => simp at hthree
  | cons first rest =>
      cases rest with
      | nil => simp at hthree
      | cons second rest =>
          cases rest with
          | nil => simp at hthree
          | cons third rest =>
              let tailVertices := third :: rest
              let closing :=
                (CliqueInstance.lastFrom second tailVertices, first)
              have hpathNodup :
                  ((pathPairsFrom first (second :: tailVertices)).map
                    normalizeQuery).Nodup :=
                normalizedPathPairs_nodup first (second :: tailVertices) hnodup
              have hfirstNotTail : first ∉ second :: tailVertices :=
                (List.nodup_cons.mp hnodup).1
              have hsecondNotTail : second ∉ tailVertices := by
                exact (List.nodup_cons.mp
                  (List.nodup_cons.mp hnodup).2).1
              have hlastMem : CliqueInstance.lastFrom second tailVertices ∈
                  tailVertices := lastFrom_mem_tail second third rest
              rw [cyclePairs, List.map_append, List.map_singleton,
                List.nodup_append']
              refine ⟨hpathNodup, List.nodup_singleton _, ?_⟩
              rw [List.disjoint_left]
              intro candidate hcandidate hclosing
              simp only [List.mem_singleton] at hclosing
              subst candidate
              rcases List.mem_map.mp hcandidate with
                ⟨pair, hpair, heq⟩
              rw [pathPairsFrom] at hpair
              rcases List.mem_cons.mp hpair with rfl | htail
              · have horientation :=
                  (normalizeQuery_eq_iff _ _).mp heq
                rcases horientation with horientation | horientation
                · have hfirst := congrArg Prod.fst horientation
                  have hsecond := congrArg Prod.snd horientation
                  simp only at hfirst hsecond
                  apply hfirstNotTail
                  rw [← hsecond]
                  exact List.mem_cons_self
                · have hsecond := congrArg Prod.snd horientation
                  simp only at hsecond
                  apply hsecondNotTail
                  rw [hsecond]
                  exact hlastMem
              · have hendpoints := pathPairsFrom_endpoints_mem htail
                have horientation :=
                  (normalizeQuery_eq_iff _ _).mp heq
                rcases horientation with horientation | horientation
                · have hsecond := congrArg Prod.snd horientation
                  simp only at hsecond
                  apply hfirstNotTail
                  rw [← hsecond]
                  exact hendpoints.2
                · have hfirst := congrArg Prod.fst horientation
                  simp only at hfirst
                  apply hfirstNotTail
                  rw [← hfirst]
                  exact hendpoints.1

/-- Summing a weight function over the concrete cycle-pair list is exactly
the recursive textbook tour-cost definition. -/
theorem cyclePairs_weight_sum (I : TSPInstance)
    (vertices : List Nat) :
    ((cyclePairs vertices).map fun pair =>
      I.edgeWeight pair.1 pair.2).sum =
      I.tourCost vertices := by
  have pathSum (previous : Nat) (rest : List Nat) :
      ((pathPairsFrom previous rest).map fun pair =>
          I.edgeWeight pair.1 pair.2).sum =
        I.pathCost (previous :: rest) := by
    induction rest generalizing previous with
    | nil => simp [pathPairsFrom, TSPInstance.pathCost]
    | cons current rest ih =>
        simp [pathPairsFrom, TSPInstance.pathCost, ih]
  cases vertices with
  | nil => simp [cyclePairs, TSPInstance.tourCost]
  | cons first rest =>
      simp [cyclePairs, TSPInstance.tourCost, pathSum, lastFrom_eq]

end CLRS.Chapter34.Turing.TSPVerifier.CostSemantics

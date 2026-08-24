import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Construction.WellFormed
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Encoding.Length

/-!
# Polynomial size of the VERTEX-COVER-to-HAM-CYCLE gadget

The four generated edge families receive separate cardinality bounds.  These
bounds are then combined with the shared unary graph encoder to obtain a cubic
bound in the source vertex count, target, and stored edge-occurrence count.

Main results:

- Theorem `clrsReductionEdges_length_le`: a structural edge-count bound.
- Theorem `encode_vertexCoverToHamiltonianInstance_length_le`: a uniform
  cubic bound for the total typed construction.
-/

namespace CLRS.Chapter34.HamiltonianCycleReduction

/-- Filtering edge occurrences by one endpoint never increases their count. -/
theorem incidentOccurrencesFrom_length_le
    (u start : Nat) (edges : List (Nat × Nat)) :
    (incidentOccurrencesFrom u start edges).length ≤ edges.length := by
  induction edges generalizing start with
  | nil => simp [incidentOccurrencesFrom]
  | cons edge edges ih =>
      simp only [incidentOccurrencesFrom]
      split
      · simp only [List.length_cons]
        exact Nat.succ_le_succ (ih (start + 1))
      · split
        · simp only [List.length_cons]
          exact Nat.succ_le_succ (ih (start + 1))
        · exact Nat.le_trans (ih (start + 1)) (Nat.le_succ _)

/-- The incident-occurrence list for one source vertex is bounded by the
number of stored source-edge occurrences. -/
theorem incidentOccurrences_length_le (I : CliqueInstance) (u : Nat) :
    (incidentOccurrences I u).length ≤ I.edges.length := by
  exact incidentOccurrencesFrom_length_le u 0 I.edges

/-- All incidence-chain links together are bounded by one source edge count
per source vertex. -/
theorem allIncidenceChainEdges_length_le (I : CliqueInstance) :
    (allIncidenceChainEdges I).length ≤
      I.vertexCount * I.edges.length := by
  have haux : ∀ vertices : List Nat,
      (vertices.flatMap fun u =>
        incidenceChainEdges (incidentOccurrences I u)).length ≤
        vertices.length * I.edges.length := by
    intro vertices
    induction vertices with
    | nil => simp
    | cons u vertices ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_cons]
        have hchain := incidenceChainEdges_length_le (incidentOccurrences I u)
        have hoccurrences := incidentOccurrences_length_le I u
        nlinarith
  simpa [allIncidenceChainEdges] using haux (List.range I.vertexCount)

/-- One nonempty source incidence chain contributes exactly two endpoint links
per selector, and an empty chain contributes none. -/
theorem selectorEndpointEdgesFor_length_le
    (edgeCount selectorCount : Nat) (refs : List IncidentOccurrence) :
    (selectorEndpointEdgesFor edgeCount selectorCount refs).length ≤
      2 * selectorCount := by
  cases refs with
  | nil => simp [selectorEndpointEdgesFor]
  | cons first rest =>
      simp [selectorEndpointEdgesFor, Nat.mul_comm]

/-- Selector endpoint links are bounded by two links for every source-vertex
and selector pair. -/
theorem allSelectorEndpointEdges_length_le (I : CliqueInstance) :
    (allSelectorEndpointEdges I).length ≤
      2 * I.vertexCount * I.targetSize := by
  have haux : ∀ vertices : List Nat,
      (vertices.flatMap fun u =>
        selectorEndpointEdgesFor I.edges.length I.targetSize
          (incidentOccurrences I u)).length ≤
        2 * vertices.length * I.targetSize := by
    intro vertices
    induction vertices with
    | nil => simp
    | cons u vertices ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_cons]
        have hlinks := selectorEndpointEdgesFor_length_le
          I.edges.length I.targetSize (incidentOccurrences I u)
        nlinarith
  simpa [allSelectorEndpointEdges] using haux (List.range I.vertexCount)

/-- The complete nondegenerate target edge list has a quadratic structural
bound in the three source size parameters. -/
theorem clrsReductionEdges_length_le (I : CliqueInstance) :
    (clrsReductionEdges I).length ≤
      14 * I.edges.length + I.vertexCount * I.edges.length +
        2 * I.vertexCount * I.targetSize + I.targetSize ^ 2 := by
  have hwidgets := allGlobalWidgetEdges_length I.edges.length
  have hchains := allIncidenceChainEdges_length_le I
  have hselectors := allSelectorEndpointEdges_length_le I
  have hclique := selectorCliqueEdges_length_le_square
    I.edges.length I.targetSize
  simp only [clrsReductionEdges, List.length_append]
  omega

/-- Every list of normalized bounded edges has bounded aggregate unary
serialization cost. -/
theorem cliqueEdgesEncodingLength_le_of_wellFormed
    {edges : List (Nat × Nat)} {vertexCount : Nat}
    (hwellFormed : ∀ edge ∈ edges,
      edge.1 < edge.2 ∧ edge.2 < vertexCount) :
    cliqueEdgesEncodingLength edges ≤
      edges.length * (2 * vertexCount + 3) := by
  induction edges with
  | nil => simp [cliqueEdgesEncodingLength]
  | cons edge edges ih =>
      have hedge := hwellFormed edge (by simp)
      have htail : ∀ tailEdge ∈ edges,
          tailEdge.1 < tailEdge.2 ∧ tailEdge.2 < vertexCount := by
        intro tailEdge htailEdge
        exact hwellFormed tailEdge (by simp [htailEdge])
      have hcost : edge.1 + edge.2 + 3 ≤ 2 * vertexCount + 3 := by
        omega
      have hrest := ih htail
      change edge.1 + edge.2 + 3 + cliqueEdgesEncodingLength edges ≤
        (edges.length + 1) * (2 * vertexCount + 3)
      calc
        edge.1 + edge.2 + 3 + cliqueEdgesEncodingLength edges ≤
            (2 * vertexCount + 3) + cliqueEdgesEncodingLength edges :=
          Nat.add_le_add_right hcost _
        _ ≤ (2 * vertexCount + 3) +
            edges.length * (2 * vertexCount + 3) :=
          Nat.add_le_add_left hrest _
        _ = (edges.length + 1) * (2 * vertexCount + 3) := by ring

/-- The nondegenerate CLRS target has cubic unary encoding size in the sum of
the source vertex, target, and edge-occurrence counts. -/
theorem encode_clrsHamiltonianInstance_length_le (I : CliqueInstance) :
    (encodeHamiltonianCycleInstance (clrsHamiltonianInstance I)).length ≤
      1000 * (I.vertexCount + I.targetSize + I.edges.length + 1) ^ 3 := by
  let sourceSize := I.vertexCount + I.targetSize + I.edges.length + 1
  let targetVertices := selectorBase I.edges.length + I.targetSize
  have hsource : 1 ≤ sourceSize := by
    simp [sourceSize]
  have hn : I.vertexCount ≤ sourceSize := by
    dsimp [sourceSize]
    omega
  have hk : I.targetSize ≤ sourceSize := by
    dsimp [sourceSize]
    omega
  have hm : I.edges.length ≤ sourceSize := by
    dsimp [sourceSize]
    omega
  have hsourceSquare : sourceSize ≤ sourceSize ^ 2 := by
    nlinarith [Nat.mul_self_le_mul_self hsource]
  have hsourceCube : sourceSize ≤ sourceSize ^ 3 := by
    nlinarith [Nat.mul_self_le_mul_self hsource,
      Nat.mul_le_mul_left sourceSize hsourceSquare]
  have hnm : I.vertexCount * I.edges.length ≤ sourceSize ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul hn hm
  have hnk : I.vertexCount * I.targetSize ≤ sourceSize ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul hn hk
  have hkk : I.targetSize ^ 2 ≤ sourceSize ^ 2 :=
    Nat.pow_le_pow_left hk 2
  have hmLinear : 14 * I.edges.length ≤ 14 * sourceSize ^ 2 := by
    exact Nat.mul_le_mul_left 14 (Nat.le_trans hm hsourceSquare)
  have hedgeCount : (clrsReductionEdges I).length ≤
      18 * sourceSize ^ 2 := by
    have hstructural := clrsReductionEdges_length_le I
    nlinarith
  have hvertices : targetVertices ≤ 13 * sourceSize := by
    dsimp [targetVertices, selectorBase, widgetVertexCount]
    nlinarith
  have hedgeCost : 2 * targetVertices + 3 ≤ 29 * sourceSize := by
    nlinarith
  have hencodedEdges :
      cliqueEdgesEncodingLength (clrsReductionEdges I) ≤
        (clrsReductionEdges I).length * (2 * targetVertices + 3) := by
    apply cliqueEdgesEncodingLength_le_of_wellFormed
    intro edge hedge
    exact mem_clrsReductionEdges_wellFormed I hedge
  have hencodedEdgesCubic :
      cliqueEdgesEncodingLength (clrsReductionEdges I) ≤
        522 * sourceSize ^ 3 := by
    have hproduct := Nat.mul_le_mul hedgeCount hedgeCost
    calc
      cliqueEdgesEncodingLength (clrsReductionEdges I) ≤
          (clrsReductionEdges I).length * (2 * targetVertices + 3) :=
        hencodedEdges
      _ ≤ (18 * sourceSize ^ 2) * (29 * sourceSize) := hproduct
      _ = 522 * sourceSize ^ 3 := by ring
  rw [encodeCliqueInstance_length]
  change targetVertices + targetVertices + 3 +
      cliqueEdgesEncodingLength (clrsReductionEdges I) ≤ _
  have hheader : targetVertices + targetVertices + 3 ≤
      29 * sourceSize := by nlinarith
  have hheaderCubic : targetVertices + targetVertices + 3 ≤
      29 * sourceSize ^ 3 :=
    Nat.le_trans hheader (Nat.mul_le_mul_left 29 hsourceCube)
  change targetVertices + targetVertices + 3 +
      cliqueEdgesEncodingLength (clrsReductionEdges I) ≤
        1000 * sourceSize ^ 3
  nlinarith

/-- The total typed construction, including its two constant degenerate
instances, obeys the same cubic encoding bound. -/
theorem encode_vertexCoverToHamiltonianInstance_length_le
    (I : VertexCoverInstance) :
    (encodeHamiltonianCycleInstance
      (vertexCoverToHamiltonianInstance I)).length ≤
      1000 * (I.vertexCount + I.targetSize + I.edges.length + 1) ^ 3 := by
  simp only [vertexCoverToHamiltonianInstance]
  split
  · rw [encodeCliqueInstance_length]
    norm_num [canonicalHamiltonianYesInstance, cliqueEdgesEncodingLength]
    have hpow := Nat.one_le_pow' 3
      (I.vertexCount + I.targetSize + I.edges.length)
    nlinarith
  · split
    · rw [encodeCliqueInstance_length]
      norm_num [canonicalHamiltonianNoInstance, cliqueEdgesEncodingLength]
      have hpow := Nat.one_le_pow' 3
        (I.vertexCount + I.targetSize + I.edges.length)
      nlinarith
    · exact encode_clrsHamiltonianInstance_length_le I

end CLRS.Chapter34.HamiltonianCycleReduction

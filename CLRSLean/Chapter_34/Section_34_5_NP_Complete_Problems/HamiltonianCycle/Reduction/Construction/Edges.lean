import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Construction.Numbering

/-!
# Edge families in the CLRS Hamiltonian-cycle reduction

The target graph has four explicit edge families: internal gadget edges,
links along each source-vertex incidence chain, selector-to-chain endpoint
edges, and selector-selector edges.  The final family is the small extension
that makes the construction represent covers of size *at most* `k`, matching
the chapter's serialized VERTEX-COVER language.
-/

namespace CLRS.Chapter34.HamiltonianCycleReduction

/-- Store an undirected edge in increasing endpoint order. -/
def normalizeUndirectedEdge (u v : Nat) : Nat × Nat :=
  if u < v then (u, v) else (v, u)

theorem normalizeUndirectedEdge_fst_lt_snd {u v : Nat} (hne : u ≠ v) :
    (normalizeUndirectedEdge u v).1 < (normalizeUndirectedEdge u v).2 := by
  simp only [normalizeUndirectedEdge]
  split <;> omega

theorem normalizeUndirectedEdge_snd_lt
    {u v bound : Nat} (hu : u < bound) (hv : v < bound) :
    (normalizeUndirectedEdge u v).2 < bound := by
  simp only [normalizeUndirectedEdge]
  split <;> simp_all

/-- The fourteen internal edges of one globally numbered gadget. -/
def globalWidgetEdges (occurrence : Nat) : List (Nat × Nat) :=
  widgetEdges.map fun e =>
    (globalWidgetVertex occurrence e.1,
      globalWidgetVertex occurrence e.2)

/-- Internal edges of all source-edge occurrences. -/
def allGlobalWidgetEdges (edgeCount : Nat) : List (Nat × Nat) :=
  (List.range edgeCount).flatMap globalWidgetEdges

/-- Links successive gadget sides along one source vertex's incidence chain. -/
def incidenceChainEdges : List IncidentOccurrence → List (Nat × Nat)
  | first :: second :: rest =>
      normalizeUndirectedEdge (incidentVertex first 5)
          (incidentVertex second 0) ::
        incidenceChainEdges (second :: rest)
  | _ => []

/-- All links between successive gadgets in source-vertex chains. -/
def allIncidenceChainEdges (I : CliqueInstance) : List (Nat × Nat) :=
  (List.range I.vertexCount).flatMap fun u =>
    incidenceChainEdges (incidentOccurrences I u)

/-- Join every selector to both endpoints of one nonempty incidence chain. -/
def selectorEndpointEdgesFor
    (edgeCount selectorCount : Nat) :
    List IncidentOccurrence → List (Nat × Nat)
  | [] => []
  | first :: rest =>
      let last := (first :: rest).getLast (by simp)
      (List.range selectorCount).flatMap fun selector =>
        [ normalizeUndirectedEdge (incidentVertex first 0)
            (selectorVertex edgeCount selector),
          normalizeUndirectedEdge (incidentVertex last 5)
            (selectorVertex edgeCount selector) ]

/-- Selector-to-chain edges for every source vertex.  Isolated source vertices
have empty incidence chains and intentionally contribute no target vertices. -/
def allSelectorEndpointEdges (I : CliqueInstance) : List (Nat × Nat) :=
  (List.range I.vertexCount).flatMap fun u =>
    selectorEndpointEdgesFor I.edges.length I.targetSize
      (incidentOccurrences I u)

/-- A clique on the selectors permits unused selector slots, so a source cover
of size below `k` is represented without padding it with isolated vertices. -/
def selectorCliqueEdges (edgeCount : Nat) : Nat → List (Nat × Nat)
  | 0 => []
  | selectorCount + 1 =>
      selectorCliqueEdges edgeCount selectorCount ++
        (List.range selectorCount).map fun selector =>
          (selectorVertex edgeCount selector,
            selectorVertex edgeCount selectorCount)

/-- Complete edge list of the nondegenerate CLRS construction. -/
def clrsReductionEdges (I : CliqueInstance) : List (Nat × Nat) :=
  allGlobalWidgetEdges I.edges.length ++
    allIncidenceChainEdges I ++
    allSelectorEndpointEdges I ++
    selectorCliqueEdges I.edges.length I.targetSize

theorem globalWidgetEdges_length (occurrence : Nat) :
    (globalWidgetEdges occurrence).length = 14 := by
  simp [globalWidgetEdges, widgetEdges_length]

theorem allGlobalWidgetEdges_length (edgeCount : Nat) :
    (allGlobalWidgetEdges edgeCount).length = 14 * edgeCount := by
  simp [allGlobalWidgetEdges, globalWidgetEdges_length, Nat.mul_comm]

theorem incidenceChainEdges_length_le
    (refs : List IncidentOccurrence) :
    (incidenceChainEdges refs).length ≤ refs.length := by
  induction refs using List.twoStepInduction with
  | nil => simp [incidenceChainEdges]
  | singleton ref => simp [incidenceChainEdges]
  | cons_cons first second rest ihRest ihTail =>
      simp only [incidenceChainEdges, List.length_cons]
      have := ihTail second
      simp only [List.length_cons] at this
      omega

theorem mem_incidenceChainEdges_of_pairwise
    {refs : List IncidentOccurrence} {edge : Nat × Nat}
    (hpairwise : refs.Pairwise
      (fun first second => first.occurrence < second.occurrence))
    (hedge : edge ∈ incidenceChainEdges refs) :
    ∃ first second,
      first ∈ refs ∧ second ∈ refs ∧
      first.occurrence < second.occurrence ∧
      edge = normalizeUndirectedEdge (incidentVertex first 5)
        (incidentVertex second 0) := by
  induction refs using List.twoStepInduction generalizing edge with
  | nil => simp [incidenceChainEdges] at hedge
  | singleton ref => simp [incidenceChainEdges] at hedge
  | cons_cons first second rest ihRest ihTail =>
      simp only [incidenceChainEdges, List.mem_cons] at hedge
      rcases hedge with hedge | hedge
      · refine ⟨first, second, by simp, by simp, ?_, hedge⟩
        exact (List.pairwise_cons.mp hpairwise).1 second (by simp)
      · rcases ihTail second hpairwise.tail hedge with
          ⟨left, right, hleft, hright, hlt, hedge⟩
        exact ⟨left, right, by simp [hleft], by simp [hright], hlt, hedge⟩

theorem mem_selectorEndpointEdgesFor
    {edgeCount selectorCount : Nat} {refs : List IncidentOccurrence}
    {edge : Nat × Nat}
    (hedge : edge ∈ selectorEndpointEdgesFor edgeCount selectorCount refs) :
    ∃ ref position selector,
      ref ∈ refs ∧ position < 6 ∧ selector < selectorCount ∧
      edge = normalizeUndirectedEdge (incidentVertex ref position)
        (selectorVertex edgeCount selector) := by
  cases refs with
  | nil => simp [selectorEndpointEdgesFor] at hedge
  | cons first rest =>
      simp only [selectorEndpointEdgesFor, List.mem_flatMap,
        List.mem_range] at hedge
      rcases hedge with ⟨selector, hselector, hedge⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hedge
      rcases hedge with hedge | hedge
      · exact ⟨first, 0, selector, by simp, by omega, hselector, hedge⟩
      · exact ⟨(first :: rest).getLast (by simp), 5, selector,
          List.getLast_mem _, by omega, hselector, hedge⟩

theorem mem_selectorCliqueEdges_iff
    {edgeCount selectorCount : Nat} {edge : Nat × Nat} :
    edge ∈ selectorCliqueEdges edgeCount selectorCount ↔
      ∃ first second,
        first < second ∧ second < selectorCount ∧
        edge = (selectorVertex edgeCount first,
          selectorVertex edgeCount second) := by
  induction selectorCount with
  | zero => simp [selectorCliqueEdges]
  | succ selectorCount ih =>
      simp only [selectorCliqueEdges, List.mem_append, ih, List.mem_map,
        List.mem_range]
      constructor
      · rintro (⟨first, second, hlt, hbound, rfl⟩ | ⟨first, hfirst, rfl⟩)
        · exact ⟨first, second, hlt, Nat.lt.step hbound, rfl⟩
        · exact ⟨first, selectorCount, hfirst, Nat.lt_add_one _, rfl⟩
      · rintro ⟨first, second, hlt, hbound, hedge⟩
        by_cases hsecond : second = selectorCount
        · right
          subst second
          exact ⟨first, hlt, hedge.symm⟩
        · left
          exact ⟨first, second, hlt, by omega, hedge⟩

theorem selectorCliqueEdges_length_le_square
    (edgeCount selectorCount : Nat) :
    (selectorCliqueEdges edgeCount selectorCount).length ≤ selectorCount ^ 2 := by
  induction selectorCount with
  | zero => simp [selectorCliqueEdges]
  | succ selectorCount ih =>
      simp only [selectorCliqueEdges, List.length_append, List.length_map,
        List.length_range]
      calc
        (selectorCliqueEdges edgeCount selectorCount).length + selectorCount ≤
            selectorCount ^ 2 + selectorCount :=
          Nat.add_le_add_right ih selectorCount
        _ ≤ (selectorCount + 1) ^ 2 := by nlinarith

end CLRS.Chapter34.HamiltonianCycleReduction

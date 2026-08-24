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

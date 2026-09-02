import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Construction

/-!
# Edge-family classification for reduction soundness

Soundness repeatedly needs to rule out incidence-chain and selector edges at
the four degree-two core vertices of a gadget.  This file exposes the endpoint
shape of every generated edge family and proves the arithmetic separation
once.
-/

namespace CLRS.Chapter34.HamiltonianCycleReduction

/-- The four local vertices whose only target neighbors are internal gadget
neighbors. -/
def IsWidgetCoreVertex (localVertex : Nat) : Prop :=
  localVertex = 1 ∨ localVertex = 4 ∨
    localVertex = 7 ∨ localVertex = 10

/-- The four branching vertices are internal to a gadget as well, but have
three local neighbors rather than two. -/
def IsWidgetBranchVertex (localVertex : Nat) : Prop :=
  localVertex = 2 ∨ localVertex = 3 ∨
    localVertex = 8 ∨ localVertex = 9

/-- Precisely the local vertices that cannot be endpoints of an incidence or
selector edge. -/
def IsWidgetInternalVertex (localVertex : Nat) : Prop :=
  IsWidgetCoreVertex localVertex ∨ IsWidgetBranchVertex localVertex

theorem widgetCoreVertex_lt
    {localVertex : Nat} (hcore : IsWidgetCoreVertex localVertex) :
    localVertex < widgetVertexCount := by
  rcases hcore with rfl | rfl | rfl | rfl <;>
    simp [widgetVertexCount]

theorem widgetBranchVertex_lt
    {localVertex : Nat} (hbranch : IsWidgetBranchVertex localVertex) :
    localVertex < widgetVertexCount := by
  rcases hbranch with rfl | rfl | rfl | rfl <;>
    simp [widgetVertexCount]

theorem widgetInternalVertex_lt
    {localVertex : Nat} (hinternal : IsWidgetInternalVertex localVertex) :
    localVertex < widgetVertexCount := by
  rcases hinternal with hcore | hbranch
  · exact widgetCoreVertex_lt hcore
  · exact widgetBranchVertex_lt hbranch

theorem mem_allGlobalWidgetEdges_iff
    {edgeCount : Nat} {edge : Nat × Nat} :
    edge ∈ allGlobalWidgetEdges edgeCount ↔
      ∃ occurrence, occurrence < edgeCount ∧
        ∃ localEdge, localEdge ∈ widgetEdges ∧
          edge = (globalWidgetVertex occurrence localEdge.1,
            globalWidgetVertex occurrence localEdge.2) := by
  simp [allGlobalWidgetEdges, globalWidgetEdges, eq_comm]

theorem mem_allIncidenceChainEdges_shape
    {I : CliqueInstance} {edge : Nat × Nat}
    (hedge : edge ∈ allIncidenceChainEdges I) :
    ∃ u first second,
      u < I.vertexCount ∧
      first ∈ incidentOccurrences I u ∧
      second ∈ incidentOccurrences I u ∧
      first.occurrence < second.occurrence ∧
      edge = normalizeUndirectedEdge (incidentVertex first 5)
        (incidentVertex second 0) := by
  simp only [allIncidenceChainEdges, List.mem_flatMap,
    List.mem_range] at hedge
  rcases hedge with ⟨u, hu, hedge⟩
  rcases mem_incidenceChainEdges_of_pairwise
      (incidentOccurrences_pairwise I u) hedge with
    ⟨first, second, hfirst, hsecond, hlt, rfl⟩
  exact ⟨u, first, second, hu, hfirst, hsecond, hlt, rfl⟩

theorem mem_selectorEndpointEdgesFor_port_shape
    {edgeCount selectorCount : Nat} {refs : List IncidentOccurrence}
    {edge : Nat × Nat}
    (hedge : edge ∈ selectorEndpointEdgesFor edgeCount selectorCount refs) :
    ∃ ref selector,
      ref ∈ refs ∧ selector < selectorCount ∧
      (edge = normalizeUndirectedEdge (incidentVertex ref 0)
          (selectorVertex edgeCount selector) ∨
        edge = normalizeUndirectedEdge (incidentVertex ref 5)
          (selectorVertex edgeCount selector)) := by
  cases refs with
  | nil => simp [selectorEndpointEdgesFor] at hedge
  | cons first rest =>
      simp only [selectorEndpointEdgesFor, List.mem_flatMap,
        List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hedge
      rcases hedge with ⟨selector, hselector, hedge | hedge⟩
      · exact ⟨first, selector, by simp, hselector, Or.inl hedge⟩
      · exact ⟨(first :: rest).getLast (by simp), selector,
          List.getLast_mem _, hselector, Or.inr hedge⟩

theorem mem_allSelectorEndpointEdges_shape
    {I : CliqueInstance} {edge : Nat × Nat}
    (hedge : edge ∈ allSelectorEndpointEdges I) :
    ∃ u ref position selector,
      u < I.vertexCount ∧
      ref ∈ incidentOccurrences I u ∧
      (position = 0 ∨ position = 5) ∧
      selector < I.targetSize ∧
      edge = normalizeUndirectedEdge (incidentVertex ref position)
        (selectorVertex I.edges.length selector) := by
  simp only [allSelectorEndpointEdges, List.mem_flatMap,
    List.mem_range] at hedge
  rcases hedge with ⟨u, hu, hedge⟩
  rcases mem_selectorEndpointEdgesFor_port_shape hedge with
    ⟨ref, selector, href, hselector, hedge | hedge⟩
  · exact ⟨u, ref, 0, selector, hu, href, Or.inl rfl,
      hselector, hedge⟩
  · exact ⟨u, ref, 5, selector, hu, href, Or.inr rfl,
      hselector, hedge⟩

theorem endpoint_of_normalizeUndirectedEdge
    {u v endpoint : Nat}
    (hendpoint : endpoint = (normalizeUndirectedEdge u v).1 ∨
      endpoint = (normalizeUndirectedEdge u v).2) :
    endpoint = u ∨ endpoint = v := by
  simp only [normalizeUndirectedEdge] at hendpoint
  split at hendpoint
  · exact hendpoint
  · exact hendpoint.elim Or.inr Or.inl

theorem endpoint_of_adj
    {I : CliqueInstance} {u v : Nat} (hadj : I.Adj u v) :
    ∃ edge ∈ I.edges,
      (u = edge.1 ∧ v = edge.2) ∨
      (u = edge.2 ∧ v = edge.1) := by
  rw [I.adj_iff] at hadj
  rcases hadj with ⟨_, hedge⟩ | ⟨_, hedge⟩
  · exact ⟨(u, v), hedge, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨(v, u), hedge, Or.inr ⟨rfl, rfl⟩⟩

theorem globalWidgetCoreVertex_ne_incidentVertex
    {I : CliqueInstance} {occurrence localVertex u position : Nat}
    {ref : IncidentOccurrence}
    (hoccurrence : occurrence < I.edges.length)
    (hcore : IsWidgetCoreVertex localVertex)
    (href : ref ∈ incidentOccurrences I u)
    (hposition : position = 0 ∨ position = 5) :
    globalWidgetVertex occurrence localVertex ≠ incidentVertex ref position := by
  have hrefOccurrence := occurrence_lt_of_mem_incidentOccurrences href
  rcases hcore with rfl | rfl | rfl | rfl <;>
    rcases hposition with rfl | rfl <;>
      cases ref with
      | mk refOccurrence rightSide =>
          cases rightSide <;>
            simp [globalWidgetVertex, incidentVertex, widgetVertex,
              widgetVertexCount] <;> omega

theorem globalWidgetInternalVertex_ne_incidentVertex
    {I : CliqueInstance} {occurrence localVertex u position : Nat}
    {ref : IncidentOccurrence}
    (hoccurrence : occurrence < I.edges.length)
    (hinternal : IsWidgetInternalVertex localVertex)
    (href : ref ∈ incidentOccurrences I u)
    (hposition : position = 0 ∨ position = 5) :
    globalWidgetVertex occurrence localVertex ≠ incidentVertex ref position := by
  rcases hinternal with hcore | hbranch
  · exact globalWidgetCoreVertex_ne_incidentVertex
      hoccurrence hcore href hposition
  · have hrefOccurrence := occurrence_lt_of_mem_incidentOccurrences href
    rcases hbranch with rfl | rfl | rfl | rfl <;>
      rcases hposition with rfl | rfl <;>
        cases ref with
        | mk refOccurrence rightSide =>
            cases rightSide <;>
              simp [globalWidgetVertex, incidentVertex, widgetVertex,
                widgetVertexCount] <;> omega

theorem globalWidgetCoreVertex_ne_selectorVertex
    {occurrence localVertex edgeCount selector : Nat}
    (hoccurrence : occurrence < edgeCount)
    (hcore : IsWidgetCoreVertex localVertex) :
    globalWidgetVertex occurrence localVertex ≠
      selectorVertex edgeCount selector := by
  have hlt := globalWidgetVertex_lt_selectorBase hoccurrence
    (widgetCoreVertex_lt hcore)
  simp only [selectorVertex]
  omega

theorem globalWidgetInternalVertex_ne_selectorVertex
    {occurrence localVertex edgeCount selector : Nat}
    (hoccurrence : occurrence < edgeCount)
    (hinternal : IsWidgetInternalVertex localVertex) :
    globalWidgetVertex occurrence localVertex ≠
      selectorVertex edgeCount selector := by
  have hlt := globalWidgetVertex_lt_selectorBase hoccurrence
    (widgetInternalVertex_lt hinternal)
  simp only [selectorVertex]
  omega

theorem globalWidgetCoreVertex_not_endpoint_incidenceChainEdge
    {I : CliqueInstance} {occurrence localVertex : Nat}
    (hoccurrence : occurrence < I.edges.length)
    (hcore : IsWidgetCoreVertex localVertex)
    {edge : Nat × Nat} (hedge : edge ∈ allIncidenceChainEdges I) :
    globalWidgetVertex occurrence localVertex ≠ edge.1 ∧
      globalWidgetVertex occurrence localVertex ≠ edge.2 := by
  rcases mem_allIncidenceChainEdges_shape hedge with
    ⟨u, first, second, _, hfirst, hsecond, _, rfl⟩
  constructor <;> intro heq
  · have hendpoint : globalWidgetVertex occurrence localVertex =
        incidentVertex first 5 ∨
        globalWidgetVertex occurrence localVertex = incidentVertex second 0 :=
      endpoint_of_normalizeUndirectedEdge (Or.inl heq)
    rcases hendpoint with hendpoint | hendpoint
    · exact globalWidgetCoreVertex_ne_incidentVertex
        hoccurrence hcore hfirst (Or.inr rfl) hendpoint
    · exact globalWidgetCoreVertex_ne_incidentVertex
        hoccurrence hcore hsecond (Or.inl rfl) hendpoint
  · have hendpoint : globalWidgetVertex occurrence localVertex =
        incidentVertex first 5 ∨
        globalWidgetVertex occurrence localVertex = incidentVertex second 0 :=
      endpoint_of_normalizeUndirectedEdge (Or.inr heq)
    rcases hendpoint with hendpoint | hendpoint
    · exact globalWidgetCoreVertex_ne_incidentVertex
        hoccurrence hcore hfirst (Or.inr rfl) hendpoint
    · exact globalWidgetCoreVertex_ne_incidentVertex
        hoccurrence hcore hsecond (Or.inl rfl) hendpoint

theorem globalWidgetCoreVertex_not_endpoint_selectorEndpointEdge
    {I : CliqueInstance} {occurrence localVertex : Nat}
    (hoccurrence : occurrence < I.edges.length)
    (hcore : IsWidgetCoreVertex localVertex)
    {edge : Nat × Nat} (hedge : edge ∈ allSelectorEndpointEdges I) :
    globalWidgetVertex occurrence localVertex ≠ edge.1 ∧
      globalWidgetVertex occurrence localVertex ≠ edge.2 := by
  rcases mem_allSelectorEndpointEdges_shape hedge with
    ⟨u, ref, position, selector, _, href, hposition, _, rfl⟩
  constructor <;> intro heq
  · have hendpoint := endpoint_of_normalizeUndirectedEdge (Or.inl heq)
    rcases hendpoint with hendpoint | hendpoint
    · exact globalWidgetCoreVertex_ne_incidentVertex
        hoccurrence hcore href hposition hendpoint
    · exact globalWidgetCoreVertex_ne_selectorVertex
        hoccurrence hcore hendpoint
  · have hendpoint := endpoint_of_normalizeUndirectedEdge (Or.inr heq)
    rcases hendpoint with hendpoint | hendpoint
    · exact globalWidgetCoreVertex_ne_incidentVertex
        hoccurrence hcore href hposition hendpoint
    · exact globalWidgetCoreVertex_ne_selectorVertex
        hoccurrence hcore hendpoint

theorem globalWidgetCoreVertex_not_endpoint_selectorCliqueEdge
    {edgeCount selectorCount occurrence localVertex : Nat}
    (hoccurrence : occurrence < edgeCount)
    (hcore : IsWidgetCoreVertex localVertex)
    {edge : Nat × Nat} (hedge : edge ∈
      selectorCliqueEdges edgeCount selectorCount) :
    globalWidgetVertex occurrence localVertex ≠ edge.1 ∧
      globalWidgetVertex occurrence localVertex ≠ edge.2 := by
  rcases mem_selectorCliqueEdges_iff.mp hedge with
    ⟨first, second, _, _, rfl⟩
  exact ⟨globalWidgetCoreVertex_ne_selectorVertex hoccurrence hcore,
    globalWidgetCoreVertex_ne_selectorVertex hoccurrence hcore⟩

theorem globalWidgetInternalVertex_not_endpoint_incidenceChainEdge
    {I : CliqueInstance} {occurrence localVertex : Nat}
    (hoccurrence : occurrence < I.edges.length)
    (hinternal : IsWidgetInternalVertex localVertex)
    {edge : Nat × Nat} (hedge : edge ∈ allIncidenceChainEdges I) :
    globalWidgetVertex occurrence localVertex ≠ edge.1 ∧
      globalWidgetVertex occurrence localVertex ≠ edge.2 := by
  rcases mem_allIncidenceChainEdges_shape hedge with
    ⟨u, first, second, _, hfirst, hsecond, _, rfl⟩
  constructor <;> intro heq
  · rcases endpoint_of_normalizeUndirectedEdge (Or.inl heq) with
      hendpoint | hendpoint
    · exact globalWidgetInternalVertex_ne_incidentVertex
        hoccurrence hinternal hfirst (Or.inr rfl) hendpoint
    · exact globalWidgetInternalVertex_ne_incidentVertex
        hoccurrence hinternal hsecond (Or.inl rfl) hendpoint
  · rcases endpoint_of_normalizeUndirectedEdge (Or.inr heq) with
      hendpoint | hendpoint
    · exact globalWidgetInternalVertex_ne_incidentVertex
        hoccurrence hinternal hfirst (Or.inr rfl) hendpoint
    · exact globalWidgetInternalVertex_ne_incidentVertex
        hoccurrence hinternal hsecond (Or.inl rfl) hendpoint

theorem globalWidgetInternalVertex_not_endpoint_selectorEndpointEdge
    {I : CliqueInstance} {occurrence localVertex : Nat}
    (hoccurrence : occurrence < I.edges.length)
    (hinternal : IsWidgetInternalVertex localVertex)
    {edge : Nat × Nat} (hedge : edge ∈ allSelectorEndpointEdges I) :
    globalWidgetVertex occurrence localVertex ≠ edge.1 ∧
      globalWidgetVertex occurrence localVertex ≠ edge.2 := by
  rcases mem_allSelectorEndpointEdges_shape hedge with
    ⟨u, ref, position, selector, _, href, hposition, _, rfl⟩
  constructor <;> intro heq
  · rcases endpoint_of_normalizeUndirectedEdge (Or.inl heq) with
      hendpoint | hendpoint
    · exact globalWidgetInternalVertex_ne_incidentVertex
        hoccurrence hinternal href hposition hendpoint
    · exact globalWidgetInternalVertex_ne_selectorVertex
        hoccurrence hinternal hendpoint
  · rcases endpoint_of_normalizeUndirectedEdge (Or.inr heq) with
      hendpoint | hendpoint
    · exact globalWidgetInternalVertex_ne_incidentVertex
        hoccurrence hinternal href hposition hendpoint
    · exact globalWidgetInternalVertex_ne_selectorVertex
        hoccurrence hinternal hendpoint

theorem globalWidgetInternalVertex_not_endpoint_selectorCliqueEdge
    {edgeCount selectorCount occurrence localVertex : Nat}
    (hoccurrence : occurrence < edgeCount)
    (hinternal : IsWidgetInternalVertex localVertex)
    {edge : Nat × Nat} (hedge : edge ∈
      selectorCliqueEdges edgeCount selectorCount) :
    globalWidgetVertex occurrence localVertex ≠ edge.1 ∧
      globalWidgetVertex occurrence localVertex ≠ edge.2 := by
  rcases mem_selectorCliqueEdges_iff.mp hedge with
    ⟨first, second, _, _, rfl⟩
  exact ⟨globalWidgetInternalVertex_ne_selectorVertex
      hoccurrence hinternal,
    globalWidgetInternalVertex_ne_selectorVertex hoccurrence hinternal⟩

end CLRS.Chapter34.HamiltonianCycleReduction

import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.Incidence.Scanner.Cleanup

/-!
# HAM-CYCLE incidence scanner: one complete vertex query
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Scanner

open PolyBuilder
open HamiltonianCycleReduction

/-- Exact cost of parsing one vertex, scanning the graph, clearing the
counters, and restoring the graph for the next vertex. -/
def iterationSteps (query : Nat) (I : VertexCoverInstance) : Nat :=
  querySteps query + headerSteps I + edgesSteps query 0 I.edges +
    (query + I.edges.length + (encodeCliqueInstance I).length + 6)

private theorem encodeCliqueInstance_split (I : CliqueInstance) :
    encodeCliqueInstance I =
      encodeCliqueInstance { I with edges := [] } ++
        I.edges.flatMap encodeCliqueEdge := by
  simp [encodeCliqueInstance, prependCliqueTicks_append]

/-- One reversed vertex query is processed while the canonical graph is
restored exactly for the following query. -/
def iteration_run (query : Nat) (tail : List (Option CliqueSym))
    (I : VertexCoverInstance) (output : List UnaryFrameSym)
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .nextQuery buffer₁ buffer₂ test
        ((encodeCliqueInstance I).map some) output
        (((encodeCliqueVertex query).map some).reverse ++ tail) [] [] [] [])
      (some (cfg .nextQuery (some (some CliqueSym.vertexMark)) none false
        ((encodeCliqueInstance I).map some)
        ((incidenceRow I query ++ [UnaryFrameSym.frameEnd]).reverse ++ output)
        tail [] [] [] []))
      (iterationSteps query I) := by
  have parsed := query_run query tail ((encodeCliqueInstance I).map some)
    output [] buffer₁ buffer₂ test
  have header := header_run query 0 I output tail []
    (some (some CliqueSym.vertexMark)) buffer₂ test
  let headerStored :=
    ((encodeCliqueInstance { I with edges := [] }).map some).reverse
  have header' : EvalsToInTime (step program)
      (cfg .instanceMark (some (some .vertexMark)) buffer₂ test
        ((encodeCliqueInstance I).map some) output tail []
        (List.replicate query ()) [] [])
      (some (cfg .edges (some (some .vertexMark))
        (some (some .fieldSep)) test
        ((I.edges.flatMap encodeCliqueEdge).map some) output tail headerStored
        (List.replicate query ()) [] []))
      (headerSteps I) := by
    simpa [headerStored] using header
  have scanned := edges_run query 0 I.edges output tail headerStored
    (some (some CliqueSym.vertexMark)) (some (some CliqueSym.fieldSep)) test
  let graphStored := ((encodeCliqueInstance I).map some).reverse
  have hstored :
      ((I.edges.flatMap encodeCliqueEdge).map some).reverse ++ headerStored =
        graphStored := by
    unfold headerStored graphStored
    rw [encodeCliqueInstance_split I]
    simp [List.map_append, List.reverse_append]
  rw [hstored] at scanned
  have hfinal : edgesFinalTest test I.edges =
      (if I.edges = [] then test else false) := by
    cases I.edges <;> rfl
  have finished := finishQuery_run query I.edges.length 0 []
    (((incidentOccurrencesFrom query 0 I.edges).flatMap
      encodeIncidentOccurrence).reverse ++ output)
    tail graphStored (some (some CliqueSym.vertexMark)) none
    (edgesFinalTest test I.edges)
  have finished' : EvalsToInTime (step program)
      (cfg .finishQuery (some (some CliqueSym.vertexMark)) none
        (edgesFinalTest test I.edges) []
        (((incidentOccurrencesFrom query 0 I.edges).flatMap
          encodeIncidentOccurrence).reverse ++ output)
        tail graphStored (List.replicate query ())
        (List.replicate I.edges.length ()) [])
      (some (cfg .nextQuery (some (some CliqueSym.vertexMark)) none false
        ((encodeCliqueInstance I).map some)
        ((incidenceRow I query ++ [UnaryFrameSym.frameEnd]).reverse ++ output)
        tail [] [] [] []))
      (query + I.edges.length + (encodeCliqueInstance I).length + 6) := by
    simpa [graphStored, incidenceRow, incidentOccurrences,
      List.reverse_append, List.append_assoc] using finished
  have finished'' : EvalsToInTime (step program)
      (cfg .finishQuery (some (some CliqueSym.vertexMark)) none
        (edgesFinalTest test I.edges) []
        (((incidentOccurrencesFrom query 0 I.edges).flatMap
          encodeIncidentOccurrence).reverse ++ output)
        tail graphStored (List.replicate query ())
        (List.replicate (0 + I.edges.length) ()) [])
      (some (cfg .nextQuery (some (some CliqueSym.vertexMark)) none false
        ((encodeCliqueInstance I).map some)
        ((incidenceRow I query ++ [UnaryFrameSym.frameEnd]).reverse ++ output)
        tail [] [] [] []))
      (query + I.edges.length + (encodeCliqueInstance I).length + 6) := by
    simpa using finished'
  let throughHeader := EvalsToInTime.trans (step program)
    (querySteps query) (headerSteps I) _ _ _ parsed header'
  let throughEdges := EvalsToInTime.trans (step program)
    _ (edgesSteps query 0 I.edges) _ _ _ throughHeader scanned
  let full := EvalsToInTime.trans (step program)
    _ (query + I.edges.length + (encodeCliqueInstance I).length + 6)
    _ _ _ throughEdges finished''
  convert full using 1
  all_goals simp [iterationSteps, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm]

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Scanner

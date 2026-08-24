import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.BatchEdgeLookup.FinalCleanup

/-!
# Batch edge lookup: one complete query iteration
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.BatchEdgeLookup

open PolyBuilder

/-- Exact cost of parsing one query, scanning one graph, clearing its counters,
and restoring the graph for the next query. -/
def iterationSteps (query : Nat × Nat) (I : CliqueInstance) : Nat :=
  querySteps query + headerSteps I + edgesSteps query I.edges +
    (query.1 + query.2 + 3) + (encodeCliqueInstance I).length + 2

private theorem encodeCliqueInstance_split (I : CliqueInstance) :
    encodeCliqueInstance I =
      encodeCliqueInstance { I with edges := [] } ++
        I.edges.flatMap encodeCliqueEdge := by
  simp [encodeCliqueInstance, prependCliqueTicks_append]

/-- One reversed query is checked, while the canonical graph is restored
exactly for the following query. -/
def iteration_run (aggregate : Bool) (query : Nat × Nat)
    (tail : List (Option CliqueSym)) (I : CliqueInstance)
    (output : List Bool)
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.nextQuery aggregate) buffer₁ buffer₂ test
        ((encodeCliqueInstance I).map some) output
        (((encodeCliqueEdge query).map some).reverse ++ tail) [] [] [] [])
      (some (cfg (.nextQuery
        (aggregate && decide (query ∈ I.edges)))
        (some (some .edgeMark)) none false
        ((encodeCliqueInstance I).map some)
        (decide (query ∈ I.edges) :: output) tail [] [] [] []))
      (iterationSteps query I) := by
  have parsed := query_run aggregate query tail
    ((encodeCliqueInstance I).map some) output [] buffer₁ buffer₂ test
  have header := header_run aggregate query I output tail []
    (some (some CliqueSym.edgeMark)) buffer₂ test
  let headerStored :=
    ((encodeCliqueInstance { I with edges := [] }).map some).reverse
  have header' : EvalsToInTime (step program)
      (cfg (.instanceMark aggregate) (some (some .edgeMark)) buffer₂ test
        ((encodeCliqueInstance I).map some) output tail []
        (List.replicate query.1 ()) (List.replicate query.2 ()) [])
      (some (cfg (.edges aggregate) (some (some .edgeMark))
        (some (some .fieldSep)) test
        ((I.edges.flatMap encodeCliqueEdge).map some) output tail headerStored
        (List.replicate query.1 ()) (List.replicate query.2 ()) []))
      (headerSteps I) := by
    simpa [headerStored] using header
  have scanned := edges_run aggregate query I.edges output tail headerStored
    (some (some CliqueSym.edgeMark)) (some (some CliqueSym.fieldSep)) test
  let graphStored := ((encodeCliqueInstance I).map some).reverse
  have hstored :
      ((I.edges.flatMap encodeCliqueEdge).map some).reverse ++ headerStored =
        graphStored := by
    unfold headerStored graphStored
    rw [encodeCliqueInstance_split I]
    simp [List.map_append, List.reverse_append]
  rw [hstored] at scanned
  have cleared := clearQuery_run aggregate (decide (query ∈ I.edges))
    query.1 query.2 0 [] output tail graphStored
    (some (some CliqueSym.edgeMark)) none (edgesFinalTest test I.edges)
  have cleared' : EvalsToInTime (step program)
      (cfg (.clearLeft aggregate (decide (query ∈ I.edges)))
        (some (some .edgeMark)) none (edgesFinalTest test I.edges) [] output tail
        graphStored (List.replicate query.1 ())
        (List.replicate query.2 ()) [])
      (some (cfg (.restoreGraph aggregate (decide (query ∈ I.edges)))
        (some (some .edgeMark)) none false [] output tail graphStored [] [] []))
      (query.1 + query.2 + 3) := by
    simpa using cleared
  have restored := restoreGraph_run aggregate (decide (query ∈ I.edges))
    [] tail graphStored output (some (some CliqueSym.edgeMark)) none false
  have restored' : EvalsToInTime (step program)
      (cfg (.restoreGraph aggregate (decide (query ∈ I.edges)))
        (some (some .edgeMark)) none false [] output tail graphStored [] [] [])
      (some (cfg (.nextQuery (aggregate && decide (query ∈ I.edges)))
        (some (some .edgeMark)) none false
        ((encodeCliqueInstance I).map some)
        (decide (query ∈ I.edges) :: output) tail [] [] [] []))
      ((encodeCliqueInstance I).length + 2) := by
    simpa [graphStored] using restored
  let throughHeader := EvalsToInTime.trans (step program)
    (querySteps query) (headerSteps I) _ _ _ parsed header'
  let throughEdges := EvalsToInTime.trans (step program)
    _ (edgesSteps query I.edges) _ _ _ throughHeader scanned
  let throughClear := EvalsToInTime.trans (step program)
    _ (query.1 + query.2 + 3) _ _ _ throughEdges cleared'
  let full := EvalsToInTime.trans (step program)
    _ ((encodeCliqueInstance I).length + 2) _ _ _ throughClear restored'
  convert full using 1
  all_goals
    simp [iterationSteps, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.BatchEdgeLookup

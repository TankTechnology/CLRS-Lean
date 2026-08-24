import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.Incidence.Chain.Family

/-!
# HAM-CYCLE incidence-chain formatter: complete execution
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Chain

open PolyBuilder
open HamiltonianCycleReduction

/-- Mathematical incidence rows consumed by the chain formatter. -/
def incidenceReferenceRows (I : VertexCoverInstance) :
    List (List IncidentOccurrence) :=
  (List.range I.vertexCount).map (incidentOccurrences I)

theorem encodeReferenceRows_incidence (I : VertexCoverInstance) :
    encodeReferenceRows (incidenceReferenceRows I) = Scanner.stream I := by
  simp [encodeReferenceRows, incidenceReferenceRows, Scanner.stream,
    Scanner.incidenceFamily, Scanner.incidenceRow,
    encodeUnaryFrameMarkedRowFamily, List.flatMap_map]

theorem referenceRowsEdges_incidence (I : VertexCoverInstance) :
    referenceRowsEdges (incidenceReferenceRows I) =
      allIncidenceChainEdges I := by
  simp [referenceRowsEdges, incidenceReferenceRows,
    allIncidenceChainEdges, List.flatMap_map]

private theorem incidenceReferenceRows_ordered (I : VertexCoverInstance) :
    ∀ refs ∈ incidenceReferenceRows I,
      refs.Pairwise
        (fun first second => first.occurrence < second.occurrence) := by
  intro refs hrefs
  rw [incidenceReferenceRows, List.mem_map] at hrefs
  rcases hrefs with ⟨u, _, rfl⟩
  exact incidentOccurrences_pairwise I u

private def finish_run (buffer : Option UnaryFrameSym) (test : Bool)
    (output : List CliqueSym) :
    EvalsToInTime (step program)
      (cfg .beginRow buffer test [] output [] [])
      (some (haltCfg program output)) 2 := by
  exact ⟨⟨2, by
    simp [Function.iterate_succ_apply, flip, step, program, cfg, stepOp,
      haltCfg]⟩, le_rfl⟩

/-- Exact cost of the prepend-only incidence-chain formatter. -/
def formatterSteps (I : VertexCoverInstance) : Nat :=
  rowsSteps (incidenceReferenceRows I) + 2

/-- The fixed controller consumes the canonical incidence rows and emits the
reverse of the chain-edge stream. -/
def formatter_run (I : VertexCoverInstance) :
    EvalsToInTime (step program)
      (initialCfg program (Scanner.stream I))
      (some (haltCfg program (chainEdgeStream I).reverse))
      (formatterSteps I) := by
  have rows := rows_run (incidenceReferenceRows I)
    (incidenceReferenceRows_ordered I) [] none false
  rw [encodeReferenceRows_incidence I] at rows
  simp only [List.append_nil] at rows
  have finish := finish_run
    (rowsFinalBuffer none (incidenceReferenceRows I))
    (rowsFinalTest false (incidenceReferenceRows I))
    (((referenceRowsEdges (incidenceReferenceRows I)).flatMap
      encodeCliqueEdge).reverse)
  let full := EvalsToInTime.trans (step program)
    (rowsSteps (incidenceReferenceRows I)) 2 _ _ _ rows finish
  simpa [initialCfg, program, cfg, formatterSteps, chainEdgeStream,
    referenceRowsEdges_incidence, Nat.add_comm] using full

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Chain

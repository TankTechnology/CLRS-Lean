import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.Incidence.Endpoints.Family

/-!
# HAM-CYCLE selector endpoints: complete extractor run
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Endpoints

open PolyBuilder
open HamiltonianCycleReduction

def incidenceReferenceRows (I : VertexCoverInstance) :
    List (List IncidentOccurrence) :=
  (List.range I.vertexCount).map (incidentOccurrences I)

theorem encodeReferenceRows_incidence (I : VertexCoverInstance) :
    encodeReferenceRows (incidenceReferenceRows I) = Scanner.stream I := by
  simp [encodeReferenceRows, incidenceReferenceRows, Scanner.stream,
    Scanner.incidenceFamily, Scanner.incidenceRow,
    encodeUnaryFrameMarkedRowFamily, List.flatMap_map]

theorem referenceRowsCells_incidence (I : VertexCoverInstance) :
    referenceRowsCells (incidenceReferenceRows I) = endpointCellStream I := by
  rw [referenceRowsCells, incidenceReferenceRows, List.flatMap_map]
  unfold endpointCellStream
  apply congrArg (fun emit => (List.range I.vertexCount).flatMap emit)
  funext u
  rfl

private def finish_run (buffer : Option UnaryFrameSym) (test : Bool)
    (output : List UnaryFrameSym) :
    EvalsToInTime (step program)
      (cfg .beginRow buffer test [] output [] [])
      (some (haltCfg program output)) 2 := by
  exact ⟨⟨2, by
    simp [Function.iterate_succ_apply, flip, step, program, cfg, stepOp,
      haltCfg]⟩, le_rfl⟩

def extractorSteps (I : VertexCoverInstance) : Nat :=
  rowsSteps (incidenceReferenceRows I) + 2

/-- The fixed extractor emits the reverse physical endpoint-cell stream. -/
def extractor_run (I : VertexCoverInstance) :
    EvalsToInTime (step program)
      (initialCfg program (Scanner.stream I))
      (some (haltCfg program (endpointCellStream I).reverse))
      (extractorSteps I) := by
  have rows := rows_run (incidenceReferenceRows I) [] none false
  rw [encodeReferenceRows_incidence I] at rows
  simp only [List.append_nil] at rows
  have finish := finish_run
    (rowsFinalBuffer none (incidenceReferenceRows I))
    (rowsFinalTest false (incidenceReferenceRows I))
    (referenceRowsCells (incidenceReferenceRows I)).reverse
  let full := EvalsToInTime.trans (step program)
    (rowsSteps (incidenceReferenceRows I)) 2 _ _ _ rows finish
  simpa [initialCfg, program, cfg, extractorSteps,
    referenceRowsCells_incidence, Nat.add_comm] using full

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Endpoints

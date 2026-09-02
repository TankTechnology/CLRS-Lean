import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.Incidence.Chain.Parse

/-!
# HAM-CYCLE incidence-chain formatter: row simulation
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Chain

open PolyBuilder
open HamiltonianCycleReduction

private def clearPrevious_run (remaining : Nat)
    (buffer : Option UnaryFrameSym) (test : Bool)
    (input : List UnaryFrameSym) (output : List CliqueSym) :
    EvalsToInTime (step program)
      (cfg .clearPrevious buffer test input output
        (List.replicate remaining ()) [])
      (some (cfg .beginRow buffer false input output [] []))
      (remaining + 1) := by
  induction remaining generalizing test with
  | zero =>
      exact ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | succ remaining ih =>
      have first : EvalsToInTime (step program)
          (cfg .clearPrevious buffer test input output
            (List.replicate (remaining + 1) ()) [])
          (some (cfg .clearPrevious buffer true input output
            (List.replicate remaining ()) [])) 1 :=
        ⟨⟨1, by simp [flip, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have rest := ih true
      let full := EvalsToInTime.trans (step program) 1 (remaining + 1)
        _ _ _ first rest
      convert full using 1

private def rowBoundary_run (previous : IncidentOccurrence)
    (tail : List UnaryFrameSym) (output : List CliqueSym)
    (buffer : Option UnaryFrameSym) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.nextOccurrence previous.rightSide) buffer test
        (.frameEnd :: tail) output
        (List.replicate previous.occurrence ()) [])
      (some (cfg .beginRow (some .frameEnd) false tail output [] []))
      (previous.occurrence + 2) := by
  let afterBoundary := cfg .clearPrevious (some .frameEnd) test tail output
    (List.replicate previous.occurrence ()) []
  have first : EvalsToInTime (step program)
      (cfg (.nextOccurrence previous.rightSide) buffer test
        (.frameEnd :: tail) output
        (List.replicate previous.occurrence ()) [])
      (some afterBoundary) 1 :=
    ⟨⟨1, by simp [flip, afterBoundary, step, program, cfg, stepOp]⟩,
      le_rfl⟩
  have rest := clearPrevious_run previous.occurrence (some .frameEnd) test
    tail output
  let full := EvalsToInTime.trans (step program) 1
    (previous.occurrence + 1) _ afterBoundary _ first rest
  convert full using 1

/-- Exact cost after the first reference of a nonempty row has been loaded. -/
def remainingSteps : IncidentOccurrence → List IncidentOccurrence → Nat
  | previous, [] => previous.occurrence + 2
  | previous, current :: rest =>
      referenceSteps current + emitSteps previous current +
        remainingSteps current rest

private theorem normalize_consecutive
    (previous current : IncidentOccurrence)
    (hlt : previous.occurrence < current.occurrence) :
    normalizeUndirectedEdge (incidentVertex previous 5)
        (incidentVertex current 0) =
      (incidentVertex previous 5, incidentVertex current 0) := by
  have hvertices := incidentVertex_lt_of_occurrence_lt hlt
    (firstPosition := 5) (secondPosition := 0) (by omega) (by omega)
  unfold normalizeUndirectedEdge
  rw [if_pos hvertices]

/-- Consume the rest of one incidence row, emitting one edge per consecutive
reference pair. -/
def remaining_run (previous : IncidentOccurrence)
    (refs : List IncidentOccurrence)
    (hordered : (previous :: refs).Pairwise
      (fun first second => first.occurrence < second.occurrence))
    (tail : List UnaryFrameSym) (output : List CliqueSym)
    (buffer : Option UnaryFrameSym) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.nextOccurrence previous.rightSide) buffer test
        (refs.flatMap Scanner.encodeIncidentOccurrence ++ .frameEnd :: tail)
        output (List.replicate previous.occurrence ()) [])
      (some (cfg .beginRow (some .frameEnd) false tail
        (((incidenceChainEdges (previous :: refs)).flatMap
          encodeCliqueEdge).reverse ++ output)
        [] []))
      (remainingSteps previous refs) := by
  induction refs generalizing previous output buffer test with
  | nil =>
      simpa [remainingSteps, incidenceChainEdges] using
        rowBoundary_run previous tail output buffer test
  | cons current refs ih =>
      have hprevious : previous.occurrence < current.occurrence :=
        (List.pairwise_cons.mp hordered).1 current (by simp)
      have htail : (current :: refs).Pairwise
          (fun first second => first.occurrence < second.occurrence) :=
        hordered.tail
      let restInput :=
        refs.flatMap Scanner.encodeIncidentOccurrence ++ .frameEnd :: tail
      have loadRun := nextReference_run previous current restInput output
        buffer test
      have emitRun := emit_run previous current (some .separator) test
        restInput output
      have restRun := ih current htail
        (((encodeCliqueEdge
          (incidentVertex previous 5, incidentVertex current 0)).reverse ++
            output))
        (some .separator) false
      let throughLoad := EvalsToInTime.trans (step program)
        (referenceSteps current) (emitSteps previous current)
        _ _ _ loadRun emitRun
      let full := EvalsToInTime.trans (step program) _
        (remainingSteps current refs) _ _ _ throughLoad restRun
      have hnormalize :
          normalizeUndirectedEdge
              (12 * previous.occurrence +
                incidentOffset previous.rightSide 5)
              (12 * current.occurrence +
                incidentOffset current.rightSide 0) =
            (12 * previous.occurrence +
                incidentOffset previous.rightSide 5,
              12 * current.occurrence +
                incidentOffset current.rightSide 0) := by
        simpa only [incidentVertex_eq] using
          normalize_consecutive previous current hprevious
      convert full using 1
      · simp [restInput, List.append_assoc]
      · simp [incidenceChainEdges, hnormalize,
          List.reverse_append, List.append_assoc]
      · simp [remainingSteps]
        omega

/-- Exact cost of one complete marked incidence row. -/
def rowSteps : List IncidentOccurrence → Nat
  | [] => 1
  | first :: rest => referenceSteps first + remainingSteps first rest

/-- Exact simulation of one complete marked incidence row. -/
def row_run (refs : List IncidentOccurrence)
    (hordered : refs.Pairwise
      (fun first second => first.occurrence < second.occurrence))
    (tail : List UnaryFrameSym) (output : List CliqueSym)
    (buffer : Option UnaryFrameSym) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .beginRow buffer test
        (refs.flatMap Scanner.encodeIncidentOccurrence ++ .frameEnd :: tail)
        output [] [])
      (some (cfg .beginRow (some .frameEnd)
        (if refs.isEmpty then test else false) tail
        (((incidenceChainEdges refs).flatMap encodeCliqueEdge).reverse ++ output)
        [] []))
      (rowSteps refs) := by
  cases refs with
  | nil =>
      exact ⟨⟨1, rfl⟩, le_rfl⟩
  | cons first rest =>
      let restInput :=
        rest.flatMap Scanner.encodeIncidentOccurrence ++ .frameEnd :: tail
      have firstRun := firstReference_run first restInput output buffer test
      have restRun := remaining_run first rest hordered tail output
        (some .separator) test
      let full := EvalsToInTime.trans (step program)
        (referenceSteps first) (remainingSteps first rest)
        _ _ _ firstRun restRun
      convert full using 1
      · simp [restInput, List.append_assoc]
      · simp
      · simp [rowSteps]
        omega

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Chain

import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.Incidence.Endpoints.Emit

/-!
# HAM-CYCLE selector endpoints: row simulation
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Endpoints

open PolyBuilder
open HamiltonianCycleReduction

/-- Latest reference after scanning a possibly empty suffix. -/
def lastReference (previous : IncidentOccurrence) :
    List IncidentOccurrence → IncidentOccurrence
  | [] => previous
  | current :: refs => lastReference current refs

@[simp] theorem lastReference_nil (previous : IncidentOccurrence) :
    lastReference previous [] = previous := rfl

@[simp] theorem lastReference_cons (previous current : IncidentOccurrence)
    (refs : List IncidentOccurrence) :
    lastReference previous (current :: refs) =
      lastReference current refs := rfl

private theorem lastReference_eq_getLast (first : IncidentOccurrence)
    (rest : List IncidentOccurrence) :
    lastReference first rest = (first :: rest).getLast (by simp) := by
  induction rest generalizing first with
  | nil => rfl
  | cons current rest ih =>
      rw [lastReference_cons, ih current]
      cases rest <;> rfl

private theorem endpointValues_cons (first : IncidentOccurrence)
    (rest : List IncidentOccurrence) :
    (endpointValues (first :: rest)).flatMap endpointCell =
      endpointPairStream first (lastReference first rest) := by
  simp [endpointValues, endpointPairStream,
    lastReference_eq_getLast first rest]

private def rowBoundary_run (first last : IncidentOccurrence)
    (tail output : List UnaryFrameSym)
    (buffer : Option UnaryFrameSym) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.nextOccurrence first.rightSide last.rightSide) buffer test
        (.frameEnd :: tail) output
        (List.replicate first.occurrence ())
        (List.replicate last.occurrence ()))
      (some (cfg .beginRow (some .frameEnd) false tail
        ((endpointPairStream first last).reverse ++ output) [] []))
      (emitSteps first last + 1) := by
  let afterBoundary := cfg (.emitFirst first.rightSide last.rightSide)
    (some .frameEnd) test tail output
    (List.replicate first.occurrence ())
    (List.replicate last.occurrence ())
  have boundary : EvalsToInTime (step program)
      (cfg (.nextOccurrence first.rightSide last.rightSide) buffer test
        (.frameEnd :: tail) output
        (List.replicate first.occurrence ())
        (List.replicate last.occurrence ()))
      (some afterBoundary) 1 :=
    ⟨⟨1, by simp [flip, afterBoundary, step, program, cfg, stepOp]⟩,
      le_rfl⟩
  have emit := emit_run first last (some .frameEnd) test tail output
  let full := EvalsToInTime.trans (step program) 1 (emitSteps first last)
    _ afterBoundary _ boundary emit
  simpa [Nat.add_comm] using full

/-- Exact cost after the first reference has been retained. -/
def remainingSteps : IncidentOccurrence → IncidentOccurrence →
    List IncidentOccurrence → Nat
  | first, last, [] => emitSteps first last + 1
  | first, last, current :: refs =>
      nextReferenceSteps last current +
        remainingSteps first current refs

/-- Scan the remaining row, retain its latest reference, and emit exactly the
first and last endpoint cells at the boundary. -/
def remaining_run (first last : IncidentOccurrence)
    (refs : List IncidentOccurrence) (tail output : List UnaryFrameSym)
    (buffer : Option UnaryFrameSym) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.nextOccurrence first.rightSide last.rightSide) buffer test
        (refs.flatMap Scanner.encodeIncidentOccurrence ++ .frameEnd :: tail)
        output (List.replicate first.occurrence ())
        (List.replicate last.occurrence ()))
      (some (cfg .beginRow (some .frameEnd) false tail
        ((endpointPairStream first (lastReference last refs)).reverse ++
          output)
        [] []))
      (remainingSteps first last refs) := by
  induction refs generalizing last buffer test with
  | nil =>
      simpa [remainingSteps] using
        rowBoundary_run first last tail output buffer test
  | cons current refs ih =>
      let restInput :=
        refs.flatMap Scanner.encodeIncidentOccurrence ++ .frameEnd :: tail
      have load := nextReference_run first last current restInput output
        buffer test
      have rest := ih current (some .separator) false
      let full := EvalsToInTime.trans (step program)
        (nextReferenceSteps last current)
        (remainingSteps first current refs) _ _ _ load rest
      simpa [remainingSteps, restInput, List.append_assoc,
        Nat.add_assoc, Nat.add_comm] using full

/-- Exact cost of one complete incidence row. -/
def rowSteps : List IncidentOccurrence → Nat
  | [] => 1
  | first :: rest =>
      firstReferenceSteps first + remainingSteps first first rest

/-- Exact simulation of one complete marked incidence row. -/
def row_run (refs : List IncidentOccurrence)
    (tail output : List UnaryFrameSym)
    (buffer : Option UnaryFrameSym) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .beginRow buffer test
        (refs.flatMap Scanner.encodeIncidentOccurrence ++ .frameEnd :: tail)
        output [] [])
      (some (cfg .beginRow (some .frameEnd)
        (if refs.isEmpty then test else false) tail
        (((endpointValues refs).flatMap endpointCell).reverse ++ output)
        [] []))
      (rowSteps refs) := by
  cases refs with
  | nil =>
      exact ⟨⟨1, rfl⟩, le_rfl⟩
  | cons first rest =>
      let restInput :=
        rest.flatMap Scanner.encodeIncidentOccurrence ++ .frameEnd :: tail
      have firstRun := firstReference_run first restInput output buffer test
      have remainingRun := remaining_run first first rest tail output
        (some .separator) test
      let full := EvalsToInTime.trans (step program)
        (firstReferenceSteps first) (remainingSteps first first rest)
        _ _ _ firstRun remainingRun
      rw [endpointValues_cons first rest]
      convert full using 1
      · simp [restInput, List.append_assoc]
      · simp
      · simp [rowSteps]
        omega

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Endpoints

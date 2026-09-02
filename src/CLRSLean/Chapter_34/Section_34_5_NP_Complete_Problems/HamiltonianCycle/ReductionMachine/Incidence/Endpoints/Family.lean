import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.Incidence.Endpoints.Rows

/-!
# HAM-CYCLE selector endpoints: row-family simulation
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Endpoints

open PolyBuilder
open HamiltonianCycleReduction

def encodeReferenceRows (rows : List (List IncidentOccurrence)) :
    List UnaryFrameSym :=
  rows.flatMap fun refs =>
    refs.flatMap Scanner.encodeIncidentOccurrence ++ [.frameEnd]

def referenceRowsCells (rows : List (List IncidentOccurrence)) :
    List UnaryFrameSym :=
  rows.flatMap fun refs => (endpointValues refs).flatMap endpointCell

def rowsSteps : List (List IncidentOccurrence) → Nat
  | [] => 0
  | refs :: rows => rowSteps refs + rowsSteps rows

def rowsFinalBuffer (initial : Option UnaryFrameSym) :
    List (List IncidentOccurrence) → Option UnaryFrameSym
  | [] => initial
  | _ :: _ => some .frameEnd

def rowsFinalTest (initial : Bool) :
    List (List IncidentOccurrence) → Bool
  | [] => initial
  | refs :: rows =>
      rowsFinalTest (if refs.isEmpty then initial else false) rows

/-- Execute every marked incidence row in one continuous run. -/
def rows_run (rows : List (List IncidentOccurrence))
    (output : List UnaryFrameSym) (buffer : Option UnaryFrameSym)
    (test : Bool) :
    EvalsToInTime (step program)
      (cfg .beginRow buffer test (encodeReferenceRows rows) output [] [])
      (some (cfg .beginRow (rowsFinalBuffer buffer rows)
        (rowsFinalTest test rows) []
        ((referenceRowsCells rows).reverse ++ output) [] []))
      (rowsSteps rows) := by
  induction rows generalizing output buffer test with
  | nil => exact ⟨⟨0, rfl⟩, le_rfl⟩
  | cons refs rows ih =>
      have first := row_run refs (encodeReferenceRows rows) output buffer test
      have rest := ih
        ((((endpointValues refs).flatMap endpointCell).reverse ++ output))
        (some .frameEnd) (if refs.isEmpty then test else false)
      let full := EvalsToInTime.trans (step program)
        (rowSteps refs) (rowsSteps rows) _ _ _ first rest
      convert full using 1
      · simp [encodeReferenceRows]
      · cases rows <;>
          simp [rowsFinalBuffer, rowsFinalTest, referenceRowsCells,
            List.reverse_append, List.append_assoc]
      · simp [rowsSteps, Nat.add_comm]

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Endpoints

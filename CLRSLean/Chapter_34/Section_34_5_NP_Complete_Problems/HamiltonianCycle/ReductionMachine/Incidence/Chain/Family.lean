import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.Incidence.Chain.Rows

/-!
# HAM-CYCLE incidence-chain formatter: row-family simulation
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Chain

open PolyBuilder
open HamiltonianCycleReduction

/-- Scanner encoding of a mathematical family of incidence-reference rows. -/
def encodeReferenceRows (rows : List (List IncidentOccurrence)) :
    List UnaryFrameSym :=
  rows.flatMap fun refs =>
    refs.flatMap Scanner.encodeIncidentOccurrence ++ [.frameEnd]

/-- Chain edges contributed by a mathematical family of incidence rows. -/
def referenceRowsEdges (rows : List (List IncidentOccurrence)) :
    List (Nat × Nat) :=
  rows.flatMap incidenceChainEdges

/-- Exact cost of formatting a complete family of marked rows. -/
def rowsSteps : List (List IncidentOccurrence) → Nat
  | [] => 0
  | refs :: rows => rowSteps refs + rowsSteps rows

/-- Buffer one after a complete family has been consumed. -/
def rowsFinalBuffer (initial : Option UnaryFrameSym) :
    List (List IncidentOccurrence) → Option UnaryFrameSym
  | [] => initial
  | _ :: _ => some .frameEnd

@[simp] theorem rowsFinalBuffer_frameEnd
    (rows : List (List IncidentOccurrence)) :
    rowsFinalBuffer (some .frameEnd) rows = some .frameEnd := by
  cases rows <;> rfl

/-- Counter-test bit after a complete family has been consumed. -/
def rowsFinalTest (initial : Bool) :
    List (List IncidentOccurrence) → Bool
  | [] => initial
  | refs :: rows =>
      rowsFinalTest (if refs.isEmpty then initial else false) rows

/-- Exact simulation of every marked incidence row in one continuous run. -/
def rows_run (rows : List (List IncidentOccurrence))
    (hordered : ∀ refs ∈ rows,
      refs.Pairwise
        (fun first second => first.occurrence < second.occurrence))
    (output : List CliqueSym) (buffer : Option UnaryFrameSym)
    (test : Bool) :
    EvalsToInTime (step program)
      (cfg .beginRow buffer test (encodeReferenceRows rows) output [] [])
      (some (cfg .beginRow (rowsFinalBuffer buffer rows)
        (rowsFinalTest test rows) []
        (((referenceRowsEdges rows).flatMap encodeCliqueEdge).reverse ++ output)
        [] []))
      (rowsSteps rows) := by
  induction rows generalizing output buffer test with
  | nil =>
      exact ⟨⟨0, rfl⟩, le_rfl⟩
  | cons refs rows ih =>
      have hrefs : refs.Pairwise
          (fun first second => first.occurrence < second.occurrence) :=
        hordered refs (by simp)
      have hrows : ∀ row ∈ rows,
          row.Pairwise
            (fun first second => first.occurrence < second.occurrence) := by
        intro row hrow
        exact hordered row (by simp [hrow])
      have first := row_run refs hrefs (encodeReferenceRows rows) output
        buffer test
      have rest := ih hrows
        ((((incidenceChainEdges refs).flatMap encodeCliqueEdge).reverse ++
          output))
        (some .frameEnd) (if refs.isEmpty then test else false)
      let full := EvalsToInTime.trans (step program)
        (rowSteps refs) (rowsSteps rows) _ _ _ first rest
      convert full using 1
      · simp [encodeReferenceRows]
      · cases rows <;>
          simp [rowsFinalBuffer, rowsFinalTest, referenceRowsEdges,
            List.reverse_append, List.append_assoc]
      · simp [rowsSteps, Nat.add_comm]

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Chain

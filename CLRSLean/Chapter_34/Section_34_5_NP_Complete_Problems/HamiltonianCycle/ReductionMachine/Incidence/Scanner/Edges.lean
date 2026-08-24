import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.Incidence.Scanner.OccurrenceEmit

/-!
# HAM-CYCLE incidence scanner: canonical edge-list scan
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Scanner

open PolyBuilder
open HamiltonianCycleReduction

private theorem unit_cons_replicate (n : Nat) :
    () :: List.replicate n () = List.replicate (n + 1) () := by
  rw [List.replicate_succ]

/-- Exact cost of scanning a canonical source edge list. -/
def edgesSteps (query occurrence : Nat) : List (Nat × Nat) → Nat
  | [] => 1
  | edge :: edges =>
      1 + leftFieldSteps query 0 edge.1 + rightFieldSteps query 0 edge.2 +
        (if edge.1 = query then emitOccurrenceSteps occurrence false + 1
          else if edge.2 = query then emitOccurrenceSteps occurrence true + 1
          else 1) +
        edgesSteps query (occurrence + 1) edges

/-- Empty scans preserve the incoming test bit; every nonempty edge record
leaves it false after the comparison restoration. -/
def edgesFinalTest (initial : Bool) : List (Nat × Nat) → Bool
  | [] => initial
  | _ :: _ => false

private theorem encodeCliqueEdge_append (edge : Nat × Nat)
    (rest : List CliqueSym) :
    encodeCliqueEdge edge ++ rest =
      .edgeMark :: prependCliqueTicks edge.1
        (.pairSep :: prependCliqueTicks edge.2 (.recordEnd :: rest)) := by
  simp [encodeCliqueEdge, prependCliqueTicks_append]

/-- Scan every source edge, preserving its symbols in reverse order and
prepending precisely the reverse incidence-descriptor stream. -/
def edges_run (query occurrence : Nat) (edges : List (Nat × Nat))
    (output : List UnaryFrameSym) (work₁ work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .edges buffer₁ buffer₂ test
        ((edges.flatMap encodeCliqueEdge).map some) output work₁ work₂
        (List.replicate query ()) (List.replicate occurrence ()) [])
      (some (cfg .finishQuery buffer₁ none (edgesFinalTest test edges) []
        (((incidentOccurrencesFrom query occurrence edges).flatMap
          encodeIncidentOccurrence).reverse ++ output)
        work₁ (((edges.flatMap encodeCliqueEdge).map some).reverse ++ work₂)
        (List.replicate query ())
        (List.replicate (occurrence + edges.length) ()) []))
      (edgesSteps query occurrence edges) := by
  induction edges generalizing occurrence buffer₂ test work₂ output with
  | nil =>
      exact ⟨⟨1, by simp [flip, edgesFinalTest,
        incidentOccurrencesFrom, step, program, cfg, stepOp]⟩, le_rfl⟩
  | cons edge edges ih =>
      let tail := edges.flatMap encodeCliqueEdge
      let rightInput := prependCliqueTicks edge.2 (.recordEnd :: tail)
      let afterPop := cfg (.left true) buffer₁ (some (some .edgeMark)) test
        ((prependCliqueTicks edge.1 (.pairSep :: rightInput)).map some)
        output work₁ (some CliqueSym.edgeMark :: work₂)
        (List.replicate query ()) (List.replicate occurrence ()) []
      have first : EvalsToInTime (step program)
          (cfg .edges buffer₁ buffer₂ test
            (((edge :: edges).flatMap encodeCliqueEdge).map some) output
            work₁ work₂ (List.replicate query ())
            (List.replicate occurrence ()) [])
          (some afterPop) 1 :=
        ⟨⟨1, by simp [flip, afterPop, tail, rightInput,
          List.flatMap_cons, encodeCliqueEdge_append, step, program, cfg,
          stepOp]⟩, le_rfl⟩
      have leftRun := leftField_run query occurrence edge.1 true rightInput
        output work₁ (some CliqueSym.edgeMark :: work₂) buffer₁
        (some (some .edgeMark)) test
      let leftStored :=
        ((prependCliqueTicks edge.1 [.pairSep]).map some).reverse ++
          some CliqueSym.edgeMark :: work₂
      have leftRun' : EvalsToInTime (step program) afterPop
          (some (cfg (.right (decide (edge.1 = query)) true)
            buffer₁ (some (some .pairSep)) false (rightInput.map some) output
            work₁ leftStored (List.replicate query ())
            (List.replicate occurrence ()) []))
          (leftFieldSteps query 0 edge.1) := by
        simpa [afterPop, leftStored] using leftRun
      have rightRun := rightField_run query occurrence edge.2
        (decide (edge.1 = query)) true tail output work₁ leftStored buffer₁
        (some (some .pairSep)) false
      let edgeStored := ((encodeCliqueEdge edge).map some).reverse ++ work₂
      have hstored :
          ((prependCliqueTicks edge.2 [.recordEnd]).map some).reverse ++
              leftStored = edgeStored := by
        unfold leftStored edgeStored
        simp only [encodeCliqueEdge, List.map_cons, List.reverse_cons]
        have hsplit :
            prependCliqueTicks edge.1
                (.pairSep :: prependCliqueTicks edge.2 [.recordEnd]) =
              prependCliqueTicks edge.1 [.pairSep] ++
                prependCliqueTicks edge.2 [.recordEnd] := by
          symm
          exact prependCliqueTicks_append _ _ _
        rw [hsplit]
        simp [List.map_append, List.reverse_append, List.append_assoc]
      rw [hstored] at rightRun
      have rightRun' : EvalsToInTime (step program)
          (cfg (.right (decide (edge.1 = query)) true)
            buffer₁ (some (some .pairSep)) false (rightInput.map some) output
            work₁ leftStored (List.replicate query ())
            (List.replicate occurrence ()) [])
          (some (cfg
            (if edge.1 = query then .emitOccurrence false
              else if edge.2 = query then .emitOccurrence true
              else .advanceOccurrence)
            buffer₁ (some (some .recordEnd)) false (tail.map some) output
            work₁ edgeStored (List.replicate query ())
            (List.replicate occurrence ()) []))
          (rightFieldSteps query 0 edge.2) := by
        simpa [rightInput] using rightRun
      let throughLeft := EvalsToInTime.trans (step program)
        1 (leftFieldSteps query 0 edge.1) _ afterPop _ first leftRun'
      have throughLeft' : EvalsToInTime (step program)
          (cfg .edges buffer₁ buffer₂ test
            (((edge :: edges).flatMap encodeCliqueEdge).map some) output
            work₁ work₂ (List.replicate query ())
            (List.replicate occurrence ()) [])
          (some (cfg (.right (decide (edge.1 = query)) true)
            buffer₁ (some (some .pairSep)) false (rightInput.map some) output
            work₁ leftStored (List.replicate query ())
            (List.replicate occurrence ()) []))
          (1 + leftFieldSteps query 0 edge.1) := by
        simpa [Nat.add_comm] using throughLeft
      let throughRight := EvalsToInTime.trans (step program)
        (1 + leftFieldSteps query 0 edge.1)
        (rightFieldSteps query 0 edge.2) _ _ _ throughLeft' rightRun'
      by_cases hleft : edge.1 = query
      · have emitted := emitOccurrence_run query occurrence false (tail.map some)
          output work₁ edgeStored buffer₁ (some (some .recordEnd)) false
        have advanced : EvalsToInTime (step program)
            (cfg .advanceOccurrence buffer₁ (some (some .recordEnd)) false
              (tail.map some)
              ((encodeIncidentOccurrence
                { occurrence := occurrence, rightSide := false }).reverse ++ output)
              work₁ edgeStored (List.replicate query ())
              (List.replicate occurrence ()) [])
            (some (cfg .edges buffer₁ (some (some .recordEnd)) false
              (tail.map some)
              ((encodeIncidentOccurrence
                { occurrence := occurrence, rightSide := false }).reverse ++ output)
              work₁ edgeStored (List.replicate query ())
              (List.replicate (occurrence + 1) ()) [])) 1 :=
          ⟨⟨1, by simp [flip, step, program, cfg, stepOp,
            unit_cons_replicate]⟩, le_rfl⟩
        have recurse := ih (occurrence := occurrence + 1)
          (buffer₂ := some (some CliqueSym.recordEnd)) (test := false)
          (work₂ := edgeStored)
          (output := (encodeIncidentOccurrence
            { occurrence := occurrence, rightSide := false }).reverse ++ output)
        have hfinal : edgesFinalTest false edges = false := by
          cases edges <;> rfl
        rw [hfinal] at recurse
        let throughEmit := EvalsToInTime.trans (step program)
          _ (emitOccurrenceSteps occurrence false) _ _ _
          (by simpa [hleft] using throughRight) emitted
        let throughAdvance := EvalsToInTime.trans (step program)
          _ 1 _ _ _ throughEmit advanced
        let full := EvalsToInTime.trans (step program)
          _ (edgesSteps query (occurrence + 1) edges) _ _ _
          throughAdvance (by simpa [tail] using recurse)
        simpa [edgesSteps, edgesFinalTest, incidentOccurrencesFrom, hleft,
          tail, edgeStored, List.flatMap_cons, List.reverse_append,
          List.append_assoc, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using full
      · by_cases hright : edge.2 = query
        · have emitted := emitOccurrence_run query occurrence true (tail.map some)
            output work₁ edgeStored buffer₁ (some (some .recordEnd)) false
          have advanced : EvalsToInTime (step program)
              (cfg .advanceOccurrence buffer₁ (some (some .recordEnd)) false
                (tail.map some)
                ((encodeIncidentOccurrence
                  { occurrence := occurrence, rightSide := true }).reverse ++ output)
                work₁ edgeStored (List.replicate query ())
                (List.replicate occurrence ()) [])
              (some (cfg .edges buffer₁ (some (some .recordEnd)) false
                (tail.map some)
                ((encodeIncidentOccurrence
                  { occurrence := occurrence, rightSide := true }).reverse ++ output)
                work₁ edgeStored (List.replicate query ())
                (List.replicate (occurrence + 1) ()) [])) 1 :=
            ⟨⟨1, by simp [flip, step, program, cfg, stepOp,
              unit_cons_replicate]⟩, le_rfl⟩
          have recurse := ih (occurrence := occurrence + 1)
            (buffer₂ := some (some CliqueSym.recordEnd)) (test := false)
            (work₂ := edgeStored)
            (output := (encodeIncidentOccurrence
              { occurrence := occurrence, rightSide := true }).reverse ++ output)
          have hfinal : edgesFinalTest false edges = false := by
            cases edges <;> rfl
          rw [hfinal] at recurse
          let throughEmit := EvalsToInTime.trans (step program)
            _ (emitOccurrenceSteps occurrence true) _ _ _
            (by simpa [hleft, hright] using throughRight) emitted
          let throughAdvance := EvalsToInTime.trans (step program)
            _ 1 _ _ _ throughEmit advanced
          let full := EvalsToInTime.trans (step program)
            _ (edgesSteps query (occurrence + 1) edges) _ _ _
            throughAdvance (by simpa [tail] using recurse)
          simpa [edgesSteps, edgesFinalTest, incidentOccurrencesFrom, hleft,
            hright, tail, edgeStored, List.flatMap_cons, List.reverse_append,
            List.append_assoc, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using full
        · have advanced : EvalsToInTime (step program)
              (cfg .advanceOccurrence buffer₁ (some (some .recordEnd)) false
                (tail.map some) output work₁ edgeStored
                (List.replicate query ()) (List.replicate occurrence ()) [])
              (some (cfg .edges buffer₁ (some (some .recordEnd)) false
                (tail.map some) output work₁ edgeStored
                (List.replicate query ())
                (List.replicate (occurrence + 1) ()) [])) 1 :=
            ⟨⟨1, by simp [flip, step, program, cfg, stepOp,
              unit_cons_replicate]⟩, le_rfl⟩
          have recurse := ih (occurrence := occurrence + 1)
            (buffer₂ := some (some CliqueSym.recordEnd)) (test := false)
            (work₂ := edgeStored) (output := output)
          have hfinal : edgesFinalTest false edges = false := by
            cases edges <;> rfl
          rw [hfinal] at recurse
          let throughAdvance := EvalsToInTime.trans (step program)
            _ 1 _ _ _ (by simpa [hleft, hright] using throughRight) advanced
          let full := EvalsToInTime.trans (step program)
            _ (edgesSteps query (occurrence + 1) edges) _ _ _
            throughAdvance (by simpa [tail] using recurse)
          simpa [edgesSteps, edgesFinalTest, incidentOccurrencesFrom, hleft,
            hright, tail, edgeStored, List.flatMap_cons, List.reverse_append,
            List.append_assoc, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using full

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Scanner

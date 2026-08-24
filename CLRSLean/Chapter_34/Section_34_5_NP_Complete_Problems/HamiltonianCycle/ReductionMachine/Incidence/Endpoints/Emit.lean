import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.Incidence.Endpoints.Parse
import Mathlib.Tactic

/-!
# HAM-CYCLE selector endpoints: first/last port emission
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Endpoints

open PolyBuilder
open HamiltonianCycleReduction

def endpointCell (value : Nat) : List UnaryFrameSym :=
  encodeUnaryFrame [value] ++ [.frameEnd]

def endpointPairStream (first last : IncidentOccurrence) :
    List UnaryFrameSym :=
  endpointCell (incidentVertex first 0) ++
    endpointCell (incidentVertex last 5)

private def firstUnit_run (remaining : Nat) (firstSide lastSide : Bool)
    (buffer : Option UnaryFrameSym) (test : Bool)
    (input output : List UnaryFrameSym) (last : List Unit) :
    EvalsToInTime (step program)
      (cfg (.emitFirst firstSide lastSide) buffer test input output
        (List.replicate (remaining + 1) ()) last)
      (some (cfg (.emitFirst firstSide lastSide) buffer true input
        (List.replicate 12 UnaryFrameSym.tick ++ output)
        (List.replicate remaining ()) last)) 13 := by
  exact ⟨⟨13, by
    simp [flip, step, program, cfg, stepOp, firstTicksStart, predFin,
      List.replicate_succ]⟩, le_rfl⟩

def firstFinishLabel (firstSide lastSide : Bool) : Label :=
  if firstSide then firstOffsetStart lastSide else .firstSeparator lastSide

private def firstMultiplicity_run (remaining : Nat)
    (firstSide lastSide : Bool) (buffer : Option UnaryFrameSym) (test : Bool)
    (input output : List UnaryFrameSym) (last : List Unit) :
    EvalsToInTime (step program)
      (cfg (.emitFirst firstSide lastSide) buffer test input output
        (List.replicate remaining ()) last)
      (some (cfg (firstFinishLabel firstSide lastSide) buffer false input
        (List.replicate (12 * remaining) UnaryFrameSym.tick ++ output)
        [] last))
      (13 * remaining + 1) := by
  induction remaining generalizing test output with
  | zero =>
      cases firstSide <;>
        exact ⟨⟨1, by simp [flip, step, program, cfg, stepOp,
          firstFinishLabel, firstOffsetStart]⟩, le_rfl⟩
  | succ remaining ih =>
      have first := firstUnit_run remaining firstSide lastSide buffer test
        input output last
      have rest := ih true (List.replicate 12 .tick ++ output)
      let full := EvalsToInTime.trans (step program) 13
        (13 * remaining + 1) _ _ _ first rest
      have hout :
          List.replicate (12 * (remaining + 1)) UnaryFrameSym.tick ++ output =
            List.replicate (12 * remaining) UnaryFrameSym.tick ++
              (List.replicate 12 .tick ++ output) := by
        rw [show 12 * (remaining + 1) = 12 * remaining + 12 by omega,
          List.replicate_add, List.append_assoc]
      convert full using 1
      · rw [hout]
      · omega

private def firstOffset_run (firstSide lastSide : Bool)
    (buffer : Option UnaryFrameSym) (input output : List UnaryFrameSym)
    (last : List Unit) :
    EvalsToInTime (step program)
      (cfg (firstFinishLabel firstSide lastSide) buffer false input output [] last)
      (some (cfg (.firstSeparator lastSide) buffer false input
        (List.replicate (if firstSide then 6 else 0) .tick ++ output)
        [] last))
      (if firstSide then 6 else 0) := by
  cases firstSide
  · exact ⟨⟨0, by simp [firstFinishLabel]⟩, le_rfl⟩
  · exact ⟨⟨6, by simp [flip, step, program, cfg, stepOp,
      firstFinishLabel, firstOffsetStart, predFin]⟩, le_rfl⟩

private def firstDelimiters_run (lastSide : Bool)
    (buffer : Option UnaryFrameSym) (input output : List UnaryFrameSym)
    (last : List Unit) :
    EvalsToInTime (step program)
      (cfg (.firstSeparator lastSide) buffer false input output [] last)
      (some (cfg (.emitLast lastSide) buffer false input
        (.frameEnd :: .separator :: output) [] last)) 2 := by
  exact ⟨⟨2, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩

private def lastUnit_run (remaining : Nat) (lastSide : Bool)
    (buffer : Option UnaryFrameSym) (test : Bool)
    (input output : List UnaryFrameSym) :
    EvalsToInTime (step program)
      (cfg (.emitLast lastSide) buffer test input output []
        (List.replicate (remaining + 1) ()))
      (some (cfg (.emitLast lastSide) buffer true input
        (List.replicate 12 UnaryFrameSym.tick ++ output) []
        (List.replicate remaining ()))) 13 := by
  exact ⟨⟨13, by
    simp [flip, step, program, cfg, stepOp, lastTicksStart, predFin,
      List.replicate_succ]⟩, le_rfl⟩

private def lastMultiplicity_run (remaining : Nat) (lastSide : Bool)
    (buffer : Option UnaryFrameSym) (test : Bool)
    (input output : List UnaryFrameSym) :
    EvalsToInTime (step program)
      (cfg (.emitLast lastSide) buffer test input output []
        (List.replicate remaining ()))
      (some (cfg (if lastSide then lastOffsetStart else .lastOffset ⟨4, by omega⟩)
        buffer false input
        (List.replicate (12 * remaining) UnaryFrameSym.tick ++ output)
        [] []))
      (13 * remaining + 1) := by
  induction remaining generalizing test output with
  | zero =>
      exact ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | succ remaining ih =>
      have first := lastUnit_run remaining lastSide buffer test input output
      have rest := ih true (List.replicate 12 .tick ++ output)
      let full := EvalsToInTime.trans (step program) 13
        (13 * remaining + 1) _ _ _ first rest
      have hout :
          List.replicate (12 * (remaining + 1)) UnaryFrameSym.tick ++ output =
            List.replicate (12 * remaining) UnaryFrameSym.tick ++
              (List.replicate 12 .tick ++ output) := by
        rw [show 12 * (remaining + 1) = 12 * remaining + 12 by omega,
          List.replicate_add, List.append_assoc]
      convert full using 1
      · rw [hout]
      · omega

private def lastOffset_run (lastSide : Bool)
    (buffer : Option UnaryFrameSym) (input output : List UnaryFrameSym) :
    EvalsToInTime (step program)
      (cfg (if lastSide then lastOffsetStart else .lastOffset ⟨4, by omega⟩)
        buffer false input output [] [])
      (some (cfg .lastSeparator buffer false input
        (List.replicate (if lastSide then 11 else 5) .tick ++ output) [] []))
      (if lastSide then 11 else 5) := by
  cases lastSide
  · exact ⟨⟨5, by simp [flip, step, program, cfg, stepOp, predFin]⟩,
      le_rfl⟩
  · exact ⟨⟨11, by simp [flip, step, program, cfg, stepOp,
      lastOffsetStart, predFin]⟩, le_rfl⟩

private def lastDelimiters_run
    (buffer : Option UnaryFrameSym) (input output : List UnaryFrameSym) :
    EvalsToInTime (step program)
      (cfg .lastSeparator buffer false input output [] [])
      (some (cfg .beginRow buffer false input
        (.frameEnd :: .separator :: output) [] [])) 2 := by
  exact ⟨⟨2, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩

/-- Exact cost of emitting both endpoint cells for one nonempty row. -/
def emitSteps (first last : IncidentOccurrence) : Nat :=
  13 * first.occurrence + (if first.rightSide then 6 else 0) +
    13 * last.occurrence + (if last.rightSide then 11 else 5) + 6

/-- Consume both endpoint counters and emit their marked unary cells. -/
def emit_run (first last : IncidentOccurrence)
    (buffer : Option UnaryFrameSym) (test : Bool)
    (input output : List UnaryFrameSym) :
    EvalsToInTime (step program)
      (cfg (.emitFirst first.rightSide last.rightSide) buffer test input output
        (List.replicate first.occurrence ())
        (List.replicate last.occurrence ()))
      (some (cfg .beginRow buffer false input
        ((endpointPairStream first last).reverse ++ output) [] []))
      (emitSteps first last) := by
  have firstMultiplicity := firstMultiplicity_run first.occurrence
    first.rightSide last.rightSide buffer test input output
    (List.replicate last.occurrence ())
  have firstOffset := firstOffset_run first.rightSide last.rightSide buffer input
    (List.replicate (12 * first.occurrence) .tick ++ output)
    (List.replicate last.occurrence ())
  let firstOutput :=
    List.replicate (incidentVertex first 0) UnaryFrameSym.tick ++ output
  have firstDelimiters := firstDelimiters_run last.rightSide buffer input
    firstOutput (List.replicate last.occurrence ())
  let beforeLast := .frameEnd :: .separator :: firstOutput
  have lastMultiplicity := lastMultiplicity_run last.occurrence last.rightSide
    buffer false input beforeLast
  have lastOffset := lastOffset_run last.rightSide buffer input
    (List.replicate (12 * last.occurrence) .tick ++ beforeLast)
  let lastOutput :=
    List.replicate (incidentVertex last 5) UnaryFrameSym.tick ++ beforeLast
  have lastDelimiters := lastDelimiters_run buffer input lastOutput
  let run₁ := EvalsToInTime.trans (step program) _ _ _ _ _
    firstMultiplicity firstOffset
  have hfirst :
      List.replicate (if first.rightSide then 6 else 0) .tick ++
          (List.replicate (12 * first.occurrence) .tick ++ output) =
        firstOutput := by
    dsimp only [firstOutput]
    rw [← List.append_assoc, ← List.replicate_add]
    congr 2
    simp [incidentVertex, globalWidgetVertex, widgetVertex,
      widgetVertexCount]
    cases first.rightSide <;> omega
  have throughFirstOffset : EvalsToInTime (step program)
      (cfg (.emitFirst first.rightSide last.rightSide) buffer test input output
        (List.replicate first.occurrence ())
        (List.replicate last.occurrence ()))
      (some (cfg (.firstSeparator last.rightSide) buffer false input
        firstOutput [] (List.replicate last.occurrence ())))
      ((if first.rightSide then 6 else 0) +
        (13 * first.occurrence + 1)) := by
    simpa only [hfirst] using run₁
  let run₂ := EvalsToInTime.trans (step program) _ 2 _ _ _
    throughFirstOffset firstDelimiters
  let run₃ := EvalsToInTime.trans (step program) _ _ _ _ _
    run₂ lastMultiplicity
  let run₄ := EvalsToInTime.trans (step program) _ _ _ _ _
    run₃ lastOffset
  have hlast :
      List.replicate (if last.rightSide then 11 else 5) .tick ++
          (List.replicate (12 * last.occurrence) .tick ++ beforeLast) =
        lastOutput := by
    dsimp only [lastOutput]
    rw [← List.append_assoc, ← List.replicate_add]
    congr 2
    cases hside : last.rightSide <;>
      simp [hside, incidentVertex, globalWidgetVertex, widgetVertex,
        widgetVertexCount] <;> omega
  have throughLastOffset : EvalsToInTime (step program)
      (cfg (.emitFirst first.rightSide last.rightSide) buffer test input output
        (List.replicate first.occurrence ())
        (List.replicate last.occurrence ()))
      (some (cfg .lastSeparator buffer false input lastOutput [] []))
      ((if last.rightSide then 11 else 5) +
        (13 * last.occurrence + 1 +
          (2 + ((if first.rightSide then 6 else 0) +
            (13 * first.occurrence + 1))))) := by
    simpa only [hlast] using run₄
  let full := EvalsToInTime.trans (step program) _ 2 _ _ _
    throughLastOffset lastDelimiters
  convert full using 1
  · simp [endpointPairStream, endpointCell, encodeUnaryFrame,
      encodeUnaryFrameBlock, firstOutput, beforeLast, lastOutput,
      List.reverse_append, List.append_assoc]
  · simp [emitSteps]
    omega

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Endpoints

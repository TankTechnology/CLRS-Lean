import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.Incidence.Chain.Core
import Mathlib.Tactic

/-!
# HAM-CYCLE incidence-chain formatter: edge emission
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Chain

open PolyBuilder
open HamiltonianCycleReduction

private theorem prependCliqueTicks_eq_replicate (count : Nat)
    (tail : List CliqueSym) :
    prependCliqueTicks count tail =
      List.replicate count CliqueSym.tick ++ tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [prependCliqueTicks, ih, List.replicate_succ]
      rfl

private def leftUnit_run (remaining : Nat)
    (previousSide currentSide : Bool)
    (buffer : Option UnaryFrameSym) (test : Bool)
    (input : List UnaryFrameSym) (output : List CliqueSym)
    (current : List Unit) :
    EvalsToInTime (step program)
      (cfg (.emitLeft previousSide currentSide) buffer test input output
        (List.replicate (remaining + 1) ()) current)
      (some (cfg (.emitLeft previousSide currentSide) buffer true input
        (List.replicate 12 CliqueSym.tick ++ output)
        (List.replicate remaining ()) current)) 13 := by
  exact ⟨⟨13, by
    simp [flip, step, program, cfg, stepOp, leftTicksStart, predFin,
      List.replicate_succ]⟩, le_rfl⟩

/-- Emit twelve ticks per preceding occurrence token. -/
def leftMultiplicity_run (remaining : Nat)
    (previousSide currentSide : Bool)
    (buffer : Option UnaryFrameSym) (test : Bool)
    (input : List UnaryFrameSym) (output : List CliqueSym)
    (current : List Unit) :
    EvalsToInTime (step program)
      (cfg (.emitLeft previousSide currentSide) buffer test input output
        (List.replicate remaining ()) current)
      (some (cfg (leftOffsetStart previousSide currentSide) buffer false input
        (List.replicate (12 * remaining) CliqueSym.tick ++ output)
        [] current)) (13 * remaining + 1) := by
  induction remaining generalizing test output with
  | zero =>
      exact ⟨⟨1, by
        simp [flip, step, program, cfg, stepOp, leftOffsetStart]⟩, le_rfl⟩
  | succ remaining ih =>
      have first := leftUnit_run remaining previousSide currentSide buffer test
        input output current
      have rest := ih true (List.replicate 12 CliqueSym.tick ++ output)
      let full := EvalsToInTime.trans (step program)
        13 (13 * remaining + 1) _ _ _ first rest
      have hout :
          List.replicate (12 * (remaining + 1)) CliqueSym.tick ++ output =
            List.replicate (12 * remaining) CliqueSym.tick ++
              (List.replicate 12 CliqueSym.tick ++ output) := by
        rw [show 12 * (remaining + 1) = 12 * remaining + 12 by omega,
          List.replicate_add, List.append_assoc]
      convert full using 1
      · rw [hout]
      · omega

private def leftOffset_run (previousSide currentSide : Bool)
    (buffer : Option UnaryFrameSym) (input : List UnaryFrameSym)
    (output : List CliqueSym) (current : List Unit) :
    EvalsToInTime (step program)
      (cfg (leftOffsetStart previousSide currentSide) buffer false input output
        [] current)
      (some (cfg (.emitPairSeparator currentSide) buffer false input
        (List.replicate (incidentOffset previousSide 5) CliqueSym.tick ++
          output) [] current))
      (incidentOffset previousSide 5) := by
  cases previousSide <;>
    exact ⟨⟨_, by
      simp [flip, step, program, cfg, stepOp, leftOffsetStart, predFin,
        incidentOffset]⟩, le_rfl⟩

private def rightUnit_run (remaining loaded : Nat) (currentSide : Bool)
    (buffer : Option UnaryFrameSym) (test : Bool)
    (input : List UnaryFrameSym) (output : List CliqueSym) :
    EvalsToInTime (step program)
      (cfg (.emitRight currentSide) buffer test input output
        (List.replicate loaded ()) (List.replicate (remaining + 1) ()))
      (some (cfg (.emitRight currentSide) buffer true input
        (List.replicate 12 CliqueSym.tick ++ output)
        (List.replicate (loaded + 1) ())
        (List.replicate remaining ()))) 14 := by
  exact ⟨⟨14, by
    simp [flip, step, program, cfg, stepOp, rightTicksStart, predFin,
      List.replicate_succ]⟩, le_rfl⟩

def rightFinishLabel (currentSide : Bool) : Label :=
  if currentSide then rightOffsetStart else .emitRecordEnd false

/-- Emit twelve ticks per current occurrence token while moving the current
counter into the next-previous counter. -/
def rightMultiplicity_run (remaining loaded : Nat) (currentSide : Bool)
    (buffer : Option UnaryFrameSym) (test : Bool)
    (input : List UnaryFrameSym) (output : List CliqueSym) :
    EvalsToInTime (step program)
      (cfg (.emitRight currentSide) buffer test input output
        (List.replicate loaded ()) (List.replicate remaining ()))
      (some (cfg (rightFinishLabel currentSide) buffer false input
        (List.replicate (12 * remaining) CliqueSym.tick ++ output)
        (List.replicate (loaded + remaining) ()) []))
      (14 * remaining + 1) := by
  induction remaining generalizing loaded test output with
  | zero =>
      cases currentSide <;>
        exact ⟨⟨1, by
          simp [flip, step, program, cfg, stepOp, rightFinishLabel,
            rightOffsetStart]⟩, le_rfl⟩
  | succ remaining ih =>
      have first := rightUnit_run remaining loaded currentSide buffer test
        input output
      have rest := ih (loaded + 1) true
        (List.replicate 12 CliqueSym.tick ++ output)
      let full := EvalsToInTime.trans (step program)
        14 (14 * remaining + 1) _ _ _ first rest
      have hout :
          List.replicate (12 * (remaining + 1)) CliqueSym.tick ++ output =
            List.replicate (12 * remaining) CliqueSym.tick ++
              (List.replicate 12 CliqueSym.tick ++ output) := by
        rw [show 12 * (remaining + 1) = 12 * remaining + 12 by omega,
          List.replicate_add, List.append_assoc]
      have hloaded : loaded + (remaining + 1) = loaded + 1 + remaining := by
        omega
      convert full using 1
      · rw [hout, hloaded]
      · omega

private def rightOffset_run (currentSide : Bool)
    (buffer : Option UnaryFrameSym) (input : List UnaryFrameSym)
    (output : List CliqueSym) (previous : List Unit) :
    EvalsToInTime (step program)
      (cfg (rightFinishLabel currentSide) buffer false input output previous [])
      (some (cfg (.emitRecordEnd currentSide) buffer false input
        (List.replicate (incidentOffset currentSide 0) CliqueSym.tick ++
          output) previous []))
      (incidentOffset currentSide 0) := by
  cases currentSide
  · exact ⟨⟨0, by simp [rightFinishLabel, incidentOffset]⟩, le_rfl⟩
  · exact ⟨⟨6, by
      simp [flip, step, program, cfg, stepOp, rightFinishLabel,
        rightOffsetStart, predFin, incidentOffset]⟩, le_rfl⟩

/-- Exact cost of emitting one chain edge after both incident references have
been loaded. -/
def emitSteps (previous current : IncidentOccurrence) : Nat :=
  13 * previous.occurrence + 14 * current.occurrence +
    incidentOffset previous.rightSide 5 +
    incidentOffset current.rightSide 0 + 5

/-- Exact emission of one direct consecutive-occurrence edge. -/
def emit_run (previous current : IncidentOccurrence)
    (buffer : Option UnaryFrameSym) (test : Bool)
    (input : List UnaryFrameSym) (output : List CliqueSym) :
    EvalsToInTime (step program)
      (cfg (.emitMark previous.rightSide current.rightSide) buffer test input
        output (List.replicate previous.occurrence ())
        (List.replicate current.occurrence ()))
      (some (cfg (.nextOccurrence current.rightSide) buffer false input
        ((encodeCliqueEdge
          (incidentVertex previous 5, incidentVertex current 0)).reverse ++
            output)
        (List.replicate current.occurrence ()) []))
      (emitSteps previous current) := by
  let afterMark := cfg (.emitLeft previous.rightSide current.rightSide) buffer
    test input (.edgeMark :: output)
    (List.replicate previous.occurrence ())
    (List.replicate current.occurrence ())
  have markRun : EvalsToInTime (step program)
      (cfg (.emitMark previous.rightSide current.rightSide) buffer test input
        output (List.replicate previous.occurrence ())
        (List.replicate current.occurrence ()))
      (some afterMark) 1 :=
    ⟨⟨1, by simp [flip, afterMark, step, program, cfg, stepOp]⟩, le_rfl⟩
  have leftRun := leftMultiplicity_run previous.occurrence
    previous.rightSide current.rightSide buffer test input
    (.edgeMark :: output) (List.replicate current.occurrence ())
  have leftOffsetRun := leftOffset_run previous.rightSide current.rightSide
    buffer input
    (List.replicate (12 * previous.occurrence) CliqueSym.tick ++
      .edgeMark :: output)
    (List.replicate current.occurrence ())
  let leftOutput :=
    List.replicate (incidentVertex previous 5) CliqueSym.tick ++
      .edgeMark :: output
  let beforeRight := cfg (.emitRight current.rightSide) buffer false input
    (.pairSep :: leftOutput) [] (List.replicate current.occurrence ())
  have separatorRun : EvalsToInTime (step program)
      (cfg (.emitPairSeparator current.rightSide) buffer false input
        leftOutput
        [] (List.replicate current.occurrence ()))
      (some beforeRight) 1 :=
    ⟨⟨1, by simp [flip, beforeRight, step, program, cfg, stepOp]⟩, le_rfl⟩
  have rightRun := rightMultiplicity_run current.occurrence 0
    current.rightSide buffer false input
    (.pairSep :: leftOutput)
  have rightOffsetRun := rightOffset_run current.rightSide buffer input
    (List.replicate (12 * current.occurrence) CliqueSym.tick ++
      .pairSep :: leftOutput)
    (List.replicate current.occurrence ())
  let rightOutput :=
    List.replicate (incidentVertex current 0) CliqueSym.tick ++
      .pairSep :: leftOutput
  let finalOutput := .recordEnd :: rightOutput
  have recordRun : EvalsToInTime (step program)
      (cfg (.emitRecordEnd current.rightSide) buffer false input
        rightOutput
        (List.replicate current.occurrence ()) [])
      (some (cfg (.nextOccurrence current.rightSide) buffer false input
        finalOutput (List.replicate current.occurrence ()) [])) 1 :=
    ⟨⟨1, by simp [flip, finalOutput, step, program, cfg, stepOp]⟩, le_rfl⟩
  let run₁ := EvalsToInTime.trans (step program) 1 _ _ afterMark _
    markRun leftRun
  let run₂ := EvalsToInTime.trans (step program) _ _ _ _ _
    run₁ leftOffsetRun
  have hleftOutput :
      List.replicate (incidentOffset previous.rightSide 5) CliqueSym.tick ++
          (List.replicate (12 * previous.occurrence) CliqueSym.tick ++
            .edgeMark :: output) =
        leftOutput := by
    dsimp only [leftOutput]
    rw [← List.append_assoc, ← List.replicate_add]
    congr 2
    simp [incidentVertex_eq]
    omega
  have throughLeft : EvalsToInTime (step program)
      (cfg (.emitMark previous.rightSide current.rightSide) buffer test input
        output (List.replicate previous.occurrence ())
        (List.replicate current.occurrence ()))
      (some (cfg (.emitPairSeparator current.rightSide) buffer false input
        leftOutput [] (List.replicate current.occurrence ())))
      (incidentOffset previous.rightSide 5 +
        (13 * previous.occurrence + 1 + 1)) := by
    simpa only [hleftOutput] using run₂
  let run₃ := EvalsToInTime.trans (step program) _ 1 _ _ _
    throughLeft separatorRun
  have rightRun' : EvalsToInTime (step program)
      beforeRight
      (some (cfg (rightFinishLabel current.rightSide) buffer false input
        (List.replicate (12 * current.occurrence) CliqueSym.tick ++
          .pairSep :: leftOutput)
        (List.replicate current.occurrence ()) []))
      (14 * current.occurrence + 1) := by
    simpa using rightRun
  let run₄ := EvalsToInTime.trans (step program) _ _ _ beforeRight _
    run₃ rightRun'
  have hrightOutput :
      List.replicate (incidentOffset current.rightSide 0) CliqueSym.tick ++
          (List.replicate (12 * current.occurrence) CliqueSym.tick ++
            .pairSep :: leftOutput) =
        rightOutput := by
    dsimp only [rightOutput]
    rw [← List.append_assoc, ← List.replicate_add]
    congr 2
    simp [incidentVertex_eq]
    omega
  have throughRight : EvalsToInTime (step program)
      (cfg (.emitMark previous.rightSide current.rightSide) buffer test input
        output (List.replicate previous.occurrence ())
        (List.replicate current.occurrence ()))
      (some (cfg (.emitRecordEnd current.rightSide) buffer false input
        rightOutput (List.replicate current.occurrence ()) []))
      (incidentOffset current.rightSide 0 +
        (14 * current.occurrence + 1 +
          (1 + (incidentOffset previous.rightSide 5 +
            (13 * previous.occurrence + 1 + 1))))) := by
    let raw := EvalsToInTime.trans (step program) _ _ _ _ _
      run₄ rightOffsetRun
    simpa only [hrightOutput] using raw
  let full := EvalsToInTime.trans (step program) _ 1 _ _ _
    throughRight recordRun
  convert full using 1
  · simp [finalOutput, encodeCliqueEdge, incidentVertex_eq,
      prependCliqueTicks_eq_replicate, List.reverse_append,
      leftOutput, rightOutput, List.append_assoc]
  · simp [emitSteps]
    omega

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Chain

import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.Incidence.Endpoints.Core

/-!
# HAM-CYCLE selector endpoints: incidence-reference parsing
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Endpoints

open PolyBuilder
open HamiltonianCycleReduction

def sideSteps (side : Bool) : Nat := if side then 2 else 1

def firstReferenceSteps (ref : IncidentOccurrence) : Nat :=
  3 * ref.occurrence + 1 + sideSteps ref.rightSide

def nextReferenceSteps (previous current : IncidentOccurrence) : Nat :=
  previous.occurrence + 2 * current.occurrence + 2 +
    sideSteps current.rightSide

private def firstOccurrence_run (remaining loaded : Nat)
    (tail output : List UnaryFrameSym)
    (buffer : Option UnaryFrameSym) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .firstOccurrence buffer test
        (List.replicate remaining .tick ++ .separator :: tail)
        output (List.replicate loaded ()) (List.replicate loaded ()))
      (some (cfg .firstSide (some .separator) test tail output
        (List.replicate (loaded + remaining) ())
        (List.replicate (loaded + remaining) ())))
      (3 * remaining + 1) := by
  induction remaining generalizing loaded buffer with
  | zero =>
      exact ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | succ remaining ih =>
      let afterPop := cfg .incFirstOne (some .tick) test
        (List.replicate remaining .tick ++ .separator :: tail)
        output (List.replicate loaded ()) (List.replicate loaded ())
      let afterFirst := cfg .incFirstTwo (some .tick) test
        (List.replicate remaining .tick ++ .separator :: tail)
        output (List.replicate (loaded + 1) ()) (List.replicate loaded ())
      let afterSecond := cfg .firstOccurrence (some .tick) test
        (List.replicate remaining .tick ++ .separator :: tail)
        output (List.replicate (loaded + 1) ())
        (List.replicate (loaded + 1) ())
      have pop : EvalsToInTime (step program)
          (cfg .firstOccurrence buffer test
            (List.replicate (remaining + 1) .tick ++ .separator :: tail)
            output (List.replicate loaded ()) (List.replicate loaded ()))
          (some afterPop) 1 :=
        ⟨⟨1, by simp [flip, afterPop, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have first : EvalsToInTime (step program) afterPop
          (some afterFirst) 1 :=
        ⟨⟨1, by simp [flip, afterPop, afterFirst, step, program, cfg,
          stepOp, List.replicate_succ]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterFirst
          (some afterSecond) 1 :=
        ⟨⟨1, by simp [flip, afterFirst, afterSecond, step, program, cfg,
          stepOp, List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (loaded + 1) (some .tick)
      let firstTwo := EvalsToInTime.trans (step program) 1 1 _ afterPop _
        pop first
      let firstThree := EvalsToInTime.trans (step program) 2 1 _ afterFirst _
        firstTwo second
      let full := EvalsToInTime.trans (step program) 3
        (3 * remaining + 1) _ afterSecond _ firstThree rest
      convert full using 1
      · rw [show loaded + (remaining + 1) = loaded + 1 + remaining by omega]
      · omega

private def firstSide_run (side : Bool) (tail output : List UnaryFrameSym)
    (occurrence : List Unit) (buffer : Option UnaryFrameSym) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .firstSide buffer test
        (List.replicate (Scanner.sideValue side) .tick ++ .separator :: tail)
        output occurrence occurrence)
      (some (cfg (.nextOccurrence side side) (some .separator) test tail
        output occurrence occurrence))
      (sideSteps side) := by
  cases side <;>
    exact ⟨⟨_, by simp [flip, step, program, cfg, stepOp,
      Scanner.sideValue]⟩, le_rfl⟩

/-- Load the first reference into both the first and latest counters. -/
def firstReference_run (ref : IncidentOccurrence)
    (tail output : List UnaryFrameSym)
    (buffer : Option UnaryFrameSym) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .beginRow buffer test
        (Scanner.encodeIncidentOccurrence ref ++ tail) output [] [])
      (some (cfg (.nextOccurrence ref.rightSide ref.rightSide)
        (some .separator) test tail output
        (List.replicate ref.occurrence ())
        (List.replicate ref.occurrence ())))
      (firstReferenceSteps ref) := by
  rcases ref with ⟨occurrence, side⟩
  let sideInput :=
    List.replicate (Scanner.sideValue side) UnaryFrameSym.tick ++
      .separator :: tail
  cases occurrence with
  | zero =>
      let afterOccurrence := cfg .firstSide (some .separator) test sideInput
        output [] []
      have first : EvalsToInTime (step program)
          (cfg .beginRow buffer test
            (Scanner.encodeIncidentOccurrence ⟨0, side⟩ ++ tail)
            output [] [])
          (some afterOccurrence) 1 :=
        ⟨⟨1, by simp [flip, afterOccurrence, sideInput,
          Scanner.encodeIncidentOccurrence, encodeUnaryFrame,
          encodeUnaryFrameBlock, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := firstSide_run side tail output [] (some .separator) test
      let full := EvalsToInTime.trans (step program) 1 (sideSteps side)
        _ afterOccurrence _ first rest
      convert full using 1 <;> simp [firstReferenceSteps] <;> omega
  | succ occurrence =>
      let occurrenceInput :=
        List.replicate occurrence UnaryFrameSym.tick ++
          .separator :: sideInput
      let afterPop := cfg .incFirstOne (some .tick) test occurrenceInput
        output [] []
      let afterFirst := cfg .incFirstTwo (some .tick) test occurrenceInput
        output [()] []
      let afterSecond := cfg .firstOccurrence (some .tick) test occurrenceInput
        output [()] [()]
      have pop : EvalsToInTime (step program)
          (cfg .beginRow buffer test
            (Scanner.encodeIncidentOccurrence ⟨occurrence + 1, side⟩ ++ tail)
            output [] [])
          (some afterPop) 1 :=
        ⟨⟨1, by simp [flip, afterPop, occurrenceInput, sideInput,
          Scanner.encodeIncidentOccurrence, encodeUnaryFrame,
          encodeUnaryFrameBlock, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have first : EvalsToInTime (step program) afterPop
          (some afterFirst) 1 :=
        ⟨⟨1, by simp [flip, afterPop, afterFirst, step, program, cfg,
          stepOp]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterFirst
          (some afterSecond) 1 :=
        ⟨⟨1, by simp [flip, afterFirst, afterSecond, step, program, cfg,
          stepOp]⟩, le_rfl⟩
      have occurrenceRun := firstOccurrence_run occurrence 1 sideInput output
        (some .tick) test
      have sideRun := firstSide_run side tail output
        (List.replicate (occurrence + 1) ()) (some .separator) test
      have occurrenceRun' : EvalsToInTime (step program) afterSecond
          (some (cfg .firstSide (some .separator) test sideInput output
            (List.replicate (occurrence + 1) ())
            (List.replicate (occurrence + 1) ())))
          (3 * occurrence + 1) := by
        simpa [Nat.add_comm] using occurrenceRun
      let firstTwo := EvalsToInTime.trans (step program) 1 1 _ afterPop _
        pop first
      let firstThree := EvalsToInTime.trans (step program) 2 1 _ afterFirst _
        firstTwo second
      let throughOccurrence := EvalsToInTime.trans (step program) 3
        (3 * occurrence + 1) _ afterSecond _ firstThree occurrenceRun'
      let full := EvalsToInTime.trans (step program) _ (sideSteps side)
        _ _ _ throughOccurrence sideRun
      convert full using 1 <;> simp [firstReferenceSteps] <;> omega

private def clearLast_run (remaining : Nat) (firstSide beganWithTick : Bool)
    (first : List Unit) (tail output : List UnaryFrameSym)
    (buffer : Option UnaryFrameSym) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.clearLast firstSide beganWithTick) buffer test tail output first
        (List.replicate remaining ()))
      (some (cfg (if beganWithTick then .incLast firstSide
          else .currentSide firstSide)
        buffer false tail output first []))
      (remaining + 1) := by
  induction remaining generalizing test with
  | zero =>
      exact ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | succ remaining ih =>
      have firstStep : EvalsToInTime (step program)
          (cfg (.clearLast firstSide beganWithTick) buffer test tail output
            first (List.replicate (remaining + 1) ()))
          (some (cfg (.clearLast firstSide beganWithTick) buffer true tail
            output first (List.replicate remaining ()))) 1 :=
        ⟨⟨1, by simp [flip, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have rest := ih true
      let full := EvalsToInTime.trans (step program) 1 (remaining + 1)
        _ _ _ firstStep rest
      convert full using 1

private def currentOccurrence_run (remaining loaded : Nat)
    (firstSide : Bool) (first : List Unit)
    (tail output : List UnaryFrameSym)
    (buffer : Option UnaryFrameSym) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.currentOccurrence firstSide) buffer test
        (List.replicate remaining .tick ++ .separator :: tail)
        output first (List.replicate loaded ()))
      (some (cfg (.currentSide firstSide) (some .separator) test tail output
        first (List.replicate (loaded + remaining) ())))
      (2 * remaining + 1) := by
  induction remaining generalizing loaded buffer with
  | zero =>
      exact ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | succ remaining ih =>
      let afterPop := cfg (.incLast firstSide) (some .tick) test
        (List.replicate remaining .tick ++ .separator :: tail)
        output first (List.replicate loaded ())
      let afterInc := cfg (.currentOccurrence firstSide) (some .tick) test
        (List.replicate remaining .tick ++ .separator :: tail)
        output first (List.replicate (loaded + 1) ())
      have pop : EvalsToInTime (step program)
          (cfg (.currentOccurrence firstSide) buffer test
            (List.replicate (remaining + 1) .tick ++ .separator :: tail)
            output first (List.replicate loaded ()))
          (some afterPop) 1 :=
        ⟨⟨1, by simp [flip, afterPop, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have inc : EvalsToInTime (step program) afterPop
          (some afterInc) 1 :=
        ⟨⟨1, by simp [flip, afterPop, afterInc, step, program, cfg,
          stepOp, List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (loaded + 1) (some .tick)
      let firstTwo := EvalsToInTime.trans (step program) 1 1 _ afterPop _
        pop inc
      let full := EvalsToInTime.trans (step program) 2
        (2 * remaining + 1) _ afterInc _ firstTwo rest
      convert full using 1
      · rw [show loaded + (remaining + 1) = loaded + 1 + remaining by omega]
      · omega

private def currentSide_run (firstSide currentSide : Bool)
    (first current : List Unit) (tail output : List UnaryFrameSym)
    (buffer : Option UnaryFrameSym) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.currentSide firstSide) buffer test
        (List.replicate (Scanner.sideValue currentSide) .tick ++
          .separator :: tail)
        output first current)
      (some (cfg (.nextOccurrence firstSide currentSide) (some .separator)
        test tail output first current))
      (sideSteps currentSide) := by
  cases currentSide <;>
    exact ⟨⟨_, by simp [flip, step, program, cfg, stepOp,
      Scanner.sideValue]⟩, le_rfl⟩

/-- Replace the latest reference while retaining the first one. -/
def nextReference_run (first previous current : IncidentOccurrence)
    (tail output : List UnaryFrameSym)
    (buffer : Option UnaryFrameSym) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.nextOccurrence first.rightSide previous.rightSide) buffer test
        (Scanner.encodeIncidentOccurrence current ++ tail) output
        (List.replicate first.occurrence ())
        (List.replicate previous.occurrence ()))
      (some (cfg (.nextOccurrence first.rightSide current.rightSide)
        (some .separator) false tail output
        (List.replicate first.occurrence ())
        (List.replicate current.occurrence ())))
      (nextReferenceSteps previous current) := by
  rcases current with ⟨currentOccurrence, currentSide⟩
  let sideInput :=
    List.replicate (Scanner.sideValue currentSide) UnaryFrameSym.tick ++
      .separator :: tail
  cases currentOccurrence with
  | zero =>
      let afterPop := cfg (.clearLast first.rightSide false)
        (some .separator) test sideInput output
        (List.replicate first.occurrence ())
        (List.replicate previous.occurrence ())
      have pop : EvalsToInTime (step program)
          (cfg (.nextOccurrence first.rightSide previous.rightSide) buffer test
            (Scanner.encodeIncidentOccurrence
              ⟨0, currentSide⟩ ++ tail)
            output (List.replicate first.occurrence ())
            (List.replicate previous.occurrence ()))
          (some afterPop) 1 :=
        ⟨⟨1, by simp [flip, afterPop, sideInput,
          Scanner.encodeIncidentOccurrence, encodeUnaryFrame,
          encodeUnaryFrameBlock, step, program, cfg, stepOp]⟩, le_rfl⟩
      have clear := clearLast_run previous.occurrence first.rightSide false
        (List.replicate first.occurrence ()) sideInput output
        (some .separator) test
      have side := currentSide_run first.rightSide currentSide
        (List.replicate first.occurrence ()) [] tail output
        (some .separator) false
      let throughClear := EvalsToInTime.trans (step program) 1
        (previous.occurrence + 1) _ afterPop _ pop clear
      let full := EvalsToInTime.trans (step program) _
        (sideSteps currentSide) _ _ _ throughClear side
      convert full using 1
      · simp
      · simp [nextReferenceSteps]
        omega
  | succ occurrence =>
      let occurrenceInput :=
        List.replicate occurrence UnaryFrameSym.tick ++
          .separator :: sideInput
      let afterPop := cfg (.clearLast first.rightSide true) (some .tick) test
        occurrenceInput output (List.replicate first.occurrence ())
        (List.replicate previous.occurrence ())
      have pop : EvalsToInTime (step program)
          (cfg (.nextOccurrence first.rightSide previous.rightSide) buffer test
            (Scanner.encodeIncidentOccurrence
              ⟨occurrence + 1, currentSide⟩ ++ tail)
            output (List.replicate first.occurrence ())
            (List.replicate previous.occurrence ()))
          (some afterPop) 1 :=
        ⟨⟨1, by simp [flip, afterPop, occurrenceInput, sideInput,
          Scanner.encodeIncidentOccurrence, encodeUnaryFrame,
          encodeUnaryFrameBlock, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have clear := clearLast_run previous.occurrence first.rightSide true
        (List.replicate first.occurrence ()) occurrenceInput output
        (some .tick) test
      let afterInc := cfg (.currentOccurrence first.rightSide) (some .tick)
        false occurrenceInput output (List.replicate first.occurrence ()) [()]
      have inc : EvalsToInTime (step program)
          (cfg (.incLast first.rightSide) (some .tick) false occurrenceInput
            output (List.replicate first.occurrence ()) [])
          (some afterInc) 1 :=
        ⟨⟨1, by simp [flip, afterInc, step, program, cfg, stepOp]⟩,
          le_rfl⟩
      have occurrenceRun := currentOccurrence_run occurrence 1
        first.rightSide (List.replicate first.occurrence ()) sideInput output
        (some .tick) false
      have sideRun := currentSide_run first.rightSide currentSide
        (List.replicate first.occurrence ())
        (List.replicate (occurrence + 1) ()) tail output
        (some .separator) false
      have occurrenceRun' : EvalsToInTime (step program) afterInc
          (some (cfg (.currentSide first.rightSide) (some .separator) false
            sideInput output (List.replicate first.occurrence ())
            (List.replicate (occurrence + 1) ())))
          (2 * occurrence + 1) := by
        simpa [Nat.add_comm] using occurrenceRun
      let throughClear := EvalsToInTime.trans (step program) 1
        (previous.occurrence + 1) _ afterPop _ pop clear
      let throughInc := EvalsToInTime.trans (step program) _ 1 _ _ _
        throughClear inc
      let throughOccurrence := EvalsToInTime.trans (step program) _
        (2 * occurrence + 1) _ afterInc _ throughInc occurrenceRun'
      let full := EvalsToInTime.trans (step program) _
        (sideSteps currentSide) _ _ _ throughOccurrence sideRun
      convert full using 1
      simp [nextReferenceSteps]
      omega

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Endpoints

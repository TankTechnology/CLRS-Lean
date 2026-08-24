import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.Incidence.Chain.Emit

/-!
# HAM-CYCLE incidence-chain formatter: reference parsing
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Chain

open PolyBuilder
open HamiltonianCycleReduction

/-- Cost of consuming the unary side bit and its delimiter. -/
def sideSteps (side : Bool) : Nat := if side then 2 else 1

/-- Cost of loading one complete `(occurrence, side)` pair. -/
def referenceSteps (ref : IncidentOccurrence) : Nat :=
  2 * ref.occurrence + 1 + sideSteps ref.rightSide

private def firstOccurrence_run (remaining loaded : Nat)
    (tail : List UnaryFrameSym) (output : List CliqueSym)
    (buffer : Option UnaryFrameSym) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .firstOccurrence buffer test
        (List.replicate remaining .tick ++ .separator :: tail)
        output (List.replicate loaded ()) [])
      (some (cfg .firstSide (some .separator) test tail output
        (List.replicate (loaded + remaining) ()) []))
      (2 * remaining + 1) := by
  induction remaining generalizing loaded buffer with
  | zero =>
      exact ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | succ remaining ih =>
      let afterPop := cfg .incPrevious (some .tick) test
        (List.replicate remaining .tick ++ .separator :: tail)
        output (List.replicate loaded ()) []
      let afterInc := cfg .firstOccurrence (some .tick) test
        (List.replicate remaining .tick ++ .separator :: tail)
        output (List.replicate (loaded + 1) ()) []
      have first : EvalsToInTime (step program)
          (cfg .firstOccurrence buffer test
            (List.replicate (remaining + 1) .tick ++ .separator :: tail)
            output (List.replicate loaded ()) [])
          (some afterPop) 1 :=
        ⟨⟨1, by simp [flip, afterPop, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterPop
          (some afterInc) 1 :=
        ⟨⟨1, by simp [flip, afterPop, afterInc, step, program, cfg,
          stepOp, List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (loaded + 1) (some .tick)
      let firstTwo := EvalsToInTime.trans (step program) 1 1 _ afterPop _
        first second
      let full := EvalsToInTime.trans (step program) 2
        (2 * remaining + 1) _ afterInc _ firstTwo rest
      convert full using 1
      · rw [show loaded + (remaining + 1) = loaded + 1 + remaining by omega]
      · omega

private def firstSide_run (side : Bool) (tail : List UnaryFrameSym)
    (output : List CliqueSym) (previous : List Unit)
    (buffer : Option UnaryFrameSym) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .firstSide buffer test
        (List.replicate (Scanner.sideValue side) .tick ++ .separator :: tail)
        output previous [])
      (some (cfg (.nextOccurrence side) (some .separator) test tail output
        previous []))
      (sideSteps side) := by
  cases side <;>
    exact ⟨⟨_, by simp [flip, step, program, cfg, stepOp,
      Scanner.sideValue]⟩, le_rfl⟩

/-- Load the first reference of a nonempty row. -/
def firstReference_run (ref : IncidentOccurrence)
    (tail : List UnaryFrameSym) (output : List CliqueSym)
    (buffer : Option UnaryFrameSym) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .beginRow buffer test
        (Scanner.encodeIncidentOccurrence ref ++ tail) output [] [])
      (some (cfg (.nextOccurrence ref.rightSide) (some .separator) test tail
        output (List.replicate ref.occurrence ()) []))
      (referenceSteps ref) := by
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
      convert full using 1 <;>
        simp [referenceSteps] <;> omega
  | succ occurrence =>
      let occurrenceInput :=
        List.replicate occurrence UnaryFrameSym.tick ++
          .separator :: sideInput
      let afterPop := cfg .incPrevious (some .tick) test occurrenceInput
        output [] []
      let afterInc := cfg .firstOccurrence (some .tick) test occurrenceInput
        output [()] []
      have first : EvalsToInTime (step program)
          (cfg .beginRow buffer test
            (Scanner.encodeIncidentOccurrence ⟨occurrence + 1, side⟩ ++ tail)
            output [] [])
          (some afterPop) 1 :=
        ⟨⟨1, by simp [flip, afterPop, occurrenceInput, sideInput,
          Scanner.encodeIncidentOccurrence, encodeUnaryFrame,
          encodeUnaryFrameBlock, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterPop
          (some afterInc) 1 :=
        ⟨⟨1, by simp [flip, afterPop, afterInc, step, program, cfg,
          stepOp]⟩, le_rfl⟩
      have occurrenceRun := firstOccurrence_run occurrence 1 sideInput output
        (some .tick) test
      have sideRun := firstSide_run side tail output
        (List.replicate (occurrence + 1) ()) (some .separator) test
      have occurrenceRun' : EvalsToInTime (step program)
          afterInc
          (some (cfg .firstSide (some .separator) test sideInput output
            (List.replicate (occurrence + 1) ()) []))
          (2 * occurrence + 1) := by
        simpa [Nat.add_comm] using occurrenceRun
      let firstTwo := EvalsToInTime.trans (step program) 1 1 _ afterPop _
        first second
      let throughOccurrence := EvalsToInTime.trans (step program) 2
        (2 * occurrence + 1) _ afterInc _ firstTwo occurrenceRun'
      let full := EvalsToInTime.trans (step program) _ (sideSteps side)
        _ _ _ throughOccurrence sideRun
      convert full using 1 <;>
        simp [referenceSteps] <;> omega

private def currentOccurrence_run (remaining loaded : Nat)
    (previousSide : Bool) (tail : List UnaryFrameSym)
    (output : List CliqueSym) (previous : List Unit)
    (buffer : Option UnaryFrameSym) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.nextOccurrence previousSide) buffer test
        (List.replicate remaining .tick ++ .separator :: tail)
        output previous (List.replicate loaded ()))
      (some (cfg (.currentSide previousSide) (some .separator) test tail
        output previous (List.replicate (loaded + remaining) ())))
      (2 * remaining + 1) := by
  induction remaining generalizing loaded buffer with
  | zero =>
      exact ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | succ remaining ih =>
      let afterPop := cfg (.incCurrent previousSide) (some .tick) test
        (List.replicate remaining .tick ++ .separator :: tail)
        output previous (List.replicate loaded ())
      let afterInc := cfg (.nextOccurrence previousSide) (some .tick) test
        (List.replicate remaining .tick ++ .separator :: tail)
        output previous (List.replicate (loaded + 1) ())
      have first : EvalsToInTime (step program)
          (cfg (.nextOccurrence previousSide) buffer test
            (List.replicate (remaining + 1) .tick ++ .separator :: tail)
            output previous (List.replicate loaded ()))
          (some afterPop) 1 :=
        ⟨⟨1, by simp [flip, afterPop, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterPop
          (some afterInc) 1 :=
        ⟨⟨1, by simp [flip, afterPop, afterInc, step, program, cfg,
          stepOp, List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (loaded + 1) (some .tick)
      let firstTwo := EvalsToInTime.trans (step program) 1 1 _ afterPop _
        first second
      let full := EvalsToInTime.trans (step program) 2
        (2 * remaining + 1) _ afterInc _ firstTwo rest
      convert full using 1
      · rw [show loaded + (remaining + 1) = loaded + 1 + remaining by omega]
      · omega

private def currentSide_run (previousSide currentSide : Bool)
    (tail : List UnaryFrameSym) (output : List CliqueSym)
    (previous current : List Unit) (buffer : Option UnaryFrameSym)
    (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.currentSide previousSide) buffer test
        (List.replicate (Scanner.sideValue currentSide) .tick ++
          .separator :: tail)
        output previous current)
      (some (cfg (.emitMark previousSide currentSide) (some .separator) test
        tail output previous current))
      (sideSteps currentSide) := by
  cases currentSide <;>
    exact ⟨⟨_, by simp [flip, step, program, cfg, stepOp,
      Scanner.sideValue]⟩, le_rfl⟩

/-- Load a later reference while retaining its predecessor. -/
def nextReference_run (previous current : IncidentOccurrence)
    (tail : List UnaryFrameSym) (output : List CliqueSym)
    (buffer : Option UnaryFrameSym) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.nextOccurrence previous.rightSide) buffer test
        (Scanner.encodeIncidentOccurrence current ++ tail) output
        (List.replicate previous.occurrence ()) [])
      (some (cfg (.emitMark previous.rightSide current.rightSide)
        (some .separator) test tail output
        (List.replicate previous.occurrence ())
        (List.replicate current.occurrence ())))
      (referenceSteps current) := by
  let sideInput :=
    List.replicate (Scanner.sideValue current.rightSide) UnaryFrameSym.tick ++
      .separator :: tail
  have occurrenceRun := currentOccurrence_run current.occurrence 0
    previous.rightSide sideInput output
    (List.replicate previous.occurrence ()) buffer test
  have sideRun := currentSide_run previous.rightSide current.rightSide tail
    output (List.replicate previous.occurrence ())
    (List.replicate current.occurrence ()) (some .separator) test
  have occurrenceRun' : EvalsToInTime (step program)
      (cfg (.nextOccurrence previous.rightSide) buffer test
        (List.replicate current.occurrence .tick ++ .separator :: sideInput)
        output (List.replicate previous.occurrence ()) [])
      (some (cfg (.currentSide previous.rightSide) (some .separator) test
        sideInput output (List.replicate previous.occurrence ())
        (List.replicate current.occurrence ())))
      (2 * current.occurrence + 1) := by
    simpa using occurrenceRun
  let full := EvalsToInTime.trans (step program)
    (2 * current.occurrence + 1) (sideSteps current.rightSide)
    _ _ _ occurrenceRun' sideRun
  convert full using 1 <;>
    simp [referenceSteps, sideInput, Scanner.encodeIncidentOccurrence,
      encodeUnaryFrame, encodeUnaryFrameBlock] <;> omega

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Chain

import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.Incidence.Scanner.CandidateLeft

/-!
# HAM-CYCLE incidence scanner: right endpoint comparison
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Scanner

open PolyBuilder

/-- Exact controller cost for comparing a right endpoint. -/
def rightFieldSteps : Nat → Nat → Nat → Nat
  | remaining, saved, 0 =>
      1 + (2 * remaining + 1) + (2 * (remaining + saved) + 1)
  | 0, saved, candidate + 1 => rightFieldSteps 0 saved candidate + 2
  | remaining + 1, saved, candidate + 1 =>
      rightFieldSteps remaining (saved + 1) candidate + 3

private theorem decide_nat_eq_comm (a b : Nat) :
    decide (a = b) = decide (b = a) := by
  by_cases h : a = b
  · subst b
    rfl
  · have h' : b ≠ a := fun hba => h hba.symm
    simp [h, h']

private def rightField_run_aux (remaining saved occurrence candidate : Nat)
    (leftEqual rightEqual : Bool) (rest : List CliqueSym)
    (output : List UnaryFrameSym) (work₁ work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.right leftEqual rightEqual) buffer₁ buffer₂ test
        ((prependCliqueTicks candidate (.recordEnd :: rest)).map some) output
        work₁ work₂ (List.replicate remaining ())
        (List.replicate occurrence ()) (List.replicate saved ()))
      (some (cfg
        (if leftEqual then .emitOccurrence false
          else if rightEqual && decide (remaining = candidate) then
            .emitOccurrence true else .advanceOccurrence)
        buffer₁ (some (some .recordEnd)) false (rest.map some) output work₁
        (((prependCliqueTicks candidate [.recordEnd]).map some).reverse ++ work₂)
        (List.replicate (remaining + saved) ())
        (List.replicate occurrence ()) []))
      (rightFieldSteps remaining saved candidate) := by
  induction candidate generalizing remaining saved rightEqual buffer₂ test work₂ with
  | zero =>
      let afterPop := cfg (.rightEnd leftEqual rightEqual) buffer₁
        (some (some .recordEnd)) test (rest.map some) output work₁
        (some CliqueSym.recordEnd :: work₂) (List.replicate remaining ())
        (List.replicate occurrence ()) (List.replicate saved ())
      have first : EvalsToInTime (step program)
          (cfg (.right leftEqual rightEqual) buffer₁ buffer₂ test
            ((prependCliqueTicks 0 (.recordEnd :: rest)).map some) output
            work₁ work₂ (List.replicate remaining ())
            (List.replicate occurrence ()) (List.replicate saved ()))
          (some afterPop) 1 :=
        ⟨⟨1, by simp [flip, afterPop, prependCliqueTicks, step, program,
          cfg, stepOp]⟩, le_rfl⟩
      have finish := rightEnd_run remaining saved occurrence leftEqual rightEqual
        (rest.map some) output work₁ (some CliqueSym.recordEnd :: work₂)
        buffer₁ (some (some .recordEnd)) test
      have restore := restoreRight_run (remaining + saved) 0 occurrence
        leftEqual (rightEqual && decide (remaining = 0)) (rest.map some) output
        work₁ (some CliqueSym.recordEnd :: work₂) buffer₁
        (some (some .recordEnd)) false
      let throughEnd := EvalsToInTime.trans (step program)
        1 (2 * remaining + 1) _ afterPop _ first finish
      have throughEnd' : EvalsToInTime (step program)
          (cfg (.right leftEqual rightEqual) buffer₁ buffer₂ test
            ((prependCliqueTicks 0 (.recordEnd :: rest)).map some) output
            work₁ work₂ (List.replicate remaining ())
            (List.replicate occurrence ()) (List.replicate saved ()))
          (some (cfg
            (.restoreRight leftEqual (rightEqual && decide (remaining = 0)))
            buffer₁ (some (some .recordEnd)) false (rest.map some) output
            work₁ (some CliqueSym.recordEnd :: work₂) []
            (List.replicate occurrence ())
            (List.replicate (remaining + saved) ())))
          (1 + (2 * remaining + 1)) := by
        simpa [Nat.add_comm] using throughEnd
      let full := EvalsToInTime.trans (step program)
        (1 + (2 * remaining + 1)) (2 * (remaining + saved) + 1)
        _ _ _ throughEnd' restore
      simpa [rightFieldSteps, prependCliqueTicks, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full
  | succ candidate ih =>
      let remainingInput :=
        (prependCliqueTicks candidate (.recordEnd :: rest)).map some
      let afterPop := cfg (.spendRight leftEqual rightEqual) buffer₁
        (some (some .tick)) test remainingInput output work₁
        (some CliqueSym.tick :: work₂) (List.replicate remaining ())
        (List.replicate occurrence ()) (List.replicate saved ())
      have first : EvalsToInTime (step program)
          (cfg (.right leftEqual rightEqual) buffer₁ buffer₂ test
            ((prependCliqueTicks (candidate + 1) (.recordEnd :: rest)).map some)
            output work₁ work₂ (List.replicate remaining ())
            (List.replicate occurrence ()) (List.replicate saved ()))
          (some afterPop) 1 :=
        ⟨⟨1, by simp [flip, afterPop, remainingInput, prependCliqueTicks,
          step, program, cfg, stepOp]⟩, le_rfl⟩
      cases remaining with
      | zero =>
          let afterSpend := cfg (.right leftEqual false) buffer₁
            (some (some .tick)) false remainingInput output work₁
            (some CliqueSym.tick :: work₂) [] (List.replicate occurrence ())
            (List.replicate saved ())
          have second : EvalsToInTime (step program) afterPop
              (some afterSpend) 1 :=
            ⟨⟨1, by simp [flip, afterPop, afterSpend, step, program, cfg,
              stepOp]⟩, le_rfl⟩
          have restRun := ih (remaining := 0) (saved := saved)
            (rightEqual := false) (buffer₂ := some (some CliqueSym.tick))
            (test := false) (work₂ := some CliqueSym.tick :: work₂)
          let throughSpend := EvalsToInTime.trans (step program)
            1 1 _ afterPop _ first second
          let full := EvalsToInTime.trans (step program)
            2 (rightFieldSteps 0 saved candidate) _ afterSpend _ throughSpend
            (by simpa [remainingInput] using restRun)
          simpa [rightFieldSteps, prependCliqueTicks, List.reverse_cons,
            List.append_assoc, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using full
      | succ remaining =>
          let afterSpend := cfg (.saveRight leftEqual rightEqual) buffer₁
            (some (some .tick)) true remainingInput output work₁
            (some CliqueSym.tick :: work₂) (List.replicate remaining ())
            (List.replicate occurrence ()) (List.replicate saved ())
          let afterSave := cfg (.right leftEqual rightEqual) buffer₁
            (some (some .tick)) true remainingInput output work₁
            (some CliqueSym.tick :: work₂) (List.replicate remaining ())
            (List.replicate occurrence ()) (List.replicate (saved + 1) ())
          have second : EvalsToInTime (step program) afterPop
              (some afterSpend) 1 :=
            ⟨⟨1, by simp [flip, afterPop, afterSpend, step, program, cfg,
              stepOp, List.replicate_succ]⟩, le_rfl⟩
          have third : EvalsToInTime (step program) afterSpend
              (some afterSave) 1 :=
            ⟨⟨1, by simp [flip, afterSpend, afterSave, step, program, cfg,
              stepOp, List.replicate_succ]⟩, le_rfl⟩
          have restRun := ih (remaining := remaining) (saved := saved + 1)
            (rightEqual := rightEqual)
            (buffer₂ := some (some CliqueSym.tick)) (test := true)
            (work₂ := some CliqueSym.tick :: work₂)
          let throughSpend := EvalsToInTime.trans (step program)
            1 1 _ afterPop _ first second
          let throughSave := EvalsToInTime.trans (step program)
            2 1 _ afterSpend _ throughSpend third
          let full := EvalsToInTime.trans (step program)
            3 (rightFieldSteps remaining (saved + 1) candidate)
            _ afterSave _ throughSave (by
              simpa [remainingInput] using restRun)
          simpa [rightFieldSteps, prependCliqueTicks, List.reverse_cons,
            List.append_assoc, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using full

/-- Compare a canonical right endpoint and choose the incidence action. -/
def rightField_run (query occurrence candidate : Nat)
    (leftEqual rightEqual : Bool) (rest : List CliqueSym)
    (output : List UnaryFrameSym) (work₁ work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.right leftEqual rightEqual) buffer₁ buffer₂ test
        ((prependCliqueTicks candidate (.recordEnd :: rest)).map some) output
        work₁ work₂ (List.replicate query ())
        (List.replicate occurrence ()) [])
      (some (cfg
        (if leftEqual then .emitOccurrence false
          else if rightEqual && decide (candidate = query) then
            .emitOccurrence true else .advanceOccurrence)
        buffer₁ (some (some .recordEnd)) false (rest.map some) output work₁
        (((prependCliqueTicks candidate [.recordEnd]).map some).reverse ++ work₂)
        (List.replicate query ()) (List.replicate occurrence ()) []))
      (rightFieldSteps query 0 candidate) := by
  have run := rightField_run_aux query 0 occurrence candidate leftEqual rightEqual
    rest output work₁ work₂ buffer₁ buffer₂ test
  rw [decide_nat_eq_comm query candidate] at run
  simpa using run

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Scanner

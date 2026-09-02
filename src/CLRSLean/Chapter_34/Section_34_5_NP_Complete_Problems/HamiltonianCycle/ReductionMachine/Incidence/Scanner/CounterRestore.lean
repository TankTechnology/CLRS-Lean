import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.Incidence.Scanner.Header

/-!
# HAM-CYCLE incidence scanner: query-counter restoration
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Scanner

open PolyBuilder

/-- Restore temporarily consumed query ticks after the left endpoint. -/
def restoreLeft_run (remaining restored occurrence : Nat) (equal : Bool)
    (input : List (Option CliqueSym)) (output : List UnaryFrameSym)
    (work₁ work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.restoreLeft equal) buffer₁ buffer₂ test input output work₁ work₂
        (List.replicate restored ()) (List.replicate occurrence ())
        (List.replicate remaining ()))
      (some (cfg (.right equal true) buffer₁ buffer₂ false input output
        work₁ work₂ (List.replicate (remaining + restored) ())
        (List.replicate occurrence ()) []))
      (2 * remaining + 1) := by
  induction remaining generalizing restored test with
  | zero =>
      exact ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | succ remaining ih =>
      let afterDec := cfg (.restoreLeftInc equal) buffer₁ buffer₂ true input
        output work₁ work₂ (List.replicate restored ())
        (List.replicate occurrence ()) (List.replicate remaining ())
      let afterInc := cfg (.restoreLeft equal) buffer₁ buffer₂ true input output
        work₁ work₂ (List.replicate (restored + 1) ())
        (List.replicate occurrence ()) (List.replicate remaining ())
      have first : EvalsToInTime (step program)
          (cfg (.restoreLeft equal) buffer₁ buffer₂ test input output work₁ work₂
            (List.replicate restored ()) (List.replicate occurrence ())
            (List.replicate (remaining + 1) ()))
          (some afterDec) 1 :=
        ⟨⟨1, by simp [flip, afterDec, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterDec (some afterInc) 1 :=
        ⟨⟨1, by simp [flip, afterDec, afterInc, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (restored := restored + 1) (test := true)
      let firstTwo := EvalsToInTime.trans (step program) 1 1
        _ afterDec _ first second
      let full := EvalsToInTime.trans (step program)
        2 (2 * remaining + 1) _ afterInc _ firstTwo rest
      simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full

/-- Restore temporarily consumed query ticks after the right endpoint. -/
def restoreRight_run (remaining restored occurrence : Nat)
    (leftEqual rightEqual : Bool)
    (input : List (Option CliqueSym)) (output : List UnaryFrameSym)
    (work₁ work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.restoreRight leftEqual rightEqual) buffer₁ buffer₂ test input output
        work₁ work₂ (List.replicate restored ())
        (List.replicate occurrence ()) (List.replicate remaining ()))
      (some (cfg
        (if leftEqual then .emitOccurrence false
          else if rightEqual then .emitOccurrence true else .advanceOccurrence)
        buffer₁ buffer₂ false input output work₁ work₂
        (List.replicate (remaining + restored) ())
        (List.replicate occurrence ()) []))
      (2 * remaining + 1) := by
  induction remaining generalizing restored test with
  | zero =>
      exact ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | succ remaining ih =>
      let afterDec := cfg (.restoreRightInc leftEqual rightEqual) buffer₁ buffer₂
        true input output work₁ work₂ (List.replicate restored ())
        (List.replicate occurrence ()) (List.replicate remaining ())
      let afterInc := cfg (.restoreRight leftEqual rightEqual) buffer₁ buffer₂ true
        input output work₁ work₂ (List.replicate (restored + 1) ())
        (List.replicate occurrence ()) (List.replicate remaining ())
      have first : EvalsToInTime (step program)
          (cfg (.restoreRight leftEqual rightEqual) buffer₁ buffer₂ test input output
            work₁ work₂ (List.replicate restored ())
            (List.replicate occurrence ()) (List.replicate (remaining + 1) ()))
          (some afterDec) 1 :=
        ⟨⟨1, by simp [flip, afterDec, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterDec (some afterInc) 1 :=
        ⟨⟨1, by simp [flip, afterDec, afterInc, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (restored := restored + 1) (test := true)
      let firstTwo := EvalsToInTime.trans (step program) 1 1
        _ afterDec _ first second
      let full := EvalsToInTime.trans (step program)
        2 (2 * remaining + 1) _ afterInc _ firstTwo rest
      simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full

/-- Move the unconsumed query suffix into the scratch counter. -/
def drainLeft_run (remaining saved occurrence : Nat)
    (input : List (Option CliqueSym)) (output : List UnaryFrameSym)
    (work₁ work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .drainLeft buffer₁ buffer₂ test input output work₁ work₂
        (List.replicate remaining ()) (List.replicate occurrence ())
        (List.replicate saved ()))
      (some (cfg (.restoreLeft false) buffer₁ buffer₂ false input output
        work₁ work₂ [] (List.replicate occurrence ())
        (List.replicate (remaining + saved) ())))
      (2 * remaining + 1) := by
  induction remaining generalizing saved test with
  | zero =>
      exact ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | succ remaining ih =>
      let afterDec := cfg .saveLeftRemainder buffer₁ buffer₂ true input output
        work₁ work₂ (List.replicate remaining ())
        (List.replicate occurrence ()) (List.replicate saved ())
      let afterInc := cfg .drainLeft buffer₁ buffer₂ true input output work₁
        work₂ (List.replicate remaining ()) (List.replicate occurrence ())
        (List.replicate (saved + 1) ())
      have first : EvalsToInTime (step program)
          (cfg .drainLeft buffer₁ buffer₂ test input output work₁ work₂
            (List.replicate (remaining + 1) ()) (List.replicate occurrence ())
            (List.replicate saved ()))
          (some afterDec) 1 :=
        ⟨⟨1, by simp [flip, afterDec, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterDec (some afterInc) 1 :=
        ⟨⟨1, by simp [flip, afterDec, afterInc, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (saved := saved + 1) (test := true)
      let firstTwo := EvalsToInTime.trans (step program) 1 1
        _ afterDec _ first second
      let full := EvalsToInTime.trans (step program)
        2 (2 * remaining + 1) _ afterInc _ firstTwo rest
      simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full

/-- Right-end counterpart of `drainLeft_run`. -/
def drainRight_run (remaining saved occurrence : Nat) (leftEqual : Bool)
    (input : List (Option CliqueSym)) (output : List UnaryFrameSym)
    (work₁ work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.drainRight leftEqual) buffer₁ buffer₂ test input output work₁ work₂
        (List.replicate remaining ()) (List.replicate occurrence ())
        (List.replicate saved ()))
      (some (cfg (.restoreRight leftEqual false) buffer₁ buffer₂ false input output
        work₁ work₂ [] (List.replicate occurrence ())
        (List.replicate (remaining + saved) ())))
      (2 * remaining + 1) := by
  induction remaining generalizing saved test with
  | zero =>
      exact ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | succ remaining ih =>
      let afterDec := cfg (.saveRightRemainder leftEqual) buffer₁ buffer₂ true
        input output work₁ work₂ (List.replicate remaining ())
        (List.replicate occurrence ()) (List.replicate saved ())
      let afterInc := cfg (.drainRight leftEqual) buffer₁ buffer₂ true input output
        work₁ work₂ (List.replicate remaining ())
        (List.replicate occurrence ()) (List.replicate (saved + 1) ())
      have first : EvalsToInTime (step program)
          (cfg (.drainRight leftEqual) buffer₁ buffer₂ test input output work₁ work₂
            (List.replicate (remaining + 1) ()) (List.replicate occurrence ())
            (List.replicate saved ()))
          (some afterDec) 1 :=
        ⟨⟨1, by simp [flip, afterDec, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterDec (some afterInc) 1 :=
        ⟨⟨1, by simp [flip, afterDec, afterInc, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (saved := saved + 1) (test := true)
      let firstTwo := EvalsToInTime.trans (step program) 1 1
        _ afterDec _ first second
      let full := EvalsToInTime.trans (step program)
        2 (2 * remaining + 1) _ afterInc _ firstTwo rest
      simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full

/-- Finish the left field and restore the complete query counter. -/
def leftEnd_run (remaining saved occurrence : Nat) (equal : Bool)
    (input : List (Option CliqueSym)) (output : List UnaryFrameSym)
    (work₁ work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.leftEnd equal) buffer₁ buffer₂ test input output work₁ work₂
        (List.replicate remaining ()) (List.replicate occurrence ())
        (List.replicate saved ()))
      (some (cfg (.restoreLeft (equal && decide (remaining = 0)))
        buffer₁ buffer₂ false input output work₁ work₂ []
        (List.replicate occurrence ()) (List.replicate (remaining + saved) ())))
      (2 * remaining + 1) := by
  cases remaining with
  | zero =>
      exact ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | succ remaining =>
      let afterDec := cfg .saveLeftRemainder buffer₁ buffer₂ true input output
        work₁ work₂ (List.replicate remaining ())
        (List.replicate occurrence ()) (List.replicate saved ())
      let afterInc := cfg .drainLeft buffer₁ buffer₂ true input output work₁
        work₂ (List.replicate remaining ()) (List.replicate occurrence ())
        (List.replicate (saved + 1) ())
      have first : EvalsToInTime (step program)
          (cfg (.leftEnd equal) buffer₁ buffer₂ test input output work₁ work₂
            (List.replicate (remaining + 1) ()) (List.replicate occurrence ())
            (List.replicate saved ()))
          (some afterDec) 1 :=
        ⟨⟨1, by simp [flip, afterDec, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterDec (some afterInc) 1 :=
        ⟨⟨1, by simp [flip, afterDec, afterInc, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have rest := drainLeft_run remaining (saved + 1) occurrence input output
        work₁ work₂ buffer₁ buffer₂ true
      let firstTwo := EvalsToInTime.trans (step program) 1 1
        _ afterDec _ first second
      let full := EvalsToInTime.trans (step program)
        2 (2 * remaining + 1) _ afterInc _ firstTwo rest
      simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full

/-- Finish the right field and restore the complete query counter. -/
def rightEnd_run (remaining saved occurrence : Nat)
    (leftEqual rightEqual : Bool)
    (input : List (Option CliqueSym)) (output : List UnaryFrameSym)
    (work₁ work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.rightEnd leftEqual rightEqual) buffer₁ buffer₂ test input output
        work₁ work₂ (List.replicate remaining ())
        (List.replicate occurrence ()) (List.replicate saved ()))
      (some (cfg (.restoreRight leftEqual (rightEqual && decide (remaining = 0)))
        buffer₁ buffer₂ false input output work₁ work₂ []
        (List.replicate occurrence ()) (List.replicate (remaining + saved) ())))
      (2 * remaining + 1) := by
  cases remaining with
  | zero =>
      exact ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | succ remaining =>
      let afterDec := cfg (.saveRightRemainder leftEqual) buffer₁ buffer₂ true
        input output work₁ work₂ (List.replicate remaining ())
        (List.replicate occurrence ()) (List.replicate saved ())
      let afterInc := cfg (.drainRight leftEqual) buffer₁ buffer₂ true input output
        work₁ work₂ (List.replicate remaining ())
        (List.replicate occurrence ()) (List.replicate (saved + 1) ())
      have first : EvalsToInTime (step program)
          (cfg (.rightEnd leftEqual rightEqual) buffer₁ buffer₂ test input output
            work₁ work₂ (List.replicate (remaining + 1) ())
            (List.replicate occurrence ()) (List.replicate saved ()))
          (some afterDec) 1 :=
        ⟨⟨1, by simp [flip, afterDec, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterDec (some afterInc) 1 :=
        ⟨⟨1, by simp [flip, afterDec, afterInc, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have rest := drainRight_run remaining (saved + 1) occurrence leftEqual
        input output work₁ work₂ buffer₁ buffer₂ true
      let firstTwo := EvalsToInTime.trans (step program) 1 1
        _ afterDec _ first second
      let full := EvalsToInTime.trans (step program)
        2 (2 * remaining + 1) _ afterInc _ firstTwo rest
      simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Scanner

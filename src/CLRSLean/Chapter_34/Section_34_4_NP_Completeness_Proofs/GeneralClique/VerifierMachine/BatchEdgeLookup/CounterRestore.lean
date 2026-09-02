import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.BatchEdgeLookup.Cleanup

/-!
# Batch edge lookup: query-counter restoration
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.BatchEdgeLookup

open PolyBuilder

/-- Restore temporarily consumed left-query tokens from counter three. -/
def restoreLeft_run (aggregate : Bool) (remaining restored right : Nat)
    (equal : Bool) (input : List (Option CliqueSym)) (output : List Bool)
    (work₁ work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.restoreLeft aggregate equal) buffer₁ buffer₂ test input output
        work₁ work₂ (List.replicate restored ()) (List.replicate right ())
        (List.replicate remaining ()))
      (some (cfg (.right aggregate equal) buffer₁ buffer₂ false input output
        work₁ work₂ (List.replicate (remaining + restored) ())
        (List.replicate right ()) []))
      (2 * remaining + 1) := by
  induction remaining generalizing restored test with
  | zero =>
      exact ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | succ remaining ih =>
      let afterDec := cfg (.restoreLeftInc aggregate equal) buffer₁ buffer₂
        true input output work₁ work₂ (List.replicate restored ())
        (List.replicate right ()) (List.replicate remaining ())
      let afterInc := cfg (.restoreLeft aggregate equal) buffer₁ buffer₂ true
        input output work₁ work₂ (List.replicate (restored + 1) ())
        (List.replicate right ()) (List.replicate remaining ())
      have first : EvalsToInTime (step program)
          (cfg (.restoreLeft aggregate equal) buffer₁ buffer₂ test input output
            work₁ work₂ (List.replicate restored ())
            (List.replicate right ()) (List.replicate (remaining + 1) ()))
          (some afterDec) 1 :=
        ⟨⟨1, by simp [flip, afterDec, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterDec
          (some afterInc) 1 :=
        ⟨⟨1, by simp [flip, afterDec, afterInc, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (restored := restored + 1) (test := true)
      let firstTwo := EvalsToInTime.trans (step program) 1 1
        _ afterDec _ first second
      let full := EvalsToInTime.trans (step program)
        2 (2 * remaining + 1) _ afterInc _ firstTwo rest
      simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full

/-- Restore temporarily consumed right-query tokens from counter three. -/
def restoreRight_run (aggregate : Bool) (left remaining restored : Nat)
    (answer : Bool) (input : List (Option CliqueSym)) (output : List Bool)
    (work₁ work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.restoreRight aggregate answer) buffer₁ buffer₂ test input output
        work₁ work₂ (List.replicate left ()) (List.replicate restored ())
        (List.replicate remaining ()))
      (some (cfg
        (if answer then .drainGraph aggregate else .edges aggregate)
        buffer₁ buffer₂ false input output work₁ work₂
        (List.replicate left ()) (List.replicate (remaining + restored) ()) []))
      (2 * remaining + 1) := by
  induction remaining generalizing restored test with
  | zero =>
      exact ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | succ remaining ih =>
      let afterDec := cfg (.restoreRightInc aggregate answer) buffer₁ buffer₂
        true input output work₁ work₂ (List.replicate left ())
        (List.replicate restored ()) (List.replicate remaining ())
      let afterInc := cfg (.restoreRight aggregate answer) buffer₁ buffer₂ true
        input output work₁ work₂ (List.replicate left ())
        (List.replicate (restored + 1) ()) (List.replicate remaining ())
      have first : EvalsToInTime (step program)
          (cfg (.restoreRight aggregate answer) buffer₁ buffer₂ test input
            output work₁ work₂ (List.replicate left ())
            (List.replicate restored ()) (List.replicate (remaining + 1) ()))
          (some afterDec) 1 :=
        ⟨⟨1, by simp [flip, afterDec, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterDec
          (some afterInc) 1 :=
        ⟨⟨1, by simp [flip, afterDec, afterInc, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (restored := restored + 1) (test := true)
      let firstTwo := EvalsToInTime.trans (step program) 1 1
        _ afterDec _ first second
      let full := EvalsToInTime.trans (step program)
        2 (2 * remaining + 1) _ afterInc _ firstTwo rest
      simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full

/-- Move the unconsumed left-query suffix into the restoration counter. -/
def drainLeft_run (aggregate : Bool) (remaining saved right : Nat)
    (input : List (Option CliqueSym)) (output : List Bool)
    (work₁ work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.drainLeft aggregate) buffer₁ buffer₂ test input output work₁
        work₂ (List.replicate remaining ()) (List.replicate right ())
        (List.replicate saved ()))
      (some (cfg (.restoreLeft aggregate false) buffer₁ buffer₂ false input
        output work₁ work₂ [] (List.replicate right ())
        (List.replicate (remaining + saved) ())))
      (2 * remaining + 1) := by
  induction remaining generalizing saved test with
  | zero =>
      exact ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | succ remaining ih =>
      let afterDec := cfg (.saveLeftRemainder aggregate) buffer₁ buffer₂ true
        input output work₁ work₂ (List.replicate remaining ())
        (List.replicate right ()) (List.replicate saved ())
      let afterInc := cfg (.drainLeft aggregate) buffer₁ buffer₂ true input
        output work₁ work₂ (List.replicate remaining ())
        (List.replicate right ()) (List.replicate (saved + 1) ())
      have first : EvalsToInTime (step program)
          (cfg (.drainLeft aggregate) buffer₁ buffer₂ test input output work₁
            work₂ (List.replicate (remaining + 1) ())
            (List.replicate right ()) (List.replicate saved ()))
          (some afterDec) 1 :=
        ⟨⟨1, by simp [flip, afterDec, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterDec
          (some afterInc) 1 :=
        ⟨⟨1, by simp [flip, afterDec, afterInc, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (saved := saved + 1) (test := true)
      let firstTwo := EvalsToInTime.trans (step program) 1 1
        _ afterDec _ first second
      let full := EvalsToInTime.trans (step program)
        2 (2 * remaining + 1) _ afterInc _ firstTwo rest
      simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full

/-- Move the unconsumed right-query suffix into the restoration counter. -/
def drainRight_run (aggregate : Bool) (left remaining saved : Nat)
    (input : List (Option CliqueSym)) (output : List Bool)
    (work₁ work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.drainRight aggregate) buffer₁ buffer₂ test input output work₁
        work₂ (List.replicate left ()) (List.replicate remaining ())
        (List.replicate saved ()))
      (some (cfg (.restoreRight aggregate false) buffer₁ buffer₂ false input
        output work₁ work₂ (List.replicate left ()) []
        (List.replicate (remaining + saved) ())))
      (2 * remaining + 1) := by
  induction remaining generalizing saved test with
  | zero =>
      exact ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | succ remaining ih =>
      let afterDec := cfg (.saveRightRemainder aggregate) buffer₁ buffer₂ true
        input output work₁ work₂ (List.replicate left ())
        (List.replicate remaining ()) (List.replicate saved ())
      let afterInc := cfg (.drainRight aggregate) buffer₁ buffer₂ true input
        output work₁ work₂ (List.replicate left ())
        (List.replicate remaining ()) (List.replicate (saved + 1) ())
      have first : EvalsToInTime (step program)
          (cfg (.drainRight aggregate) buffer₁ buffer₂ test input output work₁
            work₂ (List.replicate left ())
            (List.replicate (remaining + 1) ()) (List.replicate saved ()))
          (some afterDec) 1 :=
        ⟨⟨1, by simp [flip, afterDec, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterDec
          (some afterInc) 1 :=
        ⟨⟨1, by simp [flip, afterDec, afterInc, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (saved := saved + 1) (test := true)
      let firstTwo := EvalsToInTime.trans (step program) 1 1
        _ afterDec _ first second
      let full := EvalsToInTime.trans (step program)
        2 (2 * remaining + 1) _ afterInc _ firstTwo rest
      simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full

/-- Finish a left candidate field and preserve the original query count. -/
def leftEnd_run (aggregate : Bool) (remaining saved right : Nat)
    (equal : Bool) (input : List (Option CliqueSym)) (output : List Bool)
    (work₁ work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.leftEnd aggregate equal) buffer₁ buffer₂ test input output work₁
        work₂ (List.replicate remaining ()) (List.replicate right ())
        (List.replicate saved ()))
      (some (cfg
        (.restoreLeft aggregate (equal && decide (remaining = 0)))
        buffer₁ buffer₂ false input output work₁ work₂ []
        (List.replicate right ()) (List.replicate (remaining + saved) ())))
      (2 * remaining + 1) := by
  cases remaining with
  | zero =>
      exact ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | succ remaining =>
      let afterDec := cfg (.saveLeftRemainder aggregate) buffer₁ buffer₂ true
        input output work₁ work₂ (List.replicate remaining ())
        (List.replicate right ()) (List.replicate saved ())
      let afterInc := cfg (.drainLeft aggregate) buffer₁ buffer₂ true input
        output work₁ work₂ (List.replicate remaining ())
        (List.replicate right ()) (List.replicate (saved + 1) ())
      have first : EvalsToInTime (step program)
          (cfg (.leftEnd aggregate equal) buffer₁ buffer₂ test input output
            work₁ work₂ (List.replicate (remaining + 1) ())
            (List.replicate right ()) (List.replicate saved ()))
          (some afterDec) 1 :=
        ⟨⟨1, by simp [flip, afterDec, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterDec
          (some afterInc) 1 :=
        ⟨⟨1, by simp [flip, afterDec, afterInc, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have rest := drainLeft_run aggregate remaining (saved + 1) right input
        output work₁ work₂ buffer₁ buffer₂ true
      let firstTwo := EvalsToInTime.trans (step program) 1 1
        _ afterDec _ first second
      let full := EvalsToInTime.trans (step program)
        2 (2 * remaining + 1) _ afterInc _ firstTwo rest
      simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full

/-- Finish a right candidate field and preserve the original query count. -/
def rightEnd_run (aggregate : Bool) (left remaining saved : Nat)
    (equal : Bool) (input : List (Option CliqueSym)) (output : List Bool)
    (work₁ work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.rightEnd aggregate equal) buffer₁ buffer₂ test input output work₁
        work₂ (List.replicate left ()) (List.replicate remaining ())
        (List.replicate saved ()))
      (some (cfg
        (.restoreRight aggregate (equal && decide (remaining = 0)))
        buffer₁ buffer₂ false input output work₁ work₂
        (List.replicate left ()) [] (List.replicate (remaining + saved) ())))
      (2 * remaining + 1) := by
  cases remaining with
  | zero =>
      exact ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | succ remaining =>
      let afterDec := cfg (.saveRightRemainder aggregate) buffer₁ buffer₂ true
        input output work₁ work₂ (List.replicate left ())
        (List.replicate remaining ()) (List.replicate saved ())
      let afterInc := cfg (.drainRight aggregate) buffer₁ buffer₂ true input
        output work₁ work₂ (List.replicate left ())
        (List.replicate remaining ()) (List.replicate (saved + 1) ())
      have first : EvalsToInTime (step program)
          (cfg (.rightEnd aggregate equal) buffer₁ buffer₂ test input output
            work₁ work₂ (List.replicate left ())
            (List.replicate (remaining + 1) ()) (List.replicate saved ()))
          (some afterDec) 1 :=
        ⟨⟨1, by simp [flip, afterDec, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterDec
          (some afterInc) 1 :=
        ⟨⟨1, by simp [flip, afterDec, afterInc, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have rest := drainRight_run aggregate left remaining (saved + 1) input
        output work₁ work₂ buffer₁ buffer₂ true
      let firstTwo := EvalsToInTime.trans (step program) 1 1
        _ afterDec _ first second
      let full := EvalsToInTime.trans (step program)
        2 (2 * remaining + 1) _ afterInc _ firstTwo rest
      simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.BatchEdgeLookup

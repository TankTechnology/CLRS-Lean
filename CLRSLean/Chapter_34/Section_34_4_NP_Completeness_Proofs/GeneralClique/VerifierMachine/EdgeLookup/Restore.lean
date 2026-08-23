import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.EdgeLookup.Cleanup

/-!
# General CLIQUE verifier: edge-query budget restoration
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.EdgeLookup

open PolyBuilder

/-- Restore temporarily consumed left-query tokens from counter three. -/
def restoreLeft_run (remaining restored right : Nat) (equal : Bool)
    (input : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.restoreLeft equal) buffer₁ buffer₂ test input []
        (List.replicate restored ()) (List.replicate right ())
        (List.replicate remaining ()))
      (some (cfg (.right equal) buffer₁ buffer₂ false input []
        (List.replicate (remaining + restored) ())
        (List.replicate right ()) []))
      (2 * remaining + 1) := by
  induction remaining generalizing restored test with
  | zero =>
      exact ⟨⟨1, by
        simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | succ remaining ih =>
      let afterDec := cfg (.restoreLeftInc equal) buffer₁ buffer₂ true input []
        (List.replicate restored ()) (List.replicate right ())
        (List.replicate remaining ())
      let afterInc := cfg (.restoreLeft equal) buffer₁ buffer₂ true input []
        (List.replicate (restored + 1) ()) (List.replicate right ())
        (List.replicate remaining ())
      have first : EvalsToInTime (step program)
          (cfg (.restoreLeft equal) buffer₁ buffer₂ test input []
            (List.replicate restored ()) (List.replicate right ())
            (List.replicate (remaining + 1) ()))
          (some afterDec) 1 := by
        exact ⟨⟨1, by
          simp [flip, afterDec, step, program, cfg, stepOp,
            List.replicate_succ]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterDec
          (some afterInc) 1 := by
        exact ⟨⟨1, by
          simp [flip, afterDec, afterInc, step, program, cfg, stepOp,
            List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (restored := restored + 1) (test := true)
      have throughInc := EvalsToInTime.trans (step program)
        1 1 _ afterDec _ first second
      let full := EvalsToInTime.trans (step program)
        2 (2 * remaining + 1) _ afterInc _ throughInc rest
      simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full

/-- Restore temporarily consumed right-query tokens from counter three. -/
def restoreRight_run (left remaining restored : Nat) (answer : Bool)
    (input : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.restoreRight answer) buffer₁ buffer₂ test input []
        (List.replicate left ()) (List.replicate restored ())
        (List.replicate remaining ()))
      (some (cfg (if answer then .clearInput true else .edges)
        buffer₁ buffer₂ false input [] (List.replicate left ())
        (List.replicate (remaining + restored) ()) []))
      (2 * remaining + 1) := by
  induction remaining generalizing restored test with
  | zero =>
      exact ⟨⟨1, by
        simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | succ remaining ih =>
      let afterDec := cfg (.restoreRightInc answer) buffer₁ buffer₂ true
        input [] (List.replicate left ()) (List.replicate restored ())
        (List.replicate remaining ())
      let afterInc := cfg (.restoreRight answer) buffer₁ buffer₂ true
        input [] (List.replicate left ())
        (List.replicate (restored + 1) ()) (List.replicate remaining ())
      have first : EvalsToInTime (step program)
          (cfg (.restoreRight answer) buffer₁ buffer₂ test input []
            (List.replicate left ()) (List.replicate restored ())
            (List.replicate (remaining + 1) ()))
          (some afterDec) 1 := by
        exact ⟨⟨1, by
          simp [flip, afterDec, step, program, cfg, stepOp,
            List.replicate_succ]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterDec
          (some afterInc) 1 := by
        exact ⟨⟨1, by
          simp [flip, afterDec, afterInc, step, program, cfg, stepOp,
            List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (restored := restored + 1) (test := true)
      have throughInc := EvalsToInTime.trans (step program)
        1 1 _ afterDec _ first second
      let full := EvalsToInTime.trans (step program)
        2 (2 * remaining + 1) _ afterInc _ throughInc rest
      simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full

/-- Move the unconsumed left-query suffix into the restoration counter. -/
def drainLeft_run (remaining saved right : Nat)
    (input : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .drainLeft buffer₁ buffer₂ test input []
        (List.replicate remaining ()) (List.replicate right ())
        (List.replicate saved ()))
      (some (cfg (.restoreLeft false) buffer₁ buffer₂ false input [] []
        (List.replicate right ())
        (List.replicate (remaining + saved) ())))
      (2 * remaining + 1) := by
  induction remaining generalizing saved test with
  | zero =>
      exact ⟨⟨1, by
        simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | succ remaining ih =>
      let afterDec := cfg .saveLeftRemainder buffer₁ buffer₂ true input []
        (List.replicate remaining ()) (List.replicate right ())
        (List.replicate saved ())
      let afterInc := cfg .drainLeft buffer₁ buffer₂ true input []
        (List.replicate remaining ()) (List.replicate right ())
        (List.replicate (saved + 1) ())
      have first : EvalsToInTime (step program)
          (cfg .drainLeft buffer₁ buffer₂ test input []
            (List.replicate (remaining + 1) ()) (List.replicate right ())
            (List.replicate saved ()))
          (some afterDec) 1 := by
        exact ⟨⟨1, by
          simp [flip, afterDec, step, program, cfg, stepOp,
            List.replicate_succ]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterDec
          (some afterInc) 1 := by
        exact ⟨⟨1, by
          simp [flip, afterDec, afterInc, step, program, cfg, stepOp,
            List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (saved := saved + 1) (test := true)
      have throughInc := EvalsToInTime.trans (step program)
        1 1 _ afterDec _ first second
      let full := EvalsToInTime.trans (step program)
        2 (2 * remaining + 1) _ afterInc _ throughInc rest
      simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full

/-- Move the unconsumed right-query suffix into the restoration counter. -/
def drainRight_run (left remaining saved : Nat)
    (input : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .drainRight buffer₁ buffer₂ test input []
        (List.replicate left ()) (List.replicate remaining ())
        (List.replicate saved ()))
      (some (cfg (.restoreRight false) buffer₁ buffer₂ false input []
        (List.replicate left ()) []
        (List.replicate (remaining + saved) ())))
      (2 * remaining + 1) := by
  induction remaining generalizing saved test with
  | zero =>
      exact ⟨⟨1, by
        simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | succ remaining ih =>
      let afterDec := cfg .saveRightRemainder buffer₁ buffer₂ true input []
        (List.replicate left ()) (List.replicate remaining ())
        (List.replicate saved ())
      let afterInc := cfg .drainRight buffer₁ buffer₂ true input []
        (List.replicate left ()) (List.replicate remaining ())
        (List.replicate (saved + 1) ())
      have first : EvalsToInTime (step program)
          (cfg .drainRight buffer₁ buffer₂ test input []
            (List.replicate left ()) (List.replicate (remaining + 1) ())
            (List.replicate saved ()))
          (some afterDec) 1 := by
        exact ⟨⟨1, by
          simp [flip, afterDec, step, program, cfg, stepOp,
            List.replicate_succ]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterDec
          (some afterInc) 1 := by
        exact ⟨⟨1, by
          simp [flip, afterDec, afterInc, step, program, cfg, stepOp,
            List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (saved := saved + 1) (test := true)
      have throughInc := EvalsToInTime.trans (step program)
        1 1 _ afterDec _ first second
      let full := EvalsToInTime.trans (step program)
        2 (2 * remaining + 1) _ afterInc _ throughInc rest
      simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full

/-- Finish a left field, preserving the complete original query count. -/
def leftEnd_run (remaining saved right : Nat) (equal : Bool)
    (input : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.leftEnd equal) buffer₁ buffer₂ test input []
        (List.replicate remaining ()) (List.replicate right ())
        (List.replicate saved ()))
      (some (cfg (.restoreLeft (equal && decide (remaining = 0)))
        buffer₁ buffer₂ false input [] []
        (List.replicate right ())
        (List.replicate (remaining + saved) ())))
      (2 * remaining + 1) := by
  cases remaining with
  | zero =>
      exact ⟨⟨1, by
        simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | succ remaining =>
      let afterDec := cfg .saveLeftRemainder buffer₁ buffer₂ true input []
        (List.replicate remaining ()) (List.replicate right ())
        (List.replicate saved ())
      let afterInc := cfg .drainLeft buffer₁ buffer₂ true input []
        (List.replicate remaining ()) (List.replicate right ())
        (List.replicate (saved + 1) ())
      have first : EvalsToInTime (step program)
          (cfg (.leftEnd equal) buffer₁ buffer₂ test input []
            (List.replicate (remaining + 1) ()) (List.replicate right ())
            (List.replicate saved ()))
          (some afterDec) 1 := by
        exact ⟨⟨1, by
          simp [flip, afterDec, step, program, cfg, stepOp,
            List.replicate_succ]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterDec
          (some afterInc) 1 := by
        exact ⟨⟨1, by
          simp [flip, afterDec, afterInc, step, program, cfg, stepOp,
            List.replicate_succ]⟩, le_rfl⟩
      have rest := drainLeft_run remaining (saved + 1) right input
        buffer₁ buffer₂ true
      have throughInc := EvalsToInTime.trans (step program)
        1 1 _ afterDec _ first second
      let full := EvalsToInTime.trans (step program)
        2 (2 * remaining + 1) _ afterInc _ throughInc rest
      simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full

/-- Finish a right field, preserving the complete original query count. -/
def rightEnd_run (left remaining saved : Nat) (equal : Bool)
    (input : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.rightEnd equal) buffer₁ buffer₂ test input []
        (List.replicate left ()) (List.replicate remaining ())
        (List.replicate saved ()))
      (some (cfg (.restoreRight (equal && decide (remaining = 0)))
        buffer₁ buffer₂ false input []
        (List.replicate left ()) []
        (List.replicate (remaining + saved) ())))
      (2 * remaining + 1) := by
  cases remaining with
  | zero =>
      exact ⟨⟨1, by
        simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | succ remaining =>
      let afterDec := cfg .saveRightRemainder buffer₁ buffer₂ true input []
        (List.replicate left ()) (List.replicate remaining ())
        (List.replicate saved ())
      let afterInc := cfg .drainRight buffer₁ buffer₂ true input []
        (List.replicate left ()) (List.replicate remaining ())
        (List.replicate (saved + 1) ())
      have first : EvalsToInTime (step program)
          (cfg (.rightEnd equal) buffer₁ buffer₂ test input []
            (List.replicate left ()) (List.replicate (remaining + 1) ())
            (List.replicate saved ()))
          (some afterDec) 1 := by
        exact ⟨⟨1, by
          simp [flip, afterDec, step, program, cfg, stepOp,
            List.replicate_succ]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterDec
          (some afterInc) 1 := by
        exact ⟨⟨1, by
          simp [flip, afterDec, afterInc, step, program, cfg, stepOp,
            List.replicate_succ]⟩, le_rfl⟩
      have rest := drainRight_run left remaining (saved + 1) input
        buffer₁ buffer₂ true
      have throughInc := EvalsToInTime.trans (step program)
        1 1 _ afterDec _ first second
      let full := EvalsToInTime.trans (step program)
        2 (2 * remaining + 1) _ afterInc _ throughInc rest
      simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.EdgeLookup

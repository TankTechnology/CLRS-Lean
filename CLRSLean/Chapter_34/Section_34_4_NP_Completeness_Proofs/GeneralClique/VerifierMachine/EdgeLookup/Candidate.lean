import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.EdgeLookup.Restore

/-!
# General CLIQUE verifier: canonical candidate-edge comparison

This file proves the two unary field comparisons used by the reusable edge
lookup controller.  The statements expose exact step counts and, crucially,
show that both query counters are restored before the next candidate begins.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.EdgeLookup

open PolyBuilder

/-- Exact cost of comparing a canonical left unary field. -/
def leftFieldSteps : Nat → Nat → Nat → Nat
  | remaining, saved, 0 =>
      1 + (2 * remaining + 1) + (2 * (remaining + saved) + 1)
  | 0, saved, candidate + 1 => leftFieldSteps 0 saved candidate + 2
  | remaining + 1, saved, candidate + 1 =>
      leftFieldSteps remaining (saved + 1) candidate + 3

/-- Exact cost of comparing a canonical right unary field. -/
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

private def leftField_run_aux (remaining saved right candidate : Nat)
    (equal : Bool) (rest : List CliqueSym)
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.left equal) buffer₁ buffer₂ test
        ((prependCliqueTicks candidate (.pairSep :: rest)).map some) []
        (List.replicate remaining ()) (List.replicate right ())
        (List.replicate saved ()))
      (some (cfg (.right (equal && decide (remaining = candidate)))
        (some (some .pairSep)) buffer₂ false (rest.map some) []
        (List.replicate (remaining + saved) ())
        (List.replicate right ()) []))
      (leftFieldSteps remaining saved candidate) := by
  induction candidate generalizing remaining saved equal buffer₁ test with
  | zero =>
      let afterPop := cfg (.leftEnd equal) (some (some .pairSep)) buffer₂
        test (rest.map some) [] (List.replicate remaining ())
        (List.replicate right ()) (List.replicate saved ())
      have first : EvalsToInTime (step program)
          (cfg (.left equal) buffer₁ buffer₂ test
            ((prependCliqueTicks 0 (.pairSep :: rest)).map some) []
            (List.replicate remaining ()) (List.replicate right ())
            (List.replicate saved ()))
          (some afterPop) 1 := by
        exact ⟨⟨1, by
          simp [flip, afterPop, prependCliqueTicks, step, program, cfg,
            stepOp]⟩, le_rfl⟩
      have finish := leftEnd_run remaining saved right equal (rest.map some)
        (some (some .pairSep)) buffer₂ test
      have restore := restoreLeft_run (remaining + saved) 0 right
        (equal && decide (remaining = 0)) (rest.map some)
        (some (some .pairSep)) buffer₂ false
      let throughEnd := EvalsToInTime.trans (step program)
        1 (2 * remaining + 1) _ afterPop _ first finish
      have throughEnd' : EvalsToInTime (step program)
          (cfg (.left equal) buffer₁ buffer₂ test
            ((prependCliqueTicks 0 (.pairSep :: rest)).map some) []
            (List.replicate remaining ()) (List.replicate right ())
            (List.replicate saved ()))
          (some (cfg
            (.restoreLeft (equal && decide (remaining = 0)))
            (some (some .pairSep)) buffer₂ false (rest.map some) [] []
            (List.replicate right ())
            (List.replicate (remaining + saved) ())))
          (1 + (2 * remaining + 1)) := by
        simpa [Nat.add_comm] using throughEnd
      have restore' : EvalsToInTime (step program)
          (cfg (.restoreLeft (equal && decide (remaining = 0)))
            (some (some .pairSep)) buffer₂ false (rest.map some) [] []
            (List.replicate right ())
            (List.replicate (remaining + saved) ()))
          (some (cfg (.right (equal && decide (remaining = 0)))
            (some (some .pairSep)) buffer₂ false (rest.map some) []
            (List.replicate (remaining + saved) ())
            (List.replicate right ()) []))
          (2 * (remaining + saved) + 1) := by
        simpa using restore
      let full := EvalsToInTime.trans (step program)
        (1 + (2 * remaining + 1)) (2 * (remaining + saved) + 1)
        _ _ _ throughEnd' restore'
      simpa [leftFieldSteps, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full
  | succ candidate ih =>
      let afterPop := cfg (.spendLeft equal) (some (some .tick)) buffer₂
        test ((prependCliqueTicks candidate (.pairSep :: rest)).map some) []
        (List.replicate remaining ()) (List.replicate right ())
        (List.replicate saved ())
      have first : EvalsToInTime (step program)
          (cfg (.left equal) buffer₁ buffer₂ test
            ((prependCliqueTicks (candidate + 1)
              (.pairSep :: rest)).map some) []
            (List.replicate remaining ()) (List.replicate right ())
            (List.replicate saved ()))
          (some afterPop) 1 := by
        exact ⟨⟨1, by
          simp [flip, afterPop, prependCliqueTicks, step, program, cfg,
            stepOp]⟩, le_rfl⟩
      cases remaining with
      | zero =>
          let afterSpend := cfg (.left false) (some (some .tick)) buffer₂
            false ((prependCliqueTicks candidate
              (.pairSep :: rest)).map some) [] []
            (List.replicate right ()) (List.replicate saved ())
          have second : EvalsToInTime (step program) afterPop
              (some afterSpend) 1 := by
            exact ⟨⟨1, by
              simp [flip, afterPop, afterSpend, step, program, cfg,
                stepOp]⟩, le_rfl⟩
          have restRun := ih 0 saved false (some (some .tick)) false
          let throughSpend := EvalsToInTime.trans (step program)
            1 1 _ afterPop _ first second
          let full := EvalsToInTime.trans (step program)
            2 (leftFieldSteps 0 saved candidate)
            _ afterSpend _ throughSpend restRun
          simpa [leftFieldSteps, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using full
      | succ remaining =>
          let afterSpend := cfg (.saveLeft equal) (some (some .tick))
            buffer₂ true ((prependCliqueTicks candidate
              (.pairSep :: rest)).map some) []
            (List.replicate remaining ()) (List.replicate right ())
            (List.replicate saved ())
          let afterSave := cfg (.left equal) (some (some .tick)) buffer₂
            true ((prependCliqueTicks candidate
              (.pairSep :: rest)).map some) []
            (List.replicate remaining ()) (List.replicate right ())
            (List.replicate (saved + 1) ())
          have second : EvalsToInTime (step program) afterPop
              (some afterSpend) 1 := by
            exact ⟨⟨1, by
              simp [flip, afterPop, afterSpend, step, program, cfg, stepOp,
                List.replicate_succ]⟩, le_rfl⟩
          have third : EvalsToInTime (step program) afterSpend
              (some afterSave) 1 := by
            exact ⟨⟨1, by
              simp [flip, afterSpend, afterSave, step, program, cfg,
                stepOp, List.replicate_succ]⟩, le_rfl⟩
          have restRun := ih remaining (saved + 1) equal
            (some (some .tick)) true
          let throughSpend := EvalsToInTime.trans (step program)
            1 1 _ afterPop _ first second
          let throughSave := EvalsToInTime.trans (step program)
            2 1 _ afterSpend _ throughSpend third
          let full := EvalsToInTime.trans (step program)
            3 (leftFieldSteps remaining (saved + 1) candidate)
            _ afterSave _ throughSave restRun
          simpa [leftFieldSteps, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using full

/-- A canonical left endpoint is compared exactly and the left query budget is
restored before control enters the right endpoint. -/
def leftField_run (queryLeft queryRight candidate : Nat) (equal : Bool)
    (rest : List CliqueSym)
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.left equal) buffer₁ buffer₂ test
        ((prependCliqueTicks candidate (.pairSep :: rest)).map some) []
        (List.replicate queryLeft ()) (List.replicate queryRight ()) [])
      (some (cfg (.right (equal && decide (candidate = queryLeft)))
        (some (some .pairSep)) buffer₂ false (rest.map some) []
        (List.replicate queryLeft ()) (List.replicate queryRight ()) []))
      (leftFieldSteps queryLeft 0 candidate) := by
  have run := leftField_run_aux queryLeft 0 queryRight candidate equal rest
    buffer₁ buffer₂ test
  rw [decide_nat_eq_comm queryLeft candidate] at run
  simpa using run

private def rightField_run_aux (left remaining saved candidate : Nat)
    (equal : Bool) (rest : List CliqueSym)
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.right equal) buffer₁ buffer₂ test
        ((prependCliqueTicks candidate (.recordEnd :: rest)).map some) []
        (List.replicate left ()) (List.replicate remaining ())
        (List.replicate saved ()))
      (some (cfg
        (if equal && decide (remaining = candidate) then .clearInput true
          else .edges)
        (some (some .recordEnd)) buffer₂ false (rest.map some) []
        (List.replicate left ())
        (List.replicate (remaining + saved) ()) []))
      (rightFieldSteps remaining saved candidate) := by
  induction candidate generalizing remaining saved equal buffer₁ test with
  | zero =>
      let afterPop := cfg (.rightEnd equal) (some (some .recordEnd)) buffer₂
        test (rest.map some) [] (List.replicate left ())
        (List.replicate remaining ()) (List.replicate saved ())
      have first : EvalsToInTime (step program)
          (cfg (.right equal) buffer₁ buffer₂ test
            ((prependCliqueTicks 0 (.recordEnd :: rest)).map some) []
            (List.replicate left ()) (List.replicate remaining ())
            (List.replicate saved ()))
          (some afterPop) 1 := by
        exact ⟨⟨1, by
          simp [flip, afterPop, prependCliqueTicks, step, program, cfg,
            stepOp]⟩, le_rfl⟩
      have finish := rightEnd_run left remaining saved equal (rest.map some)
        (some (some .recordEnd)) buffer₂ test
      have restore := restoreRight_run left (remaining + saved) 0
        (equal && decide (remaining = 0)) (rest.map some)
        (some (some .recordEnd)) buffer₂ false
      let throughEnd := EvalsToInTime.trans (step program)
        1 (2 * remaining + 1) _ afterPop _ first finish
      have throughEnd' : EvalsToInTime (step program)
          (cfg (.right equal) buffer₁ buffer₂ test
            ((prependCliqueTicks 0 (.recordEnd :: rest)).map some) []
            (List.replicate left ()) (List.replicate remaining ())
            (List.replicate saved ()))
          (some (cfg
            (.restoreRight (equal && decide (remaining = 0)))
            (some (some .recordEnd)) buffer₂ false (rest.map some) []
            (List.replicate left ()) []
            (List.replicate (remaining + saved) ())))
          (1 + (2 * remaining + 1)) := by
        simpa [Nat.add_comm] using throughEnd
      have restore' : EvalsToInTime (step program)
          (cfg (.restoreRight (equal && decide (remaining = 0)))
            (some (some .recordEnd)) buffer₂ false (rest.map some) []
            (List.replicate left ()) []
            (List.replicate (remaining + saved) ()))
          (some (cfg
            (if equal && decide (remaining = 0) then .clearInput true
              else .edges)
            (some (some .recordEnd)) buffer₂ false (rest.map some) []
            (List.replicate left ())
            (List.replicate (remaining + saved) ()) []))
          (2 * (remaining + saved) + 1) := by
        simpa using restore
      let full := EvalsToInTime.trans (step program)
        (1 + (2 * remaining + 1)) (2 * (remaining + saved) + 1)
        _ _ _ throughEnd' restore'
      simpa [rightFieldSteps, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full
  | succ candidate ih =>
      let afterPop := cfg (.spendRight equal) (some (some .tick)) buffer₂
        test ((prependCliqueTicks candidate (.recordEnd :: rest)).map some) []
        (List.replicate left ()) (List.replicate remaining ())
        (List.replicate saved ())
      have first : EvalsToInTime (step program)
          (cfg (.right equal) buffer₁ buffer₂ test
            ((prependCliqueTicks (candidate + 1)
              (.recordEnd :: rest)).map some) []
            (List.replicate left ()) (List.replicate remaining ())
            (List.replicate saved ()))
          (some afterPop) 1 := by
        exact ⟨⟨1, by
          simp [flip, afterPop, prependCliqueTicks, step, program, cfg,
            stepOp]⟩, le_rfl⟩
      cases remaining with
      | zero =>
          let afterSpend := cfg (.right false) (some (some .tick)) buffer₂
            false ((prependCliqueTicks candidate
              (.recordEnd :: rest)).map some) []
            (List.replicate left ()) [] (List.replicate saved ())
          have second : EvalsToInTime (step program) afterPop
              (some afterSpend) 1 := by
            exact ⟨⟨1, by
              simp [flip, afterPop, afterSpend, step, program, cfg,
                stepOp]⟩, le_rfl⟩
          have restRun := ih 0 saved false (some (some .tick)) false
          let throughSpend := EvalsToInTime.trans (step program)
            1 1 _ afterPop _ first second
          let full := EvalsToInTime.trans (step program)
            2 (rightFieldSteps 0 saved candidate)
            _ afterSpend _ throughSpend restRun
          simpa [rightFieldSteps, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using full
      | succ remaining =>
          let afterSpend := cfg (.saveRight equal) (some (some .tick))
            buffer₂ true ((prependCliqueTicks candidate
              (.recordEnd :: rest)).map some) []
            (List.replicate left ()) (List.replicate remaining ())
            (List.replicate saved ())
          let afterSave := cfg (.right equal) (some (some .tick)) buffer₂
            true ((prependCliqueTicks candidate
              (.recordEnd :: rest)).map some) []
            (List.replicate left ()) (List.replicate remaining ())
            (List.replicate (saved + 1) ())
          have second : EvalsToInTime (step program) afterPop
              (some afterSpend) 1 := by
            exact ⟨⟨1, by
              simp [flip, afterPop, afterSpend, step, program, cfg, stepOp,
                List.replicate_succ]⟩, le_rfl⟩
          have third : EvalsToInTime (step program) afterSpend
              (some afterSave) 1 := by
            exact ⟨⟨1, by
              simp [flip, afterSpend, afterSave, step, program, cfg,
                stepOp, List.replicate_succ]⟩, le_rfl⟩
          have restRun := ih remaining (saved + 1) equal
            (some (some .tick)) true
          let throughSpend := EvalsToInTime.trans (step program)
            1 1 _ afterPop _ first second
          let throughSave := EvalsToInTime.trans (step program)
            2 1 _ afterSpend _ throughSpend third
          let full := EvalsToInTime.trans (step program)
            3 (rightFieldSteps remaining (saved + 1) candidate)
            _ afterSave _ throughSave restRun
          simpa [rightFieldSteps, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using full

/-- A canonical right endpoint is compared exactly and the right query budget
is restored before a miss returns to the edge scanner. -/
def rightField_run (queryLeft queryRight candidate : Nat) (equal : Bool)
    (rest : List CliqueSym)
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.right equal) buffer₁ buffer₂ test
        ((prependCliqueTicks candidate (.recordEnd :: rest)).map some) []
        (List.replicate queryLeft ()) (List.replicate queryRight ()) [])
      (some (cfg
        (if equal && decide (candidate = queryRight) then .clearInput true
          else .edges)
        (some (some .recordEnd)) buffer₂ false (rest.map some) []
        (List.replicate queryLeft ()) (List.replicate queryRight ()) []))
      (rightFieldSteps queryRight 0 candidate) := by
  have run := rightField_run_aux queryLeft queryRight 0 candidate equal rest
    buffer₁ buffer₂ test
  rw [decide_nat_eq_comm queryRight candidate] at run
  simpa using run

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.EdgeLookup

import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.BatchEdgeLookup.CandidateLeft

/-!
# Batch edge lookup: right candidate field
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.BatchEdgeLookup

open PolyBuilder

private theorem decide_nat_eq_comm (a b : Nat) :
    decide (a = b) = decide (b = a) := by
  by_cases h : a = b
  · subst b
    rfl
  · have h' : b ≠ a := fun hba => h hba.symm
    simp [h, h']

private def rightField_run_aux (aggregate : Bool)
    (left remaining saved candidate : Nat) (equal : Bool)
    (rest : List CliqueSym) (output : List Bool)
    (work₁ work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.right aggregate equal) buffer₁ buffer₂ test
        ((prependCliqueTicks candidate (.recordEnd :: rest)).map some) output
        work₁ work₂ (List.replicate left ()) (List.replicate remaining ())
        (List.replicate saved ()))
      (some (cfg
        (if equal && decide (remaining = candidate) then
          .drainGraph aggregate else .edges aggregate)
        buffer₁ (some (some .recordEnd)) false (rest.map some) output work₁
        (((prependCliqueTicks candidate [.recordEnd]).map some).reverse ++
          work₂)
        (List.replicate left ()) (List.replicate (remaining + saved) ()) []))
      (EdgeLookup.rightFieldSteps remaining saved candidate) := by
  induction candidate generalizing remaining saved equal buffer₂ test work₂ with
  | zero =>
      let afterPop := cfg (.rightEnd aggregate equal) buffer₁
        (some (some .recordEnd)) test (rest.map some) output work₁
        (some CliqueSym.recordEnd :: work₂) (List.replicate left ())
        (List.replicate remaining ()) (List.replicate saved ())
      have first : EvalsToInTime (step program)
          (cfg (.right aggregate equal) buffer₁ buffer₂ test
            ((prependCliqueTicks 0 (.recordEnd :: rest)).map some) output
            work₁ work₂ (List.replicate left ())
            (List.replicate remaining ()) (List.replicate saved ()))
          (some afterPop) 1 :=
        ⟨⟨1, by simp [flip, afterPop, prependCliqueTicks, step, program,
          cfg, stepOp]⟩, le_rfl⟩
      have finish := rightEnd_run aggregate left remaining saved equal
        (rest.map some) output work₁ (some CliqueSym.recordEnd :: work₂)
        buffer₁ (some (some .recordEnd)) test
      have restore := restoreRight_run aggregate left (remaining + saved) 0
        (equal && decide (remaining = 0)) (rest.map some) output work₁
        (some CliqueSym.recordEnd :: work₂) buffer₁
        (some (some .recordEnd)) false
      let throughEnd := EvalsToInTime.trans (step program)
        1 (2 * remaining + 1) _ afterPop _ first finish
      have throughEnd' : EvalsToInTime (step program)
          (cfg (.right aggregate equal) buffer₁ buffer₂ test
            ((prependCliqueTicks 0 (.recordEnd :: rest)).map some) output
            work₁ work₂ (List.replicate left ())
            (List.replicate remaining ()) (List.replicate saved ()))
          (some (cfg
            (.restoreRight aggregate (equal && decide (remaining = 0)))
            buffer₁ (some (some .recordEnd)) false (rest.map some) output
            work₁ (some CliqueSym.recordEnd :: work₂)
            (List.replicate left ()) []
            (List.replicate (remaining + saved) ())))
          (1 + (2 * remaining + 1)) := by
        simpa [Nat.add_comm] using throughEnd
      let full := EvalsToInTime.trans (step program)
        (1 + (2 * remaining + 1)) (2 * (remaining + saved) + 1)
        _ _ _ throughEnd' restore
      simpa [EdgeLookup.rightFieldSteps, prependCliqueTicks,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full
  | succ candidate ih =>
      let remainingInput :=
        (prependCliqueTicks candidate (.recordEnd :: rest)).map some
      let afterPop := cfg (.spendRight aggregate equal) buffer₁
        (some (some .tick)) test remainingInput output work₁
        (some CliqueSym.tick :: work₂) (List.replicate left ())
        (List.replicate remaining ()) (List.replicate saved ())
      have first : EvalsToInTime (step program)
          (cfg (.right aggregate equal) buffer₁ buffer₂ test
            ((prependCliqueTicks (candidate + 1)
              (.recordEnd :: rest)).map some) output work₁ work₂
            (List.replicate left ()) (List.replicate remaining ())
            (List.replicate saved ()))
          (some afterPop) 1 :=
        ⟨⟨1, by simp [flip, afterPop, remainingInput, prependCliqueTicks,
          step, program, cfg, stepOp]⟩, le_rfl⟩
      cases remaining with
      | zero =>
          let afterSpend := cfg (.right aggregate false) buffer₁
            (some (some .tick)) false remainingInput output work₁
            (some CliqueSym.tick :: work₂) (List.replicate left ()) []
            (List.replicate saved ())
          have second : EvalsToInTime (step program) afterPop
              (some afterSpend) 1 :=
            ⟨⟨1, by simp [flip, afterPop, afterSpend, step, program, cfg,
              stepOp]⟩, le_rfl⟩
          have restRun := ih (remaining := 0) (saved := saved)
            (equal := false) (buffer₂ := some (some CliqueSym.tick))
            (test := false) (work₂ := some CliqueSym.tick :: work₂)
          let throughSpend := EvalsToInTime.trans (step program)
            1 1 _ afterPop _ first second
          let full := EvalsToInTime.trans (step program)
            2 (EdgeLookup.rightFieldSteps 0 saved candidate)
            _ afterSpend _ throughSpend (by
              simpa [remainingInput] using restRun)
          simpa [EdgeLookup.rightFieldSteps, prependCliqueTicks,
            List.reverse_cons, List.append_assoc, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using full
      | succ remaining =>
          let afterSpend := cfg (.saveRight aggregate equal) buffer₁
            (some (some .tick)) true remainingInput output work₁
            (some CliqueSym.tick :: work₂) (List.replicate left ())
            (List.replicate remaining ()) (List.replicate saved ())
          let afterSave := cfg (.right aggregate equal) buffer₁
            (some (some .tick)) true remainingInput output work₁
            (some CliqueSym.tick :: work₂) (List.replicate left ())
            (List.replicate remaining ()) (List.replicate (saved + 1) ())
          have second : EvalsToInTime (step program) afterPop
              (some afterSpend) 1 :=
            ⟨⟨1, by simp [flip, afterPop, afterSpend, step, program, cfg,
              stepOp, List.replicate_succ]⟩, le_rfl⟩
          have third : EvalsToInTime (step program) afterSpend
              (some afterSave) 1 :=
            ⟨⟨1, by simp [flip, afterSpend, afterSave, step, program, cfg,
              stepOp, List.replicate_succ]⟩, le_rfl⟩
          have restRun := ih (remaining := remaining) (saved := saved + 1)
            (equal := equal) (buffer₂ := some (some CliqueSym.tick))
            (test := true) (work₂ := some CliqueSym.tick :: work₂)
          let throughSpend := EvalsToInTime.trans (step program)
            1 1 _ afterPop _ first second
          let throughSave := EvalsToInTime.trans (step program)
            2 1 _ afterSpend _ throughSpend third
          let full := EvalsToInTime.trans (step program)
            3 (EdgeLookup.rightFieldSteps remaining (saved + 1) candidate)
            _ afterSave _ throughSave (by
              simpa [remainingInput] using restRun)
          simpa [EdgeLookup.rightFieldSteps, prependCliqueTicks,
            List.reverse_cons, List.append_assoc, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using full

/-- Compare a canonical right endpoint, preserve its graph symbols on work
two, and restore the complete query budget. -/
def rightField_run (aggregate : Bool)
    (queryLeft queryRight candidate : Nat) (equal : Bool)
    (rest : List CliqueSym) (output : List Bool)
    (work₁ work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.right aggregate equal) buffer₁ buffer₂ test
        ((prependCliqueTicks candidate (.recordEnd :: rest)).map some) output
        work₁ work₂ (List.replicate queryLeft ())
        (List.replicate queryRight ()) [])
      (some (cfg
        (if equal && decide (candidate = queryRight) then
          .drainGraph aggregate else .edges aggregate)
        buffer₁ (some (some .recordEnd)) false (rest.map some) output work₁
        (((prependCliqueTicks candidate [.recordEnd]).map some).reverse ++
          work₂)
        (List.replicate queryLeft ()) (List.replicate queryRight ()) []))
      (EdgeLookup.rightFieldSteps queryRight 0 candidate) := by
  have run := rightField_run_aux aggregate queryLeft queryRight 0 candidate
    equal rest output work₁ work₂ buffer₁ buffer₂ test
  rw [decide_nat_eq_comm queryRight candidate] at run
  simpa using run

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.BatchEdgeLookup

import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.BatchEdgeLookup.Basic
import Mathlib.Tactic

/-!
# Batch edge lookup: restoration and cleanup
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.BatchEdgeLookup

open PolyBuilder

/-- Drain the unread graph suffix onto work two. -/
def drainGraph_run (aggregate : Bool)
    (input : List (Option CliqueSym)) (output : List Bool)
    (work₁ work₂ : List (Option CliqueSym)) (left right scratch : Nat)
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.drainGraph aggregate) buffer₁ buffer₂ test input output
        work₁ work₂ (List.replicate left ()) (List.replicate right ())
        (List.replicate scratch ()))
      (some (cfg (.clearLeft aggregate true) buffer₁ none test [] output
        work₁ (input.reverse ++ work₂) (List.replicate left ())
        (List.replicate right ()) (List.replicate scratch ())))
      (input.length + 1) := by
  induction input generalizing buffer₂ work₂ with
  | nil =>
      exact ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | cons symbol input ih =>
      let after := cfg (.drainGraph aggregate) buffer₁ (some symbol) test
        input output work₁ (symbol :: work₂) (List.replicate left ())
        (List.replicate right ()) (List.replicate scratch ())
      have first : EvalsToInTime (step program)
          (cfg (.drainGraph aggregate) buffer₁ buffer₂ test
            (symbol :: input) output work₁ work₂ (List.replicate left ())
            (List.replicate right ()) (List.replicate scratch ()))
          (some after) 1 :=
        ⟨⟨1, by simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := ih (buffer₂ := some symbol) (work₂ := symbol :: work₂)
      let full := EvalsToInTime.trans (step program)
        1 (input.length + 1) _ after _ first rest
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using full

/-- Clear scratch after both endpoint counters have been cleared. -/
def clearScratch_run (aggregate answer : Bool) (scratch : Nat)
    (input : List (Option CliqueSym)) (output : List Bool)
    (work₁ work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.clearScratch aggregate answer) buffer₁ buffer₂ test input output
        work₁ work₂ [] [] (List.replicate scratch ()))
      (some (cfg (.restoreGraph aggregate answer) buffer₁ buffer₂ false input
        output work₁ work₂ [] [] []))
      (scratch + 1) := by
  induction scratch generalizing test with
  | zero =>
      exact ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | succ scratch ih =>
      have first : EvalsToInTime (step program)
          (cfg (.clearScratch aggregate answer) buffer₁ buffer₂ test input
            output work₁ work₂ [] [] (List.replicate (scratch + 1) ()))
          (some (cfg (.clearScratch aggregate answer) buffer₁ buffer₂ true
            input output work₁ work₂ [] [] (List.replicate scratch ()))) 1 :=
        ⟨⟨1, by simp [flip, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (test := true)
      let full := EvalsToInTime.trans (step program)
        1 (scratch + 1) _ _ _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

/-- Clear the right endpoint counter and then scratch. -/
def clearRight_run (aggregate answer : Bool) (right scratch : Nat)
    (input : List (Option CliqueSym)) (output : List Bool)
    (work₁ work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.clearRight aggregate answer) buffer₁ buffer₂ test input output
        work₁ work₂ [] (List.replicate right ())
        (List.replicate scratch ()))
      (some (cfg (.restoreGraph aggregate answer) buffer₁ buffer₂ false input
        output work₁ work₂ [] [] []))
      (right + scratch + 2) := by
  induction right generalizing test with
  | zero =>
      have run := clearScratch_run aggregate answer scratch input output
        work₁ work₂ buffer₁ buffer₂ false
      let first : EvalsToInTime (step program)
          (cfg (.clearRight aggregate answer) buffer₁ buffer₂ test input
            output work₁ work₂ [] [] (List.replicate scratch ()))
          (some (cfg (.clearScratch aggregate answer) buffer₁ buffer₂ false
            input output work₁ work₂ [] [] (List.replicate scratch ()))) 1 :=
        ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
      let full := EvalsToInTime.trans (step program)
        1 (scratch + 1) _ _ _ first run
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full
  | succ right ih =>
      have first : EvalsToInTime (step program)
          (cfg (.clearRight aggregate answer) buffer₁ buffer₂ test input
            output work₁ work₂ [] (List.replicate (right + 1) ())
            (List.replicate scratch ()))
          (some (cfg (.clearRight aggregate answer) buffer₁ buffer₂ true input
            output work₁ work₂ [] (List.replicate right ())
            (List.replicate scratch ()))) 1 :=
        ⟨⟨1, by simp [flip, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (test := true)
      let full := EvalsToInTime.trans (step program)
        1 (right + scratch + 2) _ _ _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

/-- Clear every query counter before restoring the graph. -/
def clearQuery_run (aggregate answer : Bool) (left right scratch : Nat)
    (input : List (Option CliqueSym)) (output : List Bool)
    (work₁ work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.clearLeft aggregate answer) buffer₁ buffer₂ test input output
        work₁ work₂ (List.replicate left ()) (List.replicate right ())
        (List.replicate scratch ()))
      (some (cfg (.restoreGraph aggregate answer) buffer₁ buffer₂ false input
        output work₁ work₂ [] [] []))
      (left + right + scratch + 3) := by
  induction left generalizing test with
  | zero =>
      have run := clearRight_run aggregate answer right scratch input output
        work₁ work₂ buffer₁ buffer₂ false
      let first : EvalsToInTime (step program)
          (cfg (.clearLeft aggregate answer) buffer₁ buffer₂ test input output
            work₁ work₂ [] (List.replicate right ())
            (List.replicate scratch ()))
          (some (cfg (.clearRight aggregate answer) buffer₁ buffer₂ false input
            output work₁ work₂ [] (List.replicate right ())
            (List.replicate scratch ()))) 1 :=
        ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
      let full := EvalsToInTime.trans (step program)
        1 (right + scratch + 2) _ _ _ first run
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full
  | succ left ih =>
      have first : EvalsToInTime (step program)
          (cfg (.clearLeft aggregate answer) buffer₁ buffer₂ test input output
            work₁ work₂ (List.replicate (left + 1) ())
            (List.replicate right ()) (List.replicate scratch ()))
          (some (cfg (.clearLeft aggregate answer) buffer₁ buffer₂ true input
            output work₁ work₂ (List.replicate left ())
            (List.replicate right ()) (List.replicate scratch ()))) 1 :=
        ⟨⟨1, by simp [flip, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (test := true)
      let full := EvalsToInTime.trans (step program)
        1 (left + right + scratch + 3) _ _ _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

/-- Restore the graph from work two to the input stack. -/
def restoreGraph_run (aggregate answer : Bool)
    (input work₁ work₂ : List (Option CliqueSym)) (output : List Bool)
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.restoreGraph aggregate answer) buffer₁ buffer₂ test input output
        work₁ work₂ [] [] [])
      (some (cfg (.nextQuery (aggregate && answer)) buffer₁ none test
        (work₂.reverse ++ input) output work₁ [] [] [] []))
      (work₂.length + 1) := by
  induction work₂ generalizing input buffer₂ with
  | nil =>
      exact ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | cons symbol work₂ ih =>
      let after := cfg (.restoreGraph aggregate answer) buffer₁ (some symbol)
        test (symbol :: input) output work₁ work₂ [] [] []
      have first : EvalsToInTime (step program)
          (cfg (.restoreGraph aggregate answer) buffer₁ buffer₂ test input
            output work₁ (symbol :: work₂) [] [] [])
          (some after) 1 :=
        ⟨⟨1, by simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := ih (input := symbol :: input) (buffer₂ := some symbol)
      let full := EvalsToInTime.trans (step program)
        1 (work₂.length + 1) _ after _ first rest
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using full

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.BatchEdgeLookup

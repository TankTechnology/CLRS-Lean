import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.Incidence.Scanner.Edges

/-!
# HAM-CYCLE incidence scanner: counter cleanup and graph restoration
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Scanner

open PolyBuilder

/-- Clear scratch after the query and occurrence counters are empty. -/
def clearScratch_run (scratch : Nat) (input : List (Option CliqueSym))
    (output : List UnaryFrameSym) (work₁ work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .clearScratch buffer₁ buffer₂ test input output work₁ work₂
        [] [] (List.replicate scratch ()))
      (some (cfg .restoreGraph buffer₁ buffer₂ false input output work₁ work₂
        [] [] []))
      (scratch + 1) := by
  induction scratch generalizing test with
  | zero =>
      exact ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | succ scratch ih =>
      have first : EvalsToInTime (step program)
          (cfg .clearScratch buffer₁ buffer₂ test input output work₁ work₂
            [] [] (List.replicate (scratch + 1) ()))
          (some (cfg .clearScratch buffer₁ buffer₂ true input output work₁ work₂
            [] [] (List.replicate scratch ()))) 1 :=
        ⟨⟨1, by simp [flip, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (test := true)
      let full := EvalsToInTime.trans (step program)
        1 (scratch + 1) _ _ _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

/-- Clear the occurrence counter and then scratch. -/
def clearOccurrence_run (occurrence scratch : Nat)
    (input : List (Option CliqueSym)) (output : List UnaryFrameSym)
    (work₁ work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .clearOccurrence buffer₁ buffer₂ test input output work₁ work₂
        [] (List.replicate occurrence ()) (List.replicate scratch ()))
      (some (cfg .restoreGraph buffer₁ buffer₂ false input output work₁ work₂
        [] [] []))
      (occurrence + scratch + 2) := by
  induction occurrence generalizing test with
  | zero =>
      have run := clearScratch_run scratch input output work₁ work₂
        buffer₁ buffer₂ false
      have first : EvalsToInTime (step program)
          (cfg .clearOccurrence buffer₁ buffer₂ test input output work₁ work₂
            [] [] (List.replicate scratch ()))
          (some (cfg .clearScratch buffer₁ buffer₂ false input output work₁ work₂
            [] [] (List.replicate scratch ()))) 1 :=
        ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
      let full := EvalsToInTime.trans (step program)
        1 (scratch + 1) _ _ _ first run
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full
  | succ occurrence ih =>
      have first : EvalsToInTime (step program)
          (cfg .clearOccurrence buffer₁ buffer₂ test input output work₁ work₂
            [] (List.replicate (occurrence + 1) ())
            (List.replicate scratch ()))
          (some (cfg .clearOccurrence buffer₁ buffer₂ true input output work₁ work₂
            [] (List.replicate occurrence ())
            (List.replicate scratch ()))) 1 :=
        ⟨⟨1, by simp [flip, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (test := true)
      let full := EvalsToInTime.trans (step program)
        1 (occurrence + scratch + 2) _ _ _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

/-- Clear all counters belonging to the completed query. -/
def clearQuery_run (query occurrence scratch : Nat)
    (input : List (Option CliqueSym)) (output : List UnaryFrameSym)
    (work₁ work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .clearQuery buffer₁ buffer₂ test input output work₁ work₂
        (List.replicate query ()) (List.replicate occurrence ())
        (List.replicate scratch ()))
      (some (cfg .restoreGraph buffer₁ buffer₂ false input output work₁ work₂
        [] [] []))
      (query + occurrence + scratch + 3) := by
  induction query generalizing test with
  | zero =>
      have run := clearOccurrence_run occurrence scratch input output work₁ work₂
        buffer₁ buffer₂ false
      have first : EvalsToInTime (step program)
          (cfg .clearQuery buffer₁ buffer₂ test input output work₁ work₂
            [] (List.replicate occurrence ()) (List.replicate scratch ()))
          (some (cfg .clearOccurrence buffer₁ buffer₂ false input output work₁ work₂
            [] (List.replicate occurrence ())
            (List.replicate scratch ()))) 1 :=
        ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
      let full := EvalsToInTime.trans (step program)
        1 (occurrence + scratch + 2) _ _ _ first run
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full
  | succ query ih =>
      have first : EvalsToInTime (step program)
          (cfg .clearQuery buffer₁ buffer₂ test input output work₁ work₂
            (List.replicate (query + 1) ()) (List.replicate occurrence ())
            (List.replicate scratch ()))
          (some (cfg .clearQuery buffer₁ buffer₂ true input output work₁ work₂
            (List.replicate query ()) (List.replicate occurrence ())
            (List.replicate scratch ()))) 1 :=
        ⟨⟨1, by simp [flip, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (test := true)
      let full := EvalsToInTime.trans (step program)
        1 (query + occurrence + scratch + 3) _ _ _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

/-- Restore the graph from work two and emit the completed row boundary. -/
def restoreRow_run (input : List (Option CliqueSym))
    (output : List UnaryFrameSym) (work₁ work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .restoreGraph buffer₁ buffer₂ test input output work₁ work₂ [] [] [])
      (some (cfg .nextQuery buffer₁ none test (work₂.reverse ++ input)
        (UnaryFrameSym.frameEnd :: output) work₁ [] [] [] []))
      (work₂.length + 2) := by
  induction work₂ generalizing input buffer₂ with
  | nil =>
      exact ⟨⟨2, by
        simp [Function.iterate_succ_apply, flip, step, program, cfg,
          stepOp]⟩, le_rfl⟩
  | cons symbol work₂ ih =>
      let after := cfg .restoreGraph buffer₁ (some symbol) test
        (symbol :: input) output work₁ work₂ [] [] []
      have first : EvalsToInTime (step program)
          (cfg .restoreGraph buffer₁ buffer₂ test input output work₁
            (symbol :: work₂) [] [] [])
          (some after) 1 :=
        ⟨⟨1, by simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := ih (input := symbol :: input) (buffer₂ := some symbol)
      let full := EvalsToInTime.trans (step program)
        1 (work₂.length + 2) _ after _ first rest
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using full

/-- Complete one scanned row: jump to cleanup, clear its counters, restore the
canonical graph, and prepend one row boundary. -/
def finishQuery_run (query occurrence scratch : Nat)
    (input : List (Option CliqueSym)) (output : List UnaryFrameSym)
    (work₁ work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .finishQuery buffer₁ buffer₂ test input output work₁ work₂
        (List.replicate query ()) (List.replicate occurrence ())
        (List.replicate scratch ()))
      (some (cfg .nextQuery buffer₁ none false (work₂.reverse ++ input)
        (UnaryFrameSym.frameEnd :: output) work₁ [] [] [] []))
      (query + occurrence + scratch + work₂.length + 6) := by
  have first : EvalsToInTime (step program)
      (cfg .finishQuery buffer₁ buffer₂ test input output work₁ work₂
        (List.replicate query ()) (List.replicate occurrence ())
        (List.replicate scratch ()))
      (some (cfg .clearQuery buffer₁ buffer₂ test input output work₁ work₂
        (List.replicate query ()) (List.replicate occurrence ())
        (List.replicate scratch ()))) 1 :=
    ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  have cleared := clearQuery_run query occurrence scratch input output work₁ work₂
    buffer₁ buffer₂ test
  have restored := restoreRow_run input output work₁ work₂ buffer₁ buffer₂ false
  let throughClear := EvalsToInTime.trans (step program)
    1 (query + occurrence + scratch + 3) _ _ _ first cleared
  let full := EvalsToInTime.trans (step program)
    _ (work₂.length + 2) _ _ _ throughClear restored
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Scanner

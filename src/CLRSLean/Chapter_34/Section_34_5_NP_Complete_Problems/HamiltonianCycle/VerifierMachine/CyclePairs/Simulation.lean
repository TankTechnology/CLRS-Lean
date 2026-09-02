import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.VerifierMachine.CyclePairs.Basic
import Mathlib.Tactic

/-!
# HAM-CYCLE consecutive-pair generator simulation

Local simulations for loading certificate values and serializing ordinary and
closing query records.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.HamiltonianCycle.VerifierMachine.CyclePairs

open PolyBuilder

private theorem prependCliqueTicks_eq_replicate (count : Nat)
    (tail : List CliqueSym) :
    prependCliqueTicks count tail = List.replicate count .tick ++ tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [prependCliqueTicks, List.replicate_succ, ih]

private theorem replicate_append_cons {α : Type} (value : α)
    (count : Nat) (tail : List α) :
    List.replicate count value ++ value :: tail =
      value :: (List.replicate count value ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons value) ih

/-- Test bit after loading a unary field: the empty field preserves the
incoming bit, while a nonempty field ends after successful increments. -/
def loadTest : Nat → Bool → Bool
  | _, test => test

/-- Load the first certificate value into both the persistent first counter
and the mutable previous counter. -/
def loadFirstRun (value : Nat) (tail output : List CliqueSym)
    (buffer : Option CliqueSym) (test : Bool)
    (firstLoaded previousLoaded : List Unit := []) :
    EvalsToInTime (step revProgram)
      (cfg .loadFirst buffer test
        (prependCliqueTicks value (.recordEnd :: tail)) output
        firstLoaded previousLoaded [])
      (some (cfg .nextRecord (some .recordEnd) (loadTest value test) tail
        output (List.replicate value () ++ firstLoaded)
        (List.replicate value () ++ previousLoaded) []))
      (3 * value + 1) := by
  induction value generalizing buffer test firstLoaded previousLoaded with
  | zero =>
      exact ⟨⟨1, by simp [prependCliqueTicks, flip, step, revProgram,
        cfg, stepOp, loadTest]⟩, le_rfl⟩
  | succ value ih =>
      have first : EvalsToInTime (step revProgram)
          (cfg .loadFirst buffer test
            (prependCliqueTicks (value + 1) (.recordEnd :: tail))
            output firstLoaded previousLoaded [])
          (some (cfg .loadFirst (some .tick) test
            (prependCliqueTicks value (.recordEnd :: tail))
            output (() :: firstLoaded) (() :: previousLoaded) [])) 3 := by
        exact ⟨⟨3, by simp [prependCliqueTicks, Function.iterate_succ_apply,
          flip, step, revProgram, cfg, stepOp]⟩, le_rfl⟩
      have rest := ih (some CliqueSym.tick) test (() :: firstLoaded)
        (() :: previousLoaded)
      let full := EvalsToInTime.trans (step revProgram)
        3 (3 * value + 1) _ _ _ first rest
      convert full using 1
      · simp [loadTest, List.replicate_succ, replicate_append_cons]
      · omega

/-- Load one later certificate value into the current counter. -/
def loadCurrentRun (value : Nat) (tail output : List CliqueSym)
    (first previous : List Unit) (buffer : Option CliqueSym)
    (test : Bool) (currentLoaded : List Unit := []) :
    EvalsToInTime (step revProgram)
      (cfg .loadCurrent buffer test
        (prependCliqueTicks value (.recordEnd :: tail))
        output first previous currentLoaded)
      (some (cfg .pushEdgeMark (some .recordEnd) (loadTest value test) tail
        output first previous (List.replicate value () ++ currentLoaded)))
      (2 * value + 1) := by
  induction value generalizing buffer test currentLoaded with
  | zero =>
      exact ⟨⟨1, by simp [prependCliqueTicks, flip, step, revProgram,
        cfg, stepOp, loadTest]⟩, le_rfl⟩
  | succ value ih =>
      have firstStep : EvalsToInTime (step revProgram)
          (cfg .loadCurrent buffer test
            (prependCliqueTicks (value + 1) (.recordEnd :: tail))
            output first previous currentLoaded)
          (some (cfg .loadCurrent (some .tick) test
            (prependCliqueTicks value (.recordEnd :: tail))
            output first previous (() :: currentLoaded))) 2 :=
        ⟨⟨2, by simp [prependCliqueTicks, Function.iterate_succ_apply,
          flip, step, revProgram, cfg, stepOp]⟩, le_rfl⟩
      have rest := ih (some CliqueSym.tick) test (() :: currentLoaded)
      let full := EvalsToInTime.trans (step revProgram)
        2 (2 * value + 1) _ _ _ firstStep rest
      convert full using 1
      · simp [loadTest, List.replicate_succ, replicate_append_cons]
      · omega

private theorem previous_eval (value : Nat) (buffer : Option CliqueSym)
    (test : Bool) (input output : List CliqueSym)
    (first current : List Unit) :
    (flip Option.bind (step revProgram))^[2 * value + 1]
      (some (cfg .previous buffer test input output first
        (List.replicate value ()) current)) =
      some (cfg .pushPairSeparator buffer false input
        (List.replicate value .tick ++ output) first [] current) := by
  induction value generalizing test output with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change (flip Option.bind (step revProgram))^[2 * value + 1]
        (some (cfg .previous buffer true input (.tick :: output) first
          (List.replicate value ()) current)) = _
      simpa only [List.replicate_succ, List.cons_append,
        replicate_append_cons] using ih true (.tick :: output)

private theorem current_eval (value : Nat) (buffer : Option CliqueSym)
    (test : Bool) (input output : List CliqueSym)
    (first restored : List Unit) :
    (flip Option.bind (step revProgram))^[3 * value + 1]
      (some (cfg .current buffer test input output first restored
        (List.replicate value ()))) =
      some (cfg .pushRecordEnd buffer false input
        (List.replicate value .tick ++ output) first
        (List.replicate value () ++ restored) []) := by
  induction value generalizing test output restored with
  | zero => rfl
  | succ value ih =>
      rw [show 3 * (value + 1) + 1 =
          (3 * value + 1) + 1 + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change (flip Option.bind (step revProgram))^[3 * value + 1]
        (some (cfg .current buffer true input (.tick :: output) first
          (() :: restored) (List.replicate value ()))) = _
      simpa only [List.replicate_succ, List.cons_append,
        List.append_assoc, replicate_append_cons] using
        ih true (.tick :: output) (() :: restored)

/-- Serialize one ordinary previous/current pair and retain the current value
as the next previous value. -/
def edgeRun (previous current : Nat) (buffer : Option CliqueSym)
    (test : Bool) (input output : List CliqueSym) (first : List Unit) :
    EvalsToInTime (step revProgram)
      (cfg .pushEdgeMark buffer test input output first
        (List.replicate previous ()) (List.replicate current ()))
      (some (cfg .nextRecord buffer false input
        ((encodeCliqueEdge (previous, current)).reverse ++ output)
        first (List.replicate current ()) []))
      (2 * previous + 3 * current + 5) := by
  let afterMark := cfg .previous buffer test input (.edgeMark :: output)
    first (List.replicate previous ()) (List.replicate current ())
  let afterPrevious := cfg .pushPairSeparator buffer false input
    (List.replicate previous .tick ++ .edgeMark :: output)
    first [] (List.replicate current ())
  let afterSeparator := cfg .current buffer false input
    (.pairSep :: (List.replicate previous .tick ++ .edgeMark :: output))
    first [] (List.replicate current ())
  let afterCurrent := cfg .pushRecordEnd buffer false input
    (List.replicate current .tick ++
      .pairSep :: (List.replicate previous .tick ++ .edgeMark :: output))
    first (List.replicate current ()) []
  have hmark : EvalsToInTime (step revProgram)
      (cfg .pushEdgeMark buffer test input output first
        (List.replicate previous ()) (List.replicate current ()))
      (some afterMark) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hprevious : EvalsToInTime (step revProgram) afterMark
      (some afterPrevious) (2 * previous + 1) :=
    ⟨⟨2 * previous + 1, by
      simpa [afterMark, afterPrevious] using
        previous_eval previous buffer test input (.edgeMark :: output)
          first (List.replicate current ())⟩, le_rfl⟩
  have hseparator : EvalsToInTime (step revProgram) afterPrevious
      (some afterSeparator) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hcurrent : EvalsToInTime (step revProgram) afterSeparator
      (some afterCurrent) (3 * current + 1) :=
    ⟨⟨3 * current + 1, by
      simpa [afterSeparator, afterCurrent] using
        current_eval current buffer false input
          (.pairSep :: (List.replicate previous .tick ++
            .edgeMark :: output)) first []⟩, le_rfl⟩
  have hend : EvalsToInTime (step revProgram) afterCurrent
      (some (cfg .nextRecord buffer false input
        (.recordEnd :: (List.replicate current .tick ++
          .pairSep :: (List.replicate previous .tick ++
            .edgeMark :: output)))
        first (List.replicate current ()) [])) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let firstRun := EvalsToInTime.trans (step revProgram)
    1 (2 * previous + 1) _ afterMark _ hmark hprevious
  let secondRun := EvalsToInTime.trans (step revProgram)
    _ 1 _ afterPrevious _ firstRun hseparator
  let thirdRun := EvalsToInTime.trans (step revProgram)
    _ (3 * current + 1) _ afterSeparator _ secondRun hcurrent
  let full := EvalsToInTime.trans (step revProgram)
    _ 1 _ afterCurrent _ thirdRun hend
  convert full using 1
  · simp [encodeCliqueEdge, prependCliqueTicks_eq_replicate,
      List.reverse_append, List.append_assoc]
  · omega

private theorem closingLast_eval (value : Nat)
    (buffer : Option CliqueSym) (test : Bool)
    (input output : List CliqueSym) (first : List Unit) :
    (flip Option.bind (step revProgram))^[2 * value + 1]
      (some (cfg .closingLast buffer test input output first
        (List.replicate value ()) [])) =
      some (cfg .pushClosingSeparator buffer false input
        (List.replicate value .tick ++ output) first [] []) := by
  induction value generalizing test output with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change (flip Option.bind (step revProgram))^[2 * value + 1]
        (some (cfg .closingLast buffer true input (.tick :: output) first
          (List.replicate value ()) [])) = _
      simpa only [List.replicate_succ, List.cons_append,
        replicate_append_cons] using ih true (.tick :: output)

private theorem closingFirst_eval (value : Nat)
    (buffer : Option CliqueSym) (test : Bool)
    (input output : List CliqueSym) :
    (flip Option.bind (step revProgram))^[2 * value + 1]
      (some (cfg .closingFirst buffer test input output
        (List.replicate value ()) [] [])) =
      some (cfg .pushClosingEnd buffer false input
        (List.replicate value .tick ++ output) [] [] []) := by
  induction value generalizing test output with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change (flip Option.bind (step revProgram))^[2 * value + 1]
        (some (cfg .closingFirst buffer true input (.tick :: output)
          (List.replicate value ()) [] [])) = _
      simpa only [List.replicate_succ, List.cons_append,
        replicate_append_cons] using ih true (.tick :: output)

/-- Serialize the final last/first closing query. -/
def closeRun (first last : Nat) (buffer : Option CliqueSym)
    (test : Bool) (input output : List CliqueSym) :
    EvalsToInTime (step revProgram)
      (cfg .closeEdgeMark buffer test input output
        (List.replicate first ()) (List.replicate last ()) [])
      (some (cfg .halt buffer false input
        ((encodeCliqueEdge (last, first)).reverse ++ output) [] [] []))
      (2 * last + 2 * first + 5) := by
  let afterMark := cfg .closingLast buffer test input (.edgeMark :: output)
    (List.replicate first ()) (List.replicate last ()) []
  let afterLast := cfg .pushClosingSeparator buffer false input
    (List.replicate last .tick ++ .edgeMark :: output)
    (List.replicate first ()) [] []
  let afterSeparator := cfg .closingFirst buffer false input
    (.pairSep :: (List.replicate last .tick ++ .edgeMark :: output))
    (List.replicate first ()) [] []
  let afterFirst := cfg .pushClosingEnd buffer false input
    (List.replicate first .tick ++
      .pairSep :: (List.replicate last .tick ++ .edgeMark :: output))
    [] [] []
  have hmark : EvalsToInTime (step revProgram)
      (cfg .closeEdgeMark buffer test input output
        (List.replicate first ()) (List.replicate last ()) [])
      (some afterMark) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hlast : EvalsToInTime (step revProgram) afterMark
      (some afterLast) (2 * last + 1) :=
    ⟨⟨2 * last + 1, by
      simpa [afterMark, afterLast] using
        closingLast_eval last buffer test input (.edgeMark :: output)
          (List.replicate first ())⟩, le_rfl⟩
  have hseparator : EvalsToInTime (step revProgram) afterLast
      (some afterSeparator) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hfirst : EvalsToInTime (step revProgram) afterSeparator
      (some afterFirst) (2 * first + 1) :=
    ⟨⟨2 * first + 1, by
      simpa [afterSeparator, afterFirst] using
        closingFirst_eval first buffer false input
          (.pairSep :: (List.replicate last .tick ++
            .edgeMark :: output))⟩, le_rfl⟩
  have hend : EvalsToInTime (step revProgram) afterFirst
      (some (cfg .halt buffer false input
        (.recordEnd :: (List.replicate first .tick ++
          .pairSep :: (List.replicate last .tick ++
            .edgeMark :: output))) [] [] [])) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let firstRun := EvalsToInTime.trans (step revProgram)
    1 (2 * last + 1) _ afterMark _ hmark hlast
  let secondRun := EvalsToInTime.trans (step revProgram)
    _ 1 _ afterLast _ firstRun hseparator
  let thirdRun := EvalsToInTime.trans (step revProgram)
    _ (2 * first + 1) _ afterSeparator _ secondRun hfirst
  let full := EvalsToInTime.trans (step revProgram)
    _ 1 _ afterFirst _ thirdRun hend
  convert full using 1
  · simp [encodeCliqueEdge, prependCliqueTicks_eq_replicate,
      List.reverse_append, List.append_assoc]
  · omega

/-- Exact cost of all non-closing certificate rows. -/
def rowsStepsFrom : Nat → List Nat → Nat
  | _, [] => 0
  | previous, current :: rest =>
      2 * previous + 5 * current + 7 + rowsStepsFrom current rest

/-- Test bit after zero or more complete later records. -/
def rowsTest : List Nat → Bool → Bool
  | [], test => test
  | _ :: _, _ => false

@[simp] theorem rowsTest_false (vertices : List Nat) :
    rowsTest vertices false = false := by
  cases vertices <;> rfl

/-- Last input symbol buffered after zero or more complete later records. -/
def rowsBuffer : List Nat → Option CliqueSym → Option CliqueSym
  | [], buffer => buffer
  | _ :: _, _ => some .recordEnd

@[simp] theorem rowsBuffer_recordEnd (vertices : List Nat) :
    rowsBuffer vertices (some .recordEnd) = some .recordEnd := by
  cases vertices <;> rfl

/-- Generate every ordinary path pair, retaining first and final values for
the closing phase. -/
def rowsRun (first previous : Nat) (vertices : List Nat)
    (tail output : List CliqueSym) (buffer : Option CliqueSym)
    (test : Bool) :
    EvalsToInTime (step revProgram)
      (cfg .nextRecord buffer test
        (vertices.flatMap encodeCliqueVertex ++ tail) output
        (List.replicate first ()) (List.replicate previous ()) [])
      (some (cfg .nextRecord (rowsBuffer vertices buffer)
        (rowsTest vertices test) tail
        (((pathPairsFrom previous vertices).flatMap encodeCliqueEdge).reverse ++
          output)
        (List.replicate first ())
        (List.replicate (CliqueInstance.lastFrom previous vertices) ()) []))
      (rowsStepsFrom previous vertices) := by
  induction vertices generalizing previous output buffer test with
  | nil =>
      exact ⟨⟨0, by simp [pathPairsFrom, CliqueInstance.lastFrom,
        rowsTest, rowsBuffer, cfg]⟩,
        le_rfl⟩
  | cons current vertices ih =>
      let remainingInput := vertices.flatMap encodeCliqueVertex ++ tail
      have marker : EvalsToInTime (step revProgram)
          (cfg .nextRecord buffer test
            ((current :: vertices).flatMap encodeCliqueVertex ++ tail) output
            (List.replicate first ()) (List.replicate previous ()) [])
          (some (cfg .loadCurrent (some .vertexMark) test
            (prependCliqueTicks current (.recordEnd :: remainingInput)) output
            (List.replicate first ()) (List.replicate previous ()) [])) 1 := by
        exact ⟨⟨1, by simp [remainingInput, encodeCliqueVertex,
          prependCliqueTicks_append, flip, step,
          revProgram, cfg, stepOp]⟩, le_rfl⟩
      have loaded := loadCurrentRun current remainingInput output
        (List.replicate first ()) (List.replicate previous ())
        (some .vertexMark) test
      have emitted := edgeRun previous current (some .recordEnd)
        (loadTest current test) remainingInput output
        (List.replicate first ())
      have rest := ih current
        ((encodeCliqueEdge (previous, current)).reverse ++ output)
        (some .recordEnd) false
      let firstRun := EvalsToInTime.trans (step revProgram)
        1 (2 * current + 1) _ _ _ marker (by simpa using loaded)
      let secondRun := EvalsToInTime.trans (step revProgram)
        _ (2 * previous + 3 * current + 5) _ _ _ firstRun emitted
      let full := EvalsToInTime.trans (step revProgram)
        _ (rowsStepsFrom current vertices) _ _ _ secondRun rest
      rw [rowsBuffer_recordEnd, rowsTest_false] at full
      convert full using 1
      · simp [rowsTest, rowsBuffer, pathPairsFrom,
          CliqueInstance.lastFrom, List.reverse_append,
          List.append_assoc]
      · simp only [rowsStepsFrom]
        omega

end CLRS.Chapter34.Turing.HamiltonianCycle.VerifierMachine.CyclePairs

import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.Cardinality.Basic
import Mathlib.Tactic

/-!
# General CLIQUE verifier: cardinality-controller semantics

This file proves an exact terminating run for the fixed controller in
`Cardinality.Basic`.  The proof is deliberately split from the controller and
from its later polynomial bound so that each layer remains quick to elaborate.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.Cardinality

open PolyBuilder

/-- Recursive Boolean semantics of the target-field phase. -/
def targetResult : Nat → List CliqueSym → Bool
  | _, [] => false
  | 0, .tick :: _ => false
  | count + 1, .tick :: rest => targetResult count rest
  | count, .fieldSep :: _ => decide (count = 0)
  | count, _ :: rest => targetResult count rest

/-- Recursive Boolean semantics while locating the target field. -/
def headerResult : Nat → List CliqueSym → Bool
  | _, [] => false
  | count, .fieldSep :: rest => targetResult count rest
  | count, _ :: rest => headerResult count rest

/-- Exact steps spent after discovering that the target exceeds the count. -/
def targetTooLargeSteps : List CliqueSym → Nat
  | [] => 4
  | .fieldSep :: rest => rest.length + 4
  | _ :: rest => targetTooLargeSteps rest + 1

/-- Exact steps of the target-field phase. -/
def targetSteps : Nat → List CliqueSym → Nat
  | count, [] => count + 4
  | 0, .tick :: rest => targetTooLargeSteps rest + 2
  | count + 1, .tick :: rest => targetSteps count rest + 2
  | count, .fieldSep :: rest => rest.length + count + 5
  | count, _ :: rest => targetSteps count rest + 1

/-- Exact steps spent locating and checking the target field. -/
def headerSteps : Nat → List CliqueSym → Nat
  | count, [] => count + 4
  | count, .fieldSep :: rest => targetSteps count rest + 1
  | count, _ :: rest => headerSteps count rest + 1

/-- Exact steps spent counting certificate vertex records. -/
def certificateSteps (certificate : List CliqueSym) : Nat :=
  certificate.length + certificate.count .vertexMark + 1

private theorem replicate_unit_append_cons (count : Nat)
    (tail : List Unit) :
    List.replicate count () ++ () :: tail =
      () :: (List.replicate count () ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih => simp [List.replicate_succ, ih]

private def emit_run (answer : Bool) (buffer : Option (Option CliqueSym))
    (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.emit answer) buffer test [] [] [])
      (some (haltCfg program [answer])) 2 := by
  exact ⟨⟨2, by
    simp [flip, step, program, cfg, haltCfg, stepOp]⟩, le_rfl⟩

private def clearCount_run (count : Nat)
    (buffer : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .clearCount buffer test [] [] (List.replicate count ()))
      (some (haltCfg program [false])) (count + 3) := by
  induction count generalizing test with
  | zero =>
      exact ⟨⟨3, by
        simp [flip, step, program, cfg, haltCfg, stepOp]⟩, le_rfl⟩
  | succ count ih =>
      let after := cfg .clearCount buffer true [] []
        (List.replicate count ())
      have first : EvalsToInTime (step program)
          (cfg .clearCount buffer test [] []
            (List.replicate (count + 1) ()))
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp,
            List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (test := true)
      let full := EvalsToInTime.trans (step program)
        1 (count + 3) _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

private def checkCount_run (count : Nat)
    (buffer : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .checkCount buffer test [] [] (List.replicate count ()))
      (some (haltCfg program [decide (count = 0)])) (count + 3) := by
  cases count with
  | zero =>
      exact ⟨⟨3, by
        simp [flip, step, program, cfg, haltCfg, stepOp]⟩, le_rfl⟩
  | succ count =>
      let after := cfg .clearCount buffer true [] []
        (List.replicate count ())
      have first : EvalsToInTime (step program)
          (cfg .checkCount buffer test [] []
            (List.replicate (count + 1) ()))
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp,
            List.replicate_succ]⟩, le_rfl⟩
      have rest := clearCount_run count buffer true
      let full := EvalsToInTime.trans (step program)
        1 (count + 3) _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

private def clearInput_false_run (input : List (Option CliqueSym))
    (count : Nat) (buffer : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.clearInput false) buffer test input []
        (List.replicate count ()))
      (some (haltCfg program [decide (count = 0)]))
      (input.length + count + 4) := by
  induction input generalizing buffer test with
  | nil =>
      let after := cfg .checkCount none test [] [] (List.replicate count ())
      have first : EvalsToInTime (step program)
          (cfg (.clearInput false) buffer test [] []
            (List.replicate count ()))
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := checkCount_run count none test
      let full := EvalsToInTime.trans (step program)
        1 (count + 3) _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full
  | cons symbol input ih =>
      let after := cfg (.clearInput false) (some symbol) test input []
        (List.replicate count ())
      have first : EvalsToInTime (step program)
          (cfg (.clearInput false) buffer test (symbol :: input) []
            (List.replicate count ()))
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := ih (buffer := some symbol) (test := test)
      let full := EvalsToInTime.trans (step program)
        1 (input.length + count + 4) _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

private def clearInput_true_run (input : List (Option CliqueSym))
    (buffer : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.clearInput true) buffer test input [] [])
      (some (haltCfg program [false])) (input.length + 3) := by
  induction input generalizing buffer test with
  | nil =>
      let after := cfg (.emit false) none test [] [] []
      have first : EvalsToInTime (step program)
          (cfg (.clearInput true) buffer test [] [] [])
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := emit_run false none test
      let full := EvalsToInTime.trans (step program)
        1 2 _ after _ first rest
      simpa using full
  | cons symbol input ih =>
      let after := cfg (.clearInput true) (some symbol) test input [] []
      have first : EvalsToInTime (step program)
          (cfg (.clearInput true) buffer test (symbol :: input) [] [])
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := ih (buffer := some symbol) (test := test)
      let full := EvalsToInTime.trans (step program)
        1 (input.length + 3) _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

private def targetTooLarge_run (input : List CliqueSym)
    (buffer : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .targetTooLarge buffer test (input.map some) [] [])
      (some (haltCfg program [false])) (targetTooLargeSteps input) := by
  induction input generalizing buffer test with
  | nil =>
      let after := cfg .clearCount none test [] [] []
      have first : EvalsToInTime (step program)
          (cfg .targetTooLarge buffer test [] [] []) (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := clearCount_run 0 none test
      let full := EvalsToInTime.trans (step program) 1 3 _ after _ first rest
      simpa [targetTooLargeSteps] using full
  | cons symbol input ih =>
      have nonseparator (symbol : CliqueSym) (h : symbol ≠ .fieldSep) :
          EvalsToInTime (step program)
            (cfg .targetTooLarge buffer test ((symbol :: input).map some)
              [] [])
            (some (haltCfg program [false]))
            (targetTooLargeSteps (symbol :: input)) := by
        let after := cfg .targetTooLarge (some (some symbol)) test
          (input.map some) [] []
        have first : EvalsToInTime (step program)
            (cfg .targetTooLarge buffer test ((symbol :: input).map some)
              [] []) (some after) 1 := by
          exact ⟨⟨1, by
            simp [flip, after, step, program, cfg, stepOp, h]⟩, le_rfl⟩
        have rest := ih (buffer := some (some symbol)) (test := test)
        let full := EvalsToInTime.trans (step program)
          1 (targetTooLargeSteps input) _ after _ first rest
        simpa [targetTooLargeSteps, h, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using full
      cases symbol with
      | fieldSep =>
          let after := cfg (.clearInput true) (some (some .fieldSep)) test
            (input.map some) [] []
          have first : EvalsToInTime (step program)
              (cfg .targetTooLarge buffer test
                ((.fieldSep :: input).map some) [] [])
              (some after) 1 := by
            exact ⟨⟨1, by
              simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
          have rest : EvalsToInTime (step program) after
              (some (haltCfg program [false])) (input.length + 3) := by
            simpa using clearInput_true_run (input.map some)
              (some (some .fieldSep)) test
          let full := EvalsToInTime.trans (step program)
            1 (input.length + 3) _ after _ first rest
          simpa [targetTooLargeSteps, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using full
      | instanceMark => exact nonseparator .instanceMark (by decide)
      | certificateMark => exact nonseparator .certificateMark (by decide)
      | tick => exact nonseparator .tick (by decide)
      | edgeMark => exact nonseparator .edgeMark (by decide)
      | vertexMark => exact nonseparator .vertexMark (by decide)
      | pairSep => exact nonseparator .pairSep (by decide)
      | recordEnd => exact nonseparator .recordEnd (by decide)

private def target_run (count : Nat) (input : List CliqueSym)
    (buffer : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .target buffer test (input.map some) []
        (List.replicate count ()))
      (some (haltCfg program [targetResult count input]))
      (targetSteps count input) := by
  induction input generalizing count buffer test with
  | nil =>
      let after := cfg .clearCount none test [] [] (List.replicate count ())
      have first : EvalsToInTime (step program)
          (cfg .target buffer test [] [] (List.replicate count ()))
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := clearCount_run count none test
      let full := EvalsToInTime.trans (step program)
        1 (count + 3) _ after _ first rest
      simpa [targetResult, targetSteps, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full
  | cons symbol input ih =>
      have ordinary (symbol : CliqueSym) (htick : symbol ≠ .tick)
          (hsep : symbol ≠ .fieldSep) :
          EvalsToInTime (step program)
            (cfg .target buffer test ((symbol :: input).map some) []
              (List.replicate count ()))
            (some (haltCfg program [targetResult count (symbol :: input)]))
            (targetSteps count (symbol :: input)) := by
        let after := cfg .target (some (some symbol)) test
          (input.map some) [] (List.replicate count ())
        have first : EvalsToInTime (step program)
            (cfg .target buffer test ((symbol :: input).map some) []
              (List.replicate count ()))
            (some after) 1 := by
          exact ⟨⟨1, by
            simp [flip, after, step, program, cfg, stepOp, htick, hsep]⟩,
            le_rfl⟩
        have rest := ih (count := count) (buffer := some (some symbol))
          (test := test)
        let full := EvalsToInTime.trans (step program)
          1 (targetSteps count input) _ after _ first rest
        simpa [targetResult, targetSteps, htick, hsep, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using full
      cases symbol with
      | tick =>
          cases count with
          | zero =>
              let afterPop := cfg .decrementTarget (some (some .tick)) test
                (input.map some) [] []
              let afterDec := cfg .targetTooLarge (some (some .tick)) false
                (input.map some) [] []
              have first : EvalsToInTime (step program)
                  (cfg .target buffer test ((.tick :: input).map some) [] [])
                  (some afterPop) 1 := by
                exact ⟨⟨1, by
                  simp [flip, afterPop, step, program, cfg, stepOp]⟩, le_rfl⟩
              have second : EvalsToInTime (step program) afterPop
                  (some afterDec) 1 := by
                exact ⟨⟨1, by
                  simp [flip, afterPop, afterDec, step, program, cfg,
                    stepOp]⟩, le_rfl⟩
              have rest := targetTooLarge_run input
                (some (some .tick)) false
              let throughDec := EvalsToInTime.trans (step program)
                1 1 _ afterPop _ first second
              let full := EvalsToInTime.trans (step program)
                _ (targetTooLargeSteps input) _ afterDec _ throughDec rest
              simpa [targetResult, targetSteps, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using full
          | succ count =>
              let afterPop := cfg .decrementTarget (some (some .tick)) test
                (input.map some) [] (List.replicate (count + 1) ())
              let afterDec := cfg .target (some (some .tick)) true
                (input.map some) [] (List.replicate count ())
              have first : EvalsToInTime (step program)
                  (cfg .target buffer test ((.tick :: input).map some) []
                    (List.replicate (count + 1) ()))
                  (some afterPop) 1 := by
                exact ⟨⟨1, by
                  simp [flip, afterPop, step, program, cfg, stepOp]⟩,
                  le_rfl⟩
              have second : EvalsToInTime (step program) afterPop
                  (some afterDec) 1 := by
                exact ⟨⟨1, by
                  simp [flip, afterPop, afterDec, step, program, cfg,
                    stepOp, List.replicate_succ]⟩, le_rfl⟩
              have rest := ih (count := count)
                (buffer := some (some .tick)) (test := true)
              let throughDec := EvalsToInTime.trans (step program)
                1 1 _ afterPop _ first second
              let full := EvalsToInTime.trans (step program)
                _ (targetSteps count input) _ afterDec _ throughDec rest
              simpa [targetResult, targetSteps, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using full
      | fieldSep =>
          let after := cfg (.clearInput false) (some (some .fieldSep)) test
            (input.map some) [] (List.replicate count ())
          have first : EvalsToInTime (step program)
              (cfg .target buffer test ((.fieldSep :: input).map some) []
                (List.replicate count ()))
              (some after) 1 := by
            exact ⟨⟨1, by
              simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
          have rest : EvalsToInTime (step program) after
              (some (haltCfg program [decide (count = 0)]))
              (input.length + count + 4) := by
            simpa using clearInput_false_run (input.map some) count
              (some (some .fieldSep)) test
          let full := EvalsToInTime.trans (step program)
            1 (input.length + count + 4) _ after _ first rest
          simpa [targetResult, targetSteps, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using full
      | instanceMark => exact ordinary .instanceMark (by decide) (by decide)
      | certificateMark =>
          exact ordinary .certificateMark (by decide) (by decide)
      | edgeMark => exact ordinary .edgeMark (by decide) (by decide)
      | vertexMark => exact ordinary .vertexMark (by decide) (by decide)
      | pairSep => exact ordinary .pairSep (by decide) (by decide)
      | recordEnd => exact ordinary .recordEnd (by decide) (by decide)

private def header_run (count : Nat) (input : List CliqueSym)
    (buffer : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .instanceHeader buffer test (input.map some) []
        (List.replicate count ()))
      (some (haltCfg program [headerResult count input]))
      (headerSteps count input) := by
  induction input generalizing buffer test with
  | nil =>
      let after := cfg .clearCount none test [] [] (List.replicate count ())
      have first : EvalsToInTime (step program)
          (cfg .instanceHeader buffer test [] []
            (List.replicate count ())) (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := clearCount_run count none test
      let full := EvalsToInTime.trans (step program)
        1 (count + 3) _ after _ first rest
      simpa [headerResult, headerSteps, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full
  | cons symbol input ih =>
      have nonseparator (symbol : CliqueSym) (h : symbol ≠ .fieldSep) :
          EvalsToInTime (step program)
            (cfg .instanceHeader buffer test ((symbol :: input).map some) []
              (List.replicate count ()))
            (some (haltCfg program [headerResult count (symbol :: input)]))
            (headerSteps count (symbol :: input)) := by
        let after := cfg .instanceHeader (some (some symbol)) test
          (input.map some) [] (List.replicate count ())
        have first : EvalsToInTime (step program)
            (cfg .instanceHeader buffer test ((symbol :: input).map some) []
              (List.replicate count ())) (some after) 1 := by
          exact ⟨⟨1, by
            simp [flip, after, step, program, cfg, stepOp, h]⟩, le_rfl⟩
        have rest := ih (buffer := some (some symbol)) (test := test)
        let full := EvalsToInTime.trans (step program)
          1 (headerSteps count input) _ after _ first rest
        simpa [headerResult, headerSteps, h, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using full
      cases symbol with
      | fieldSep =>
          let after := cfg .target (some (some .fieldSep)) test
            (input.map some) [] (List.replicate count ())
          have first : EvalsToInTime (step program)
              (cfg .instanceHeader buffer test
                ((.fieldSep :: input).map some) []
                (List.replicate count ())) (some after) 1 := by
            exact ⟨⟨1, by
              simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
          have rest := target_run count input (some (some .fieldSep)) test
          let full := EvalsToInTime.trans (step program)
            1 (targetSteps count input) _ after _ first rest
          simpa [headerResult, headerSteps, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using full
      | instanceMark => exact nonseparator .instanceMark (by decide)
      | certificateMark => exact nonseparator .certificateMark (by decide)
      | tick => exact nonseparator .tick (by decide)
      | edgeMark => exact nonseparator .edgeMark (by decide)
      | vertexMark => exact nonseparator .vertexMark (by decide)
      | pairSep => exact nonseparator .pairSep (by decide)
      | recordEnd => exact nonseparator .recordEnd (by decide)

private def certificate_run (certificate input : List CliqueSym)
    (count : List Unit) (buffer : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .certificate buffer test
        (certificate.map some ++ none :: input.map some) [] count)
      (some (cfg .instanceHeader (some none) test (input.map some) []
        (List.replicate (certificate.count .vertexMark) () ++ count)))
      (certificateSteps certificate) := by
  induction certificate generalizing count buffer with
  | nil =>
      exact ⟨⟨1, by
        simp [flip, certificateSteps, step, program, cfg, stepOp]⟩, le_rfl⟩
  | cons symbol certificate ih =>
      have nonvertex (symbol : CliqueSym) (h : symbol ≠ .vertexMark) :
          EvalsToInTime (step program)
            (cfg .certificate buffer test
              ((symbol :: certificate).map some ++ none :: input.map some)
              [] count)
            (some (cfg .instanceHeader (some none) test (input.map some) []
              (List.replicate
                ((symbol :: certificate).count .vertexMark) () ++ count)))
            (certificateSteps (symbol :: certificate)) := by
        let after := cfg .certificate (some (some symbol)) test
          (certificate.map some ++ none :: input.map some) [] count
        have first : EvalsToInTime (step program)
            (cfg .certificate buffer test
              ((symbol :: certificate).map some ++ none :: input.map some)
              [] count) (some after) 1 := by
          exact ⟨⟨1, by
            simp [flip, after, step, program, cfg, stepOp, h]⟩, le_rfl⟩
        have rest := ih (count := count) (buffer := some (some symbol))
        let full := EvalsToInTime.trans (step program)
          1 (certificateSteps certificate) _ after _ first rest
        simpa [certificateSteps, h, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using full
      cases symbol with
      | vertexMark =>
          let afterPop := cfg .countVertex (some (some .vertexMark)) test
            (certificate.map some ++ none :: input.map some) [] count
          let afterInc := cfg .certificate (some (some .vertexMark)) test
            (certificate.map some ++ none :: input.map some) [] (() :: count)
          have first : EvalsToInTime (step program)
              (cfg .certificate buffer test
                ((.vertexMark :: certificate).map some ++
                  none :: input.map some) [] count)
              (some afterPop) 1 := by
            exact ⟨⟨1, by
              simp [flip, afterPop, step, program, cfg, stepOp]⟩, le_rfl⟩
          have second : EvalsToInTime (step program) afterPop
              (some afterInc) 1 := by
            exact ⟨⟨1, by
              simp [flip, afterPop, afterInc, step, program, cfg, stepOp]⟩,
              le_rfl⟩
          have rest := ih (count := () :: count)
            (buffer := some (some .vertexMark))
          let throughInc := EvalsToInTime.trans (step program)
            1 1 _ afterPop _ first second
          let full := EvalsToInTime.trans (step program)
            _ (certificateSteps certificate) _ afterInc _ throughInc rest
          simpa [certificateSteps, List.replicate_succ, List.append_assoc,
            replicate_unit_append_cons, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using full
      | instanceMark => exact nonvertex .instanceMark (by decide)
      | certificateMark => exact nonvertex .certificateMark (by decide)
      | tick => exact nonvertex .tick (by decide)
      | fieldSep => exact nonvertex .fieldSep (by decide)
      | edgeMark => exact nonvertex .edgeMark (by decide)
      | pairSep => exact nonvertex .pairSep (by decide)
      | recordEnd => exact nonvertex .recordEnd (by decide)

private theorem targetResult_eq_spec (count : Nat) (input : List CliqueSym) :
    targetResult count input =
      match targetTicksUntilSeparator input with
      | none => false
      | some target => decide (count = target) := by
  induction input generalizing count with
  | nil => simp [targetResult, targetTicksUntilSeparator]
  | cons symbol input ih =>
      cases symbol <;> try simp [targetResult, targetTicksUntilSeparator, ih]
      case tick =>
        cases count with
        | zero =>
            cases h : targetTicksUntilSeparator input <;>
              simp [targetResult, targetTicksUntilSeparator, h]
        | succ count =>
            cases h : targetTicksUntilSeparator input <;>
              simp [targetResult, targetTicksUntilSeparator, h, ih]

private theorem headerResult_eq_spec (count : Nat) (input : List CliqueSym) :
    headerResult count input =
      match rawTargetSize input with
      | none => false
      | some target => decide (count = target) := by
  induction input with
  | nil => simp [headerResult, rawTargetSize]
  | cons symbol input ih =>
      cases symbol <;>
        simp [headerResult, rawTargetSize, ih, targetResult_eq_spec]

/-- Exact independent-semantics run of the complete cardinality controller. -/
def cardinality_run (certificate input : List CliqueSym) :
    EvalsToInTime (step program)
      (initialCfg program (pairEncoding certificate input))
      (some (haltCfg program [cardinalityPass certificate input]))
      (certificateSteps certificate +
        headerSteps (certificate.count .vertexMark) input) := by
  have first := certificate_run certificate input [] none false
  have first' : EvalsToInTime (step program)
      (initialCfg program (pairEncoding certificate input))
      (some (cfg .instanceHeader (some none) false (input.map some) []
        (List.replicate (certificate.count .vertexMark) ())))
      (certificateSteps certificate) := by
    simpa [pairEncoding, initialCfg, cfg, program, List.append_assoc] using first
  have second := header_run (certificate.count .vertexMark) input
    (some none) false
  let full := EvalsToInTime.trans (step program)
    (certificateSteps certificate)
    (headerSteps (certificate.count .vertexMark) input)
    _ _ _ first' second
  convert full using 1 <;>
    simp [cardinalityPass, headerResult_eq_spec, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] <;> rfl

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.Cardinality

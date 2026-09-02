import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.TargetBound.Basic
import Mathlib.Tactic

/-!
# General CLIQUE verifier: target-bound semantics

The phase lemmas below give an exact terminating run of the fixed controller.
They are kept separate from the controller definition and its polynomial
bound so later verifier passes do not enlarge one monolithic proof file.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.TargetBound

open PolyBuilder

/-- Exact steps of the target-size subtraction phase. -/
def targetSteps : Nat → List CliqueSym → Nat
  | count, [] => count + 4
  | 0, .tick :: rest => rest.length + 6
  | count + 1, .tick :: rest => targetSteps count rest + 2
  | count, .fieldSep :: rest => rest.length + count + 5
  | count, _ :: rest => targetSteps count rest + 1

/-- Exact steps of the vertex-count loading phase. -/
def vertexSteps : Nat → List CliqueSym → Nat
  | count, [] => count + 4
  | count, .tick :: rest => vertexSteps (count + 1) rest + 2
  | count, .fieldSep :: rest => targetSteps count rest + 1
  | count, _ :: rest => vertexSteps count rest + 1

/-- Exact steps after entering the instance portion, including consumption of
its leading marker. -/
def instanceSteps : List CliqueSym → Nat
  | [] => 4
  | _ :: rest => vertexSteps 0 rest + 1

private def emit_run (answer : Bool)
    (buffer : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.emit answer) buffer test [] [] [])
      (some (haltCfg program [answer])) 2 := by
  exact ⟨⟨2, by
    simp [flip, step, program, cfg, haltCfg, stepOp]⟩, le_rfl⟩

private def clearCount_run (answer : Bool) (count : Nat)
    (buffer : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.clearCount answer) buffer test [] []
        (List.replicate count ()))
      (some (haltCfg program [answer])) (count + 3) := by
  induction count generalizing test with
  | zero =>
      exact ⟨⟨3, by
        simp [flip, step, program, cfg, haltCfg, stepOp]⟩, le_rfl⟩
  | succ count ih =>
      let after := cfg (.clearCount answer) buffer true [] []
        (List.replicate count ())
      have first : EvalsToInTime (step program)
          (cfg (.clearCount answer) buffer test [] []
            (List.replicate (count + 1) ()))
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp,
            List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (test := true)
      let full := EvalsToInTime.trans (step program)
        1 (count + 3) _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

private def clearInput_run (answer : Bool)
    (input : List (Option CliqueSym)) (count : Nat)
    (buffer : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.clearInput answer) buffer test input []
        (List.replicate count ()))
      (some (haltCfg program [answer])) (input.length + count + 4) := by
  induction input generalizing buffer test with
  | nil =>
      let after := cfg (.clearCount answer) none test [] []
        (List.replicate count ())
      have first : EvalsToInTime (step program)
          (cfg (.clearInput answer) buffer test [] []
            (List.replicate count ()))
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := clearCount_run answer count none test
      let full := EvalsToInTime.trans (step program)
        1 (count + 3) _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full
  | cons symbol input ih =>
      let after := cfg (.clearInput answer) (some symbol) test input []
        (List.replicate count ())
      have first : EvalsToInTime (step program)
          (cfg (.clearInput answer) buffer test (symbol :: input) []
            (List.replicate count ()))
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := ih (buffer := some symbol) (test := test)
      let full := EvalsToInTime.trans (step program)
        1 (input.length + count + 4) _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

private def target_run (count : Nat) (input : List CliqueSym)
    (buffer : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .targetSize buffer test (input.map some) []
        (List.replicate count ()))
      (some (haltCfg program [targetResult count input]))
      (targetSteps count input) := by
  induction input generalizing count buffer test with
  | nil =>
      let after := cfg (.clearCount false) none test [] []
        (List.replicate count ())
      have first : EvalsToInTime (step program)
          (cfg .targetSize buffer test [] [] (List.replicate count ()))
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := clearCount_run false count none test
      let full := EvalsToInTime.trans (step program)
        1 (count + 3) _ after _ first rest
      simpa [targetResult, targetSteps, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full
  | cons symbol input ih =>
      have ordinary (symbol : CliqueSym) (htick : symbol ≠ .tick)
          (hsep : symbol ≠ .fieldSep) :
          EvalsToInTime (step program)
            (cfg .targetSize buffer test ((symbol :: input).map some) []
              (List.replicate count ()))
            (some (haltCfg program [targetResult count (symbol :: input)]))
            (targetSteps count (symbol :: input)) := by
        let after := cfg .targetSize (some (some symbol)) test
          (input.map some) [] (List.replicate count ())
        have first : EvalsToInTime (step program)
            (cfg .targetSize buffer test ((symbol :: input).map some) []
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
              let afterPop := cfg .decrementTargetSize
                (some (some .tick)) test (input.map some) [] []
              let afterDec := cfg (.clearInput false)
                (some (some .tick)) false (input.map some) [] []
              have first : EvalsToInTime (step program)
                  (cfg .targetSize buffer test
                    ((.tick :: input).map some) [] [])
                  (some afterPop) 1 := by
                exact ⟨⟨1, by
                  simp [flip, afterPop, step, program, cfg, stepOp]⟩,
                  le_rfl⟩
              have second : EvalsToInTime (step program) afterPop
                  (some afterDec) 1 := by
                exact ⟨⟨1, by
                  simp [flip, afterPop, afterDec, step, program, cfg,
                    stepOp]⟩, le_rfl⟩
              have rest : EvalsToInTime (step program) afterDec
                  (some (haltCfg program [false])) (input.length + 4) := by
                simpa using clearInput_run false (input.map some) 0
                  (some (some .tick)) false
              let throughDec := EvalsToInTime.trans (step program)
                1 1 _ afterPop _ first second
              let full := EvalsToInTime.trans (step program)
                2 (input.length + 4) _ afterDec _ throughDec rest
              simpa [targetResult, targetSteps, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using full
          | succ count =>
              let afterPop := cfg .decrementTargetSize
                (some (some .tick)) test (input.map some) []
                (List.replicate (count + 1) ())
              let afterDec := cfg .targetSize (some (some .tick)) true
                (input.map some) [] (List.replicate count ())
              have first : EvalsToInTime (step program)
                  (cfg .targetSize buffer test
                    ((.tick :: input).map some) []
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
                2 (targetSteps count input) _ afterDec _ throughDec rest
              simpa [targetResult, targetSteps, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using full
      | fieldSep =>
          let after := cfg (.clearInput true) (some (some .fieldSep)) test
            (input.map some) [] (List.replicate count ())
          have first : EvalsToInTime (step program)
              (cfg .targetSize buffer test
                ((.fieldSep :: input).map some) []
                (List.replicate count ()))
              (some after) 1 := by
            exact ⟨⟨1, by
              simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
          have rest : EvalsToInTime (step program) after
              (some (haltCfg program [true]))
              (input.length + count + 4) := by
            simpa using clearInput_run true (input.map some) count
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

private theorem replicate_unit_append_cons (count : Nat)
    (tail : List Unit) :
    List.replicate count () ++ () :: tail =
      () :: (List.replicate count () ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih => simp [List.replicate_succ, ih]

private def vertex_run (count : Nat) (input : List CliqueSym)
    (buffer : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .vertexCount buffer test (input.map some) []
        (List.replicate count ()))
      (some (haltCfg program [vertexResult count input]))
      (vertexSteps count input) := by
  induction input generalizing count buffer test with
  | nil =>
      let after := cfg (.clearCount false) none test [] []
        (List.replicate count ())
      have first : EvalsToInTime (step program)
          (cfg .vertexCount buffer test [] [] (List.replicate count ()))
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := clearCount_run false count none test
      let full := EvalsToInTime.trans (step program)
        1 (count + 3) _ after _ first rest
      simpa [vertexResult, vertexSteps, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full
  | cons symbol input ih =>
      have ordinary (symbol : CliqueSym) (htick : symbol ≠ .tick)
          (hsep : symbol ≠ .fieldSep) :
          EvalsToInTime (step program)
            (cfg .vertexCount buffer test ((symbol :: input).map some) []
              (List.replicate count ()))
            (some (haltCfg program [vertexResult count (symbol :: input)]))
            (vertexSteps count (symbol :: input)) := by
        let after := cfg .vertexCount (some (some symbol)) test
          (input.map some) [] (List.replicate count ())
        have first : EvalsToInTime (step program)
            (cfg .vertexCount buffer test ((symbol :: input).map some) []
              (List.replicate count ()))
            (some after) 1 := by
          exact ⟨⟨1, by
            simp [flip, after, step, program, cfg, stepOp, htick, hsep]⟩,
            le_rfl⟩
        have rest := ih (count := count) (buffer := some (some symbol))
          (test := test)
        let full := EvalsToInTime.trans (step program)
          1 (vertexSteps count input) _ after _ first rest
        simpa [vertexResult, vertexSteps, htick, hsep, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using full
      cases symbol with
      | tick =>
          let afterPop := cfg .incrementVertexCount (some (some .tick)) test
            (input.map some) [] (List.replicate count ())
          let afterInc := cfg .vertexCount (some (some .tick)) test
            (input.map some) [] (List.replicate (count + 1) ())
          have first : EvalsToInTime (step program)
              (cfg .vertexCount buffer test ((.tick :: input).map some) []
                (List.replicate count ()))
              (some afterPop) 1 := by
            exact ⟨⟨1, by
              simp [flip, afterPop, step, program, cfg, stepOp]⟩, le_rfl⟩
          have second : EvalsToInTime (step program) afterPop
              (some afterInc) 1 := by
            exact ⟨⟨1, by
              simp [flip, afterPop, afterInc, step, program, cfg, stepOp,
                List.replicate_succ]⟩, le_rfl⟩
          have rest := ih (count := count + 1)
            (buffer := some (some .tick)) (test := test)
          let throughInc := EvalsToInTime.trans (step program)
            1 1 _ afterPop _ first second
          let full := EvalsToInTime.trans (step program)
            2 (vertexSteps (count + 1) input) _ afterInc _ throughInc rest
          simpa [vertexResult, vertexSteps, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using full
      | fieldSep =>
          let after := cfg .targetSize (some (some .fieldSep)) test
            (input.map some) [] (List.replicate count ())
          have first : EvalsToInTime (step program)
              (cfg .vertexCount buffer test
                ((.fieldSep :: input).map some) []
                (List.replicate count ()))
              (some after) 1 := by
            exact ⟨⟨1, by
              simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
          have rest := target_run count input (some (some .fieldSep)) test
          let full := EvalsToInTime.trans (step program)
            1 (targetSteps count input) _ after _ first rest
          simpa [vertexResult, vertexSteps, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using full
      | instanceMark => exact ordinary .instanceMark (by decide) (by decide)
      | certificateMark =>
          exact ordinary .certificateMark (by decide) (by decide)
      | edgeMark => exact ordinary .edgeMark (by decide) (by decide)
      | vertexMark => exact ordinary .vertexMark (by decide) (by decide)
      | pairSep => exact ordinary .pairSep (by decide) (by decide)
      | recordEnd => exact ordinary .recordEnd (by decide) (by decide)

private def instance_run (input : List CliqueSym)
    (buffer : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .instanceMark buffer test (input.map some) [] [])
      (some (haltCfg program [targetBoundPass [] input]))
      (instanceSteps input) := by
  cases input with
  | nil =>
      let after := cfg (.clearCount false) none test [] [] []
      have first : EvalsToInTime (step program)
          (cfg .instanceMark buffer test [] [] []) (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := clearCount_run false 0 none test
      let full := EvalsToInTime.trans (step program) 1 3 _ after _ first rest
      simpa [targetBoundPass, instanceSteps] using full
  | cons marker input =>
      let after := cfg .vertexCount (some (some marker)) test
        (input.map some) [] []
      have first : EvalsToInTime (step program)
          (cfg .instanceMark buffer test ((marker :: input).map some) [] [])
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := vertex_run 0 input (some (some marker)) test
      let full := EvalsToInTime.trans (step program)
        1 (vertexSteps 0 input) _ after _ first rest
      simpa [targetBoundPass, instanceSteps, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full

private def certificate_run (certificate input : List CliqueSym)
    (buffer : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .certificate buffer test
        (certificate.map some ++ none :: input.map some) [] [])
      (some (cfg .instanceMark (some none) test (input.map some) [] []))
      (certificate.length + 1) := by
  induction certificate generalizing buffer with
  | nil =>
      exact ⟨⟨1, by
        simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | cons symbol certificate ih =>
      let after := cfg .certificate (some (some symbol)) test
        (certificate.map some ++ none :: input.map some) [] []
      have first : EvalsToInTime (step program)
          (cfg .certificate buffer test
            ((symbol :: certificate).map some ++ none :: input.map some)
            [] []) (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := ih (buffer := some (some symbol))
      let full := EvalsToInTime.trans (step program)
        1 (certificate.length + 1) _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

/-- Exact independent-semantics run of the complete target-bound controller. -/
def targetBound_run (certificate input : List CliqueSym) :
    EvalsToInTime (step program)
      (initialCfg program (pairEncoding certificate input))
      (some (haltCfg program [targetBoundPass certificate input]))
      (certificate.length + 1 + instanceSteps input) := by
  have first := certificate_run certificate input none false
  have first' : EvalsToInTime (step program)
      (initialCfg program (pairEncoding certificate input))
      (some (cfg .instanceMark (some none) false (input.map some) [] []))
      (certificate.length + 1) := by
    simpa [pairEncoding, initialCfg, cfg, program, List.append_assoc] using first
  have second := instance_run input (some none) false
  let full := EvalsToInTime.trans (step program)
    (certificate.length + 1) (instanceSteps input) _ _ _ first' second
  simpa [targetBoundPass, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using full

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.TargetBound

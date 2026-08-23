import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.EdgeOrder.Cleanup

/-!
# General CLIQUE verifier: normalized-edge record phases

A single phase-indexed induction proves the mutually recursive edge, left,
and right scans.  This avoids coupling three large recursive proofs.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.EdgeOrder

open PolyBuilder

/-- Mathematical phase shared by the three record scans. -/
inductive Phase
  | edges
  | left (count : Nat)
  | right (count : Nat) (exceeded : Bool)

/-- Boolean meaning of a record phase. -/
def phaseResult : Phase → List CliqueSym → Bool
  | .edges, input => edgesResult input
  | .left count, input => leftResult count input
  | .right count exceeded, input => rightResult count exceeded input

/-- Corresponding concrete controller label. -/
def phaseLabel : Phase → Label
  | .edges => .edges
  | .left _ => .left
  | .right _ exceeded => .right exceeded

/-- Unary counter content carried by a phase. -/
def phaseCount : Phase → Nat
  | .edges => 0
  | .left count => count
  | .right count _ => count

/-- Exact step count for a record phase. -/
def phaseSteps : Phase → List CliqueSym → Nat
  | .edges, [] => 4
  | .edges, .edgeMark :: rest => phaseSteps (.left 0) rest + 1
  | .edges, _ :: rest => phaseSteps .edges rest + 1
  | .left count, [] => count + 4
  | .left count, .tick :: rest => phaseSteps (.left (count + 1)) rest + 2
  | .left count, .pairSep :: rest =>
      phaseSteps (.right count false) rest + 1
  | .left count, _ :: rest => phaseSteps (.left count) rest + 1
  | .right count exceeded, [] => count + 4
  | .right 0 _, .tick :: rest => phaseSteps (.right 0 true) rest + 2
  | .right (count + 1) exceeded, .tick :: rest =>
      phaseSteps (.right count exceeded) rest + 2
  | .right 0 false, .recordEnd :: rest => rest.length + 6
  | .right 0 true, .recordEnd :: rest => phaseSteps .edges rest + 2
  | .right (count + 1) _, .recordEnd :: rest => rest.length + count + 6
  | .right count exceeded, _ :: rest =>
      phaseSteps (.right count exceeded) rest + 1

/-- Exact run of every record phase. -/
def phase_run (phase : Phase) (input : List CliqueSym)
    (buffer : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (phaseLabel phase) buffer test (input.map some) []
        (List.replicate (phaseCount phase) ()))
      (some (haltCfg program [phaseResult phase input]))
      (phaseSteps phase input) := by
  induction input generalizing phase buffer test with
  | nil =>
      cases phase with
      | edges =>
          let after := cfg (.clearCount true) none test [] [] []
          have first : EvalsToInTime (step program)
              (cfg .edges buffer test [] [] []) (some after) 1 := by
            exact ⟨⟨1, by
              simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
          have rest := clearCount_run true 0 none test
          let full := EvalsToInTime.trans (step program)
            1 3 _ after _ first rest
          simpa [phaseLabel, phaseCount, phaseResult, phaseSteps,
            edgesResult] using full
      | left count =>
          let after := cfg (.clearCount false) none test [] []
            (List.replicate count ())
          have first : EvalsToInTime (step program)
              (cfg .left buffer test [] [] (List.replicate count ()))
              (some after) 1 := by
            exact ⟨⟨1, by
              simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
          have rest := clearCount_run false count none test
          let full := EvalsToInTime.trans (step program)
            1 (count + 3) _ after _ first rest
          simpa [phaseLabel, phaseCount, phaseResult, phaseSteps,
            leftResult, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using full
      | right count exceeded =>
          let after := cfg (.clearCount false) none test [] []
            (List.replicate count ())
          have first : EvalsToInTime (step program)
              (cfg (.right exceeded) buffer test [] []
                (List.replicate count ()))
              (some after) 1 := by
            exact ⟨⟨1, by
              simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
          have rest := clearCount_run false count none test
          let full := EvalsToInTime.trans (step program)
            1 (count + 3) _ after _ first rest
          simpa [phaseLabel, phaseCount, phaseResult, phaseSteps,
            rightResult, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using full
  | cons symbol input ih =>
      cases phase with
      | edges =>
          have ordinary (symbol : CliqueSym) (h : symbol ≠ .edgeMark) :
              EvalsToInTime (step program)
                (cfg .edges buffer test ((symbol :: input).map some) [] [])
                (some (haltCfg program
                  [phaseResult .edges (symbol :: input)]))
                (phaseSteps .edges (symbol :: input)) := by
            let after := cfg .edges (some (some symbol)) test
              (input.map some) [] []
            have first : EvalsToInTime (step program)
                (cfg .edges buffer test ((symbol :: input).map some) [] [])
                (some after) 1 := by
              exact ⟨⟨1, by
                simp [flip, after, step, program, cfg, stepOp, h]⟩,
                le_rfl⟩
            have rest := ih (phase := Phase.edges)
              (buffer := some (some symbol)) (test := test)
            let full := EvalsToInTime.trans (step program)
              1 (phaseSteps .edges input) _ after _ first rest
            simpa [phaseLabel, phaseCount, phaseResult, phaseSteps,
              edgesResult, h, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using full
          cases symbol with
          | edgeMark =>
              let after := cfg .left (some (some .edgeMark)) test
                (input.map some) [] []
              have first : EvalsToInTime (step program)
                  (cfg .edges buffer test ((.edgeMark :: input).map some)
                    [] []) (some after) 1 := by
                exact ⟨⟨1, by
                  simp [flip, after, step, program, cfg, stepOp]⟩,
                  le_rfl⟩
              have rest := ih (phase := Phase.left 0)
                (buffer := some (some .edgeMark)) (test := test)
              let full := EvalsToInTime.trans (step program)
                1 (phaseSteps (.left 0) input) _ after _ first rest
              simpa [phaseLabel, phaseCount, phaseResult, phaseSteps,
                edgesResult, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using full
          | instanceMark => exact ordinary .instanceMark (by decide)
          | certificateMark => exact ordinary .certificateMark (by decide)
          | tick => exact ordinary .tick (by decide)
          | fieldSep => exact ordinary .fieldSep (by decide)
          | vertexMark => exact ordinary .vertexMark (by decide)
          | pairSep => exact ordinary .pairSep (by decide)
          | recordEnd => exact ordinary .recordEnd (by decide)
      | left count =>
          have ordinary (symbol : CliqueSym) (htick : symbol ≠ .tick)
              (hsep : symbol ≠ .pairSep) :
              EvalsToInTime (step program)
                (cfg .left buffer test ((symbol :: input).map some) []
                  (List.replicate count ()))
                (some (haltCfg program
                  [phaseResult (.left count) (symbol :: input)]))
                (phaseSteps (.left count) (symbol :: input)) := by
            let after := cfg .left (some (some symbol)) test
              (input.map some) [] (List.replicate count ())
            have first : EvalsToInTime (step program)
                (cfg .left buffer test ((symbol :: input).map some) []
                  (List.replicate count ()))
                (some after) 1 := by
              exact ⟨⟨1, by
                simp [flip, after, step, program, cfg, stepOp, htick, hsep]⟩,
                le_rfl⟩
            have rest := ih (phase := Phase.left count)
              (buffer := some (some symbol)) (test := test)
            let full := EvalsToInTime.trans (step program)
              1 (phaseSteps (.left count) input) _ after _ first rest
            simpa [phaseLabel, phaseCount, phaseResult, phaseSteps,
              leftResult, htick, hsep, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using full
          cases symbol with
          | tick =>
              let afterPop := cfg .incrementLeft (some (some .tick)) test
                (input.map some) [] (List.replicate count ())
              let afterInc := cfg .left (some (some .tick)) test
                (input.map some) [] (List.replicate (count + 1) ())
              have first : EvalsToInTime (step program)
                  (cfg .left buffer test ((.tick :: input).map some) []
                    (List.replicate count ()))
                  (some afterPop) 1 := by
                exact ⟨⟨1, by
                  simp [flip, afterPop, step, program, cfg, stepOp]⟩,
                  le_rfl⟩
              have second : EvalsToInTime (step program) afterPop
                  (some afterInc) 1 := by
                exact ⟨⟨1, by
                  simp [flip, afterPop, afterInc, step, program, cfg,
                    stepOp, List.replicate_succ]⟩, le_rfl⟩
              have rest := ih (phase := Phase.left (count + 1))
                (buffer := some (some .tick)) (test := test)
              let throughInc := EvalsToInTime.trans (step program)
                1 1 _ afterPop _ first second
              let full := EvalsToInTime.trans (step program)
                2 (phaseSteps (.left (count + 1)) input)
                _ afterInc _ throughInc rest
              simpa [phaseLabel, phaseCount, phaseResult, phaseSteps,
                leftResult, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using full
          | pairSep =>
              let after := cfg (.right false) (some (some .pairSep)) test
                (input.map some) [] (List.replicate count ())
              have first : EvalsToInTime (step program)
                  (cfg .left buffer test ((.pairSep :: input).map some) []
                    (List.replicate count ()))
                  (some after) 1 := by
                exact ⟨⟨1, by
                  simp [flip, after, step, program, cfg, stepOp]⟩,
                  le_rfl⟩
              have rest := ih (phase := Phase.right count false)
                (buffer := some (some .pairSep)) (test := test)
              let full := EvalsToInTime.trans (step program)
                1 (phaseSteps (.right count false) input)
                _ after _ first rest
              simpa [phaseLabel, phaseCount, phaseResult, phaseSteps,
                leftResult, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using full
          | instanceMark =>
              exact ordinary .instanceMark (by decide) (by decide)
          | certificateMark =>
              exact ordinary .certificateMark (by decide) (by decide)
          | fieldSep => exact ordinary .fieldSep (by decide) (by decide)
          | edgeMark => exact ordinary .edgeMark (by decide) (by decide)
          | vertexMark => exact ordinary .vertexMark (by decide) (by decide)
          | recordEnd => exact ordinary .recordEnd (by decide) (by decide)
      | right count exceeded =>
          have ordinary (symbol : CliqueSym) (htick : symbol ≠ .tick)
              (hend : symbol ≠ .recordEnd) :
              EvalsToInTime (step program)
                (cfg (.right exceeded) buffer test
                  ((symbol :: input).map some) []
                  (List.replicate count ()))
                (some (haltCfg program
                  [phaseResult (.right count exceeded) (symbol :: input)]))
                (phaseSteps (.right count exceeded) (symbol :: input)) := by
            let after := cfg (.right exceeded) (some (some symbol)) test
              (input.map some) [] (List.replicate count ())
            have first : EvalsToInTime (step program)
                (cfg (.right exceeded) buffer test
                  ((symbol :: input).map some) []
                  (List.replicate count ()))
                (some after) 1 := by
              exact ⟨⟨1, by
                simp [flip, after, step, program, cfg, stepOp, htick, hend]⟩,
                le_rfl⟩
            have rest := ih (phase := Phase.right count exceeded)
              (buffer := some (some symbol)) (test := test)
            let full := EvalsToInTime.trans (step program)
              1 (phaseSteps (.right count exceeded) input)
              _ after _ first rest
            simpa [phaseLabel, phaseCount, phaseResult, phaseSteps,
              rightResult, htick, hend, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using full
          cases symbol with
          | tick =>
              cases count with
              | zero =>
                  let afterPop := cfg (.decrementRight exceeded)
                    (some (some .tick)) test (input.map some) [] []
                  let afterDec := cfg (.right true) (some (some .tick))
                    false (input.map some) [] []
                  have first : EvalsToInTime (step program)
                      (cfg (.right exceeded) buffer test
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
                  have rest := ih (phase := Phase.right 0 true)
                    (buffer := some (some .tick)) (test := false)
                  let throughDec := EvalsToInTime.trans (step program)
                    1 1 _ afterPop _ first second
                  let full := EvalsToInTime.trans (step program)
                    2 (phaseSteps (.right 0 true) input)
                    _ afterDec _ throughDec rest
                  simpa [phaseLabel, phaseCount, phaseResult, phaseSteps,
                    rightResult, Nat.add_assoc, Nat.add_comm,
                    Nat.add_left_comm] using full
              | succ count =>
                  let afterPop := cfg (.decrementRight exceeded)
                    (some (some .tick)) test (input.map some) []
                    (List.replicate (count + 1) ())
                  let afterDec := cfg (.right exceeded) (some (some .tick))
                    true (input.map some) [] (List.replicate count ())
                  have first : EvalsToInTime (step program)
                      (cfg (.right exceeded) buffer test
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
                  have rest := ih (phase := Phase.right count exceeded)
                    (buffer := some (some .tick)) (test := true)
                  let throughDec := EvalsToInTime.trans (step program)
                    1 1 _ afterPop _ first second
                  let full := EvalsToInTime.trans (step program)
                    2 (phaseSteps (.right count exceeded) input)
                    _ afterDec _ throughDec rest
                  simpa [phaseLabel, phaseCount, phaseResult, phaseSteps,
                    rightResult, Nat.add_assoc, Nat.add_comm,
                    Nat.add_left_comm] using full
          | recordEnd =>
              let afterPop := cfg (.finishEdge exceeded)
                (some (some .recordEnd)) test (input.map some) []
                (List.replicate count ())
              have first : EvalsToInTime (step program)
                  (cfg (.right exceeded) buffer test
                    ((.recordEnd :: input).map some) []
                    (List.replicate count ()))
                  (some afterPop) 1 := by
                exact ⟨⟨1, by
                  simp [flip, afterPop, step, program, cfg, stepOp]⟩,
                  le_rfl⟩
              cases count with
              | zero =>
                  cases exceeded with
                  | false =>
                      let afterDec := cfg (.clearInput false)
                        (some (some .recordEnd)) false (input.map some) [] []
                      have second : EvalsToInTime (step program) afterPop
                          (some afterDec) 1 := by
                        exact ⟨⟨1, by
                          simp [flip, afterPop, afterDec, step, program, cfg,
                            stepOp]⟩, le_rfl⟩
                      have rest : EvalsToInTime (step program) afterDec
                          (some (haltCfg program [false]))
                          (input.length + 4) := by
                        simpa using clearInput_run false (input.map some) 0
                          (some (some .recordEnd)) false
                      let throughFinish := EvalsToInTime.trans (step program)
                        1 1 _ afterPop _ first second
                      let full := EvalsToInTime.trans (step program)
                        2 (input.length + 4) _ afterDec _ throughFinish rest
                      simpa [phaseLabel, phaseCount, phaseResult, phaseSteps,
                        rightResult, Nat.add_assoc, Nat.add_comm,
                        Nat.add_left_comm] using full
                  | true =>
                      let afterDec := cfg .edges (some (some .recordEnd))
                        false (input.map some) [] []
                      have second : EvalsToInTime (step program) afterPop
                          (some afterDec) 1 := by
                        exact ⟨⟨1, by
                          simp [flip, afterPop, afterDec, step, program, cfg,
                            stepOp]⟩, le_rfl⟩
                      have rest := ih (phase := Phase.edges)
                        (buffer := some (some .recordEnd)) (test := false)
                      let throughFinish := EvalsToInTime.trans (step program)
                        1 1 _ afterPop _ first second
                      let full := EvalsToInTime.trans (step program)
                        2 (phaseSteps .edges input)
                        _ afterDec _ throughFinish rest
                      simpa [phaseLabel, phaseCount, phaseResult, phaseSteps,
                        rightResult, Nat.add_assoc, Nat.add_comm,
                        Nat.add_left_comm] using full
              | succ count =>
                  let afterDec := cfg (.clearInput false)
                    (some (some .recordEnd)) true (input.map some) []
                    (List.replicate count ())
                  have second : EvalsToInTime (step program) afterPop
                      (some afterDec) 1 := by
                    exact ⟨⟨1, by
                      simp [flip, afterPop, afterDec, step, program, cfg,
                        stepOp, List.replicate_succ]⟩, le_rfl⟩
                  have rest : EvalsToInTime (step program) afterDec
                      (some (haltCfg program [false]))
                      (input.length + count + 4) := by
                    simpa using clearInput_run false (input.map some) count
                      (some (some .recordEnd)) true
                  let throughFinish := EvalsToInTime.trans (step program)
                    1 1 _ afterPop _ first second
                  let full := EvalsToInTime.trans (step program)
                    2 (input.length + count + 4)
                    _ afterDec _ throughFinish rest
                  simpa [phaseLabel, phaseCount, phaseResult, phaseSteps,
                    rightResult, Nat.add_assoc, Nat.add_comm,
                    Nat.add_left_comm] using full
          | instanceMark =>
              exact ordinary .instanceMark (by decide) (by decide)
          | certificateMark =>
              exact ordinary .certificateMark (by decide) (by decide)
          | fieldSep => exact ordinary .fieldSep (by decide) (by decide)
          | edgeMark => exact ordinary .edgeMark (by decide) (by decide)
          | vertexMark => exact ordinary .vertexMark (by decide) (by decide)
          | pairSep => exact ordinary .pairSep (by decide) (by decide)

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.EdgeOrder

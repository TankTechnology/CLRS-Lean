import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.CertificateRange.Cleanup

/-!
# General CLIQUE verifier: certificate-range record phases
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.CertificateRange

open PolyBuilder

inductive Phase
  | vertices (vertexCount : Nat)
  | vertex (remaining spent : Nat)

def phaseResult : Phase → List CliqueSym → Bool
  | .vertices vertexCount, input => verticesResult vertexCount input
  | .vertex remaining spent, input => vertexResult remaining spent input

def phaseLabel : Phase → Label
  | .vertices _ => .vertices
  | .vertex _ _ => .vertex

def phaseRemaining : Phase → Nat
  | .vertices vertexCount => vertexCount
  | .vertex remaining _ => remaining

def phaseSpent : Phase → Nat
  | .vertices _ => 0
  | .vertex _ spent => spent

def phaseSteps : Phase → List CliqueSym → Nat
  | .vertices vertexCount, [] => vertexCount + 5
  | .vertices vertexCount, .vertexMark :: rest =>
      phaseSteps (.vertex vertexCount 0) rest + 1
  | .vertices vertexCount, _ :: rest =>
      phaseSteps (.vertices vertexCount) rest + 1
  | .vertex remaining spent, [] => remaining + spent + 7
  | .vertex 0 spent, .tick :: rest => rest.length + spent + 8
  | .vertex (remaining + 1) spent, .tick :: rest =>
      phaseSteps (.vertex remaining (spent + 1)) rest + 3
  | .vertex 0 spent, .recordEnd :: rest => rest.length + spent + 8
  | .vertex (remaining + 1) spent, .recordEnd :: rest =>
      phaseSteps (.vertices (remaining + (spent + 1))) rest +
        2 * spent + 6
  | .vertex remaining spent, _ :: rest =>
      phaseSteps (.vertex remaining spent) rest + 1

def phase_run (phase : Phase) (input : List CliqueSym)
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (phaseLabel phase) buffer₁ buffer₂ test (input.map some) [] []
        (List.replicate (phaseRemaining phase) (some .tick))
        (List.replicate (phaseSpent phase) ()))
      (some (haltCfg program [phaseResult phase input]))
      (phaseSteps phase input) := by
  induction input generalizing phase buffer₁ buffer₂ test with
  | nil =>
      cases phase with
      | vertices vertexCount =>
          let after := cfg (.clearWork₂ true) none buffer₂ test [] [] []
            (List.replicate vertexCount (some .tick)) []
          have first : EvalsToInTime (step program)
              (cfg .vertices buffer₁ buffer₂ test [] [] []
                (List.replicate vertexCount (some .tick)) [])
              (some after) 1 := by
            exact ⟨⟨1, by
              simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
          have rest := clearWork₂_run true
            (List.replicate vertexCount (some .tick)) 0 none buffer₂ test
          have rest' : EvalsToInTime (step program) after
              (some (haltCfg program [true])) (vertexCount + 4) := by
            simpa using rest
          let full := EvalsToInTime.trans (step program)
            1 (vertexCount + 4) _ after _ first rest'
          simpa [phaseLabel, phaseRemaining, phaseSpent, phaseResult,
            phaseSteps, verticesResult] using full
      | vertex remaining spent =>
          let after := cfg (.clearInput false) none buffer₂ test [] [] []
            (List.replicate remaining (some .tick))
            (List.replicate spent ())
          have first : EvalsToInTime (step program)
              (cfg .vertex buffer₁ buffer₂ test [] [] []
                (List.replicate remaining (some .tick))
                (List.replicate spent ()))
              (some after) 1 := by
            exact ⟨⟨1, by
              simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
          have rest := clearInput_run false [] []
            (List.replicate remaining (some .tick)) spent none buffer₂ test
          have rest' : EvalsToInTime (step program) after
              (some (haltCfg program [false]))
              (remaining + spent + 6) := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rest
          let full := EvalsToInTime.trans (step program)
            1 (remaining + spent + 6) _ after _ first rest'
          simpa [phaseLabel, phaseRemaining, phaseSpent, phaseResult,
            phaseSteps, vertexResult, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using full
  | cons symbol input ih =>
      cases phase with
      | vertices vertexCount =>
          have ordinary (symbol : CliqueSym) (h : symbol ≠ .vertexMark) :
              EvalsToInTime (step program)
                (cfg .vertices buffer₁ buffer₂ test
                  ((symbol :: input).map some) [] []
                  (List.replicate vertexCount (some .tick)) [])
                (some (haltCfg program
                  [phaseResult (.vertices vertexCount) (symbol :: input)]))
                (phaseSteps (.vertices vertexCount) (symbol :: input)) := by
            let after := cfg .vertices (some (some symbol)) buffer₂ test
              (input.map some) [] []
              (List.replicate vertexCount (some .tick)) []
            have first : EvalsToInTime (step program)
                (cfg .vertices buffer₁ buffer₂ test
                  ((symbol :: input).map some) [] []
                  (List.replicate vertexCount (some .tick)) [])
                (some after) 1 := by
              exact ⟨⟨1, by
                simp [flip, after, step, program, cfg, stepOp, h]⟩,
                le_rfl⟩
            have rest := ih (phase := Phase.vertices vertexCount)
              (buffer₁ := some (some symbol)) (buffer₂ := buffer₂)
              (test := test)
            let full := EvalsToInTime.trans (step program)
              1 (phaseSteps (.vertices vertexCount) input)
              _ after _ first rest
            simpa [phaseLabel, phaseRemaining, phaseSpent, phaseResult,
              phaseSteps, verticesResult, h, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using full
          cases symbol with
          | vertexMark =>
              let after := cfg .vertex (some (some .vertexMark)) buffer₂ test
                (input.map some) [] []
                (List.replicate vertexCount (some .tick)) []
              have first : EvalsToInTime (step program)
                  (cfg .vertices buffer₁ buffer₂ test
                    ((.vertexMark :: input).map some) [] []
                    (List.replicate vertexCount (some .tick)) [])
                  (some after) 1 := by
                exact ⟨⟨1, by
                  simp [flip, after, step, program, cfg, stepOp]⟩,
                  le_rfl⟩
              have rest := ih (phase := Phase.vertex vertexCount 0)
                (buffer₁ := some (some .vertexMark))
                (buffer₂ := buffer₂) (test := test)
              let full := EvalsToInTime.trans (step program)
                1 (phaseSteps (.vertex vertexCount 0) input)
                _ after _ first rest
              simpa [phaseLabel, phaseRemaining, phaseSpent, phaseResult,
                phaseSteps, verticesResult, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using full
          | instanceMark => exact ordinary .instanceMark (by decide)
          | certificateMark => exact ordinary .certificateMark (by decide)
          | tick => exact ordinary .tick (by decide)
          | fieldSep => exact ordinary .fieldSep (by decide)
          | edgeMark => exact ordinary .edgeMark (by decide)
          | pairSep => exact ordinary .pairSep (by decide)
          | recordEnd => exact ordinary .recordEnd (by decide)
      | vertex remaining spent =>
          have ordinary (symbol : CliqueSym) (htick : symbol ≠ .tick)
              (hend : symbol ≠ .recordEnd) :
              EvalsToInTime (step program)
                (cfg .vertex buffer₁ buffer₂ test
                  ((symbol :: input).map some) [] []
                  (List.replicate remaining (some .tick))
                  (List.replicate spent ()))
                (some (haltCfg program
                  [phaseResult (.vertex remaining spent) (symbol :: input)]))
                (phaseSteps (.vertex remaining spent) (symbol :: input)) := by
            let after := cfg .vertex (some (some symbol)) buffer₂ test
              (input.map some) [] []
              (List.replicate remaining (some .tick))
              (List.replicate spent ())
            have first : EvalsToInTime (step program)
                (cfg .vertex buffer₁ buffer₂ test
                  ((symbol :: input).map some) [] []
                  (List.replicate remaining (some .tick))
                  (List.replicate spent ()))
                (some after) 1 := by
              exact ⟨⟨1, by
                simp [flip, after, step, program, cfg, stepOp, htick, hend]⟩,
                le_rfl⟩
            have rest := ih (phase := Phase.vertex remaining spent)
              (buffer₁ := some (some symbol)) (buffer₂ := buffer₂)
              (test := test)
            let full := EvalsToInTime.trans (step program)
              1 (phaseSteps (.vertex remaining spent) input)
              _ after _ first rest
            simpa [phaseLabel, phaseRemaining, phaseSpent, phaseResult,
              phaseSteps, vertexResult, htick, hend, Nat.add_assoc,
              Nat.add_comm, Nat.add_left_comm] using full
          cases symbol with
          | tick =>
              let afterPop := cfg .spendTick (some (some .tick)) buffer₂
                test (input.map some) [] []
                (List.replicate remaining (some .tick))
                (List.replicate spent ())
              have first : EvalsToInTime (step program)
                  (cfg .vertex buffer₁ buffer₂ test
                    ((.tick :: input).map some) [] []
                    (List.replicate remaining (some .tick))
                    (List.replicate spent ()))
                  (some afterPop) 1 := by
                exact ⟨⟨1, by
                  simp [flip, afterPop, step, program, cfg, stepOp]⟩,
                  le_rfl⟩
              cases remaining with
              | zero =>
                  let afterSpend := cfg (.clearInput false) (some (some .tick))
                    none test (input.map some) [] [] []
                    (List.replicate spent ())
                  have second : EvalsToInTime (step program) afterPop
                      (some afterSpend) 1 := by
                    exact ⟨⟨1, by
                      simp [flip, afterPop, afterSpend, step, program, cfg,
                        stepOp]⟩, le_rfl⟩
                  have rest := clearInput_run false (input.map some) [] []
                    spent (some (some .tick)) none test
                  have rest' : EvalsToInTime (step program) afterSpend
                      (some (haltCfg program [false]))
                      (input.length + spent + 6) := by
                    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                      using rest
                  let throughSpend := EvalsToInTime.trans (step program)
                    1 1 _ afterPop _ first second
                  let full := EvalsToInTime.trans (step program)
                    2 (input.length + spent + 6)
                    _ afterSpend _ throughSpend rest'
                  simpa [phaseLabel, phaseRemaining, phaseSpent, phaseResult,
                    phaseSteps, vertexResult, Nat.add_assoc, Nat.add_comm,
                    Nat.add_left_comm] using full
              | succ remaining =>
                  let afterSpend := cfg .incrementSpent
                    (some (some .tick)) (some (some .tick)) test
                    (input.map some) [] []
                    (List.replicate remaining (some .tick))
                    (List.replicate spent ())
                  let afterInc := cfg .vertex
                    (some (some .tick)) (some (some .tick)) test
                    (input.map some) [] []
                    (List.replicate remaining (some .tick))
                    (List.replicate (spent + 1) ())
                  have second : EvalsToInTime (step program) afterPop
                      (some afterSpend) 1 := by
                    exact ⟨⟨1, by
                      simp [flip, afterPop, afterSpend, step, program, cfg,
                        stepOp, List.replicate_succ]⟩, le_rfl⟩
                  have third : EvalsToInTime (step program) afterSpend
                      (some afterInc) 1 := by
                    exact ⟨⟨1, by
                      simp [flip, afterSpend, afterInc, step, program, cfg,
                        stepOp, List.replicate_succ]⟩, le_rfl⟩
                  have rest := ih
                    (phase := Phase.vertex remaining (spent + 1))
                    (buffer₁ := some (some .tick))
                    (buffer₂ := some (some .tick)) (test := test)
                  let throughSpend := EvalsToInTime.trans (step program)
                    1 1 _ afterPop _ first second
                  let throughInc := EvalsToInTime.trans (step program)
                    2 1 _ afterSpend _ throughSpend third
                  let full := EvalsToInTime.trans (step program)
                    3 (phaseSteps (.vertex remaining (spent + 1)) input)
                    _ afterInc _ throughInc rest
                  simpa [phaseLabel, phaseRemaining, phaseSpent, phaseResult,
                    phaseSteps, vertexResult, Nat.add_assoc, Nat.add_comm,
                    Nat.add_left_comm] using full
          | recordEnd =>
              let afterPop := cfg .demandStrict (some (some .recordEnd))
                buffer₂ test (input.map some) [] []
                (List.replicate remaining (some .tick))
                (List.replicate spent ())
              have first : EvalsToInTime (step program)
                  (cfg .vertex buffer₁ buffer₂ test
                    ((.recordEnd :: input).map some) [] []
                    (List.replicate remaining (some .tick))
                    (List.replicate spent ()))
                  (some afterPop) 1 := by
                exact ⟨⟨1, by
                  simp [flip, afterPop, step, program, cfg, stepOp]⟩,
                  le_rfl⟩
              cases remaining with
              | zero =>
                  let afterDemand := cfg (.clearInput false)
                    (some (some .recordEnd)) none test (input.map some) [] [] []
                    (List.replicate spent ())
                  have second : EvalsToInTime (step program) afterPop
                      (some afterDemand) 1 := by
                    exact ⟨⟨1, by
                      simp [flip, afterPop, afterDemand, step, program, cfg,
                        stepOp]⟩, le_rfl⟩
                  have rest := clearInput_run false (input.map some) [] []
                    spent (some (some .recordEnd)) none test
                  have rest' : EvalsToInTime (step program) afterDemand
                      (some (haltCfg program [false]))
                      (input.length + spent + 6) := by
                    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                      using rest
                  let throughDemand := EvalsToInTime.trans (step program)
                    1 1 _ afterPop _ first second
                  let full := EvalsToInTime.trans (step program)
                    2 (input.length + spent + 6)
                    _ afterDemand _ throughDemand rest'
                  simpa [phaseLabel, phaseRemaining, phaseSpent, phaseResult,
                    phaseSteps, vertexResult, Nat.add_assoc, Nat.add_comm,
                    Nat.add_left_comm] using full
              | succ remaining =>
                  let afterDemand := cfg .saveStrict
                    (some (some .recordEnd)) (some (some .tick)) test
                    (input.map some) [] []
                    (List.replicate remaining (some .tick))
                    (List.replicate spent ())
                  let afterSave := cfg .restoreBudget
                    (some (some .recordEnd)) (some (some .tick)) test
                    (input.map some) [] []
                    (List.replicate remaining (some .tick))
                    (List.replicate (spent + 1) ())
                  have second : EvalsToInTime (step program) afterPop
                      (some afterDemand) 1 := by
                    exact ⟨⟨1, by
                      simp [flip, afterPop, afterDemand, step, program, cfg,
                        stepOp, List.replicate_succ]⟩, le_rfl⟩
                  have third : EvalsToInTime (step program) afterDemand
                      (some afterSave) 1 := by
                    exact ⟨⟨1, by
                      simp [flip, afterDemand, afterSave, step, program, cfg,
                        stepOp, List.replicate_succ]⟩, le_rfl⟩
                  have restored := restoreBudget_run remaining (spent + 1)
                    (input.map some) (some (some .recordEnd))
                    (some (some .tick)) test
                  let afterRestore := cfg .vertices
                    (some (some .recordEnd)) (some (some .tick)) false
                    (input.map some) [] []
                    (List.replicate (remaining + (spent + 1))
                      (some .tick)) []
                  have rest := ih
                    (phase := Phase.vertices (remaining + (spent + 1)))
                    (buffer₁ := some (some .recordEnd))
                    (buffer₂ := some (some .tick)) (test := false)
                  let throughDemand := EvalsToInTime.trans (step program)
                    1 1 _ afterPop _ first second
                  let throughSave := EvalsToInTime.trans (step program)
                    2 1 _ afterDemand _ throughDemand third
                  let throughRestore := EvalsToInTime.trans (step program)
                    3 (2 * (spent + 1) + 1)
                    _ afterSave _ throughSave restored
                  let full := EvalsToInTime.trans (step program)
                    (2 * spent + 6)
                    (phaseSteps (.vertices (remaining + (spent + 1))) input)
                    _ afterRestore _ throughRestore rest
                  simpa [afterRestore, phaseLabel, phaseRemaining, phaseSpent,
                    phaseResult, phaseSteps, vertexResult, Nat.mul_succ,
                    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full
          | instanceMark =>
              exact ordinary .instanceMark (by decide) (by decide)
          | certificateMark =>
              exact ordinary .certificateMark (by decide) (by decide)
          | fieldSep => exact ordinary .fieldSep (by decide) (by decide)
          | edgeMark => exact ordinary .edgeMark (by decide) (by decide)
          | vertexMark => exact ordinary .vertexMark (by decide) (by decide)
          | pairSep => exact ordinary .pairSep (by decide) (by decide)

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.CertificateRange

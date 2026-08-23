import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.EndpointBound.Cleanup

/-!
# General CLIQUE verifier: endpoint-bound record phases

The phase invariant exposes both halves of the reusable unary budget.  Work
stack one contains {lit}`remaining` ticks and work stack two contains {lit}`spent`
ticks; their sum is restored before the next edge record.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.EndpointBound

open PolyBuilder

inductive Phase
  | edges (vertexCount : Nat)
  | left (vertexCount : Nat)
  | right (remaining spent : Nat)

def phaseResult : Phase → List CliqueSym → Bool
  | .edges vertexCount, input => edgesResult vertexCount input
  | .left vertexCount, input => leftResult vertexCount input
  | .right remaining spent, input => rightResult remaining spent input

def phaseLabel : Phase → Label
  | .edges _ => .edges
  | .left _ => .left
  | .right _ _ => .right

def phaseRemaining : Phase → Nat
  | .edges vertexCount => vertexCount
  | .left vertexCount => vertexCount
  | .right remaining _ => remaining

def phaseSpent : Phase → Nat
  | .edges _ => 0
  | .left _ => 0
  | .right _ spent => spent

/-- Exact independent-semantics cost of one record phase. -/
def phaseSteps : Phase → List CliqueSym → Nat
  | .edges vertexCount, [] => vertexCount + 5
  | .edges vertexCount, .edgeMark :: rest =>
      phaseSteps (.left vertexCount) rest + 1
  | .edges vertexCount, _ :: rest =>
      phaseSteps (.edges vertexCount) rest + 1
  | .left vertexCount, [] => vertexCount + 6
  | .left vertexCount, .pairSep :: rest =>
      phaseSteps (.right vertexCount 0) rest + 1
  | .left vertexCount, _ :: rest =>
      phaseSteps (.left vertexCount) rest + 1
  | .right remaining spent, [] => remaining + spent + 6
  | .right 0 spent, .tick :: rest => rest.length + spent + 7
  | .right (remaining + 1) spent, .tick :: rest =>
      phaseSteps (.right remaining (spent + 1)) rest + 2
  | .right 0 spent, .recordEnd :: rest => rest.length + spent + 7
  | .right (remaining + 1) spent, .recordEnd :: rest =>
      phaseSteps (.edges (remaining + (spent + 1))) rest + spent + 4
  | .right remaining spent, _ :: rest =>
      phaseSteps (.right remaining spent) rest + 1

/-- Exact run of all edge, left-endpoint, and right-endpoint phases. -/
def phase_run (phase : Phase) (input : List CliqueSym)
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (phaseLabel phase) buffer₁ buffer₂ test (input.map some) []
        (List.replicate (phaseRemaining phase) (some .tick))
        (List.replicate (phaseSpent phase) (some .tick)))
      (some (haltCfg program [phaseResult phase input]))
      (phaseSteps phase input) := by
  induction input generalizing phase buffer₁ buffer₂ test with
  | nil =>
      cases phase with
      | edges vertexCount =>
          let after := cfg (.clearWork₁ true) none buffer₂ test [] []
            (List.replicate vertexCount (some .tick)) []
          have first : EvalsToInTime (step program)
              (cfg .edges buffer₁ buffer₂ test [] []
                (List.replicate vertexCount (some .tick)) [])
              (some after) 1 := by
            exact ⟨⟨1, by
              simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
          have rest := clearWork₁_run true
            (List.replicate vertexCount (some .tick)) [] none buffer₂ test
          have rest' : EvalsToInTime (step program) after
              (some (haltCfg program [true])) (vertexCount + 4) := by
            simpa using rest
          let full := EvalsToInTime.trans (step program)
            1 (vertexCount + 4) _ after _ first rest'
          simpa [phaseLabel, phaseRemaining, phaseSpent, phaseResult,
            phaseSteps, edgesResult] using full
      | left vertexCount =>
          let after := cfg (.clearInput false) none buffer₂ test [] []
            (List.replicate vertexCount (some .tick)) []
          have first : EvalsToInTime (step program)
              (cfg .left buffer₁ buffer₂ test [] []
                (List.replicate vertexCount (some .tick)) [])
              (some after) 1 := by
            exact ⟨⟨1, by
              simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
          have rest := clearInput_run false []
            (List.replicate vertexCount (some .tick)) [] none buffer₂ test
          have rest' : EvalsToInTime (step program) after
              (some (haltCfg program [false])) (vertexCount + 5) := by
            simpa using rest
          let full := EvalsToInTime.trans (step program)
            1 (vertexCount + 5) _ after _ first rest'
          simpa [phaseLabel, phaseRemaining, phaseSpent, phaseResult,
            phaseSteps, leftResult] using full
      | right remaining spent =>
          let after := cfg (.clearInput false) none buffer₂ test [] []
            (List.replicate remaining (some .tick))
            (List.replicate spent (some .tick))
          have first : EvalsToInTime (step program)
              (cfg .right buffer₁ buffer₂ test [] []
                (List.replicate remaining (some .tick))
                (List.replicate spent (some .tick)))
              (some after) 1 := by
            exact ⟨⟨1, by
              simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
          have rest := clearInput_run false []
            (List.replicate remaining (some .tick))
            (List.replicate spent (some .tick)) none buffer₂ test
          have rest' : EvalsToInTime (step program) after
              (some (haltCfg program [false]))
              (remaining + spent + 5) := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rest
          let full := EvalsToInTime.trans (step program)
            1 (remaining + spent + 5) _ after _ first rest'
          simpa [phaseLabel, phaseRemaining, phaseSpent, phaseResult,
            phaseSteps, rightResult, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using full
  | cons symbol input ih =>
      cases phase with
      | edges vertexCount =>
          have ordinary (symbol : CliqueSym) (h : symbol ≠ .edgeMark) :
              EvalsToInTime (step program)
                (cfg .edges buffer₁ buffer₂ test
                  ((symbol :: input).map some) []
                  (List.replicate vertexCount (some .tick)) [])
                (some (haltCfg program
                  [phaseResult (.edges vertexCount) (symbol :: input)]))
                (phaseSteps (.edges vertexCount) (symbol :: input)) := by
            let after := cfg .edges (some (some symbol)) buffer₂ test
              (input.map some) []
              (List.replicate vertexCount (some .tick)) []
            have first : EvalsToInTime (step program)
                (cfg .edges buffer₁ buffer₂ test
                  ((symbol :: input).map some) []
                  (List.replicate vertexCount (some .tick)) [])
                (some after) 1 := by
              exact ⟨⟨1, by
                simp [flip, after, step, program, cfg, stepOp, h]⟩,
                le_rfl⟩
            have rest := ih (phase := Phase.edges vertexCount)
              (buffer₁ := some (some symbol)) (buffer₂ := buffer₂)
              (test := test)
            let full := EvalsToInTime.trans (step program)
              1 (phaseSteps (.edges vertexCount) input) _ after _ first rest
            simpa [phaseLabel, phaseRemaining, phaseSpent, phaseResult,
              phaseSteps, edgesResult, h, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using full
          cases symbol with
          | edgeMark =>
              let after := cfg .left (some (some .edgeMark)) buffer₂ test
                (input.map some) []
                (List.replicate vertexCount (some .tick)) []
              have first : EvalsToInTime (step program)
                  (cfg .edges buffer₁ buffer₂ test
                    ((.edgeMark :: input).map some) []
                    (List.replicate vertexCount (some .tick)) [])
                  (some after) 1 := by
                exact ⟨⟨1, by
                  simp [flip, after, step, program, cfg, stepOp]⟩,
                  le_rfl⟩
              have rest := ih (phase := Phase.left vertexCount)
                (buffer₁ := some (some .edgeMark))
                (buffer₂ := buffer₂) (test := test)
              let full := EvalsToInTime.trans (step program)
                1 (phaseSteps (.left vertexCount) input) _ after _ first rest
              simpa [phaseLabel, phaseRemaining, phaseSpent, phaseResult,
                phaseSteps, edgesResult, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using full
          | instanceMark => exact ordinary .instanceMark (by decide)
          | certificateMark => exact ordinary .certificateMark (by decide)
          | tick => exact ordinary .tick (by decide)
          | fieldSep => exact ordinary .fieldSep (by decide)
          | vertexMark => exact ordinary .vertexMark (by decide)
          | pairSep => exact ordinary .pairSep (by decide)
          | recordEnd => exact ordinary .recordEnd (by decide)
      | left vertexCount =>
          have ordinary (symbol : CliqueSym) (h : symbol ≠ .pairSep) :
              EvalsToInTime (step program)
                (cfg .left buffer₁ buffer₂ test
                  ((symbol :: input).map some) []
                  (List.replicate vertexCount (some .tick)) [])
                (some (haltCfg program
                  [phaseResult (.left vertexCount) (symbol :: input)]))
                (phaseSteps (.left vertexCount) (symbol :: input)) := by
            let after := cfg .left (some (some symbol)) buffer₂ test
              (input.map some) []
              (List.replicate vertexCount (some .tick)) []
            have first : EvalsToInTime (step program)
                (cfg .left buffer₁ buffer₂ test
                  ((symbol :: input).map some) []
                  (List.replicate vertexCount (some .tick)) [])
                (some after) 1 := by
              exact ⟨⟨1, by
                simp [flip, after, step, program, cfg, stepOp, h]⟩,
                le_rfl⟩
            have rest := ih (phase := Phase.left vertexCount)
              (buffer₁ := some (some symbol)) (buffer₂ := buffer₂)
              (test := test)
            let full := EvalsToInTime.trans (step program)
              1 (phaseSteps (.left vertexCount) input) _ after _ first rest
            simpa [phaseLabel, phaseRemaining, phaseSpent, phaseResult,
              phaseSteps, leftResult, h, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using full
          cases symbol with
          | pairSep =>
              let after := cfg .right (some (some .pairSep)) buffer₂ test
                (input.map some) []
                (List.replicate vertexCount (some .tick)) []
              have first : EvalsToInTime (step program)
                  (cfg .left buffer₁ buffer₂ test
                    ((.pairSep :: input).map some) []
                    (List.replicate vertexCount (some .tick)) [])
                  (some after) 1 := by
                exact ⟨⟨1, by
                  simp [flip, after, step, program, cfg, stepOp]⟩,
                  le_rfl⟩
              have rest := ih (phase := Phase.right vertexCount 0)
                (buffer₁ := some (some .pairSep))
                (buffer₂ := buffer₂) (test := test)
              let full := EvalsToInTime.trans (step program)
                1 (phaseSteps (.right vertexCount 0) input)
                _ after _ first rest
              simpa [phaseLabel, phaseRemaining, phaseSpent, phaseResult,
                phaseSteps, leftResult, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using full
          | instanceMark => exact ordinary .instanceMark (by decide)
          | certificateMark => exact ordinary .certificateMark (by decide)
          | tick => exact ordinary .tick (by decide)
          | fieldSep => exact ordinary .fieldSep (by decide)
          | edgeMark => exact ordinary .edgeMark (by decide)
          | vertexMark => exact ordinary .vertexMark (by decide)
          | recordEnd => exact ordinary .recordEnd (by decide)
      | right remaining spent =>
          have ordinary (symbol : CliqueSym) (htick : symbol ≠ .tick)
              (hend : symbol ≠ .recordEnd) :
              EvalsToInTime (step program)
                (cfg .right buffer₁ buffer₂ test
                  ((symbol :: input).map some) []
                  (List.replicate remaining (some .tick))
                  (List.replicate spent (some .tick)))
                (some (haltCfg program
                  [phaseResult (.right remaining spent) (symbol :: input)]))
                (phaseSteps (.right remaining spent) (symbol :: input)) := by
            let after := cfg .right (some (some symbol)) buffer₂ test
              (input.map some) []
              (List.replicate remaining (some .tick))
              (List.replicate spent (some .tick))
            have first : EvalsToInTime (step program)
                (cfg .right buffer₁ buffer₂ test
                  ((symbol :: input).map some) []
                  (List.replicate remaining (some .tick))
                  (List.replicate spent (some .tick)))
                (some after) 1 := by
              exact ⟨⟨1, by
                simp [flip, after, step, program, cfg, stepOp, htick, hend]⟩,
                le_rfl⟩
            have rest := ih (phase := Phase.right remaining spent)
              (buffer₁ := some (some symbol)) (buffer₂ := buffer₂)
              (test := test)
            let full := EvalsToInTime.trans (step program)
              1 (phaseSteps (.right remaining spent) input)
              _ after _ first rest
            simpa [phaseLabel, phaseRemaining, phaseSpent, phaseResult,
              phaseSteps, rightResult, htick, hend, Nat.add_assoc,
              Nat.add_comm, Nat.add_left_comm] using full
          cases symbol with
          | tick =>
              let afterPop := cfg .spendTick (some (some .tick)) buffer₂
                test (input.map some) []
                (List.replicate remaining (some .tick))
                (List.replicate spent (some .tick))
              have first : EvalsToInTime (step program)
                  (cfg .right buffer₁ buffer₂ test
                    ((.tick :: input).map some) []
                    (List.replicate remaining (some .tick))
                    (List.replicate spent (some .tick)))
                  (some afterPop) 1 := by
                exact ⟨⟨1, by
                  simp [flip, afterPop, step, program, cfg, stepOp]⟩,
                  le_rfl⟩
              cases remaining with
              | zero =>
                  let afterSpend := cfg (.clearInput false) none buffer₂
                    test (input.map some) [] []
                    (List.replicate spent (some .tick))
                  have second : EvalsToInTime (step program) afterPop
                      (some afterSpend) 1 := by
                    exact ⟨⟨1, by
                      simp [flip, afterPop, afterSpend, step, program, cfg,
                        stepOp]⟩, le_rfl⟩
                  have rest := clearInput_run false (input.map some) []
                    (List.replicate spent (some .tick)) none buffer₂ test
                  have rest' : EvalsToInTime (step program) afterSpend
                      (some (haltCfg program [false]))
                      (input.length + spent + 5) := by
                    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                      using rest
                  let throughSpend := EvalsToInTime.trans (step program)
                    1 1 _ afterPop _ first second
                  let full := EvalsToInTime.trans (step program)
                    2 (input.length + spent + 5)
                    _ afterSpend _ throughSpend rest'
                  simpa [phaseLabel, phaseRemaining, phaseSpent, phaseResult,
                    phaseSteps, rightResult, Nat.add_assoc, Nat.add_comm,
                    Nat.add_left_comm] using full
              | succ remaining =>
                  let afterSpend := cfg .right (some (some .tick)) buffer₂
                    test (input.map some) []
                    (List.replicate remaining (some .tick))
                    (List.replicate (spent + 1) (some .tick))
                  have second : EvalsToInTime (step program) afterPop
                      (some afterSpend) 1 := by
                    exact ⟨⟨1, by
                      simp [flip, afterPop, afterSpend, step, program, cfg,
                        stepOp, List.replicate_succ]⟩, le_rfl⟩
                  have rest := ih
                    (phase := Phase.right remaining (spent + 1))
                    (buffer₁ := some (some .tick))
                    (buffer₂ := buffer₂) (test := test)
                  let throughSpend := EvalsToInTime.trans (step program)
                    1 1 _ afterPop _ first second
                  let full := EvalsToInTime.trans (step program)
                    2 (phaseSteps (.right remaining (spent + 1)) input)
                    _ afterSpend _ throughSpend rest
                  simpa [phaseLabel, phaseRemaining, phaseSpent, phaseResult,
                    phaseSteps, rightResult, Nat.add_assoc, Nat.add_comm,
                    Nat.add_left_comm] using full
          | recordEnd =>
              let afterPop := cfg .demandStrict (some (some .recordEnd))
                buffer₂ test (input.map some) []
                (List.replicate remaining (some .tick))
                (List.replicate spent (some .tick))
              have first : EvalsToInTime (step program)
                  (cfg .right buffer₁ buffer₂ test
                    ((.recordEnd :: input).map some) []
                    (List.replicate remaining (some .tick))
                    (List.replicate spent (some .tick)))
                  (some afterPop) 1 := by
                exact ⟨⟨1, by
                  simp [flip, afterPop, step, program, cfg, stepOp]⟩,
                  le_rfl⟩
              cases remaining with
              | zero =>
                  let afterDemand := cfg (.clearInput false) none buffer₂
                    test (input.map some) [] []
                    (List.replicate spent (some .tick))
                  have second : EvalsToInTime (step program) afterPop
                      (some afterDemand) 1 := by
                    exact ⟨⟨1, by
                      simp [flip, afterPop, afterDemand, step, program, cfg,
                        stepOp]⟩, le_rfl⟩
                  have rest := clearInput_run false (input.map some) []
                    (List.replicate spent (some .tick)) none buffer₂ test
                  have rest' : EvalsToInTime (step program) afterDemand
                      (some (haltCfg program [false]))
                      (input.length + spent + 5) := by
                    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                      using rest
                  let throughDemand := EvalsToInTime.trans (step program)
                    1 1 _ afterPop _ first second
                  let full := EvalsToInTime.trans (step program)
                    2 (input.length + spent + 5)
                    _ afterDemand _ throughDemand rest'
                  simpa [phaseLabel, phaseRemaining, phaseSpent, phaseResult,
                    phaseSteps, rightResult, Nat.add_assoc, Nat.add_comm,
                    Nat.add_left_comm] using full
              | succ remaining =>
                  let afterDemand := cfg .restore (some (some .tick)) buffer₂
                    test (input.map some) []
                    (List.replicate remaining (some .tick))
                    (List.replicate (spent + 1) (some .tick))
                  have second : EvalsToInTime (step program) afterPop
                      (some afterDemand) 1 := by
                    exact ⟨⟨1, by
                      simp [flip, afterPop, afterDemand, step, program, cfg,
                        stepOp, List.replicate_succ]⟩, le_rfl⟩
                  have restored := restore_run remaining (spent + 1)
                    (input.map some) (some (some .tick)) buffer₂ test
                  let afterRestore := cfg .edges (some (some .tick)) none test
                    (input.map some) []
                    (List.replicate (remaining + (spent + 1))
                      (some .tick)) []
                  have rest := ih
                    (phase := Phase.edges (remaining + (spent + 1)))
                    (buffer₁ := some (some .tick)) (buffer₂ := none)
                    (test := test)
                  let throughDemand := EvalsToInTime.trans (step program)
                    1 1 _ afterPop _ first second
                  let throughRestore := EvalsToInTime.trans (step program)
                    2 (spent + 2) _ afterDemand _ throughDemand restored
                  let full := EvalsToInTime.trans (step program)
                    (spent + 4)
                    (phaseSteps (.edges (remaining + (spent + 1))) input)
                    _ afterRestore _ throughRestore rest
                  simpa [afterRestore, phaseLabel, phaseRemaining, phaseSpent,
                    phaseResult, phaseSteps, rightResult, Nat.add_assoc,
                    Nat.add_comm, Nat.add_left_comm] using full
          | instanceMark =>
              exact ordinary .instanceMark (by decide) (by decide)
          | certificateMark =>
              exact ordinary .certificateMark (by decide) (by decide)
          | fieldSep => exact ordinary .fieldSep (by decide) (by decide)
          | edgeMark => exact ordinary .edgeMark (by decide) (by decide)
          | vertexMark => exact ordinary .vertexMark (by decide) (by decide)
          | pairSep => exact ordinary .pairSep (by decide) (by decide)

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.EndpointBound

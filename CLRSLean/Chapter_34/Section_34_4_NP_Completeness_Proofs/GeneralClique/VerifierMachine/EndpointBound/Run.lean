import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.EndpointBound.Phases

/-!
# General CLIQUE verifier: complete endpoint-bound run
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.EndpointBound

open PolyBuilder

def targetFieldSteps (vertexCount : Nat) : List CliqueSym → Nat
  | [] => vertexCount + 6
  | .fieldSep :: rest => phaseSteps (.edges vertexCount) rest + 1
  | _ :: rest => targetFieldSteps vertexCount rest + 1

def vertexFieldSteps : Nat → List CliqueSym → Nat
  | loaded, [] => loaded + 6
  | loaded, .tick :: rest => vertexFieldSteps (loaded + 1) rest + 2
  | loaded, .fieldSep :: rest => targetFieldSteps loaded rest + 1
  | loaded, _ :: rest => vertexFieldSteps loaded rest + 1

def instanceSteps : List CliqueSym → Nat
  | [] => 6
  | _ :: rest => vertexFieldSteps 0 rest + 1

private def targetField_run (vertexCount : Nat) (input : List CliqueSym)
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .targetField buffer₁ buffer₂ test (input.map some) []
        (List.replicate vertexCount (some .tick)) [])
      (some (haltCfg program [targetFieldResult vertexCount input]))
      (targetFieldSteps vertexCount input) := by
  induction input generalizing buffer₁ buffer₂ test with
  | nil =>
      let after := cfg (.clearInput false) none buffer₂ test [] []
        (List.replicate vertexCount (some .tick)) []
      have first : EvalsToInTime (step program)
          (cfg .targetField buffer₁ buffer₂ test [] []
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
      simpa [targetFieldResult, targetFieldSteps] using full
  | cons symbol input ih =>
      have ordinary (symbol : CliqueSym) (h : symbol ≠ .fieldSep) :
          EvalsToInTime (step program)
            (cfg .targetField buffer₁ buffer₂ test
              ((symbol :: input).map some) []
              (List.replicate vertexCount (some .tick)) [])
            (some (haltCfg program
              [targetFieldResult vertexCount (symbol :: input)]))
            (targetFieldSteps vertexCount (symbol :: input)) := by
        let after := cfg .targetField (some (some symbol)) buffer₂ test
          (input.map some) []
          (List.replicate vertexCount (some .tick)) []
        have first : EvalsToInTime (step program)
            (cfg .targetField buffer₁ buffer₂ test
              ((symbol :: input).map some) []
              (List.replicate vertexCount (some .tick)) [])
            (some after) 1 := by
          exact ⟨⟨1, by
            simp [flip, after, step, program, cfg, stepOp, h]⟩, le_rfl⟩
        have rest := ih (buffer₁ := some (some symbol))
          (buffer₂ := buffer₂) (test := test)
        let full := EvalsToInTime.trans (step program)
          1 (targetFieldSteps vertexCount input) _ after _ first rest
        simpa [targetFieldResult, targetFieldSteps, h, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using full
      cases symbol with
      | fieldSep =>
          let after := cfg .edges (some (some .fieldSep)) buffer₂ test
            (input.map some) []
            (List.replicate vertexCount (some .tick)) []
          have first : EvalsToInTime (step program)
              (cfg .targetField buffer₁ buffer₂ test
                ((.fieldSep :: input).map some) []
                (List.replicate vertexCount (some .tick)) [])
              (some after) 1 := by
            exact ⟨⟨1, by
              simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
          have rest := phase_run (Phase.edges vertexCount) input
            (some (some .fieldSep)) buffer₂ test
          let full := EvalsToInTime.trans (step program)
            1 (phaseSteps (.edges vertexCount) input) _ after _ first rest
          simpa [targetFieldResult, targetFieldSteps, phaseLabel,
            phaseRemaining, phaseSpent, phaseResult, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using full
      | instanceMark => exact ordinary .instanceMark (by decide)
      | certificateMark => exact ordinary .certificateMark (by decide)
      | tick => exact ordinary .tick (by decide)
      | edgeMark => exact ordinary .edgeMark (by decide)
      | vertexMark => exact ordinary .vertexMark (by decide)
      | pairSep => exact ordinary .pairSep (by decide)
      | recordEnd => exact ordinary .recordEnd (by decide)

private def vertexField_run (loaded : Nat) (input : List CliqueSym)
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .vertexField buffer₁ buffer₂ test (input.map some) []
        (List.replicate loaded (some .tick)) [])
      (some (haltCfg program [vertexFieldResult loaded input]))
      (vertexFieldSteps loaded input) := by
  induction input generalizing loaded buffer₁ buffer₂ test with
  | nil =>
      let after := cfg (.clearInput false) none buffer₂ test [] []
        (List.replicate loaded (some .tick)) []
      have first : EvalsToInTime (step program)
          (cfg .vertexField buffer₁ buffer₂ test [] []
            (List.replicate loaded (some .tick)) [])
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := clearInput_run false []
        (List.replicate loaded (some .tick)) [] none buffer₂ test
      have rest' : EvalsToInTime (step program) after
          (some (haltCfg program [false])) (loaded + 5) := by
        simpa using rest
      let full := EvalsToInTime.trans (step program)
        1 (loaded + 5) _ after _ first rest'
      simpa [vertexFieldResult, vertexFieldSteps] using full
  | cons symbol input ih =>
      have ordinary (symbol : CliqueSym) (htick : symbol ≠ .tick)
          (hsep : symbol ≠ .fieldSep) :
          EvalsToInTime (step program)
            (cfg .vertexField buffer₁ buffer₂ test
              ((symbol :: input).map some) []
              (List.replicate loaded (some .tick)) [])
            (some (haltCfg program
              [vertexFieldResult loaded (symbol :: input)]))
            (vertexFieldSteps loaded (symbol :: input)) := by
        let after := cfg .vertexField (some (some symbol)) buffer₂ test
          (input.map some) [] (List.replicate loaded (some .tick)) []
        have first : EvalsToInTime (step program)
            (cfg .vertexField buffer₁ buffer₂ test
              ((symbol :: input).map some) []
              (List.replicate loaded (some .tick)) [])
            (some after) 1 := by
          exact ⟨⟨1, by
            simp [flip, after, step, program, cfg, stepOp, htick, hsep]⟩,
            le_rfl⟩
        have rest := ih (loaded := loaded)
          (buffer₁ := some (some symbol)) (buffer₂ := buffer₂)
          (test := test)
        let full := EvalsToInTime.trans (step program)
          1 (vertexFieldSteps loaded input) _ after _ first rest
        simpa [vertexFieldResult, vertexFieldSteps, htick, hsep,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full
      cases symbol with
      | tick =>
          let afterPop := cfg .saveVertexTick (some (some .tick)) buffer₂
            test (input.map some) []
            (List.replicate loaded (some .tick)) []
          let afterSave := cfg .vertexField (some (some .tick)) buffer₂
            test (input.map some) []
            (List.replicate (loaded + 1) (some .tick)) []
          have first : EvalsToInTime (step program)
              (cfg .vertexField buffer₁ buffer₂ test
                ((.tick :: input).map some) []
                (List.replicate loaded (some .tick)) [])
              (some afterPop) 1 := by
            exact ⟨⟨1, by
              simp [flip, afterPop, step, program, cfg, stepOp]⟩, le_rfl⟩
          have second : EvalsToInTime (step program) afterPop
              (some afterSave) 1 := by
            exact ⟨⟨1, by
              simp [flip, afterPop, afterSave, step, program, cfg, stepOp,
                List.replicate_succ]⟩, le_rfl⟩
          have rest := ih (loaded := loaded + 1)
            (buffer₁ := some (some .tick)) (buffer₂ := buffer₂)
            (test := test)
          let throughSave := EvalsToInTime.trans (step program)
            1 1 _ afterPop _ first second
          let full := EvalsToInTime.trans (step program)
            2 (vertexFieldSteps (loaded + 1) input)
            _ afterSave _ throughSave rest
          simpa [vertexFieldResult, vertexFieldSteps, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using full
      | fieldSep =>
          let after := cfg .targetField (some (some .fieldSep)) buffer₂ test
            (input.map some) [] (List.replicate loaded (some .tick)) []
          have first : EvalsToInTime (step program)
              (cfg .vertexField buffer₁ buffer₂ test
                ((.fieldSep :: input).map some) []
                (List.replicate loaded (some .tick)) [])
              (some after) 1 := by
            exact ⟨⟨1, by
              simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
          have rest := targetField_run loaded input
            (some (some .fieldSep)) buffer₂ test
          let full := EvalsToInTime.trans (step program)
            1 (targetFieldSteps loaded input) _ after _ first rest
          simpa [vertexFieldResult, vertexFieldSteps, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using full
      | instanceMark =>
          exact ordinary .instanceMark (by decide) (by decide)
      | certificateMark =>
          exact ordinary .certificateMark (by decide) (by decide)
      | edgeMark => exact ordinary .edgeMark (by decide) (by decide)
      | vertexMark => exact ordinary .vertexMark (by decide) (by decide)
      | pairSep => exact ordinary .pairSep (by decide) (by decide)
      | recordEnd => exact ordinary .recordEnd (by decide) (by decide)

private def instance_run (input : List CliqueSym)
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .instanceMark buffer₁ buffer₂ test (input.map some) [] [] [])
      (some (haltCfg program [endpointBoundPass [] input]))
      (instanceSteps input) := by
  cases input with
  | nil =>
      let after := cfg (.clearInput false) none buffer₂ test [] [] [] []
      have first : EvalsToInTime (step program)
          (cfg .instanceMark buffer₁ buffer₂ test [] [] [] [])
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := clearInput_run false [] [] [] none buffer₂ test
      let full := EvalsToInTime.trans (step program) 1 5 _ after _ first rest
      simpa [endpointBoundPass, instanceSteps] using full
  | cons marker input =>
      let after := cfg .vertexField (some (some marker)) buffer₂ test
        (input.map some) [] [] []
      have first : EvalsToInTime (step program)
          (cfg .instanceMark buffer₁ buffer₂ test
            ((marker :: input).map some) [] [] [])
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := vertexField_run 0 input
        (some (some marker)) buffer₂ test
      let full := EvalsToInTime.trans (step program)
        1 (vertexFieldSteps 0 input) _ after _ first rest
      simpa [endpointBoundPass, instanceSteps, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full

private def certificate_run (certificate input : List CliqueSym)
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .certificate buffer₁ buffer₂ test
        (certificate.map some ++ none :: input.map some) [] [] [])
      (some (cfg .instanceMark (some none) buffer₂ test
        (input.map some) [] [] []))
      (certificate.length + 1) := by
  induction certificate generalizing buffer₁ with
  | nil =>
      exact ⟨⟨1, by
        simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | cons symbol certificate ih =>
      let after := cfg .certificate (some (some symbol)) buffer₂ test
        (certificate.map some ++ none :: input.map some) [] [] []
      have first : EvalsToInTime (step program)
          (cfg .certificate buffer₁ buffer₂ test
            ((symbol :: certificate).map some ++ none :: input.map some)
            [] [] []) (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := ih (buffer₁ := some (some symbol))
      let full := EvalsToInTime.trans (step program)
        1 (certificate.length + 1) _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

/-- Exact independent-semantics run of the complete endpoint-bound checker. -/
def endpointBound_run (certificate input : List CliqueSym) :
    EvalsToInTime (step program)
      (initialCfg program (pairEncoding certificate input))
      (some (haltCfg program [endpointBoundPass certificate input]))
      (certificate.length + 1 + instanceSteps input) := by
  have first := certificate_run certificate input none none false
  have first' : EvalsToInTime (step program)
      (initialCfg program (pairEncoding certificate input))
      (some (cfg .instanceMark (some none) none false
        (input.map some) [] [] []))
      (certificate.length + 1) := by
    simpa [pairEncoding, initialCfg, cfg, program, List.append_assoc]
      using first
  have second := instance_run input (some none) none false
  let full := EvalsToInTime.trans (step program)
    (certificate.length + 1) (instanceSteps input) _ _ _ first' second
  simpa [endpointBoundPass, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using full

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.EndpointBound

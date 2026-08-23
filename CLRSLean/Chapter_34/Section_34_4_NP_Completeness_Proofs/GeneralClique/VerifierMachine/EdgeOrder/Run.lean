import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.EdgeOrder.Phases

/-!
# General CLIQUE verifier: complete normalized-edge run
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.EdgeOrder

open PolyBuilder

/-- Exact steps while scanning the target-size header field. -/
def targetFieldSteps : List CliqueSym → Nat
  | [] => 4
  | .fieldSep :: rest => phaseSteps .edges rest + 1
  | _ :: rest => targetFieldSteps rest + 1

/-- Exact steps while scanning the vertex-count header field. -/
def vertexFieldSteps : List CliqueSym → Nat
  | [] => 4
  | .fieldSep :: rest => targetFieldSteps rest + 1
  | _ :: rest => vertexFieldSteps rest + 1

/-- Exact steps after entering the instance portion. -/
def instanceSteps : List CliqueSym → Nat
  | [] => 4
  | _ :: rest => vertexFieldSteps rest + 1

private def targetField_run (input : List CliqueSym)
    (buffer : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .targetField buffer test (input.map some) [] [])
      (some (haltCfg program [throughField edgesResult input]))
      (targetFieldSteps input) := by
  induction input generalizing buffer test with
  | nil =>
      let after := cfg (.clearCount false) none test [] [] []
      have first : EvalsToInTime (step program)
          (cfg .targetField buffer test [] [] []) (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := clearCount_run false 0 none test
      let full := EvalsToInTime.trans (step program) 1 3 _ after _ first rest
      simpa [throughField, targetFieldSteps] using full
  | cons symbol input ih =>
      have ordinary (symbol : CliqueSym) (h : symbol ≠ .fieldSep) :
          EvalsToInTime (step program)
            (cfg .targetField buffer test ((symbol :: input).map some) [] [])
            (some (haltCfg program
              [throughField edgesResult (symbol :: input)]))
            (targetFieldSteps (symbol :: input)) := by
        let after := cfg .targetField (some (some symbol)) test
          (input.map some) [] []
        have first : EvalsToInTime (step program)
            (cfg .targetField buffer test ((symbol :: input).map some) [] [])
            (some after) 1 := by
          exact ⟨⟨1, by
            simp [flip, after, step, program, cfg, stepOp, h]⟩, le_rfl⟩
        have rest := ih (buffer := some (some symbol)) (test := test)
        let full := EvalsToInTime.trans (step program)
          1 (targetFieldSteps input) _ after _ first rest
        simpa [throughField, targetFieldSteps, h, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using full
      cases symbol with
      | fieldSep =>
          let after := cfg .edges (some (some .fieldSep)) test
            (input.map some) [] []
          have first : EvalsToInTime (step program)
              (cfg .targetField buffer test
                ((.fieldSep :: input).map some) [] [])
              (some after) 1 := by
            exact ⟨⟨1, by
              simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
          have rest := phase_run Phase.edges input
            (some (some .fieldSep)) test
          let full := EvalsToInTime.trans (step program)
            1 (phaseSteps .edges input) _ after _ first rest
          simpa [throughField, targetFieldSteps, phaseLabel, phaseCount,
            phaseResult, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using full
      | instanceMark => exact ordinary .instanceMark (by decide)
      | certificateMark => exact ordinary .certificateMark (by decide)
      | tick => exact ordinary .tick (by decide)
      | edgeMark => exact ordinary .edgeMark (by decide)
      | vertexMark => exact ordinary .vertexMark (by decide)
      | pairSep => exact ordinary .pairSep (by decide)
      | recordEnd => exact ordinary .recordEnd (by decide)

private def vertexField_run (input : List CliqueSym)
    (buffer : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .vertexField buffer test (input.map some) [] [])
      (some (haltCfg program
        [throughField (throughField edgesResult) input]))
      (vertexFieldSteps input) := by
  induction input generalizing buffer test with
  | nil =>
      let after := cfg (.clearCount false) none test [] [] []
      have first : EvalsToInTime (step program)
          (cfg .vertexField buffer test [] [] []) (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := clearCount_run false 0 none test
      let full := EvalsToInTime.trans (step program) 1 3 _ after _ first rest
      simpa [throughField, vertexFieldSteps] using full
  | cons symbol input ih =>
      have ordinary (symbol : CliqueSym) (h : symbol ≠ .fieldSep) :
          EvalsToInTime (step program)
            (cfg .vertexField buffer test ((symbol :: input).map some) [] [])
            (some (haltCfg program
              [throughField (throughField edgesResult) (symbol :: input)]))
            (vertexFieldSteps (symbol :: input)) := by
        let after := cfg .vertexField (some (some symbol)) test
          (input.map some) [] []
        have first : EvalsToInTime (step program)
            (cfg .vertexField buffer test ((symbol :: input).map some) [] [])
            (some after) 1 := by
          exact ⟨⟨1, by
            simp [flip, after, step, program, cfg, stepOp, h]⟩, le_rfl⟩
        have rest := ih (buffer := some (some symbol)) (test := test)
        let full := EvalsToInTime.trans (step program)
          1 (vertexFieldSteps input) _ after _ first rest
        simpa [throughField, vertexFieldSteps, h, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using full
      cases symbol with
      | fieldSep =>
          let after := cfg .targetField (some (some .fieldSep)) test
            (input.map some) [] []
          have first : EvalsToInTime (step program)
              (cfg .vertexField buffer test
                ((.fieldSep :: input).map some) [] [])
              (some after) 1 := by
            exact ⟨⟨1, by
              simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
          have rest := targetField_run input (some (some .fieldSep)) test
          let full := EvalsToInTime.trans (step program)
            1 (targetFieldSteps input) _ after _ first rest
          simpa [throughField, vertexFieldSteps, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using full
      | instanceMark => exact ordinary .instanceMark (by decide)
      | certificateMark => exact ordinary .certificateMark (by decide)
      | tick => exact ordinary .tick (by decide)
      | edgeMark => exact ordinary .edgeMark (by decide)
      | vertexMark => exact ordinary .vertexMark (by decide)
      | pairSep => exact ordinary .pairSep (by decide)
      | recordEnd => exact ordinary .recordEnd (by decide)

private def instance_run (input : List CliqueSym)
    (buffer : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .instanceMark buffer test (input.map some) [] [])
      (some (haltCfg program [edgeOrderPass [] input]))
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
      simpa [edgeOrderPass, instanceSteps] using full
  | cons marker input =>
      let after := cfg .vertexField (some (some marker)) test
        (input.map some) [] []
      have first : EvalsToInTime (step program)
          (cfg .instanceMark buffer test ((marker :: input).map some) [] [])
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := vertexField_run input (some (some marker)) test
      let full := EvalsToInTime.trans (step program)
        1 (vertexFieldSteps input) _ after _ first rest
      simpa [edgeOrderPass, instanceSteps, Nat.add_assoc, Nat.add_comm,
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

/-- Exact independent-semantics run of the complete normalized-edge checker. -/
def edgeOrder_run (certificate input : List CliqueSym) :
    EvalsToInTime (step program)
      (initialCfg program (pairEncoding certificate input))
      (some (haltCfg program [edgeOrderPass certificate input]))
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
  simpa [edgeOrderPass, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using full

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.EdgeOrder

import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.CertificateRange.Header

/-!
# General CLIQUE verifier: complete certificate-range run
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.CertificateRange

open PolyBuilder

/-- Exact steps for scanning the instance vertex-count field. -/
def vertexFieldSteps (certificate : List CliqueSym) :
    Nat → List CliqueSym → Nat
  | loaded, [] => certificate.length + loaded + 7
  | loaded, .tick :: rest => vertexFieldSteps certificate (loaded + 1) rest + 2
  | loaded, .fieldSep :: rest =>
      finishCertificateSteps loaded certificate rest + 1
  | loaded, _ :: rest => vertexFieldSteps certificate loaded rest + 1

/-- Exact steps after the certificate has been saved. -/
def instanceSteps (certificate : List CliqueSym) : List CliqueSym → Nat
  | [] => certificate.length + 7
  | _ :: rest => vertexFieldSteps certificate 0 rest + 1

private def vertexField_run (certificate : List CliqueSym) (loaded : Nat)
    (input : List CliqueSym)
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .vertexField buffer₁ buffer₂ test (input.map some) []
        (certificate.map some).reverse
        (List.replicate loaded (some .tick)) [])
      (some (haltCfg program
        [vertexFieldResult certificate loaded input]))
      (vertexFieldSteps certificate loaded input) := by
  induction input generalizing loaded buffer₁ buffer₂ test with
  | nil =>
      let after := cfg (.clearInput false) none buffer₂ test [] []
        (certificate.map some).reverse
        (List.replicate loaded (some .tick)) []
      have first : EvalsToInTime (step program)
          (cfg .vertexField buffer₁ buffer₂ test [] []
            (certificate.map some).reverse
            (List.replicate loaded (some .tick)) [])
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := clearInput_run false [] (certificate.map some).reverse
        (List.replicate loaded (some .tick)) 0 none buffer₂ test
      have rest' : EvalsToInTime (step program) after
          (some (haltCfg program [false]))
          (certificate.length + loaded + 6) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rest
      let full := EvalsToInTime.trans (step program)
        1 (certificate.length + loaded + 6) _ after _ first rest'
      simpa [vertexFieldResult, vertexFieldSteps, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using full
  | cons symbol input ih =>
      have ordinary (symbol : CliqueSym) (htick : symbol ≠ .tick)
          (hsep : symbol ≠ .fieldSep) :
          EvalsToInTime (step program)
            (cfg .vertexField buffer₁ buffer₂ test
              ((symbol :: input).map some) []
              (certificate.map some).reverse
              (List.replicate loaded (some .tick)) [])
            (some (haltCfg program
              [vertexFieldResult certificate loaded (symbol :: input)]))
            (vertexFieldSteps certificate loaded (symbol :: input)) := by
        let after := cfg .vertexField (some (some symbol)) buffer₂ test
          (input.map some) [] (certificate.map some).reverse
          (List.replicate loaded (some .tick)) []
        have first : EvalsToInTime (step program)
            (cfg .vertexField buffer₁ buffer₂ test
              ((symbol :: input).map some) []
              (certificate.map some).reverse
              (List.replicate loaded (some .tick)) [])
            (some after) 1 := by
          exact ⟨⟨1, by
            simp [flip, after, step, program, cfg, stepOp, htick, hsep]⟩,
            le_rfl⟩
        have rest := ih (loaded := loaded)
          (buffer₁ := some (some symbol)) (buffer₂ := buffer₂)
          (test := test)
        let full := EvalsToInTime.trans (step program)
          1 (vertexFieldSteps certificate loaded input)
          _ after _ first rest
        simpa [vertexFieldResult, vertexFieldSteps, htick, hsep,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full
      cases symbol with
      | tick =>
          let afterPop := cfg .saveVertexTick (some (some .tick)) buffer₂
            test (input.map some) [] (certificate.map some).reverse
            (List.replicate loaded (some .tick)) []
          let afterSave := cfg .vertexField (some (some .tick)) buffer₂
            test (input.map some) [] (certificate.map some).reverse
            (List.replicate (loaded + 1) (some .tick)) []
          have first : EvalsToInTime (step program)
              (cfg .vertexField buffer₁ buffer₂ test
                ((.tick :: input).map some) []
                (certificate.map some).reverse
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
          have throughSave := EvalsToInTime.trans (step program)
            1 1 _ afterPop _ first second
          let full := EvalsToInTime.trans (step program)
            2 (vertexFieldSteps certificate (loaded + 1) input)
            _ afterSave _ throughSave rest
          simpa [vertexFieldResult, vertexFieldSteps, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using full
      | fieldSep =>
          let after := cfg .discardInstance (some (some .fieldSep)) buffer₂
            test (input.map some) [] (certificate.map some).reverse
            (List.replicate loaded (some .tick)) []
          have first : EvalsToInTime (step program)
              (cfg .vertexField buffer₁ buffer₂ test
                ((.fieldSep :: input).map some) []
                (certificate.map some).reverse
                (List.replicate loaded (some .tick)) [])
              (some after) 1 := by
            exact ⟨⟨1, by
              simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
          have rest := finishCertificate_run loaded certificate input
            (some (some .fieldSep)) buffer₂ test
          let full := EvalsToInTime.trans (step program)
            1 (finishCertificateSteps loaded certificate input)
            _ after _ first rest
          simpa [vertexFieldResult, vertexFieldSteps, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using full
      | instanceMark => exact ordinary .instanceMark (by decide) (by decide)
      | certificateMark =>
          exact ordinary .certificateMark (by decide) (by decide)
      | edgeMark => exact ordinary .edgeMark (by decide) (by decide)
      | vertexMark => exact ordinary .vertexMark (by decide) (by decide)
      | pairSep => exact ordinary .pairSep (by decide) (by decide)
      | recordEnd => exact ordinary .recordEnd (by decide) (by decide)

private def instance_run (certificate input : List CliqueSym)
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .instanceMark buffer₁ buffer₂ test (input.map some) []
        (certificate.map some).reverse [] [])
      (some (haltCfg program [certificateRangePass certificate input]))
      (instanceSteps certificate input) := by
  cases input with
  | nil =>
      let after := cfg (.clearInput false) none buffer₂ test [] []
        (certificate.map some).reverse [] []
      have first : EvalsToInTime (step program)
          (cfg .instanceMark buffer₁ buffer₂ test [] []
            (certificate.map some).reverse [] [])
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := clearInput_run false [] (certificate.map some).reverse []
        0 none buffer₂ test
      have rest' : EvalsToInTime (step program) after
          (some (haltCfg program [false])) (certificate.length + 6) := by
        simpa using rest
      let full := EvalsToInTime.trans (step program)
        1 (certificate.length + 6) _ after _ first rest'
      simpa [certificateRangePass, instanceSteps, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using full
  | cons marker input =>
      let after := cfg .vertexField (some (some marker)) buffer₂ test
        (input.map some) [] (certificate.map some).reverse [] []
      have first : EvalsToInTime (step program)
          (cfg .instanceMark buffer₁ buffer₂ test
            ((marker :: input).map some) []
            (certificate.map some).reverse [] [])
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := vertexField_run certificate 0 input
        (some (some marker)) buffer₂ test
      let full := EvalsToInTime.trans (step program)
        1 (vertexFieldSteps certificate 0 input) _ after _ first rest
      simpa [certificateRangePass, instanceSteps, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using full

private def saveCertificate_run_aux (certificate input : List CliqueSym)
    (saved : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .saveCertificate buffer₁ buffer₂ test
        (certificate.map some ++ none :: input.map some) [] saved [] [])
      (some (cfg .instanceMark (some none) buffer₂ test
        (input.map some) [] ((certificate.map some).reverse ++ saved) [] []))
      (2 * certificate.length + 1) := by
  induction certificate generalizing saved buffer₁ with
  | nil =>
      exact ⟨⟨1, by
        simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | cons symbol certificate ih =>
      let afterPop := cfg (.saveCertificateSymbol (some symbol))
        (some (some symbol)) buffer₂ test
        (certificate.map some ++ none :: input.map some) [] saved [] []
      let afterSave := cfg .saveCertificate (some (some symbol)) buffer₂ test
        (certificate.map some ++ none :: input.map some) []
        (some symbol :: saved) [] []
      have first : EvalsToInTime (step program)
          (cfg .saveCertificate buffer₁ buffer₂ test
            ((symbol :: certificate).map some ++ none :: input.map some)
            [] saved [] []) (some afterPop) 1 := by
        exact ⟨⟨1, by
          simp [flip, afterPop, step, program, cfg, stepOp]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterPop
          (some afterSave) 1 := by
        exact ⟨⟨1, by
          simp [flip, afterPop, afterSave, step, program, cfg, stepOp]⟩,
          le_rfl⟩
      have rest := ih (saved := some symbol :: saved)
        (buffer₁ := some (some symbol))
      have throughSave := EvalsToInTime.trans (step program)
        1 1 _ afterPop _ first second
      let full := EvalsToInTime.trans (step program)
        2 (2 * certificate.length + 1) _ afterSave _ throughSave rest
      simpa [List.reverse_cons, List.append_assoc, Nat.mul_succ,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

/-- Exact independent-semantics run of the complete certificate-range checker. -/
def certificateRange_run (certificate input : List CliqueSym) :
    EvalsToInTime (step program)
      (initialCfg program (pairEncoding certificate input))
      (some (haltCfg program [certificateRangePass certificate input]))
      (2 * certificate.length + 1 + instanceSteps certificate input) := by
  have first := saveCertificate_run_aux certificate input [] none none false
  have first' : EvalsToInTime (step program)
      (initialCfg program (pairEncoding certificate input))
      (some (cfg .instanceMark (some none) none false
        (input.map some) [] (certificate.map some).reverse [] []))
      (2 * certificate.length + 1) := by
    simpa [pairEncoding, initialCfg, cfg, program, List.append_assoc]
      using first
  have second := instance_run certificate input (some none) none false
  let full := EvalsToInTime.trans (step program)
    (2 * certificate.length + 1) (instanceSteps certificate input)
    _ _ _ first' second
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.CertificateRange

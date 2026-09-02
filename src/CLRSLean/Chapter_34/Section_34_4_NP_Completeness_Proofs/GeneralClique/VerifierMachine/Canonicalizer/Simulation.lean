import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.Canonicalizer.Basic
import Mathlib.Tactic

/-!
# Raw-input canonicalizer: local simulations
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.Canonicalizer

open PolyBuilder

/-- Scanning stores the input in reverse order while updating the parser. -/
def scan_run (kind : Kind) (mode : ParseMode)
    (input output work : List CliqueSym)
    (buffer₁ buffer₂ : Option CliqueSym) (test : Bool) :
    Σ finalBuffer,
      EvalsToInTime (step (program kind))
        (cfg kind (.scan mode) buffer₁ buffer₂ test input output work [])
        (some (cfg kind
          (.scan (scanSymbols mode input)) finalBuffer buffer₂ test [] output
          (input.reverse ++ work) []))
        (2 * input.length) := by
  induction input generalizing mode work buffer₁ with
  | nil =>
      exact ⟨buffer₁, ⟨⟨0, by simp [scanSymbols, cfg]⟩, le_rfl⟩⟩
  | cons symbol input ih =>
      have first : EvalsToInTime (step (program kind))
          (cfg kind (.scan mode) buffer₁ buffer₂ test
            (symbol :: input) output work [])
          (some (cfg kind (.scan (stepSymbol mode symbol))
            (some symbol) buffer₂ test input output (symbol :: work) [])) 2 :=
        ⟨⟨2, rfl⟩, le_rfl⟩
      rcases ih (stepSymbol mode symbol) (symbol :: work)
          (some symbol) with ⟨finalBuffer, rest⟩
      let full := EvalsToInTime.trans (step (program kind))
        2 (2 * input.length) _ _ _ first rest
      refine ⟨finalBuffer, ?_⟩
      simpa [scanSymbols, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

/-- Restoring a reversed work stack reproduces the original input order. -/
def restore_run (kind : Kind) (input output : List CliqueSym)
    (buffer₁ buffer₂ : Option CliqueSym) (test : Bool) :
    EvalsToInTime (step (program kind))
      (cfg kind .restore buffer₁ buffer₂ test [] output input [])
      (some (haltCfg (program kind) (input.reverse ++ output)))
      (2 * input.length + 2) := by
  induction input generalizing output buffer₁ with
  | nil =>
      exact ⟨⟨2, by
        simp [Function.iterate_succ_apply, flip, step, program, cfg,
          stepOp, haltCfg]⟩, le_rfl⟩
  | cons symbol input ih =>
      let afterPop := cfg kind (.emit symbol) (some symbol) buffer₂ test
        [] output input []
      let afterEmit := cfg kind .restore (some symbol) buffer₂ test
        [] (symbol :: output) input []
      have first : EvalsToInTime (step (program kind))
          (cfg kind .restore buffer₁ buffer₂ test [] output
            (symbol :: input) [])
          (some afterPop) 1 :=
        ⟨⟨1, by simp [flip, afterPop, step, program, cfg, stepOp]⟩,
          le_rfl⟩
      have second : EvalsToInTime (step (program kind)) afterPop
          (some afterEmit) 1 :=
        ⟨⟨1, by simp [flip, afterPop, afterEmit, step, program, cfg,
          stepOp]⟩, le_rfl⟩
      have rest := ih (symbol :: output) (some symbol)
      let firstTwo := EvalsToInTime.trans (step (program kind))
        1 1 _ afterPop _ first second
      let full := EvalsToInTime.trans (step (program kind))
        2 (2 * input.length + 2) _ afterEmit _ firstTwo rest
      simpa [List.reverse_cons, List.append_assoc, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full

/-- Clearing a rejected buffer reaches the kind-specific fallback phase. -/
def clear_run (kind : Kind) (work output : List CliqueSym)
    (buffer₁ buffer₂ : Option CliqueSym) (test : Bool) :
    EvalsToInTime (step (program kind))
      (cfg kind .clear buffer₁ buffer₂ test [] output work [])
      (some (cfg kind
        (match kind with
          | .certificate => .fallbackCertificate
          | .instance => .fallbackInstanceSep₁)
        none buffer₂ test [] output [] []))
      (work.length + 1) := by
  induction work generalizing buffer₁ with
  | nil =>
      cases kind <;> exact ⟨⟨1, by simp [flip, step, program, cfg,
        stepOp]⟩, le_rfl⟩
  | cons symbol work ih =>
      have first : EvalsToInTime (step (program kind))
          (cfg kind .clear buffer₁ buffer₂ test [] output
            (symbol :: work) [])
          (some (cfg kind .clear (some symbol) buffer₂ test [] output
            work [])) 1 :=
        ⟨⟨1, rfl⟩, le_rfl⟩
      have rest := ih (some symbol)
      let full := EvalsToInTime.trans (step (program kind))
        1 (work.length + 1) _ _ _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

/-- The certificate fallback emits the canonical empty certificate. -/
def certificate_fallback_run (output : List CliqueSym)
    (buffer₁ buffer₂ : Option CliqueSym) (test : Bool) :
    EvalsToInTime (step (program .certificate))
      (cfg .certificate .fallbackCertificate buffer₁ buffer₂ test
        [] output [] [])
      (some (haltCfg (program .certificate)
        (encodeCliqueCertificate [] ++ output))) 2 := by
  exact ⟨⟨2, by simp [Function.iterate_succ_apply, flip, step, program,
    cfg, stepOp, haltCfg, encodeCliqueCertificate]⟩, le_rfl⟩

/-- The instance fallback emits the canonical empty graph instance. -/
def instance_fallback_run (output : List CliqueSym)
    (buffer₁ buffer₂ : Option CliqueSym) (test : Bool) :
    EvalsToInTime (step (program .instance))
      (cfg .instance .fallbackInstanceSep₁ buffer₁ buffer₂ test
        [] output [] [])
      (some (haltCfg (program .instance)
        (encodeCliqueInstance
          { vertexCount := 0, targetSize := 0, edges := [] } ++ output))) 4 := by
  exact ⟨⟨4, by simp [Function.iterate_succ_apply, flip, step, program,
    cfg, stepOp, haltCfg, encodeCliqueInstance, prependCliqueTicks]⟩,
    le_rfl⟩

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.Canonicalizer

import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.CertificateRange.Basic
import Mathlib.Tactic

/-!
# General CLIQUE verifier: certificate-range cleanup and restoration
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.CertificateRange

open PolyBuilder

def emit_run (answer : Bool) (buffer₁ buffer₂ : Option (Option CliqueSym))
    (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.emit answer) buffer₁ buffer₂ test [] [] [] [] [])
      (some (haltCfg program [answer])) 2 := by
  exact ⟨⟨2, by
    simp [flip, step, program, cfg, haltCfg, stepOp]⟩, le_rfl⟩

def clearCount_run (answer : Bool) (count : Nat)
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.clearCount answer) buffer₁ buffer₂ test [] [] [] []
        (List.replicate count ()))
      (some (haltCfg program [answer])) (count + 3) := by
  induction count generalizing test with
  | zero =>
      exact ⟨⟨3, by
        simp [flip, step, program, cfg, haltCfg, stepOp]⟩, le_rfl⟩
  | succ count ih =>
      let after := cfg (.clearCount answer) buffer₁ buffer₂ true
        [] [] [] [] (List.replicate count ())
      have first : EvalsToInTime (step program)
          (cfg (.clearCount answer) buffer₁ buffer₂ test [] [] [] []
            (List.replicate (count + 1) ()))
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp,
            List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (test := true)
      let full := EvalsToInTime.trans (step program)
        1 (count + 3) _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

def clearWork₂_run (answer : Bool) (work₂ : List (Option CliqueSym))
    (count : Nat) (buffer₁ buffer₂ : Option (Option CliqueSym))
    (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.clearWork₂ answer) buffer₁ buffer₂ test [] [] [] work₂
        (List.replicate count ()))
      (some (haltCfg program [answer])) (work₂.length + count + 4) := by
  induction work₂ generalizing buffer₂ with
  | nil =>
      let after := cfg (.clearCount answer) buffer₁ none test
        [] [] [] [] (List.replicate count ())
      have first : EvalsToInTime (step program)
          (cfg (.clearWork₂ answer) buffer₁ buffer₂ test [] [] [] []
            (List.replicate count ())) (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := clearCount_run answer count buffer₁ none test
      let full := EvalsToInTime.trans (step program)
        1 (count + 3) _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full
  | cons symbol work₂ ih =>
      let after := cfg (.clearWork₂ answer) buffer₁ (some symbol) test
        [] [] [] work₂ (List.replicate count ())
      have first : EvalsToInTime (step program)
          (cfg (.clearWork₂ answer) buffer₁ buffer₂ test [] [] []
            (symbol :: work₂) (List.replicate count ()))
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := ih (buffer₂ := some symbol)
      let full := EvalsToInTime.trans (step program)
        1 (work₂.length + count + 4) _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

def clearWork₁_run (answer : Bool)
    (work₁ work₂ : List (Option CliqueSym)) (count : Nat)
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.clearWork₁ answer) buffer₁ buffer₂ test [] [] work₁ work₂
        (List.replicate count ()))
      (some (haltCfg program [answer]))
      (work₁.length + work₂.length + count + 5) := by
  induction work₁ generalizing buffer₁ with
  | nil =>
      let after := cfg (.clearWork₂ answer) none buffer₂ test
        [] [] [] work₂ (List.replicate count ())
      have first : EvalsToInTime (step program)
          (cfg (.clearWork₁ answer) buffer₁ buffer₂ test [] [] [] work₂
            (List.replicate count ())) (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := clearWork₂_run answer work₂ count none buffer₂ test
      let full := EvalsToInTime.trans (step program)
        1 (work₂.length + count + 4) _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full
  | cons symbol work₁ ih =>
      let after := cfg (.clearWork₁ answer) (some symbol) buffer₂ test
        [] [] work₁ work₂ (List.replicate count ())
      have first : EvalsToInTime (step program)
          (cfg (.clearWork₁ answer) buffer₁ buffer₂ test [] []
            (symbol :: work₁) work₂ (List.replicate count ()))
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := ih (buffer₁ := some symbol)
      let full := EvalsToInTime.trans (step program)
        1 (work₁.length + work₂.length + count + 5)
        _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

def clearInput_run (answer : Bool)
    (input work₁ work₂ : List (Option CliqueSym)) (count : Nat)
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.clearInput answer) buffer₁ buffer₂ test input [] work₁ work₂
        (List.replicate count ()))
      (some (haltCfg program [answer]))
      (input.length + work₁.length + work₂.length + count + 6) := by
  induction input generalizing buffer₁ with
  | nil =>
      let after := cfg (.clearWork₁ answer) none buffer₂ test
        [] [] work₁ work₂ (List.replicate count ())
      have first : EvalsToInTime (step program)
          (cfg (.clearInput answer) buffer₁ buffer₂ test [] [] work₁ work₂
            (List.replicate count ())) (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := clearWork₁_run answer work₁ work₂ count
        none buffer₂ test
      let full := EvalsToInTime.trans (step program)
        1 (work₁.length + work₂.length + count + 5)
        _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full
  | cons symbol input ih =>
      let after := cfg (.clearInput answer) (some symbol) buffer₂ test
        input [] work₁ work₂ (List.replicate count ())
      have first : EvalsToInTime (step program)
          (cfg (.clearInput answer) buffer₁ buffer₂ test
            (symbol :: input) [] work₁ work₂ (List.replicate count ()))
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := ih (buffer₁ := some symbol)
      let full := EvalsToInTime.trans (step program)
        1 (input.length + work₁.length + work₂.length + count + 6)
        _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

/-- Discard the unused suffix of the instance before restoring the certificate. -/
def discardInstance_run (input work₁ work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .discardInstance buffer₁ buffer₂ test input [] work₁ work₂ [])
      (some (cfg .restoreCertificate none buffer₂ test [] [] work₁ work₂ []))
      (input.length + 1) := by
  induction input generalizing buffer₁ with
  | nil =>
      exact ⟨⟨1, by
        simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | cons symbol input ih =>
      let after := cfg .discardInstance (some symbol) buffer₂ test
        input [] work₁ work₂ []
      have first : EvalsToInTime (step program)
          (cfg .discardInstance buffer₁ buffer₂ test
            (symbol :: input) [] work₁ work₂ [])
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := ih (buffer₁ := some symbol)
      let full := EvalsToInTime.trans (step program)
        1 (input.length + 1) _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

/-- Moving the saved reverse certificate back to input restores its order. -/
def restoreCertificate_run (work₁ input work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .restoreCertificate buffer₁ buffer₂ test input [] work₁ work₂ [])
      (some (cfg .certificateMark none buffer₂ test
        (work₁.reverse ++ input) [] [] work₂ []))
      (work₁.length + 1) := by
  induction work₁ generalizing input buffer₁ with
  | nil =>
      exact ⟨⟨1, by
        simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | cons symbol work₁ ih =>
      let after := cfg .restoreCertificate (some symbol) buffer₂ test
        (symbol :: input) [] work₁ work₂ []
      have first : EvalsToInTime (step program)
          (cfg .restoreCertificate buffer₁ buffer₂ test input []
            (symbol :: work₁) work₂ [])
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := ih (input := symbol :: input) (buffer₁ := some symbol)
      let full := EvalsToInTime.trans (step program)
        1 (work₁.length + 1) _ after _ first rest
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using full

/-- Restore all spent comparison tokens to the reusable vertex budget. -/
def restoreBudget_run (remaining spent : Nat)
    (input : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .restoreBudget buffer₁ buffer₂ test input [] []
        (List.replicate remaining (some .tick)) (List.replicate spent ()))
      (some (cfg .vertices buffer₁ buffer₂ false input [] []
        (List.replicate (remaining + spent) (some .tick)) []))
      (2 * spent + 1) := by
  induction spent generalizing remaining test with
  | zero =>
      exact ⟨⟨1, by
        simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | succ spent ih =>
      let afterDec := cfg .restoreTick buffer₁ buffer₂ true input [] []
        (List.replicate remaining (some .tick)) (List.replicate spent ())
      let afterPush := cfg .restoreBudget buffer₁ buffer₂ true input [] []
        (List.replicate (remaining + 1) (some .tick))
        (List.replicate spent ())
      have first : EvalsToInTime (step program)
          (cfg .restoreBudget buffer₁ buffer₂ test input [] []
            (List.replicate remaining (some .tick))
            (List.replicate (spent + 1) ()))
          (some afterDec) 1 := by
        exact ⟨⟨1, by
          simp [flip, afterDec, step, program, cfg, stepOp,
            List.replicate_succ]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterDec
          (some afterPush) 1 := by
        exact ⟨⟨1, by
          simp [flip, afterDec, afterPush, step, program, cfg, stepOp,
            List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (remaining := remaining + 1) (test := true)
      let throughPush := EvalsToInTime.trans (step program)
        1 1 _ afterDec _ first second
      let full := EvalsToInTime.trans (step program)
        2 (2 * spent + 1) _ afterPush _ throughPush rest
      simpa [List.replicate_succ, Nat.mul_succ, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using full

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.CertificateRange

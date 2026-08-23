import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.PairFirstProjection.Basic

/-!
# First pair projection: exact run
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder.PairFirstProjection

private def scan_run {Γ : Type} [Fintype Γ]
    (left right : List Γ) (work : List (Option Γ))
    (buffer₁ buffer₂ : Option (Option Γ)) (test : Bool) :
    EvalsToInTime (step (program Γ))
      (cfg Γ .scan buffer₁ buffer₂ test
        (left.map some ++ none :: right.map some) [] work [])
      (some (cfg Γ .discard (some none) buffer₂ test
        (right.map some) [] ((left.map some).reverse ++ work) []))
      (2 * left.length + 1) := by
  induction left generalizing work buffer₁ with
  | nil =>
      exact ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | cons symbol left ih =>
      let afterPop := cfg Γ (.save symbol) (some (some symbol)) buffer₂ test
        (left.map some ++ none :: right.map some) [] work []
      let afterSave := cfg Γ .scan (some (some symbol)) buffer₂ test
        (left.map some ++ none :: right.map some) [] (some symbol :: work) []
      have first : EvalsToInTime (step (program Γ))
          (cfg Γ .scan buffer₁ buffer₂ test
            ((symbol :: left).map some ++ none :: right.map some) [] work [])
          (some afterPop) 1 :=
        ⟨⟨1, by simp [flip, afterPop, step, program, cfg, stepOp]⟩, le_rfl⟩
      have second : EvalsToInTime (step (program Γ)) afterPop
          (some afterSave) 1 :=
        ⟨⟨1, by simp [flip, afterPop, afterSave, step, program, cfg,
          stepOp]⟩, le_rfl⟩
      have rest := ih (work := some symbol :: work)
        (buffer₁ := some (some symbol))
      let firstTwo := EvalsToInTime.trans (step (program Γ))
        1 1 _ afterPop _ first second
      let full := EvalsToInTime.trans (step (program Γ))
        2 (2 * left.length + 1) _ afterSave _ firstTwo rest
      simpa [List.reverse_cons, Nat.mul_succ, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

private def discard_run {Γ : Type} [Fintype Γ]
    (input work : List (Option Γ)) (buffer₁ buffer₂ : Option (Option Γ))
    (test : Bool) :
    EvalsToInTime (step (program Γ))
      (cfg Γ .discard buffer₁ buffer₂ test input [] work [])
      (some (cfg Γ .restore none buffer₂ test [] [] work []))
      (input.length + 1) := by
  induction input generalizing buffer₁ with
  | nil =>
      exact ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | cons symbol input ih =>
      let after := cfg Γ .discard (some symbol) buffer₂ test input [] work []
      have first : EvalsToInTime (step (program Γ))
          (cfg Γ .discard buffer₁ buffer₂ test (symbol :: input) [] work [])
          (some after) 1 :=
        ⟨⟨1, by simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := ih (buffer₁ := some symbol)
      let full := EvalsToInTime.trans (step (program Γ))
        1 (input.length + 1) _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

private def restore_run {Γ : Type} [Fintype Γ]
    (symbols output : List Γ) (buffer₁ buffer₂ : Option (Option Γ))
    (test : Bool) :
    EvalsToInTime (step (program Γ))
      (cfg Γ .restore buffer₁ buffer₂ test [] output (symbols.map some) [])
      (some (haltCfg (program Γ) (symbols.reverse ++ output)))
      (2 * symbols.length + 2) := by
  induction symbols generalizing output buffer₁ with
  | nil =>
      exact ⟨⟨2, by
        simp [Function.iterate_succ_apply, flip, step, program, cfg,
          stepOp, haltCfg]⟩, le_rfl⟩
  | cons symbol symbols ih =>
      let afterPop := cfg Γ (.emit symbol) (some (some symbol)) buffer₂ test
        [] output (symbols.map some) []
      let afterEmit := cfg Γ .restore (some (some symbol)) buffer₂ test
        [] (symbol :: output) (symbols.map some) []
      have first : EvalsToInTime (step (program Γ))
          (cfg Γ .restore buffer₁ buffer₂ test [] output
            ((symbol :: symbols).map some) [])
          (some afterPop) 1 :=
        ⟨⟨1, by simp [flip, afterPop, step, program, cfg, stepOp]⟩, le_rfl⟩
      have second : EvalsToInTime (step (program Γ)) afterPop
          (some afterEmit) 1 :=
        ⟨⟨1, by simp [flip, afterPop, afterEmit, step, program, cfg,
          stepOp]⟩, le_rfl⟩
      have rest := ih (output := symbol :: output)
        (buffer₁ := some (some symbol))
      let firstTwo := EvalsToInTime.trans (step (program Γ))
        1 1 _ afterPop _ first second
      let full := EvalsToInTime.trans (step (program Γ))
        2 (2 * symbols.length + 2) _ afterEmit _ firstTwo rest
      simpa [List.reverse_cons, Nat.mul_succ, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

/-- Exact execution of the fixed first-projection controller. -/
def run {Γ : Type} [Fintype Γ] (left right : List Γ) :
    EvalsToInTime (step (program Γ))
      (initialCfg (program Γ) (pairEncoding left right))
      (some (haltCfg (program Γ) left))
      (4 * left.length + right.length + 4) := by
  have scanned := scan_run left right [] none none false
  have scanned' : EvalsToInTime (step (program Γ))
      (initialCfg (program Γ) (pairEncoding left right))
      (some (cfg Γ .discard (some none) none false
        (right.map some) [] (left.map some).reverse []))
      (2 * left.length + 1) := by
    simpa [initialCfg, pairEncoding, program, cfg] using scanned
  have discarded := discard_run (right.map some) (left.map some).reverse
    (some none) none false
  have discarded' : EvalsToInTime (step (program Γ))
      (cfg Γ .discard (some none) none false
        (right.map some) [] (left.map some).reverse [])
      (some (cfg Γ .restore none none false [] []
        (left.map some).reverse []))
      (right.length + 1) := by
    simpa using discarded
  have restored := restore_run left.reverse [] none none false
  have restored' : EvalsToInTime (step (program Γ))
      (cfg Γ .restore none none false [] [] (left.map some).reverse [])
      (some (haltCfg (program Γ) left))
      (2 * left.length + 2) := by
    simpa using restored
  let throughDiscard := EvalsToInTime.trans (step (program Γ))
    (2 * left.length + 1) (right.length + 1) _ _ _ scanned' discarded'
  let full := EvalsToInTime.trans (step (program Γ))
    _ (2 * left.length + 2) _ _ _ throughDiscard restored'
  convert full using 1
  all_goals simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  omega

end CLRS.Chapter34.Turing.PolyBuilder.PairFirstProjection

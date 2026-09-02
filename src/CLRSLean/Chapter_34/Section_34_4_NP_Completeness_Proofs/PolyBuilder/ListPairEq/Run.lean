import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ListPairEq.Core
import Mathlib.Tactic

/-! # Exact execution of the separated-list equality checker -/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder.ListPairEq

def compareSteps {Γ : Type} : List Γ → List Γ → Nat
  | [], [] => 4
  | [], _ :: rights => rights.length + 5
  | _ :: lefts, [] => lefts.length + 5
  | _ :: lefts, _ :: rights => compareSteps lefts rights + 2

private theorem drainLeft_eval {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (remaining : List Γ) (buffer₁ buffer₂ : Option (Option Γ)) :
    (flip Option.bind (step (program Γ)))^[remaining.length + 3]
      (some (cfg Γ .drainLeft buffer₁ buffer₂ [] []
        (remaining.map some) [])) =
      some (haltCfg (program Γ) [false]) := by
  induction remaining generalizing buffer₁ with
  | nil => rfl
  | cons symbol remaining ih =>
      rw [show (symbol :: remaining).length + 3 =
          (remaining.length + 3) + 1 by simp,
        Function.iterate_succ_apply]
      change (flip Option.bind (step (program Γ)))^[remaining.length + 3]
        (some (cfg Γ .drainLeft (some (some symbol)) buffer₂ [] []
          (remaining.map some) [])) = _
      exact ih (some (some symbol))

private theorem drainRight_eval {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (remaining : List Γ) (buffer₁ buffer₂ : Option (Option Γ)) :
    (flip Option.bind (step (program Γ)))^[remaining.length + 3]
      (some (cfg Γ .drainRight buffer₁ buffer₂ [] [] []
        (remaining.map some))) =
      some (haltCfg (program Γ) [false]) := by
  induction remaining generalizing buffer₂ with
  | nil => rfl
  | cons symbol remaining ih =>
      rw [show (symbol :: remaining).length + 3 =
          (remaining.length + 3) + 1 by simp,
        Function.iterate_succ_apply]
      change (flip Option.bind (step (program Γ)))^[remaining.length + 3]
        (some (cfg Γ .drainRight buffer₁ (some (some symbol)) [] [] []
          (remaining.map some))) = _
      exact ih (some (some symbol))

private theorem compare_eval {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (left right : List Γ) (equal : Bool)
    (buffer₁ buffer₂ : Option (Option Γ)) :
    (flip Option.bind (step (program Γ)))^[compareSteps left right]
      (some (cfg Γ (.compareLeft equal) buffer₁ buffer₂ [] []
        (left.map some) (right.map some))) =
      some (haltCfg (program Γ) [equal && decide (left = right)]) := by
  induction left generalizing right equal buffer₁ buffer₂ with
  | nil =>
      cases right with
      | nil =>
          simp only [compareSteps]
          rw [show 4 = 0 + 1 + 1 + 1 + 1 by omega,
            Function.iterate_succ_apply, Function.iterate_succ_apply,
            Function.iterate_succ_apply, Function.iterate_succ_apply]
          simp [flip, step, stepOp, program, cfg, initialCfg, haltCfg]
      | cons right rights =>
          rw [show compareSteps ([] : List Γ) (right :: rights) =
              (rights.length + 3) + 1 + 1 by simp [compareSteps],
            Function.iterate_succ_apply, Function.iterate_succ_apply]
          change (flip Option.bind (step (program Γ)))^[rights.length + 3]
            (some (cfg Γ .drainRight none (some (some right)) [] [] []
              (rights.map some))) = _
          simpa using drainRight_eval rights none (some (some right))
  | cons left lefts ih =>
      cases right with
      | nil =>
          rw [show compareSteps (left :: lefts) ([] : List Γ) =
              (lefts.length + 3) + 1 + 1 by simp [compareSteps],
            Function.iterate_succ_apply, Function.iterate_succ_apply]
          change (flip Option.bind (step (program Γ)))^[lefts.length + 3]
            (some (cfg Γ .drainLeft (some (some left)) none [] []
              (lefts.map some) [])) = _
          simpa using drainLeft_eval lefts (some (some left)) none
      | cons right rights =>
          rw [show compareSteps (left :: lefts) (right :: rights) =
              compareSteps lefts rights + 1 + 1 by simp [compareSteps],
            Function.iterate_succ_apply, Function.iterate_succ_apply]
          change (flip Option.bind (step (program Γ)))^[
              compareSteps lefts rights]
            (some (cfg Γ
              (.compareLeft (equal && decide (left = right)))
              (some (some left)) (some (some right)) [] []
              (lefts.map some) (rights.map some))) = _
          simpa [Bool.and_assoc] using ih rights
            (equal && decide (left = right))
            (some (some left)) (some (some right))

private theorem loadRight_eval {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (right : List Γ) (buffer₁ buffer₂ : Option (Option Γ))
    (work₁ work₂ : List (Option Γ)) :
    (flip Option.bind (step (program Γ)))^[2 * right.length + 1]
      (some (cfg Γ .loadRight buffer₁ buffer₂
        (right.map some) [] work₁ work₂)) =
      some (cfg Γ (.compareLeft true) none buffer₂ [] [] work₁
        (right.reverse.map some ++ work₂)) := by
  induction right generalizing buffer₁ work₂ with
  | nil => rfl
  | cons symbol right ih =>
      rw [show 2 * (symbol :: right).length + 1 =
          (2 * right.length + 1) + 1 + 1 by simp; omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change (flip Option.bind (step (program Γ)))^[2 * right.length + 1]
        (some (cfg Γ .loadRight none buffer₂ (right.map some) []
          work₁ (some symbol :: work₂))) = _
      simpa [List.reverse_cons, List.append_assoc] using
        ih none (some symbol :: work₂)

private theorem loadLeft_eval {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (left right : List Γ) (buffer₁ buffer₂ : Option (Option Γ))
    (work₁ work₂ : List (Option Γ)) :
    (flip Option.bind (step (program Γ)))^[2 * left.length + 1]
      (some (cfg Γ .loadLeft buffer₁ buffer₂
        (left.map some ++ none :: right.map some) [] work₁ work₂)) =
      some (cfg Γ .loadRight (some none) buffer₂
        (right.map some) [] (left.reverse.map some ++ work₁) work₂) := by
  induction left generalizing buffer₁ work₁ with
  | nil => rfl
  | cons symbol left ih =>
      rw [show 2 * (symbol :: left).length + 1 =
          (2 * left.length + 1) + 1 + 1 by simp; omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change (flip Option.bind (step (program Γ)))^[2 * left.length + 1]
        (some (cfg Γ .loadLeft none buffer₂
          (left.map some ++ none :: right.map some) []
          (some symbol :: work₁) work₂)) = _
      simpa [List.reverse_cons, List.append_assoc] using
        ih none (some symbol :: work₁)

def steps {Γ : Type} (left right : List Γ) : Nat :=
  (2 * left.length + 1) + (2 * right.length + 1) +
    compareSteps left.reverse right.reverse

/-- Exact run on the standard option-separated pair encoding. -/
def run {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (left right : List Γ) :
    EvalsToInTime (step (program Γ))
      (initialCfg (program Γ) (pairEncoding left right))
      (some (haltCfg (program Γ) [decide (left = right)]))
      (steps left right) := by
  have hleft : EvalsToInTime (step (program Γ))
      (initialCfg (program Γ) (pairEncoding left right))
      (some (cfg Γ .loadRight (some none) none (right.map some) []
        (left.reverse.map some) []))
      (2 * left.length + 1) := by
    refine ⟨⟨2 * left.length + 1, ?_⟩, le_rfl⟩
    simpa [pairEncoding, cfg, initialCfg, program] using
      loadLeft_eval left right none none [] []
  have hright : EvalsToInTime (step (program Γ))
      (cfg Γ .loadRight (some none) none (right.map some) []
        (left.reverse.map some) [])
      (some (cfg Γ (.compareLeft true) none none [] []
        (left.reverse.map some) (right.reverse.map some)))
      (2 * right.length + 1) :=
    ⟨⟨2 * right.length + 1, by
      simpa using loadRight_eval right (some none) none
        (left.reverse.map some) []⟩, le_rfl⟩
  have hcompare := compare_eval left.reverse right.reverse true none none
  have hdecide : decide (left.reverse = right.reverse) =
      decide (left = right) := by
    simp only [decide_eq_decide]
    exact List.reverse_injective.eq_iff
  let throughLoad := EvalsToInTime.trans (step (program Γ))
    (2 * left.length + 1) (2 * right.length + 1) _ _ _ hleft hright
  let full := EvalsToInTime.trans (step (program Γ))
    ((2 * right.length + 1) + (2 * left.length + 1))
    (compareSteps left.reverse right.reverse) _ _ _ throughLoad
    ⟨⟨compareSteps left.reverse right.reverse, by
      simpa [hdecide] using hcompare⟩, le_rfl⟩
  simpa [steps, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

end CLRS.Chapter34.Turing.PolyBuilder.ListPairEq

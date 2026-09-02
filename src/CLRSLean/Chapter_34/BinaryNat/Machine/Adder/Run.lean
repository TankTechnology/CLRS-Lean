import CLRSLean.Chapter_34.BinaryNat.Machine.Adder.Core
import Mathlib.Tactic

/-! # Exact execution of the fixed binary adder -/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.BinaryNat.Adder

open PolyBuilder

/-- Exact addition-phase step count. -/
def addSteps : List Bool → List Bool → Bool → Nat
  | [], [], false => 3
  | [], [], true => 4
  | left :: lefts, [], carry =>
      addSteps lefts [] (addCell left false carry).2 + 3
  | [], right :: rights, carry =>
      addSteps [] rights (addCell false right carry).2 + 3
  | left :: lefts, right :: rights, carry =>
      addSteps lefts rights (addCell left right carry).2 + 3

private theorem add_eval (left right : List Bool) (carry : Bool)
    (buffer₁ buffer₂ : Option (Option Bool)) (output : List Bool) :
    (flip Option.bind (step program))^[addSteps left right carry]
      (some (cfg (.addLeft carry) buffer₁ buffer₂ [] output
        (left.map some) (right.map some))) =
      some (haltCfg program (addLittle left right carry ++ output)) := by
  induction left generalizing right carry buffer₁ buffer₂ output with
  | nil =>
      induction right generalizing carry buffer₁ buffer₂ output with
      | nil =>
          cases carry with
          | false =>
              simp only [List.map_nil, addLittle, List.nil_append]
              rw [show addSteps [] [] false = 0 + 1 + 1 + 1 by
                    simp [addSteps],
                Function.iterate_succ_apply,
                Function.iterate_succ_apply,
                Function.iterate_succ_apply]
              rfl
          | true =>
              simp only [List.map_nil, addLittle, List.cons_append,
                List.nil_append]
              rw [show addSteps [] [] true = 0 + 1 + 1 + 1 + 1 by
                    simp [addSteps],
                Function.iterate_succ_apply,
                Function.iterate_succ_apply,
                Function.iterate_succ_apply,
                Function.iterate_succ_apply]
              rfl
      | cons right rights ih =>
          let cell := addCell false right carry
          rw [show addSteps [] (right :: rights) carry =
              addSteps [] rights cell.2 + 1 + 1 + 1 by
                simp [addSteps, cell],
            Function.iterate_succ_apply, Function.iterate_succ_apply,
            Function.iterate_succ_apply]
          change
            (flip Option.bind (step program))^[addSteps [] rights cell.2]
              (some (cfg (.addLeft cell.2) none (some (some right)) []
                (cell.1 :: output) [] (rights.map some))) = _
          simpa [addLittle, cell, List.append_assoc] using
            ih cell.2 none (some (some right)) (cell.1 :: output)
  | cons left lefts ih =>
      cases right with
      | nil =>
          let cell := addCell left false carry
          rw [show addSteps (left :: lefts) [] carry =
              addSteps lefts [] cell.2 + 1 + 1 + 1 by
                simp [addSteps, cell],
            Function.iterate_succ_apply, Function.iterate_succ_apply,
            Function.iterate_succ_apply]
          change
            (flip Option.bind (step program))^[addSteps lefts [] cell.2]
              (some (cfg (.addLeft cell.2) (some (some left)) none []
                (cell.1 :: output) (lefts.map some) [])) = _
          simpa [addLittle, cell, List.append_assoc] using
            ih [] cell.2 (some (some left)) none (cell.1 :: output)
      | cons right rights =>
          let cell := addCell left right carry
          rw [show addSteps (left :: lefts) (right :: rights) carry =
              addSteps lefts rights cell.2 + 1 + 1 + 1 by
                simp [addSteps, cell],
            Function.iterate_succ_apply, Function.iterate_succ_apply,
            Function.iterate_succ_apply]
          change
            (flip Option.bind (step program))^[addSteps lefts rights cell.2]
              (some (cfg (.addLeft cell.2) (some (some left))
                (some (some right)) []
                (cell.1 :: output) (lefts.map some) (rights.map some))) = _
          simpa [addLittle, cell, List.append_assoc] using
            ih rights cell.2 (some (some left)) (some (some right))
              (cell.1 :: output)

/-- Exact addition phase from the two little-endian work stacks. -/
def add_run (left right : List Bool) (carry : Bool)
    (buffer₁ buffer₂ : Option (Option Bool)) (output : List Bool) :
    EvalsToInTime (step program)
      (cfg (.addLeft carry) buffer₁ buffer₂ [] output
        (left.map some) (right.map some))
      (some (haltCfg program (addLittle left right carry ++ output)))
      (addSteps left right carry) :=
  ⟨⟨addSteps left right carry,
    add_eval left right carry buffer₁ buffer₂ output⟩, le_rfl⟩

private theorem loadRight_eval (right : List Bool)
    (buffer₁ buffer₂ : Option (Option Bool)) (output : List Bool)
    (work₁ work₂ : List (Option Bool)) :
    (flip Option.bind (step program))^[2 * right.length + 1]
      (some (cfg .loadRight buffer₁ buffer₂ (right.map some) output
        work₁ work₂)) =
      some (cfg (.addLeft false) none buffer₂ [] output work₁
        (right.reverse.map some ++ work₂)) := by
  induction right generalizing buffer₁ work₂ with
  | nil => rfl
  | cons bit right ih =>
      rw [show 2 * (bit :: right).length + 1 =
          (2 * right.length + 1) + 1 + 1 by simp; omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step program))^[2 * right.length + 1]
          (some (cfg .loadRight none buffer₂ (right.map some) output
            work₁ (some bit :: work₂))) = _
      simpa [List.reverse_cons, List.append_assoc] using
        ih none (some bit :: work₂)

private theorem loadLeft_eval (left right : List Bool)
    (buffer₁ buffer₂ : Option (Option Bool)) (output : List Bool)
    (work₁ work₂ : List (Option Bool)) :
    (flip Option.bind (step program))^[2 * left.length + 1]
      (some (cfg .loadLeft buffer₁ buffer₂
        (left.map some ++ none :: right.map some) output work₁ work₂)) =
      some (cfg .loadRight (some none) buffer₂ (right.map some) output
        (left.reverse.map some ++ work₁) work₂) := by
  induction left generalizing buffer₁ work₁ with
  | nil => rfl
  | cons bit left ih =>
      rw [show 2 * (bit :: left).length + 1 =
          (2 * left.length + 1) + 1 + 1 by simp; omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step program))^[2 * left.length + 1]
          (some (cfg .loadLeft none buffer₂
            (left.map some ++ none :: right.map some) output
            (some bit :: work₁) work₂)) = _
      simpa [List.reverse_cons, List.append_assoc] using
        ih none (some bit :: work₁)

/-- Exact total step count. -/
def steps (left right : List Bool) : Nat :=
  (2 * left.length + 1) + (2 * right.length + 1) +
    addSteps left.reverse right.reverse false

/-- Complete exact builder run on the standard separated pair encoding. -/
def run (left right : List Bool) :
    EvalsToInTime (step program)
      (initialCfg program (pairEncoding left right))
      (some (haltCfg program (addWords left right)))
      (steps left right) := by
  have hleft : EvalsToInTime (step program)
      (initialCfg program (pairEncoding left right))
      (some (cfg .loadRight (some none) none (right.map some) []
        (left.reverse.map some) []))
      (2 * left.length + 1) := by
    refine ⟨⟨2 * left.length + 1, ?_⟩, le_rfl⟩
    simpa [pairEncoding, cfg, initialCfg, program] using
      loadLeft_eval left right none none [] [] []
  have hright : EvalsToInTime (step program)
      (cfg .loadRight (some none) none (right.map some) []
        (left.reverse.map some) [])
      (some (cfg (.addLeft false) none none [] []
        (left.reverse.map some) (right.reverse.map some)))
      (2 * right.length + 1) :=
    ⟨⟨2 * right.length + 1, by
      simpa using loadRight_eval right (some none) none []
        (left.reverse.map some) []⟩, le_rfl⟩
  have hadd := add_run left.reverse right.reverse false none none []
  let throughLoad := EvalsToInTime.trans (step program)
    (2 * left.length + 1) (2 * right.length + 1) _ _ _ hleft hright
  let full := EvalsToInTime.trans (step program)
    ((2 * right.length + 1) + (2 * left.length + 1))
    (addSteps left.reverse right.reverse false)
    _ _ _ throughLoad hadd
  simpa [steps, addWords, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using full

end CLRS.Chapter34.Turing.BinaryNat.Adder

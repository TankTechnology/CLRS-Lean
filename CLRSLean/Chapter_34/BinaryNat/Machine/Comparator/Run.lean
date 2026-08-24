import CLRSLean.Chapter_34.BinaryNat.Machine.Comparator.Core
import Mathlib.Tactic

/-! # Exact execution of the fixed binary comparator -/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.BinaryNat.Comparator

open PolyBuilder

/-- Exact comparison-phase step count. -/
def compareSteps : List Bool → List Bool → Bool → Nat
  | [], [], _ => 4
  | left :: lefts, [], result =>
      compareSteps lefts [] (leCell left false result) + 2
  | [], right :: rights, result =>
      compareSteps [] rights (leCell false right result) + 2
  | left :: lefts, right :: rights, result =>
      compareSteps lefts rights (leCell left right result) + 2

private theorem compare_eval (left right : List Bool) (result : Bool)
    (buffer₁ buffer₂ : Option (Option Bool)) (output : List Bool) :
    (flip Option.bind (step program))^[compareSteps left right result]
      (some (cfg (.compareLeft result) buffer₁ buffer₂ [] output
        (left.map some) (right.map some))) =
      some (haltCfg program (compareLittle left right result :: output)) := by
  induction left generalizing right result buffer₁ buffer₂ output with
  | nil =>
      induction right generalizing result buffer₁ buffer₂ output with
      | nil =>
          simp only [List.map_nil, compareLittle]
          rw [show compareSteps [] [] result = 0 + 1 + 1 + 1 + 1 by
                simp [compareSteps],
            Function.iterate_succ_apply, Function.iterate_succ_apply,
            Function.iterate_succ_apply, Function.iterate_succ_apply]
          rfl
      | cons right rights ih =>
          rw [show compareSteps [] (right :: rights) result =
              compareSteps [] rights (leCell false right result) + 1 + 1 by
                simp [compareSteps],
            Function.iterate_succ_apply, Function.iterate_succ_apply]
          change
            (flip Option.bind (step program))^[compareSteps [] rights
                (leCell false right result)]
              (some (cfg (.compareLeft (leCell false right result)) none
                (some (some right)) [] output [] (rights.map some))) = _
          simpa [compareLittle] using
            ih (leCell false right result) none (some (some right)) output
  | cons left lefts ih =>
      cases right with
      | nil =>
          rw [show compareSteps (left :: lefts) [] result =
              compareSteps lefts [] (leCell left false result) + 1 + 1 by
                simp [compareSteps],
            Function.iterate_succ_apply, Function.iterate_succ_apply]
          change
            (flip Option.bind (step program))^[compareSteps lefts []
                (leCell left false result)]
              (some (cfg (.compareLeft (leCell left false result))
                (some (some left)) none [] output (lefts.map some) [])) = _
          simpa [compareLittle] using
            ih [] (leCell left false result) (some (some left)) none output
      | cons right rights =>
          rw [show compareSteps (left :: lefts) (right :: rights) result =
              compareSteps lefts rights (leCell left right result) + 1 + 1 by
                simp [compareSteps],
            Function.iterate_succ_apply, Function.iterate_succ_apply]
          change
            (flip Option.bind (step program))^[compareSteps lefts rights
                (leCell left right result)]
              (some (cfg (.compareLeft (leCell left right result))
                (some (some left)) (some (some right)) [] output
                (lefts.map some) (rights.map some))) = _
          simpa [compareLittle] using
            ih rights (leCell left right result) (some (some left))
              (some (some right)) output

/-- Exact comparison phase from the two little-endian work stacks. -/
def compare_run (left right : List Bool) (result : Bool)
    (buffer₁ buffer₂ : Option (Option Bool)) (output : List Bool) :
    EvalsToInTime (step program)
      (cfg (.compareLeft result) buffer₁ buffer₂ [] output
        (left.map some) (right.map some))
      (some (haltCfg program (compareLittle left right result :: output)))
      (compareSteps left right result) :=
  ⟨⟨compareSteps left right result,
    compare_eval left right result buffer₁ buffer₂ output⟩, le_rfl⟩

private theorem loadRight_eval (right : List Bool)
    (buffer₁ buffer₂ : Option (Option Bool)) (output : List Bool)
    (work₁ work₂ : List (Option Bool)) :
    (flip Option.bind (step program))^[2 * right.length + 1]
      (some (cfg .loadRight buffer₁ buffer₂ (right.map some) output
        work₁ work₂)) =
      some (cfg (.compareLeft true) none buffer₂ [] output work₁
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
    compareSteps left.reverse right.reverse true

/-- Complete exact builder run on the standard separated pair encoding. -/
def run (left right : List Bool) :
    EvalsToInTime (step program)
      (initialCfg program (CLRS.Chapter34.pairEncoding left right))
      (some (haltCfg program [leWords left right]))
      (steps left right) := by
  have hleft : EvalsToInTime (step program)
      (initialCfg program (CLRS.Chapter34.pairEncoding left right))
      (some (cfg .loadRight (some none) none (right.map some) []
        (left.reverse.map some) []))
      (2 * left.length + 1) := by
    refine ⟨⟨2 * left.length + 1, ?_⟩, le_rfl⟩
    simpa [CLRS.Chapter34.pairEncoding, cfg, initialCfg, program] using
      loadLeft_eval left right none none [] [] []
  have hright : EvalsToInTime (step program)
      (cfg .loadRight (some none) none (right.map some) []
        (left.reverse.map some) [])
      (some (cfg (.compareLeft true) none none [] []
        (left.reverse.map some) (right.reverse.map some)))
      (2 * right.length + 1) :=
    ⟨⟨2 * right.length + 1, by
      simpa using loadRight_eval right (some none) none []
        (left.reverse.map some) []⟩, le_rfl⟩
  have hcompare := compare_run left.reverse right.reverse true none none []
  let throughLoad := EvalsToInTime.trans (step program)
    (2 * left.length + 1) (2 * right.length + 1) _ _ _ hleft hright
  let full := EvalsToInTime.trans (step program)
    ((2 * right.length + 1) + (2 * left.length + 1))
    (compareSteps left.reverse right.reverse true)
    _ _ _ throughLoad hcompare
  simpa [steps, leWords, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using full

end CLRS.Chapter34.Turing.BinaryNat.Comparator

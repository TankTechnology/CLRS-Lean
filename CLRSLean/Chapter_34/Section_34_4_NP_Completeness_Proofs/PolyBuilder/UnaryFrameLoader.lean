import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Machine
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrame
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.Encoding
import Mathlib.Tactic

/-!
# Loading a persistent unary runtime frame

This module gives the validity controller its first concrete non-halting
prelude.  It consumes three delimiter-separated naturals, loads them into the
three local unary registers, preserves the remaining frame and both work
stacks, and stops at a public `ready` label rather than erasing the indices.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Finite control for loading three framed unary values. -/
inductive UnaryTripleLoaderLabel
  | load₁ | inc₁
  | load₂ | inc₂
  | load₃ | inc₃
  | ready | invalid
deriving DecidableEq, Fintype

/-- Concrete three-field frame loader.  The `ready` instruction is a halt only
for standalone safety; the family controller will replace that continuation
when it embeds this prelude. -/
def unaryTripleLoaderProgram : Program UnaryFrameSym CircuitSym where
  Label := UnaryTripleLoaderLabel
  main := .load₁
  op
    | .load₁ => .popInput .invalid fun
        | .tick => .inc₁
        | .separator => .load₂
        | .frameEnd => .invalid
    | .inc₁ => .inc₁ .load₁
    | .load₂ => .popInput .invalid fun
        | .tick => .inc₂
        | .separator => .load₃
        | .frameEnd => .invalid
    | .inc₂ => .inc₂ .load₂
    | .load₃ => .popInput .invalid fun
        | .tick => .inc₃
        | .separator => .ready
        | .frameEnd => .invalid
    | .inc₃ => .inc₃ .load₃
    | .ready => .halt
    | .invalid => .halt

/-- Independent loader configuration with all persistent symbol stacks
visible. -/
def unaryTripleLoaderCfg (label : UnaryTripleLoaderLabel)
    (buffer₁ : Option UnaryFrameSym) (input : List UnaryFrameSym)
    (output : List CircuitSym) (work₁ work₂ : List UnaryFrameSym)
    (first second third : List Unit) :
    BuilderCfg unaryTripleLoaderProgram where
  label := some label
  buffer₁ := buffer₁
  buffer₂ := none
  test := false
  input := input
  output := output
  work₁ := work₁
  work₂ := work₂
  counter₁ := first
  counter₂ := second
  counter₃ := third

/-- Public continuation configuration after all three fields have loaded. -/
def unaryTripleLoaderReadyCfg (first second third : Nat)
    (tail : List UnaryFrameSym) (output : List CircuitSym)
    (work₁ work₂ : List UnaryFrameSym) :
    BuilderCfg unaryTripleLoaderProgram :=
  unaryTripleLoaderCfg .ready (some .separator) tail output work₁ work₂
    (List.replicate first ()) (List.replicate second ())
    (List.replicate third ())

/-- Exact loader cost: two steps per tick and one per separator. -/
def unaryTripleLoaderSteps (first second third : Nat) : Nat :=
  2 * (first + second + third) + 3

private theorem replicate_append_cons (count : Nat) (tail : List Unit) :
    List.replicate count () ++ () :: tail =
      () :: (List.replicate count () ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons ()) ih

private theorem loadFirst_eval (value : Nat)
    (buffer₁ : Option UnaryFrameSym) (tail : List UnaryFrameSym)
    (output : List CircuitSym) (work₁ work₂ : List UnaryFrameSym)
    (first second third : List Unit) :
    (flip Option.bind (step unaryTripleLoaderProgram))^[2 * value + 1]
      (some (unaryTripleLoaderCfg .load₁ buffer₁
        (encodeUnaryFrameBlock value ++ tail) output work₁ work₂
        first second third)) =
      some (unaryTripleLoaderCfg .load₂ (some .separator) tail output
        work₁ work₂ (List.replicate value () ++ first) second third) := by
  induction value generalizing buffer₁ first with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step unaryTripleLoaderProgram))^[2 * value + 1]
          (some (unaryTripleLoaderCfg .load₁ (some .tick)
            (encodeUnaryFrameBlock value ++ tail) output work₁ work₂
            (() :: first) second third)) = _
      simpa only [List.replicate_succ, replicate_append_cons,
        List.cons_append] using ih (some .tick) (() :: first)

private theorem loadSecond_eval (value : Nat)
    (buffer₁ : Option UnaryFrameSym) (tail : List UnaryFrameSym)
    (output : List CircuitSym) (work₁ work₂ : List UnaryFrameSym)
    (first second third : List Unit) :
    (flip Option.bind (step unaryTripleLoaderProgram))^[2 * value + 1]
      (some (unaryTripleLoaderCfg .load₂ buffer₁
        (encodeUnaryFrameBlock value ++ tail) output work₁ work₂
        first second third)) =
      some (unaryTripleLoaderCfg .load₃ (some .separator) tail output
        work₁ work₂ first (List.replicate value () ++ second) third) := by
  induction value generalizing buffer₁ second with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step unaryTripleLoaderProgram))^[2 * value + 1]
          (some (unaryTripleLoaderCfg .load₂ (some .tick)
            (encodeUnaryFrameBlock value ++ tail) output work₁ work₂
            first (() :: second) third)) = _
      simpa only [List.replicate_succ, replicate_append_cons,
        List.cons_append] using ih (some .tick) (() :: second)

private theorem loadThird_eval (value : Nat)
    (buffer₁ : Option UnaryFrameSym) (tail : List UnaryFrameSym)
    (output : List CircuitSym) (work₁ work₂ : List UnaryFrameSym)
    (first second third : List Unit) :
    (flip Option.bind (step unaryTripleLoaderProgram))^[2 * value + 1]
      (some (unaryTripleLoaderCfg .load₃ buffer₁
        (encodeUnaryFrameBlock value ++ tail) output work₁ work₂
        first second third)) =
      some (unaryTripleLoaderCfg .ready (some .separator) tail output
        work₁ work₂ first second (List.replicate value () ++ third)) := by
  induction value generalizing buffer₁ third with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step unaryTripleLoaderProgram))^[2 * value + 1]
          (some (unaryTripleLoaderCfg .load₃ (some .tick)
            (encodeUnaryFrameBlock value ++ tail) output work₁ work₂
            first second (() :: third))) = _
      simpa only [List.replicate_succ, replicate_append_cons,
        List.cons_append] using ih (some .tick) (() :: third)

/-- Load exactly three framed naturals, preserve the unconsumed frame and both
work stacks, and enter the non-halting continuation with exact unary values. -/
def unaryTripleLoader_run (first second third : Nat)
    (tail : List UnaryFrameSym) (output : List CircuitSym)
    (work₁ work₂ : List UnaryFrameSym) :
    EvalsToInTime (step unaryTripleLoaderProgram)
      (unaryTripleLoaderCfg .load₁ none
        (encodeUnaryFrame [first, second, third] ++ tail)
        output work₁ work₂ [] [] [])
      (some (unaryTripleLoaderReadyCfg first second third tail output
        work₁ work₂))
      (unaryTripleLoaderSteps first second third) := by
  let afterFirst := unaryTripleLoaderCfg .load₂ (some .separator)
    (encodeUnaryFrameBlock second ++ encodeUnaryFrameBlock third ++ tail)
    output work₁ work₂ (List.replicate first ()) [] []
  let afterSecond := unaryTripleLoaderCfg .load₃ (some .separator)
    (encodeUnaryFrameBlock third ++ tail) output work₁ work₂
    (List.replicate first ()) (List.replicate second ()) []
  have hfirst : EvalsToInTime (step unaryTripleLoaderProgram)
      (unaryTripleLoaderCfg .load₁ none
        (encodeUnaryFrame [first, second, third] ++ tail)
        output work₁ work₂ [] [] [])
      (some afterFirst) (2 * first + 1) := by
    refine ⟨⟨2 * first + 1, ?_⟩, le_rfl⟩
    simpa [afterFirst, encodeUnaryFrame, List.append_assoc] using
      loadFirst_eval first none
        (encodeUnaryFrameBlock second ++ encodeUnaryFrameBlock third ++ tail)
        output work₁ work₂ [] [] []
  have hsecond : EvalsToInTime (step unaryTripleLoaderProgram)
      afterFirst (some afterSecond) (2 * second + 1) := by
    refine ⟨⟨2 * second + 1, ?_⟩, le_rfl⟩
    simpa [afterFirst, afterSecond, List.append_assoc] using
      loadSecond_eval second (some .separator)
        (encodeUnaryFrameBlock third ++ tail) output work₁ work₂
        (List.replicate first ()) [] []
  have hthird : EvalsToInTime (step unaryTripleLoaderProgram)
      afterSecond
      (some (unaryTripleLoaderReadyCfg first second third tail output
        work₁ work₂)) (2 * third + 1) := by
    refine ⟨⟨2 * third + 1, ?_⟩, le_rfl⟩
    simpa [afterSecond, unaryTripleLoaderReadyCfg] using
      loadThird_eval third (some .separator) tail output work₁ work₂
        (List.replicate first ()) (List.replicate second ()) []
  let throughSecond := EvalsToInTime.trans (step unaryTripleLoaderProgram)
    (2 * first + 1) (2 * second + 1) _ afterFirst _ hfirst hsecond
  let full := EvalsToInTime.trans (step unaryTripleLoaderProgram)
    ((2 * second + 1) + (2 * first + 1)) (2 * third + 1)
    _ afterSecond _ throughSecond hthird
  convert full using 1
  simp [unaryTripleLoaderSteps]
  omega

end CLRS.Chapter34.Turing.PolyBuilder

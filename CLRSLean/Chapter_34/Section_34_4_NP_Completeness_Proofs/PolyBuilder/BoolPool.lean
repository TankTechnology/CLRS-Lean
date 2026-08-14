import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Machine
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.Encoding
import Mathlib.Tactic

/-!
# Appending the shared Boolean constant pool

The Cook--Levin circuit allocates exactly two shared constants immediately
after its tableau input gates: false, then true.  This module implements a
concrete linear-time suffix builder.  It parks the existing serialized prefix,
emits the two constant tags, and restores the prefix in front of them.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Exact encoding of the shared false/true gate pool. -/
def boolPoolGateStream : List CircuitSym :=
  [.constFalseMark, .constTrueMark]

/-- Append the shared Boolean pool to an existing circuit prefix. -/
def appendBoolPool (inputPrefix : List CircuitSym) : List CircuitSym :=
  inputPrefix ++ boolPoolGateStream

/-- Finite control for the constant-pool suffix builder. -/
inductive AppendBoolPoolLabel
  | move
  | pushTrue
  | pushFalse
  | emit
  | push (symbol : CircuitSym)
  | halt
deriving DecidableEq, Fintype

/-- Park the input, place the two constant encodings on the output, then
restore the input in front of them. -/
def appendBoolPoolProgram : Program CircuitSym CircuitSym where
  Label := AppendBoolPoolLabel
  main := .move
  op
    | .move => .moveInputWork₁ .pushTrue (fun _ => .move)
    | .pushTrue => .pushOutput .constTrueMark .pushFalse
    | .pushFalse => .pushOutput .constFalseMark .emit
    | .emit => .popWork₁ .halt .push
    | .push symbol => .pushOutput symbol .emit
    | .halt => .halt

private def appendBoolPoolCfg (label : AppendBoolPoolLabel)
    (buffer : Option CircuitSym) (input output work₁ : List CircuitSym) :
    BuilderCfg appendBoolPoolProgram where
  label := some label
  buffer₁ := buffer
  buffer₂ := none
  test := false
  input := input
  output := output
  work₁ := work₁
  work₂ := []
  counter₁ := []
  counter₂ := []
  counter₃ := []

/-- Exact input-parking phase. -/
private theorem appendBoolPool_move_eval (buffer : Option CircuitSym)
    (input moved : List CircuitSym) :
    (flip Option.bind (step appendBoolPoolProgram))^[input.length + 1]
      (some (appendBoolPoolCfg .move buffer input [] moved)) =
      some (appendBoolPoolCfg .pushTrue none [] []
        (input.reverse ++ moved)) := by
  induction input generalizing buffer moved with
  | nil => rfl
  | cons symbol rest ih =>
      rw [show (symbol :: rest).length + 1 = rest.length + 1 + 1 by simp,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step appendBoolPoolProgram))^[rest.length + 1]
          (some (appendBoolPoolCfg .move (some symbol) rest []
            (symbol :: moved))) = _
      simpa [List.reverse_cons, List.append_assoc] using
        ih (some symbol) (symbol :: moved)

/-- Exact restoration phase from an arbitrary output suffix. -/
private theorem appendBoolPool_emit_eval (buffer : Option CircuitSym)
    (work output : List CircuitSym) :
    (flip Option.bind (step appendBoolPoolProgram))^[2 * work.length + 1]
      (some (appendBoolPoolCfg .emit buffer [] output work)) =
      some (appendBoolPoolCfg .halt none []
        (work.reverse ++ output) []) := by
  induction work generalizing buffer output with
  | nil => rfl
  | cons symbol rest ih =>
      rw [show 2 * (symbol :: rest).length + 1 =
          (2 * rest.length + 1) + 1 + 1 by simp; omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step appendBoolPoolProgram))^[
            2 * rest.length + 1]
          (some (appendBoolPoolCfg .emit (some symbol) []
            (symbol :: output) rest)) = _
      simpa [List.reverse_cons, List.append_assoc] using
        ih (some symbol) (symbol :: output)

/-- Exact total step count of the pool suffix builder. -/
def appendBoolPoolSteps (input : List CircuitSym) : Nat :=
  3 * input.length + 5

/-- Canonical exact builder run. -/
def appendBoolPool_run (input : List CircuitSym) :
    EvalsToInTime (step appendBoolPoolProgram)
      (initialCfg appendBoolPoolProgram input)
      (some (haltCfg appendBoolPoolProgram (appendBoolPool input)))
      (appendBoolPoolSteps input) := by
  let afterMove := appendBoolPoolCfg .pushTrue none [] [] input.reverse
  let afterConstants := appendBoolPoolCfg .emit none []
    boolPoolGateStream input.reverse
  let beforeHalt := appendBoolPoolCfg .halt none []
    (input ++ boolPoolGateStream) []
  have hmove : EvalsToInTime (step appendBoolPoolProgram)
      (initialCfg appendBoolPoolProgram input)
      (some afterMove) (input.length + 1) := by
    refine ⟨⟨input.length + 1, ?_⟩, le_rfl⟩
    simpa [initialCfg, appendBoolPoolCfg, appendBoolPoolProgram, afterMove]
      using appendBoolPool_move_eval none input []
  have hconstants : EvalsToInTime (step appendBoolPoolProgram)
      afterMove (some afterConstants) 2 := by
    refine ⟨⟨2, ?_⟩, le_rfl⟩
    rfl
  have hemit : EvalsToInTime (step appendBoolPoolProgram)
      afterConstants (some beforeHalt) (2 * input.length + 1) := by
    refine ⟨⟨2 * input.length + 1, ?_⟩, le_rfl⟩
    simpa [afterConstants, beforeHalt, boolPoolGateStream] using
      appendBoolPool_emit_eval none input.reverse boolPoolGateStream
  have hhalt : EvalsToInTime (step appendBoolPoolProgram)
      beforeHalt
      (some (haltCfg appendBoolPoolProgram
        (input ++ boolPoolGateStream))) 1 := by
    exact ⟨⟨1, rfl⟩, le_rfl⟩
  let throughConstants := EvalsToInTime.trans (step appendBoolPoolProgram)
    (input.length + 1) 2 _ afterMove _ hmove hconstants
  let throughEmit := EvalsToInTime.trans (step appendBoolPoolProgram)
    (2 + (input.length + 1)) (2 * input.length + 1)
    _ afterConstants _ throughConstants hemit
  let full := EvalsToInTime.trans (step appendBoolPoolProgram)
    ((2 * input.length + 1) + (2 + (input.length + 1))) 1
    _ beforeHalt _ throughEmit hhalt
  have hbound : 1 + ((2 * input.length + 1) +
      (2 + (input.length + 1))) = appendBoolPoolSteps input := by
    simp [appendBoolPoolSteps]
    omega
  rw [← hbound]
  simpa [appendBoolPool] using full

/-- Exact builder output contract. -/
theorem appendBoolPool_builderOutputs :
    BuilderOutputs appendBoolPoolProgram appendBoolPool appendBoolPoolSteps := by
  intro input
  exact ⟨appendBoolPool_run input⟩

/-- Exact compiled TM2 output contract. -/
theorem appendBoolPool_outputs :
    Outputs appendBoolPoolProgram appendBoolPool appendBoolPoolSteps :=
  Outputs.of_builder_run appendBoolPool_builderOutputs

/-- Linear runtime envelope for appending the two fixed gates. -/
noncomputable def appendBoolPool_polyBound :
    PolyBound appendBoolPoolSteps where
  polynomial := 3 * Polynomial.X + 5
  bound input := by
    simp [appendBoolPoolSteps, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X]

/-- Concrete polynomial-time implementation of the Boolean-pool suffix. -/
noncomputable def appendBoolPool_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id appendBoolPool :=
  ComputableInPolyTime appendBoolPoolProgram appendBoolPool
    appendBoolPoolSteps appendBoolPool_outputs appendBoolPool_polyBound

end CLRS.Chapter34.Turing.PolyBuilder

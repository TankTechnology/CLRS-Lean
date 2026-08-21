import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Machine
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrame

/-!
# Unary-frame prefix sums: core machine

The input consists of one base frame followed by a family of increment
frames.  The output contains the current value before each increment.  This
is the reusable second-order progression primitive needed when consecutive
gate-family costs themselves form an affine progression.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Runtime data for one finite prefix-sum stream. -/
structure UnaryFramePrefixSum where
  base : Nat
  increments : List Nat
deriving DecidableEq, Repr

/-- Canonical input: the base frame followed by all increment frames. -/
def encodeUnaryFramePrefixSum (frame : UnaryFramePrefixSum) :
    List UnaryFrameSym :=
  encodeUnaryFrameBlock frame.base ++ encodeUnaryFrame frame.increments

/-- Prefix values from an arbitrary current accumulator. -/
def unaryFramePrefixSumValuesFrom : Nat → List Nat → List Nat
  | _, [] => []
  | current, increment :: rest =>
      current :: unaryFramePrefixSumValuesFrom (current + increment) rest

/-- Public prefix values. -/
def unaryFramePrefixSumValues (frame : UnaryFramePrefixSum) : List Nat :=
  unaryFramePrefixSumValuesFrom frame.base frame.increments

/-- Accumulator remaining after every increment has been consumed. -/
def unaryFramePrefixSumFinal : Nat → List Nat → Nat
  | current, [] => current
  | current, increment :: rest =>
      unaryFramePrefixSumFinal (current + increment) rest

/-- Exact forward delimiter-bearing output. -/
def unaryFramePrefixSumStream (frame : UnaryFramePrefixSum) :
    List UnaryFrameSym :=
  encodeUnaryFrame (unaryFramePrefixSumValues frame)

/-- Finite control of the reverse-output prefix-sum machine. -/
inductive UnaryFramePrefixSumLabel
  | loadBase | incBase
  | check
  | emitCurrent (first : UnaryFrameSym)
  | saveCurrent (first : UnaryFrameSym)
  | pushTick (first : UnaryFrameSym)
  | pushSeparator (first : UnaryFrameSym)
  | restoreCurrent (first : UnaryFrameSym)
  | restoreCurrentInc (first : UnaryFrameSym)
  | consumeFirst (first : UnaryFrameSym)
  | loadIncrement | incIncrement
  | clearCurrent | halt | invalid
deriving DecidableEq, Fintype

/-- One fixed program computes reversed prefix-sum frames.  Counter one is
the current sum and counter two temporarily saves it while it is emitted. -/
def unaryFramePrefixSumRevProgram : Program UnaryFrameSym UnaryFrameSym where
  Label := UnaryFramePrefixSumLabel
  main := .loadBase
  op
    | .loadBase => .popInput .invalid fun
        | .tick => .incBase
        | .separator => .check
        | .frameEnd => .invalid
    | .incBase => .inc₁ .loadBase
    | .check => .popInput .clearCurrent .emitCurrent
    | .emitCurrent first =>
        .dec₁ (.pushSeparator first) (.saveCurrent first)
    | .saveCurrent first => .inc₂ (.pushTick first)
    | .pushTick first => .pushOutput .tick (.emitCurrent first)
    | .pushSeparator first =>
        .pushOutput .separator (.restoreCurrent first)
    | .restoreCurrent first =>
        .dec₂ (.consumeFirst first) (.restoreCurrentInc first)
    | .restoreCurrentInc first => .inc₁ (.restoreCurrent first)
    | .consumeFirst .tick => .inc₁ .loadIncrement
    | .consumeFirst .separator => .jump .check
    | .consumeFirst .frameEnd => .jump .invalid
    | .loadIncrement => .popInput .invalid fun
        | .tick => .incIncrement
        | .separator => .check
        | .frameEnd => .invalid
    | .incIncrement => .inc₁ .loadIncrement
    | .clearCurrent => .dec₁ .halt .clearCurrent
    | .halt => .halt
    | .invalid => .halt

/-- Proof-facing configurations of the prefix-sum program. -/
def unaryFramePrefixSumCfg
    (label : UnaryFramePrefixSumLabel)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output : List UnaryFrameSym)
    (current saved : List Unit) :
    BuilderCfg unaryFramePrefixSumRevProgram where
  label := some label
  buffer₁ := buffer₁
  buffer₂ := buffer₂
  test := test
  input := input
  output := output
  work₁ := []
  work₂ := []
  counter₁ := current
  counter₂ := saved
  counter₃ := []

end CLRS.Chapter34.Turing.PolyBuilder

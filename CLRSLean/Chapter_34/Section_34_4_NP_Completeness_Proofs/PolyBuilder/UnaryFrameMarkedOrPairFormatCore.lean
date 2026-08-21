import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OrFin

/-!
# Formatting marked operand pairs as finite-OR frames: core

The source-side representation stores one row as the ordinary unary encoding
of `[left, right]`, followed by `frameEnd`.  The finite OR controller expects
the canonical frame

`frameEnd / left / 0 / (right + 1) / frameEnd`.

This file defines the pure encodings and the fixed finite controller.  Exact
simulation and polynomial runtime packaging live in separate modules.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Marked two-field source encoding consumed by the formatter. -/
def encodeAffineOrFinMarkedPairFrame (frame : AffineOrFinPairFrame) :
    List UnaryFrameSym :=
  encodeUnaryFrame [frame.left, frame.right] ++ [.frameEnd]

def encodeAffineOrFinMarkedPairFrames
    (frames : List AffineOrFinPairFrame) : List UnaryFrameSym :=
  frames.flatMap encodeAffineOrFinMarkedPairFrame

/-- Finite phases of the direct two-field to OR-frame formatter. -/
inductive UnaryFrameMarkedOrPairFormatLabel
  | beginRow
  | emitOpen (symbol : UnaryFrameSym)
  | left (symbol : UnaryFrameSym)
  | scanLeft
  | emitZero
  | scanRight
  | right (symbol : UnaryFrameSym)
  | emitRightSeparator
  | expectEnd
  | endRow
  | finish
  | invalid
deriving DecidableEq, Fintype

/-- Prepend-output controller emitting the reverse canonical OR-frame
serialization. -/
def unaryFrameMarkedOrPairFormatRevProgram :
    Program UnaryFrameSym UnaryFrameSym where
  Label := UnaryFrameMarkedOrPairFormatLabel
  main := .beginRow
  op
    | .beginRow => .popInput .finish .emitOpen
    | .emitOpen symbol => .pushOutput .frameEnd (.left symbol)
    | .left .tick => .pushOutput .tick .scanLeft
    | .left .separator => .pushOutput .separator .emitZero
    | .left .frameEnd => .jump .invalid
    | .scanLeft => .popInput .invalid .left
    | .emitZero => .pushOutput .separator .scanRight
    | .scanRight => .popInput .invalid .right
    | .right .tick => .pushOutput .tick .scanRight
    | .right .separator => .pushOutput .tick .emitRightSeparator
    | .right .frameEnd => .jump .invalid
    | .emitRightSeparator => .pushOutput .separator .expectEnd
    | .expectEnd => .popInput .invalid fun
        | .frameEnd => .endRow
        | _ => .invalid
    | .endRow => .pushOutput .frameEnd .beginRow
    | .finish => .halt
    | .invalid => .halt

def unaryFrameMarkedOrPairFormatCfg
    (label : UnaryFrameMarkedOrPairFormatLabel)
    (buffer : Option UnaryFrameSym)
    (input output : List UnaryFrameSym) :
    BuilderCfg unaryFrameMarkedOrPairFormatRevProgram where
  label := some label
  buffer₁ := buffer
  buffer₂ := none
  test := false
  input := input
  output := output
  work₁ := []
  work₂ := []
  counter₁ := []
  counter₂ := []
  counter₃ := []

def unaryFrameMarkedOrPairFormatLoopCfg
    (input output : List UnaryFrameSym) :
    BuilderCfg unaryFrameMarkedOrPairFormatRevProgram :=
  unaryFrameMarkedOrPairFormatCfg .beginRow none input output

end CLRS.Chapter34.Turing.PolyBuilder

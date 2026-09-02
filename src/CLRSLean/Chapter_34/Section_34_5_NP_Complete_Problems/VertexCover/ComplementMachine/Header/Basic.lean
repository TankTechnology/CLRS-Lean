import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.Complement
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Machine
import Mathlib.Tactic.DeriveFintype

/-!
# VERTEX-COVER complement machine: transformed header controller

The controller preserves the unary vertex count and subtracts the unary target
count from a second copy.  Its prepend-only output is deliberately emitted from
right to left, producing the canonical header `n, n - k`.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.VertexCover.ComplementMachine.Header

open PolyBuilder

/-- Header of the complement instance, without its edge table. -/
def complementHeader (I : CliqueInstance) : List CliqueSym :=
  .instanceMark :: prependCliqueTicks I.vertexCount
    (.fieldSep :: prependCliqueTicks (I.vertexCount - I.targetSize)
      [.fieldSep])

inductive Label
  | start | vertices | incrementRemaining | incrementOriginal
  | targets | decrementRemaining | clearEdges
  | emitRightSeparator | emitRemaining | pushRemainingTick
  | emitMiddleSeparator | emitOriginal | pushOriginalTick
  | emitInstance | invalid | halt
deriving DecidableEq, Fintype

/-- Fixed controller computing the complement header from a canonical CLIQUE
instance encoding. -/
def program : Program CliqueSym CliqueSym where
  Label := Label
  main := .start
  op
    | .start => .popInput .invalid fun
        | .instanceMark => .vertices
        | _ => .invalid
    | .vertices => .popInput .invalid fun
        | .tick => .incrementRemaining
        | .fieldSep => .targets
        | _ => .invalid
    | .incrementRemaining => .inc₁ .incrementOriginal
    | .incrementOriginal => .inc₂ .vertices
    | .targets => .popInput .invalid fun
        | .tick => .decrementRemaining
        | .fieldSep => .clearEdges
        | _ => .invalid
    | .decrementRemaining => .dec₁ .targets .targets
    | .clearEdges => .popInput .emitRightSeparator fun _ => .clearEdges
    | .emitRightSeparator => .pushOutput .fieldSep .emitRemaining
    | .emitRemaining => .dec₁ .emitMiddleSeparator .pushRemainingTick
    | .pushRemainingTick => .pushOutput .tick .emitRemaining
    | .emitMiddleSeparator => .pushOutput .fieldSep .emitOriginal
    | .emitOriginal => .dec₂ .emitInstance .pushOriginalTick
    | .pushOriginalTick => .pushOutput .tick .emitOriginal
    | .emitInstance => .pushOutput .instanceMark .halt
    | .invalid => .halt
    | .halt => .halt

def cfg (label : Label) (buffer : Option CliqueSym) (test : Bool)
    (input output : List CliqueSym) (remaining original : List Unit) :
    BuilderCfg program where
  label := some label
  buffer₁ := buffer
  buffer₂ := none
  test := test
  input := input
  output := output
  work₁ := []
  work₂ := []
  counter₁ := remaining
  counter₂ := original
  counter₃ := []

end CLRS.Chapter34.Turing.VertexCover.ComplementMachine.Header

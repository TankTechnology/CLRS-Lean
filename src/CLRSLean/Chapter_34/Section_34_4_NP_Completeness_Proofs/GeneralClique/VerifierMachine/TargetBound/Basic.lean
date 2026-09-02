import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.SyntaxPass.Runtime
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Machine
import Mathlib.Tactic.DeriveFintype

/-!
# General CLIQUE verifier: target-size bound controller

This fixed controller checks the graph-side inequality `targetSize ≤
vertexCount` directly on the two leading unary fields of a raw instance.  The
syntax pass is responsible for rejecting noncanonical token arrangements.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.TargetBound

open PolyBuilder

/-- Count ticks up to the next field separator and return the remaining input.
Tokens other than ticks and the separator are ignored so that this pass stays
total on arbitrary raw strings. -/
def ticksThroughSeparator : List CliqueSym → Option (Nat × List CliqueSym)
  | [] => none
  | .tick :: rest =>
      match ticksThroughSeparator rest with
      | some (count, tail) => some (count + 1, tail)
      | none => none
  | .fieldSep :: rest => some (0, rest)
  | _ :: rest => ticksThroughSeparator rest

/-- Boolean result of subtracting the target field from a loaded unary vertex
count. -/
def targetResult : Nat → List CliqueSym → Bool
  | _, [] => false
  | 0, .tick :: _ => false
  | count + 1, .tick :: rest => targetResult count rest
  | _, .fieldSep :: _ => true
  | count, _ :: rest => targetResult count rest

/-- Boolean result of loading the vertex field before checking the target. -/
def vertexResult : Nat → List CliqueSym → Bool
  | _, [] => false
  | count, .tick :: rest => vertexResult (count + 1) rest
  | count, .fieldSep :: rest => targetResult count rest
  | count, _ :: rest => vertexResult count rest

/-- Raw Boolean semantics of the target-bound pass.  The first instance token
is consumed as the instance marker; exact grammar is checked independently. -/
def targetBoundPass (_certificate input : List CliqueSym) : Bool :=
  match input with
  | [] => false
  | _ :: fields => vertexResult 0 fields

/-- Finite control for loading the vertex-count field and subtracting the
target-size field from it. -/
inductive Label
  | certificate
  | instanceMark
  | vertexCount
  | incrementVertexCount
  | targetSize
  | decrementTargetSize
  | clearInput (answer : Bool)
  | clearCount (answer : Bool)
  | emit (answer : Bool)
  | halt
deriving DecidableEq, Fintype

/-- Concrete builder program for `targetBoundPass`. -/
def program : Program (Option CliqueSym) Bool where
  Label := Label
  main := .certificate
  op
    | .certificate => .popInput (.clearCount false) fun
        | none => .instanceMark
        | some _ => .certificate
    | .instanceMark => .popInput (.clearCount false) fun _ => .vertexCount
    | .vertexCount => .popInput (.clearCount false) fun
        | some .tick => .incrementVertexCount
        | some .fieldSep => .targetSize
        | _ => .vertexCount
    | .incrementVertexCount => .inc₁ .vertexCount
    | .targetSize => .popInput (.clearCount false) fun
        | some .tick => .decrementTargetSize
        | some .fieldSep => .clearInput true
        | _ => .targetSize
    | .decrementTargetSize => .dec₁ (.clearInput false) .targetSize
    | .clearInput answer => .popInput (.clearCount answer)
        (fun _ => .clearInput answer)
    | .clearCount answer => .dec₁ (.emit answer) (.clearCount answer)
    | .emit answer => .pushOutput answer .halt
    | .halt => .halt

/-- Explicit independent-semantics configuration used by the phase proofs. -/
def cfg (label : Label) (buffer : Option (Option CliqueSym))
    (test : Bool) (input : List (Option CliqueSym)) (output : List Bool)
    (count : List Unit) : BuilderCfg program where
  label := some label
  buffer₁ := buffer
  buffer₂ := none
  test := test
  input := input
  output := output
  work₁ := []
  work₂ := []
  counter₁ := count
  counter₂ := []
  counter₃ := []

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.TargetBound

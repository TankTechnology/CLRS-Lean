import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.Semantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Machine
import Mathlib.Tactic.DeriveFintype

/-!
# General CLIQUE verifier: concrete cardinality controller

This fixed counter program checks that the number of vertex records in the
certificate equals the unary target-size field of the instance.  Other
grammar obligations remain the responsibility of the syntax pass.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.Cardinality

open PolyBuilder

/-- Count ticks until the next field separator.  Other tokens are ignored;
missing termination is reported by `none`. -/
def targetTicksUntilSeparator : List CliqueSym → Option Nat
  | [] => none
  | .tick :: rest => (· + 1) <$> targetTicksUntilSeparator rest
  | .fieldSep :: _ => some 0
  | _ :: rest => targetTicksUntilSeparator rest

/-- Locate the first instance field separator, then read the target field. -/
def rawTargetSize : List CliqueSym → Option Nat
  | [] => none
  | .fieldSep :: rest => targetTicksUntilSeparator rest
  | _ :: rest => rawTargetSize rest

/-- Total Boolean specification computed by the cardinality controller. -/
def cardinalityPass (certificate input : List CliqueSym) : Bool :=
  match rawTargetSize input with
  | none => false
  | some targetSize =>
      decide (certificate.count .vertexMark = targetSize)

/-- Finite control for counting certificate records and subtracting the target
field from that count. -/
inductive Label
  | certificate
  | countVertex
  | instanceHeader
  | target
  | decrementTarget
  | targetTooLarge
  | clearInput (tooLarge : Bool)
  | checkCount
  | clearCount
  | emit (answer : Bool)
  | halt
deriving DecidableEq, Fintype

/-- Concrete builder program for `cardinalityPass` on a paired raw input. -/
def program : Program (Option CliqueSym) Bool where
  Label := Label
  main := .certificate
  op
    | .certificate => .popInput .clearCount fun
        | none => .instanceHeader
        | some .vertexMark => .countVertex
        | some _ => .certificate
    | .countVertex => .inc₁ .certificate
    | .instanceHeader => .popInput .clearCount fun
        | some .fieldSep => .target
        | _ => .instanceHeader
    | .target => .popInput .clearCount fun
        | some .tick => .decrementTarget
        | some .fieldSep => .clearInput false
        | _ => .target
    | .decrementTarget => .dec₁ .targetTooLarge .target
    | .targetTooLarge => .popInput .clearCount fun
        | some .fieldSep => .clearInput true
        | _ => .targetTooLarge
    | .clearInput tooLarge => .popInput
        (if tooLarge then .emit false else .checkCount)
        (fun _ => .clearInput tooLarge)
    | .checkCount => .dec₁ (.emit true) .clearCount
    | .clearCount => .dec₁ (.emit false) .clearCount
    | .emit answer => .pushOutput answer .halt
    | .halt => .halt

/-- Explicit independent-semantics configuration for phase proofs. -/
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

/-- Initial configuration specialized to a certificate/input pair. -/
def startCfg (certificate input : List CliqueSym) : BuilderCfg program :=
  cfg .certificate none false (pairEncoding certificate input) [] []

@[simp] theorem startCfg_eq_initialCfg (certificate input : List CliqueSym) :
    startCfg certificate input =
      initialCfg program (pairEncoding certificate input) := rfl

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.Cardinality

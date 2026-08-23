import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.TargetBound.Canonical
import Mathlib.Tactic.DeriveFintype

/-!
# General CLIQUE verifier: normalized-edge controller

Every stored undirected edge must have its smaller endpoint first.  This file
defines both the raw recursive Boolean and a fixed counter controller checking
`left < right` for every serialized edge record.  Grammar rejection remains a
separate syntax pass.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.EdgeOrder

open PolyBuilder

mutual
  /-- Scan the edge suffix, checking every record encountered. -/
  def edgesResult : List CliqueSym → Bool
    | [] => true
    | .edgeMark :: rest => leftResult 0 rest
    | _ :: rest => edgesResult rest

  /-- Load the unary left endpoint of one edge. -/
  def leftResult : Nat → List CliqueSym → Bool
    | _, [] => false
    | count, .tick :: rest => leftResult (count + 1) rest
    | count, .pairSep :: rest => rightResult count false rest
    | count, _ :: rest => leftResult count rest

  /-- Subtract right-endpoint ticks from the loaded left endpoint.  `exceeded`
  records that at least one right tick was seen after the counter reached zero. -/
  def rightResult : Nat → Bool → List CliqueSym → Bool
    | _, _, [] => false
    | 0, _, .tick :: rest => rightResult 0 true rest
    | count + 1, exceeded, .tick :: rest =>
        rightResult count exceeded rest
    | count, exceeded, .recordEnd :: rest =>
        decide (count = 0) && exceeded && edgesResult rest
    | count, exceeded, _ :: rest => rightResult count exceeded rest
end

/-- Scan past one header field and continue with `next` after its separator. -/
def throughField (next : List CliqueSym → Bool) : List CliqueSym → Bool
  | [] => false
  | .fieldSep :: rest => next rest
  | _ :: rest => throughField next rest

/-- Total raw Boolean computed by the normalized-edge controller. -/
def edgeOrderPass (_certificate input : List CliqueSym) : Bool :=
  match input with
  | [] => false
  | _ :: fields => throughField (throughField edgesResult) fields

/-- Finite control for repeated unary strict comparisons. -/
inductive Label
  | certificate
  | instanceMark
  | vertexField
  | targetField
  | edges
  | left
  | incrementLeft
  | right (exceeded : Bool)
  | decrementRight (exceeded : Bool)
  | finishEdge (exceeded : Bool)
  | clearInput (answer : Bool)
  | clearCount (answer : Bool)
  | emit (answer : Bool)
  | halt
deriving DecidableEq, Fintype

/-- Concrete builder program for `edgeOrderPass`. -/
def program : Program (Option CliqueSym) Bool where
  Label := Label
  main := .certificate
  op
    | .certificate => .popInput (.clearCount false) fun
        | none => .instanceMark
        | some _ => .certificate
    | .instanceMark => .popInput (.clearCount false) fun _ => .vertexField
    | .vertexField => .popInput (.clearCount false) fun
        | some .fieldSep => .targetField
        | _ => .vertexField
    | .targetField => .popInput (.clearCount false) fun
        | some .fieldSep => .edges
        | _ => .targetField
    | .edges => .popInput (.clearCount true) fun
        | some .edgeMark => .left
        | _ => .edges
    | .left => .popInput (.clearCount false) fun
        | some .tick => .incrementLeft
        | some .pairSep => .right false
        | _ => .left
    | .incrementLeft => .inc₁ .left
    | .right exceeded => .popInput (.clearCount false) fun
        | some .tick => .decrementRight exceeded
        | some .recordEnd => .finishEdge exceeded
        | _ => .right exceeded
    | .decrementRight exceeded => .dec₁ (.right true) (.right exceeded)
    | .finishEdge exceeded => .dec₁
        (if exceeded then .edges else .clearInput false) (.clearInput false)
    | .clearInput answer => .popInput (.clearCount answer)
        (fun _ => .clearInput answer)
    | .clearCount answer => .dec₁ (.emit answer) (.clearCount answer)
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

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.EdgeOrder

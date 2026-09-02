import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.EdgeOrder.Canonical
import Mathlib.Tactic.DeriveFintype

/-!
# General CLIQUE verifier: edge-endpoint bound controller

This pass loads {lit}`vertexCount` once on work stack one.  While scanning a right
endpoint it moves one saved tick to work stack two for every endpoint tick.
At the record terminator it moves one additional tick, enforcing strictness,
then restores the whole budget before scanning the next edge.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.EndpointBound

open PolyBuilder

mutual
  /-- Scan all serialized edge records with a restored vertex budget. -/
  def edgesResult : Nat → List CliqueSym → Bool
    | _, [] => true
    | vertexCount, .edgeMark :: rest => leftResult vertexCount rest
    | vertexCount, _ :: rest => edgesResult vertexCount rest

  /-- Skip the left endpoint; edge normalization is checked by another pass. -/
  def leftResult : Nat → List CliqueSym → Bool
    | _, [] => false
    | vertexCount, .pairSep :: rest =>
        rightResult vertexCount 0 rest
    | vertexCount, _ :: rest => leftResult vertexCount rest

  /-- Compare a right endpoint with the remaining vertex budget.  {lit}`spent`
  records the tokens moved aside so the full budget can be restored. -/
  def rightResult : Nat → Nat → List CliqueSym → Bool
    | _, _, [] => false
    | 0, _, .tick :: _ => false
    | remaining + 1, spent, .tick :: rest =>
        rightResult remaining (spent + 1) rest
    | 0, _, .recordEnd :: _ => false
    | remaining + 1, spent, .recordEnd :: rest =>
        edgesResult (remaining + 1 + spent) rest
    | remaining, spent, _ :: rest => rightResult remaining spent rest
end

/-- Skip the target-size field before entering the edge scan. -/
def targetFieldResult (vertexCount : Nat) : List CliqueSym → Bool
  | [] => false
  | .fieldSep :: rest => edgesResult vertexCount rest
  | _ :: rest => targetFieldResult vertexCount rest

/-- Load the unary vertex-count field. -/
def vertexFieldResult : Nat → List CliqueSym → Bool
  | _, [] => false
  | vertexCount, .tick :: rest =>
      vertexFieldResult (vertexCount + 1) rest
  | vertexCount, .fieldSep :: rest => targetFieldResult vertexCount rest
  | vertexCount, _ :: rest => vertexFieldResult vertexCount rest

/-- Total raw Boolean semantics of the endpoint-bound pass. -/
def endpointBoundPass (_certificate input : List CliqueSym) : Bool :=
  match input with
  | [] => false
  | _ :: fields => vertexFieldResult 0 fields

/-- Finite control for the reusable unary-budget algorithm. -/
inductive Label
  | certificate
  | instanceMark
  | vertexField
  | saveVertexTick
  | targetField
  | edges
  | left
  | right
  | spendTick
  | demandStrict
  | restore
  | clearInput (answer : Bool)
  | clearWork₁ (answer : Bool)
  | clearWork₂ (answer : Bool)
  | emit (answer : Bool)
  | halt
deriving DecidableEq, Fintype

/-- Concrete builder program for {name}`endpointBoundPass`. -/
def program : Program (Option CliqueSym) Bool where
  Label := Label
  main := .certificate
  op
    | .certificate => .popInput (.clearInput false) fun
        | none => .instanceMark
        | some _ => .certificate
    | .instanceMark => .popInput (.clearInput false) fun _ => .vertexField
    | .vertexField => .popInput (.clearInput false) fun
        | some .tick => .saveVertexTick
        | some .fieldSep => .targetField
        | _ => .vertexField
    | .saveVertexTick => .pushWork₁ (some .tick) .vertexField
    | .targetField => .popInput (.clearInput false) fun
        | some .fieldSep => .edges
        | _ => .targetField
    | .edges => .popInput (.clearWork₁ true) fun
        | some .edgeMark => .left
        | _ => .edges
    | .left => .popInput (.clearInput false) fun
        | some .pairSep => .right
        | _ => .left
    | .right => .popInput (.clearInput false) fun
        | some .tick => .spendTick
        | some .recordEnd => .demandStrict
        | _ => .right
    | .spendTick => .moveWork₁Work₂ (.clearInput false) fun _ => .right
    | .demandStrict =>
        .moveWork₁Work₂ (.clearInput false) fun _ => .restore
    | .restore => .moveWork₂Work₁ .edges fun _ => .restore
    | .clearInput answer =>
        .popInput (.clearWork₁ answer) fun _ => .clearInput answer
    | .clearWork₁ answer =>
        .popWork₁ (.clearWork₂ answer) fun _ => .clearWork₁ answer
    | .clearWork₂ answer =>
        .popWork₂ (.emit answer) fun _ => .clearWork₂ answer
    | .emit answer => .pushOutput answer .halt
    | .halt => .halt

/-- Explicit independent-semantics configuration for the phase proofs. -/
def cfg (label : Label) (buffer₁ buffer₂ : Option (Option CliqueSym))
    (test : Bool) (input : List (Option CliqueSym)) (output : List Bool)
    (work₁ work₂ : List (Option CliqueSym)) : BuilderCfg program where
  label := some label
  buffer₁ := buffer₁
  buffer₂ := buffer₂
  test := test
  input := input
  output := output
  work₁ := work₁
  work₂ := work₂
  counter₁ := []
  counter₂ := []
  counter₃ := []

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.EndpointBound

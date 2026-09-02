import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.EdgeBounds
import Mathlib.Tactic.DeriveFintype

/-!
# General CLIQUE verifier: certificate vertex range

The controller saves the certificate, reads {lit}`vertexCount` from the instance
header, restores the certificate to the input stack, and checks every unary
vertex record against one reusable work-stack budget.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.CertificateRange

open PolyBuilder

mutual
  /-- Scan all certificate vertex records with a restored vertex budget. -/
  def verticesResult : Nat → List CliqueSym → Bool
    | _, [] => true
    | vertexCount, .vertexMark :: rest =>
        vertexResult vertexCount 0 rest
    | vertexCount, _ :: rest => verticesResult vertexCount rest

  /-- Consume one unary vertex against the remaining budget. -/
  def vertexResult : Nat → Nat → List CliqueSym → Bool
    | _, _, [] => false
    | 0, _, .tick :: _ => false
    | remaining + 1, spent, .tick :: rest =>
        vertexResult remaining (spent + 1) rest
    | 0, _, .recordEnd :: _ => false
    | remaining + 1, spent, .recordEnd :: rest =>
        verticesResult (remaining + 1 + spent) rest
    | remaining, spent, _ :: rest => vertexResult remaining spent rest
end

/-- Interpret the first certificate token as its leading marker. -/
def certificatePayloadResult (vertexCount : Nat) : List CliqueSym → Bool
  | [] => false
  | _ :: payload => verticesResult vertexCount payload

/-- Read the unary vertex-count field before checking the saved certificate. -/
def vertexFieldResult (certificate : List CliqueSym) :
    Nat → List CliqueSym → Bool
  | _, [] => false
  | loaded, .tick :: rest => vertexFieldResult certificate (loaded + 1) rest
  | loaded, .fieldSep :: _ => certificatePayloadResult loaded certificate
  | loaded, _ :: rest => vertexFieldResult certificate loaded rest

/-- Total raw Boolean semantics of the certificate-range pass. -/
def certificateRangePass (certificate input : List CliqueSym) : Bool :=
  match input with
  | [] => false
  | _ :: fields => vertexFieldResult certificate 0 fields

/-- Finite control for saving the certificate and reusing the vertex budget. -/
inductive Label
  | saveCertificate
  | saveCertificateSymbol (symbol : Option CliqueSym)
  | instanceMark
  | vertexField
  | saveVertexTick
  | discardInstance
  | restoreCertificate
  | certificateMark
  | vertices
  | vertex
  | spendTick
  | incrementSpent
  | demandStrict
  | saveStrict
  | restoreBudget
  | restoreTick
  | clearInput (answer : Bool)
  | clearWork₁ (answer : Bool)
  | clearWork₂ (answer : Bool)
  | clearCount (answer : Bool)
  | emit (answer : Bool)
  | halt
deriving DecidableEq, Fintype

/-- Concrete builder program for {name}`certificateRangePass`. -/
def program : Program (Option CliqueSym) Bool where
  Label := Label
  main := .saveCertificate
  op
    | .saveCertificate => .popInput (.clearInput false) fun
        | none => .instanceMark
        | some symbol => .saveCertificateSymbol (some symbol)
    | .saveCertificateSymbol symbol =>
        .pushWork₁ symbol .saveCertificate
    | .instanceMark => .popInput (.clearInput false) fun _ => .vertexField
    | .vertexField => .popInput (.clearInput false) fun
        | some .tick => .saveVertexTick
        | some .fieldSep => .discardInstance
        | _ => .vertexField
    | .saveVertexTick => .pushWork₂ (some .tick) .vertexField
    | .discardInstance =>
        .popInput .restoreCertificate fun _ => .discardInstance
    | .restoreCertificate =>
        .moveWork₁Input .certificateMark fun _ => .restoreCertificate
    | .certificateMark => .popInput (.clearInput false) fun _ => .vertices
    | .vertices => .popInput (.clearWork₂ true) fun
        | some .vertexMark => .vertex
        | _ => .vertices
    | .vertex => .popInput (.clearInput false) fun
        | some .tick => .spendTick
        | some .recordEnd => .demandStrict
        | _ => .vertex
    | .spendTick =>
        .popWork₂ (.clearInput false) fun _ => .incrementSpent
    | .incrementSpent => .inc₁ .vertex
    | .demandStrict =>
        .popWork₂ (.clearInput false) fun _ => .saveStrict
    | .saveStrict => .inc₁ .restoreBudget
    | .restoreBudget => .dec₁ .vertices .restoreTick
    | .restoreTick => .pushWork₂ (some .tick) .restoreBudget
    | .clearInput answer =>
        .popInput (.clearWork₁ answer) fun _ => .clearInput answer
    | .clearWork₁ answer =>
        .popWork₁ (.clearWork₂ answer) fun _ => .clearWork₁ answer
    | .clearWork₂ answer =>
        .popWork₂ (.clearCount answer) fun _ => .clearWork₂ answer
    | .clearCount answer =>
        .dec₁ (.emit answer) (.clearCount answer)
    | .emit answer => .pushOutput answer .halt
    | .halt => .halt

/-- Explicit independent-semantics configuration for phase proofs. -/
def cfg (label : Label) (buffer₁ buffer₂ : Option (Option CliqueSym))
    (test : Bool) (input : List (Option CliqueSym)) (output : List Bool)
    (work₁ work₂ : List (Option CliqueSym))
    (count : List Unit) : BuilderCfg program where
  label := some label
  buffer₁ := buffer₁
  buffer₂ := buffer₂
  test := test
  input := input
  output := output
  work₁ := work₁
  work₂ := work₂
  counter₁ := count
  counter₂ := []
  counter₃ := []

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.CertificateRange

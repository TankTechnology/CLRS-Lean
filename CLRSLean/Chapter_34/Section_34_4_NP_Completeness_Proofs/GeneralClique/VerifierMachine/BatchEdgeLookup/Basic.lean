import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.QueryNormalizer.Composition
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.EdgeLookup.Runtime
import Mathlib.Tactic.DeriveFintype

/-!
# General CLIQUE verifier: batch edge lookup

The input is a fixed-pair encoding of a canonical query stream and one graph
instance.  Queries are first reversed onto a work stack.  For each query the
controller scans the graph, preserving every graph symbol on a second work
stack, and then restores the graph before processing the next query.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.BatchEdgeLookup

open PolyBuilder

/-- Semantic result computed by the concrete batch controller. -/
def queriesInEdgesBool (I : CliqueInstance)
    (queries : List (Nat × Nat)) : Bool :=
  queries.all fun edge => decide (edge ∈ I.edges)

/-- Pointwise membership answers, in the same order as the query stream. -/
def queryMembershipBits (I : CliqueInstance)
    (queries : List (Nat × Nat)) : List Bool :=
  queries.map fun edge => decide (edge ∈ I.edges)

/-- Public result stream: aggregate answer followed by pointwise answers. -/
def batchResultStream (I : CliqueInstance)
    (queries : List (Nat × Nat)) : List Bool :=
  queriesInEdgesBool I queries :: queryMembershipBits I queries

/-- Finite control for repeated edge-table scans. -/
inductive Label
  | loadQueries | beginQueries | nextQuery (aggregate : Bool)
  | queryRight (aggregate : Bool) | incQueryRight (aggregate : Bool)
  | queryLeft (aggregate : Bool) | incQueryLeft (aggregate : Bool)
  | instanceMark (aggregate : Bool)
  | vertexField (aggregate : Bool) | targetField (aggregate : Bool)
  | edges (aggregate : Bool)
  | left (aggregate equal : Bool) | spendLeft (aggregate equal : Bool)
  | saveLeft (aggregate equal : Bool) | leftEnd (aggregate equal : Bool)
  | saveLeftRemainder (aggregate : Bool) | drainLeft (aggregate : Bool)
  | restoreLeft (aggregate equal : Bool)
  | restoreLeftInc (aggregate equal : Bool)
  | right (aggregate equal : Bool) | spendRight (aggregate equal : Bool)
  | saveRight (aggregate equal : Bool) | rightEnd (aggregate equal : Bool)
  | saveRightRemainder (aggregate : Bool) | drainRight (aggregate : Bool)
  | restoreRight (aggregate answer : Bool)
  | restoreRightInc (aggregate answer : Bool)
  | drainGraph (aggregate : Bool)
  | clearLeft (aggregate answer : Bool)
  | clearRight (aggregate answer : Bool)
  | clearScratch (aggregate answer : Bool)
  | restoreGraph (aggregate answer : Bool)
  | emitDecision (aggregate answer : Bool)
  | discardGraph (answer : Bool) | clearWork₁ (answer : Bool)
  | clearWork₂ (answer : Bool) | clearFinalLeft (answer : Bool)
  | clearFinalRight (answer : Bool) | clearFinalScratch (answer : Bool)
  | emit (answer : Bool) | halt
deriving DecidableEq, Fintype

/-- Fixed controller for conjunction of all canonical edge queries. -/
def program : Program (Option CliqueSym) Bool where
  Label := Label
  main := .loadQueries
  op
    | .loadQueries => .moveInputWork₁ (.discardGraph false) fun
        | none => .beginQueries
        | some _ => .loadQueries
    | .beginQueries => .popWork₁ (.discardGraph false) fun
        | none => .nextQuery true
        | some _ => .discardGraph false
    | .nextQuery aggregate => .popWork₁ (.discardGraph aggregate) fun
        | some .recordEnd => .queryRight aggregate
        | _ => .discardGraph false
    | .queryRight aggregate => .popWork₁ (.discardGraph false) fun
        | some .tick => .incQueryRight aggregate
        | some .pairSep => .queryLeft aggregate
        | _ => .discardGraph false
    | .incQueryRight aggregate => .inc₂ (.queryRight aggregate)
    | .queryLeft aggregate => .popWork₁ (.discardGraph false) fun
        | some .tick => .incQueryLeft aggregate
        | some .edgeMark => .instanceMark aggregate
        | _ => .discardGraph false
    | .incQueryLeft aggregate => .inc₁ (.queryLeft aggregate)
    | .instanceMark aggregate => .moveInputWork₂ (.clearLeft aggregate false) fun
        | some .instanceMark => .vertexField aggregate
        | _ => .drainGraph aggregate
    | .vertexField aggregate =>
        .moveInputWork₂ (.clearLeft aggregate false) fun
          | some .fieldSep => .targetField aggregate
          | _ => .vertexField aggregate
    | .targetField aggregate =>
        .moveInputWork₂ (.clearLeft aggregate false) fun
          | some .fieldSep => .edges aggregate
          | _ => .targetField aggregate
    | .edges aggregate => .moveInputWork₂ (.clearLeft aggregate false) fun
        | some .edgeMark => .left aggregate true
        | _ => .drainGraph aggregate
    | .left aggregate equal =>
        .moveInputWork₂ (.clearLeft aggregate false) fun
          | some .tick => .spendLeft aggregate equal
          | some .pairSep => .leftEnd aggregate equal
          | _ => .left aggregate false
    | .spendLeft aggregate equal =>
        .dec₁ (.left aggregate false) (.saveLeft aggregate equal)
    | .saveLeft aggregate equal => .inc₃ (.left aggregate equal)
    | .leftEnd aggregate equal =>
        .dec₁ (.restoreLeft aggregate equal) (.saveLeftRemainder aggregate)
    | .saveLeftRemainder aggregate => .inc₃ (.drainLeft aggregate)
    | .drainLeft aggregate =>
        .dec₁ (.restoreLeft aggregate false) (.saveLeftRemainder aggregate)
    | .restoreLeft aggregate equal =>
        .dec₃ (.right aggregate equal) (.restoreLeftInc aggregate equal)
    | .restoreLeftInc aggregate equal => .inc₁ (.restoreLeft aggregate equal)
    | .right aggregate equal =>
        .moveInputWork₂ (.clearLeft aggregate false) fun
          | some .tick => .spendRight aggregate equal
          | some .recordEnd => .rightEnd aggregate equal
          | _ => .right aggregate false
    | .spendRight aggregate equal =>
        .dec₂ (.right aggregate false) (.saveRight aggregate equal)
    | .saveRight aggregate equal => .inc₃ (.right aggregate equal)
    | .rightEnd aggregate equal =>
        .dec₂ (.restoreRight aggregate equal)
          (.saveRightRemainder aggregate)
    | .saveRightRemainder aggregate => .inc₃ (.drainRight aggregate)
    | .drainRight aggregate =>
        .dec₂ (.restoreRight aggregate false)
          (.saveRightRemainder aggregate)
    | .restoreRight aggregate answer =>
        .dec₃
          (if answer then .drainGraph aggregate else .edges aggregate)
          (.restoreRightInc aggregate answer)
    | .restoreRightInc aggregate answer =>
        .inc₂ (.restoreRight aggregate answer)
    | .drainGraph aggregate =>
        .moveInputWork₂ (.clearLeft aggregate true) fun _ =>
          .drainGraph aggregate
    | .clearLeft aggregate answer =>
        .dec₁ (.clearRight aggregate answer) (.clearLeft aggregate answer)
    | .clearRight aggregate answer =>
        .dec₂ (.clearScratch aggregate answer) (.clearRight aggregate answer)
    | .clearScratch aggregate answer =>
        .dec₃ (.restoreGraph aggregate answer) (.clearScratch aggregate answer)
    | .restoreGraph aggregate answer =>
        .moveWork₂Input (.emitDecision aggregate answer) fun _ =>
          .restoreGraph aggregate answer
    | .emitDecision aggregate answer =>
        .pushOutput answer (.nextQuery (aggregate && answer))
    | .discardGraph answer =>
        .popInput (.clearWork₁ answer) fun _ => .discardGraph answer
    | .clearWork₁ answer =>
        .popWork₁ (.clearWork₂ answer) fun _ => .clearWork₁ answer
    | .clearWork₂ answer =>
        .popWork₂ (.clearFinalLeft answer) fun _ => .clearWork₂ answer
    | .clearFinalLeft answer =>
        .dec₁ (.clearFinalRight answer) (.clearFinalLeft answer)
    | .clearFinalRight answer =>
        .dec₂ (.clearFinalScratch answer) (.clearFinalRight answer)
    | .clearFinalScratch answer =>
        .dec₃ (.emit answer) (.clearFinalScratch answer)
    | .emit answer => .pushOutput answer .halt
    | .halt => .halt

/-- Proof-facing independent configuration. -/
def cfg (label : Label) (buffer₁ buffer₂ : Option (Option CliqueSym))
    (test : Bool) (input : List (Option CliqueSym)) (output : List Bool)
    (work₁ work₂ : List (Option CliqueSym))
    (left right scratch : List Unit) : BuilderCfg program where
  label := some label
  buffer₁ := buffer₁
  buffer₂ := buffer₂
  test := test
  input := input
  output := output
  work₁ := work₁
  work₂ := work₂
  counter₁ := left
  counter₂ := right
  counter₃ := scratch

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.BatchEdgeLookup

import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.CertificateNodup
import Mathlib.Tactic.DeriveFintype

/-!
# General CLIQUE verifier: reusable edge lookup

The controller loads a unary query pair into two counters and scans the
instance edge suffix.  A third counter temporarily stores consumed query
tokens, so both endpoint budgets are restored after every failed candidate.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.EdgeLookup

open PolyBuilder

mutual
  /-- Scan canonical edge records for one fixed endpoint pair. -/
  def edgesResult (queryLeft queryRight : Nat) : List CliqueSym → Bool
    | [] => false
    | .edgeMark :: rest =>
        leftResult queryLeft queryRight queryLeft true rest
    | _ :: rest => edgesResult queryLeft queryRight rest

  /-- Compare the candidate's left unary field with the query budget. -/
  def leftResult (queryLeft queryRight : Nat) :
      Nat → Bool → List CliqueSym → Bool
    | _, _, [] => false
    | 0, _, .tick :: rest =>
        leftResult queryLeft queryRight 0 false rest
    | remaining + 1, equal, .tick :: rest =>
        leftResult queryLeft queryRight remaining equal rest
    | remaining, equal, .pairSep :: rest =>
        rightResult queryLeft queryRight queryRight
          (equal && decide (remaining = 0)) rest
    | remaining, _, _ :: rest =>
        leftResult queryLeft queryRight remaining false rest

  /-- Compare the candidate's right unary field and continue after a miss. -/
  def rightResult (queryLeft queryRight : Nat) :
      Nat → Bool → List CliqueSym → Bool
    | _, _, [] => false
    | 0, _, .tick :: rest =>
        rightResult queryLeft queryRight 0 false rest
    | remaining + 1, equal, .tick :: rest =>
        rightResult queryLeft queryRight remaining equal rest
    | remaining, equal, .recordEnd :: rest =>
        (equal && decide (remaining = 0)) ||
          edgesResult queryLeft queryRight rest
    | remaining, _, _ :: rest =>
        rightResult queryLeft queryRight remaining false rest
end

/-- Finite control for one reusable unary edge-membership query. -/
inductive Label
  | queryMark | queryLeft | incQueryLeft
  | queryRight | incQueryRight | pairSeparator
  | instanceMark | vertexField | targetField | edges
  | left (equal : Bool) | spendLeft (equal : Bool)
  | saveLeft (equal : Bool) | leftEnd (equal : Bool)
  | saveLeftRemainder | drainLeft
  | restoreLeft (equal : Bool) | restoreLeftInc (equal : Bool)
  | right (equal : Bool) | spendRight (equal : Bool)
  | saveRight (equal : Bool) | rightEnd (equal : Bool)
  | saveRightRemainder | drainRight
  | restoreRight (answer : Bool) | restoreRightInc (answer : Bool)
  | clearInput (answer : Bool)
  | clear₁ (answer : Bool) | clear₂ (answer : Bool)
  | clear₃ (answer : Bool) | emit (answer : Bool) | halt
deriving DecidableEq, Fintype

/-- Concrete counter program for one edge-membership lookup. -/
def program : Program (Option CliqueSym) Bool where
  Label := Label
  main := .queryMark
  op
    | .queryMark => .popInput (.clearInput false) fun
        | some .edgeMark => .queryLeft
        | _ => .clearInput false
    | .queryLeft => .popInput (.clearInput false) fun
        | some .tick => .incQueryLeft
        | some .pairSep => .queryRight
        | _ => .clearInput false
    | .incQueryLeft => .inc₁ .queryLeft
    | .queryRight => .popInput (.clearInput false) fun
        | some .tick => .incQueryRight
        | some .recordEnd => .pairSeparator
        | _ => .clearInput false
    | .incQueryRight => .inc₂ .queryRight
    | .pairSeparator => .popInput (.clearInput false) fun
        | none => .instanceMark
        | _ => .clearInput false
    | .instanceMark => .popInput (.clearInput false) fun _ => .vertexField
    | .vertexField => .popInput (.clearInput false) fun
        | some .fieldSep => .targetField
        | _ => .vertexField
    | .targetField => .popInput (.clearInput false) fun
        | some .fieldSep => .edges
        | _ => .targetField
    | .edges => .popInput (.clearInput true) fun
        | some .edgeMark => .left true
        | _ => .clearInput false
    | .left equal => .popInput (.clearInput false) fun
        | some .tick => .spendLeft equal
        | some .pairSep => .leftEnd equal
        | _ => .left false
    | .spendLeft equal => .dec₁ (.left false) (.saveLeft equal)
    | .saveLeft equal => .inc₃ (.left equal)
    | .leftEnd equal =>
        .dec₁ (.restoreLeft equal) .saveLeftRemainder
    | .saveLeftRemainder => .inc₃ .drainLeft
    | .drainLeft => .dec₁ (.restoreLeft false) .saveLeftRemainder
    | .restoreLeft equal =>
        .dec₃ (.right equal) (.restoreLeftInc equal)
    | .restoreLeftInc equal => .inc₁ (.restoreLeft equal)
    | .right equal => .popInput (.clearInput false) fun
        | some .tick => .spendRight equal
        | some .recordEnd => .rightEnd equal
        | _ => .right false
    | .spendRight equal => .dec₂ (.right false) (.saveRight equal)
    | .saveRight equal => .inc₃ (.right equal)
    | .rightEnd equal =>
        .dec₂ (.restoreRight equal) .saveRightRemainder
    | .saveRightRemainder => .inc₃ .drainRight
    | .drainRight => .dec₂ (.restoreRight false) .saveRightRemainder
    | .restoreRight answer =>
        .dec₃ (if answer then .clearInput true else .edges)
          (.restoreRightInc answer)
    | .restoreRightInc answer => .inc₂ (.restoreRight answer)
    | .clearInput answer =>
        .popInput (.clear₁ answer) fun _ => .clearInput answer
    | .clear₁ answer => .dec₁ (.clear₂ answer) (.clear₁ answer)
    | .clear₂ answer => .dec₂ (.clear₃ answer) (.clear₂ answer)
    | .clear₃ answer => .dec₃ (.emit answer) (.clear₃ answer)
    | .emit answer => .pushOutput answer .halt
    | .halt => .halt

/-- Explicit independent-semantics configuration for lookup proofs. -/
def cfg (label : Label) (buffer₁ buffer₂ : Option (Option CliqueSym))
    (test : Bool) (input : List (Option CliqueSym)) (output : List Bool)
    (left right scratch : List Unit) : BuilderCfg program where
  label := some label
  buffer₁ := buffer₁
  buffer₂ := buffer₂
  test := test
  input := input
  output := output
  work₁ := []
  work₂ := []
  counter₁ := left
  counter₂ := right
  counter₃ := scratch

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.EdgeLookup

import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.PairGenerator.Runtime
import Mathlib.Tactic.DeriveFintype

/-!
# General CLIQUE verifier: normalize generated edge queries

Certificate order is semantically irrelevant, whereas instance edges are
stored with their smaller endpoint first.  This fixed counter controller
normalizes every canonical query record.  Equal endpoints are deliberately
retained as `(u,u)` so the subsequent edge-membership pass rejects them.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.QueryNormalizer

open PolyBuilder

/-- Endpoint order discovered by the destructive unary comparison. -/
inductive EndpointOrder
  | leftLess | equal | rightLess
deriving DecidableEq, Fintype

/-- Mathematical normalization used by the concrete controller. -/
def normalizeQuery (edge : Nat × Nat) : Nat × Nat :=
  if edge.1 ≤ edge.2 then edge else (edge.2, edge.1)

/-- Canonical serialization of a normalized query family. -/
def encodeNormalizedQueries (edges : List (Nat × Nat)) : List CliqueSym :=
  edges.flatMap (encodeCliqueEdge ∘ normalizeQuery)

/-- Finite control of the reverse-output normalizer. -/
inductive Label
  | scan | left | incrementLeft | right | incrementRight
  | compareLeft | compareRight | saveMatched | probeRight
  | restoreMatched (order : EndpointOrder)
  | restoreLeft (order : EndpointOrder)
  | restoreRight (order : EndpointOrder)
  | restoreExtraLeft | restoreExtraRight
  | pushEdgeMark (order : EndpointOrder)
  | lower (order : EndpointOrder) | pushLowerTick (order : EndpointOrder)
  | pushPairSeparator (order : EndpointOrder)
  | upper (order : EndpointOrder) | pushUpperTick (order : EndpointOrder)
  | pushRecordEnd | halt | invalid
deriving DecidableEq, Fintype

/-- The controller parses two unary fields, compares and restores their
counters, then drains them in normalized order onto the output stack. -/
def revProgram : Program CliqueSym CliqueSym where
  Label := Label
  main := .scan
  op
    | .scan => .popInput .halt fun
        | .edgeMark => .left
        | _ => .invalid
    | .left => .popInput .invalid fun
        | .tick => .incrementLeft
        | .pairSep => .right
        | _ => .invalid
    | .incrementLeft => .inc₁ .left
    | .right => .popInput .invalid fun
        | .tick => .incrementRight
        | .recordEnd => .compareLeft
        | _ => .invalid
    | .incrementRight => .inc₂ .right
    | .compareLeft => .dec₁ .probeRight .compareRight
    | .compareRight => .dec₂
        (.restoreMatched .rightLess) .saveMatched
    | .saveMatched => .inc₃ .compareLeft
    | .probeRight => .dec₂
        (.restoreMatched .equal) (.restoreMatched .leftLess)
    | .restoreMatched order => .dec₃
        (match order with
          | .leftLess => .restoreExtraRight
          | .equal => .pushEdgeMark .equal
          | .rightLess => .restoreExtraLeft)
        (.restoreLeft order)
    | .restoreLeft order => .inc₁ (.restoreRight order)
    | .restoreRight order => .inc₂ (.restoreMatched order)
    | .restoreExtraLeft => .inc₁ (.pushEdgeMark .rightLess)
    | .restoreExtraRight => .inc₂ (.pushEdgeMark .leftLess)
    | .pushEdgeMark order => .pushOutput .edgeMark (.lower order)
    | .lower .leftLess => .dec₁
        (.pushPairSeparator .leftLess) (.pushLowerTick .leftLess)
    | .lower .equal => .dec₁
        (.pushPairSeparator .equal) (.pushLowerTick .equal)
    | .lower .rightLess => .dec₂
        (.pushPairSeparator .rightLess) (.pushLowerTick .rightLess)
    | .pushLowerTick order => .pushOutput .tick (.lower order)
    | .pushPairSeparator order => .pushOutput .pairSep (.upper order)
    | .upper .leftLess => .dec₂ .pushRecordEnd
        (.pushUpperTick .leftLess)
    | .upper .equal => .dec₂ .pushRecordEnd
        (.pushUpperTick .equal)
    | .upper .rightLess => .dec₁ .pushRecordEnd
        (.pushUpperTick .rightLess)
    | .pushUpperTick order => .pushOutput .tick (.upper order)
    | .pushRecordEnd => .pushOutput .recordEnd .scan
    | .halt => .halt
    | .invalid => .popInput .halt fun _ => .invalid

/-- Proof-facing independent configuration. -/
def cfg (label : Label) (buffer : Option CliqueSym) (test : Bool)
    (input output : List CliqueSym) (left right scratch : List Unit) :
    BuilderCfg revProgram where
  label := some label
  buffer₁ := buffer
  buffer₂ := none
  test := test
  input := input
  output := output
  work₁ := []
  work₂ := []
  counter₁ := left
  counter₂ := right
  counter₃ := scratch

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.QueryNormalizer

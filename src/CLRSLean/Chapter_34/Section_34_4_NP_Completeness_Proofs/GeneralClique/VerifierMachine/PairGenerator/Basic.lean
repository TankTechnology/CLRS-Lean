import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesGenericRuntime
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import Mathlib.Tactic.DeriveFintype

/-!
# General CLIQUE verifier: certificate rows for pair generation

Each certificate vertex becomes the four-field row expected by the reusable
occurrence-pair controller.  The first field is the actual graph vertex; the
second is its certificate position.  Distinct positions therefore generate
every certificate pair even when two malformed certificate values coincide.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.PairGenerator

open PolyBuilder

/-- Synthetic occurrence metadata attached to one certificate position. -/
def certificatePairOccurrence (position : Nat) : IndexedOccurrence :=
  { clauseIndex := position
    positionIndex := 0
    literal := .pos 0 }

/-- Explicit row entries for a certificate suffix, starting at a position. -/
def certificatePairEntriesFrom : Nat → List Nat →
    List (IndexedOccurrence × Nat)
  | _, [] => []
  | position, vertex :: vertices =>
      (certificatePairOccurrence position, vertex) ::
        certificatePairEntriesFrom (position + 1) vertices

/-- Canonical synthetic row family for a complete certificate. -/
def certificatePairEntries (vertices : List Nat) :
    List (IndexedOccurrence × Nat) :=
  certificatePairEntriesFrom 0 vertices

@[simp] theorem certificatePairEntriesFrom_nil (position : Nat) :
    certificatePairEntriesFrom position [] = [] := rfl

@[simp] theorem certificatePairEntriesFrom_cons (position vertex : Nat)
    (vertices : List Nat) :
    certificatePairEntriesFrom position (vertex :: vertices) =
      (certificatePairOccurrence position, vertex) ::
        certificatePairEntriesFrom (position + 1) vertices := rfl

/-- The synthetic entry row contains actual vertex, position, zero polarity,
and the positive unary code one. -/
theorem encode_certificatePairEntry (position vertex : Nat) :
    TMClique.encodeIndexedOccurrenceEntry
        (certificatePairOccurrence position, vertex) =
      encodeUnaryFrame [vertex, position, 0, 1] ++ [.frameEnd] := by
  rfl

/-- Finite control of the prepend-order row generator. -/
inductive Label
  | start | scan | vertex | emitVertexTick | pushVertexSeparator
  | copyPosition | savePosition | emitPositionTick | pushPositionSeparator
  | restorePosition | restorePositionInc
  | pushPolaritySeparator | pushVariableTick | pushVariableSeparator
  | pushRowEnd | advancePosition
  | clearPosition | clearScratch | halt | invalid
deriving DecidableEq, Fintype

/-- The controller emits canonical rows in reverse order; a standard verified
reversal pass restores their forward serialization. -/
def revProgram : Program CliqueSym UnaryFrameSym where
  Label := Label
  main := .start
  op
    | .start => .popInput .clearPosition fun
        | .certificateMark => .scan
        | _ => .invalid
    | .scan => .popInput .clearPosition fun
        | .vertexMark => .vertex
        | _ => .invalid
    | .vertex => .popInput .clearPosition fun
        | .tick => .emitVertexTick
        | .recordEnd => .pushVertexSeparator
        | _ => .invalid
    | .emitVertexTick => .pushOutput .tick .vertex
    | .pushVertexSeparator => .pushOutput .separator .copyPosition
    | .copyPosition => .dec₁ .pushPositionSeparator .savePosition
    | .savePosition => .inc₃ .emitPositionTick
    | .emitPositionTick => .pushOutput .tick .copyPosition
    | .pushPositionSeparator => .pushOutput .separator .restorePosition
    | .restorePosition => .dec₃ .pushPolaritySeparator .restorePositionInc
    | .restorePositionInc => .inc₁ .restorePosition
    | .pushPolaritySeparator => .pushOutput .separator .pushVariableTick
    | .pushVariableTick => .pushOutput .tick .pushVariableSeparator
    | .pushVariableSeparator => .pushOutput .separator .pushRowEnd
    | .pushRowEnd => .pushOutput .frameEnd .advancePosition
    | .advancePosition => .inc₁ .scan
    | .clearPosition => .dec₁ .clearScratch .clearPosition
    | .clearScratch => .dec₃ .halt .clearScratch
    | .halt => .halt
    | .invalid => .popInput .clearPosition fun _ => .invalid

/-- Proof-facing configuration for the certificate-row generator. -/
def cfg (label : Label) (buffer : Option CliqueSym) (test : Bool)
    (input : List CliqueSym) (output : List UnaryFrameSym)
    (position scratch : List Unit) : BuilderCfg revProgram where
  label := some label
  buffer₁ := buffer
  buffer₂ := none
  test := test
  input := input
  output := output
  work₁ := []
  work₂ := []
  counter₁ := position
  counter₂ := []
  counter₃ := scratch

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.PairGenerator

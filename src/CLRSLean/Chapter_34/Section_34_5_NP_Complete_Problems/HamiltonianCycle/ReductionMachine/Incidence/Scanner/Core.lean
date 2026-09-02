import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.Incidence.Input
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Construction.IncidenceSemantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowOrderReverse
import Mathlib.Tactic.DeriveFintype

/-!
# HAM-CYCLE incidence scanner: core controller

The controller is a vertex-specialized sibling of the general CLIQUE batch
edge lookup.  It loads the canonical vertex queries in reverse order, scans
and restores the same graph for every query, and emits the occurrence index
plus a left/right side bit whenever an endpoint equals the query.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Scanner

open PolyBuilder
open HamiltonianCycleReduction

/-- Unary representation of the gadget-side bit. -/
def sideValue (side : Bool) : Nat := if side then 1 else 0

/-- Two-field representation `(source occurrence, gadget side)`. -/
def encodeIncidentOccurrence (ref : IncidentOccurrence) :
    List UnaryFrameSym :=
  encodeUnaryFrame [ref.occurrence, sideValue ref.rightSide]

/-- One source vertex's incidence row, without its outer row delimiter. -/
def incidenceRow (I : VertexCoverInstance) (u : Nat) :
    List UnaryFrameSym :=
  (incidentOccurrences I u).flatMap encodeIncidentOccurrence

private theorem encodeUnaryFrame_frameEnd_free (values : List Nat) :
    ∀ symbol ∈ encodeUnaryFrame values,
      symbol ≠ UnaryFrameSym.frameEnd := by
  intro symbol hsymbol
  rw [encodeUnaryFrame, List.mem_flatMap] at hsymbol
  rcases hsymbol with ⟨value, _, hvalue⟩
  simp [encodeUnaryFrameBlock] at hvalue
  rcases hvalue with ⟨_, rfl⟩ | rfl <;> decide

/-- Typed row family shared by the chain and selector-endpoint formatters. -/
def incidenceFamily (I : VertexCoverInstance) :
    UnaryFrameMarkedRowFamily where
  rows := (List.range I.vertexCount).map (incidenceRow I)
  frameEnd_free := by
    intro row hrow symbol hsymbol
    rw [List.mem_map] at hrow
    rcases hrow with ⟨u, _, rfl⟩
    rw [incidenceRow, List.mem_flatMap] at hsymbol
    rcases hsymbol with ⟨ref, _, href⟩
    exact encodeUnaryFrame_frameEnd_free _ symbol href

/-- Canonical forward incidence rows. -/
def stream (I : VertexCoverInstance) : List UnaryFrameSym :=
  encodeUnaryFrameMarkedRowFamily (incidenceFamily I)

/-- The raw prepend-only controller visits vertex queries in reverse order. -/
def descendingStream (I : VertexCoverInstance) : List UnaryFrameSym :=
  encodeUnaryFrameMarkedRowOrderReverse (incidenceFamily I)

/-- Physical result before the two public ordering passes. -/
def rawOutput (I : VertexCoverInstance) : List UnaryFrameSym :=
  (descendingStream I).reverse

/-- Finite control for repeated source-incidence scans. -/
inductive Label
  | loadQueries | beginQueries | nextQuery | queryTicks | incQuery
  | instanceMark | vertexField | targetField | edges
  | left (equal : Bool) | spendLeft (equal : Bool)
  | saveLeft (equal : Bool) | leftEnd (equal : Bool)
  | saveLeftRemainder | drainLeft
  | restoreLeft (equal : Bool) | restoreLeftInc (equal : Bool)
  | right (leftEqual rightEqual : Bool)
  | spendRight (leftEqual rightEqual : Bool)
  | saveRight (leftEqual rightEqual : Bool)
  | rightEnd (leftEqual rightEqual : Bool)
  | saveRightRemainder (leftEqual : Bool) | drainRight (leftEqual : Bool)
  | restoreRight (leftEqual rightEqual : Bool)
  | restoreRightInc (leftEqual rightEqual : Bool)
  | emitOccurrence (side : Bool) | saveOccurrence (side : Bool)
  | emitFirstSeparator (side : Bool) | emitSideTick (side : Bool)
  | emitSecondSeparator | restoreOccurrence | restoreOccurrenceInc
  | restoreOccurrenceTick
  | advanceOccurrence
  | finishQuery | clearQuery | clearOccurrence | clearScratch
  | restoreGraph | emitRowEnd
  | discardGraph | clearWorkOne | clearWorkTwo
  | clearFinalQuery | clearFinalOccurrence | clearFinalScratch | halt
deriving DecidableEq, Fintype

/-- Fixed repeated-incidence controller.  Counter one stores the current
source vertex, counter two the source-edge occurrence, and counter three is
the comparison/emission restoration scratch counter. -/
def program : Program (Option CliqueSym) UnaryFrameSym where
  Label := Label
  main := .loadQueries
  op
    | .loadQueries => .moveInputWork₁ .discardGraph fun
        | none => .beginQueries
        | some _ => .loadQueries
    | .beginQueries => .popWork₁ .discardGraph fun
        | none => .nextQuery
        | some _ => .discardGraph
    | .nextQuery => .popWork₁ .discardGraph fun
        | some .recordEnd => .queryTicks
        | _ => .discardGraph
    | .queryTicks => .popWork₁ .discardGraph fun
        | some .tick => .incQuery
        | some .vertexMark => .instanceMark
        | _ => .discardGraph
    | .incQuery => .inc₁ .queryTicks
    | .instanceMark => .moveInputWork₂ .finishQuery fun
        | some .instanceMark => .vertexField
        | _ => .finishQuery
    | .vertexField => .moveInputWork₂ .finishQuery fun
        | some .fieldSep => .targetField
        | _ => .vertexField
    | .targetField => .moveInputWork₂ .finishQuery fun
        | some .fieldSep => .edges
        | _ => .targetField
    | .edges => .moveInputWork₂ .finishQuery fun
        | some .edgeMark => .left true
        | _ => .finishQuery
    | .left equal => .moveInputWork₂ .finishQuery fun
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
        .dec₃ (.right equal true) (.restoreLeftInc equal)
    | .restoreLeftInc equal => .inc₁ (.restoreLeft equal)
    | .right leftEqual rightEqual =>
        .moveInputWork₂ .finishQuery fun
          | some .tick => .spendRight leftEqual rightEqual
          | some .recordEnd => .rightEnd leftEqual rightEqual
          | _ => .right leftEqual false
    | .spendRight leftEqual rightEqual =>
        .dec₁ (.right leftEqual false)
          (.saveRight leftEqual rightEqual)
    | .saveRight leftEqual rightEqual =>
        .inc₃ (.right leftEqual rightEqual)
    | .rightEnd leftEqual rightEqual =>
        .dec₁ (.restoreRight leftEqual rightEqual)
          (.saveRightRemainder leftEqual)
    | .saveRightRemainder leftEqual => .inc₃ (.drainRight leftEqual)
    | .drainRight leftEqual =>
        .dec₁ (.restoreRight leftEqual false)
          (.saveRightRemainder leftEqual)
    | .restoreRight leftEqual rightEqual =>
        .dec₃
          (if leftEqual then .emitOccurrence false
            else if rightEqual then .emitOccurrence true
            else .advanceOccurrence)
          (.restoreRightInc leftEqual rightEqual)
    | .restoreRightInc leftEqual rightEqual =>
        .inc₁ (.restoreRight leftEqual rightEqual)
    | .emitOccurrence side =>
        .dec₂ (.emitFirstSeparator side) (.saveOccurrence side)
    | .saveOccurrence side => .inc₃ (.emitSideTick side)
    | .emitSideTick side => .pushOutput .tick (.emitOccurrence side)
    | .emitFirstSeparator side =>
        .pushOutput .separator
          (if side then .emitSecondSeparator else .restoreOccurrence)
    | .emitSecondSeparator => .pushOutput .tick .restoreOccurrence
    | .restoreOccurrence =>
        .pushOutput .separator .restoreOccurrenceInc
    | .restoreOccurrenceInc =>
        .dec₃ .advanceOccurrence .restoreOccurrenceTick
    | .restoreOccurrenceTick => .inc₂ .restoreOccurrenceInc
    | .advanceOccurrence => .inc₂ .edges
    | .finishQuery => .jump .clearQuery
    | .clearQuery => .dec₁ .clearOccurrence .clearQuery
    | .clearOccurrence => .dec₂ .clearScratch .clearOccurrence
    | .clearScratch => .dec₃ .restoreGraph .clearScratch
    | .restoreGraph => .moveWork₂Input .emitRowEnd fun _ => .restoreGraph
    | .emitRowEnd => .pushOutput .frameEnd .nextQuery
    | .discardGraph => .popInput .clearWorkOne fun _ => .discardGraph
    | .clearWorkOne => .popWork₁ .clearWorkTwo fun _ => .clearWorkOne
    | .clearWorkTwo => .popWork₂ .clearFinalQuery fun _ => .clearWorkTwo
    | .clearFinalQuery => .dec₁ .clearFinalOccurrence .clearFinalQuery
    | .clearFinalOccurrence =>
        .dec₂ .clearFinalScratch .clearFinalOccurrence
    | .clearFinalScratch => .dec₃ .halt .clearFinalScratch
    | .halt => .halt

/-- Proof-facing independent configuration. -/
def cfg (label : Label) (buffer₁ buffer₂ : Option (Option CliqueSym))
    (test : Bool) (input : List (Option CliqueSym))
    (output : List UnaryFrameSym)
    (work₁ work₂ : List (Option CliqueSym))
    (query occurrence scratch : List Unit) : BuilderCfg program where
  label := some label
  buffer₁ := buffer₁
  buffer₂ := buffer₂
  test := test
  input := input
  output := output
  work₁ := work₁
  work₂ := work₂
  counter₁ := query
  counter₂ := occurrence
  counter₃ := scratch

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Scanner

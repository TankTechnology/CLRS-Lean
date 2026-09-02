import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.WidgetEdges.OccurrenceSeeds

/-!
# VERTEX-COVER to HAM-CYCLE machine: global widget endpoints

For every occurrence seed `(i, 0, 0)`, a fixed table of twenty-eight affine
forms emits both endpoints of the fourteen globally numbered gadget edges.
The fixed coefficients are part of finite control; only `i` is runtime data.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.WidgetEdges

open _root_.Turing
open PolyBuilder
open HamiltonianCycleReduction

/-- The affine form `12 * occurrence + localVertex`. -/
def endpointForm (localVertex : Nat) : AffineUnaryTripleForm where
  constant := localVertex
  first := widgetVertexCount
  second := 0
  third := 0

/-- Both endpoint forms for one local gadget edge. -/
def endpointFormsForEdge (edge : Nat × Nat) :
    List AffineUnaryTripleForm :=
  [endpointForm edge.1, endpointForm edge.2]

/-- The fixed twenty-eight-form table, in the exact order of `widgetEdges`. -/
def endpointForms : List AffineUnaryTripleForm :=
  widgetEdges.flatMap endpointFormsForEdge

/-- Runtime unary endpoint values before graph-record formatting. -/
def endpointValues (input : List CliqueSym) : List Nat :=
  affineUnaryTripleMapFamily endpointForms (occurrenceSeeds input)

/-- Ordinary unary frame containing all endpoint values. -/
def endpointStream (input : List CliqueSym) : List UnaryFrameSym :=
  encodeUnaryFrame (endpointValues input)

/-- The occurrence-seed generator followed by the fixed affine table is one
fixed polynomial-time TM2 from raw graph strings to unary endpoints. -/
noncomputable def endpointStreamComputableInPolyTime :
    TM2ComputableInPolyTime id id endpointStream := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    occurrenceSeedsComputableInPolyTime
    (affineUnaryTripleMapFamily_computableInPolyTime endpointForms)
  change TM2ComputableInPolyTime id id
    (fun input => encodeUnaryFrame
      (affineUnaryTripleMapFamily endpointForms (occurrenceSeeds input)))
  simpa only [Function.comp_def] using Classical.choice composed

/-- One occurrence's affine table is exactly the flattened endpoint list of
the globally numbered gadget. -/
theorem affineUnaryTripleMap_endpointForms (occurrence : Nat) :
    affineUnaryTripleMap endpointForms (occurrenceSeed occurrence) =
      (globalWidgetEdges occurrence).flatMap fun edge => [edge.1, edge.2] := by
  simp [endpointForms, endpointFormsForEdge, endpointForm,
    affineUnaryTripleMap, affineUnaryTripleFormValue, occurrenceSeed,
    globalWidgetEdges, globalWidgetVertex, widgetVertexCount, widgetEdges,
    Nat.add_comm]

/-- Exact canonical endpoint semantics in occurrence-major, gadget-edge-major
order. -/
theorem endpointValues_encode (I : VertexCoverInstance) :
    endpointValues (encodeVertexCoverInstance I) =
      (allGlobalWidgetEdges I.edges.length).flatMap fun edge =>
        [edge.1, edge.2] := by
  rw [endpointValues, occurrenceSeeds_encode]
  unfold affineUnaryTripleMapFamily allGlobalWidgetEdges
  simp only [List.flatMap_map]
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro occurrence hoccurrence
  exact affineUnaryTripleMap_endpointForms occurrence

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.WidgetEdges

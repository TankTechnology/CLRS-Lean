import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.SelectorEndpoints.OffsetRowsRuntime
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.Incidence.Endpoints.Runtime
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedCellAffineRowsRuntime

/-!
# HAM-CYCLE selector endpoints: reusable source composition

The endpoint extractor supplies one marked cell per chain endpoint.  A zero
affine step repeats that complete cell list once per selector.  The resulting
rows are paired with the already verified runtime selector base.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.SelectorEndpoints

open _root_.Turing
open PolyBuilder
open HamiltonianCycleReduction

/-- Prepend one zero-valued unary field to an arbitrary unary-frame stream. -/
def prependZeroFieldSpec :
    StatefulFlatMapSpec Bool UnaryFrameSym UnaryFrameSym where
  initial := false
  action started symbol :=
    if started then ([symbol], true)
    else ([.separator, symbol], true)
  finish started := if started then [] else [.separator]

private theorem prependZeroFieldFrom_started (input : List UnaryFrameSym) :
    rewriteStatefulFlatMapFrom prependZeroFieldSpec true input = input := by
  induction input with
  | nil => rfl
  | cons symbol input ih =>
      rw [rewriteStatefulFlatMapFrom.eq_def]
      change symbol :: rewriteStatefulFlatMapFrom prependZeroFieldSpec true
        input = symbol :: input
      exact congrArg (List.cons symbol) ih

theorem prependZeroField_eq (input : List UnaryFrameSym) :
    rewriteStatefulFlatMap prependZeroFieldSpec input =
      .separator :: input := by
  cases input with
  | nil => rfl
  | cons symbol input =>
      rw [show rewriteStatefulFlatMap prependZeroFieldSpec (symbol :: input) =
          rewriteStatefulFlatMapFrom prependZeroFieldSpec false
            (symbol :: input) by rfl,
        rewriteStatefulFlatMapFrom.eq_def]
      change .separator :: symbol ::
          rewriteStatefulFlatMapFrom prependZeroFieldSpec true input =
        .separator :: symbol :: input
      exact congrArg (List.cons .separator)
        (congrArg (List.cons symbol) (prependZeroFieldFrom_started input))

def targetFieldTyped (I : VertexCoverInstance) : List UnaryFrameSym :=
  SelectorClique.targetField (encodeVertexCoverInstance I)

private noncomputable def targetFieldTypedComputableInPolyTime :
    TM2ComputableInPolyTime encodeVertexCoverInstance id targetFieldTyped := by
  let machine := SelectorClique.targetFieldComputableInPolyTime
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun I => by
        simpa [targetFieldTyped] using
          machine.outputsFun (encodeVertexCoverInstance I) }

/-- `(step,count) = (0,k)` in the encoding expected by the affine copier. -/
def targetPrefix (I : VertexCoverInstance) : List UnaryFrameSym :=
  rewriteStatefulFlatMap prependZeroFieldSpec (targetFieldTyped I)

private noncomputable def targetPrefixComputableInPolyTime :
    TM2ComputableInPolyTime encodeVertexCoverInstance id targetPrefix := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    targetFieldTypedComputableInPolyTime
    (statefulFlatMap_computableInPolyTime prependZeroFieldSpec)
  change TM2ComputableInPolyTime encodeVertexCoverInstance id
    (fun I => rewriteStatefulFlatMap prependZeroFieldSpec
      (targetFieldTyped I))
  simpa only [Function.comp_def] using Classical.choice composed

/-- Flat endpoint cells in canonical source-vertex order. -/
def endpointCells (I : VertexCoverInstance) : List Nat :=
  (List.range I.vertexCount).flatMap fun u =>
    Incidence.Endpoints.endpointValues (incidentOccurrences I u)

theorem endpointCellStream_eq (I : VertexCoverInstance) :
    Incidence.Endpoints.endpointCellStream I =
      (endpointCells I).flatMap fun endpoint =>
        encodeUnaryFrame [endpoint] ++ [.frameEnd] := by
  simp [Incidence.Endpoints.endpointCellStream, endpointCells,
    List.flatMap_assoc]

/-- Zero-step affine family: repeat every chain endpoint once per selector. -/
def markedFamily (I : VertexCoverInstance) :
    UnaryFrameMarkedCellAffineRows where
  step := 0
  count := I.targetSize
  cells := endpointCells I

def markedFamilyInput (I : VertexCoverInstance) : List UnaryFrameSym :=
  targetPrefix I ++ Incidence.Endpoints.endpointCellStream I

theorem markedFamilyInput_eq (I : VertexCoverInstance) :
    markedFamilyInput I = encodeUnaryFrameMarkedCellAffineRows (markedFamily I) := by
  rw [markedFamilyInput, targetPrefix, prependZeroField_eq,
    targetFieldTyped, SelectorClique.targetField_eq,
    SelectorClique.targetTicks_encode, endpointCellStream_eq]
  simp [markedFamily, encodeUnaryFrameMarkedCellAffineRows,
    encodeUnaryFrame, encodeUnaryFrameBlock, List.append_assoc]

noncomputable def markedFamilyComputableInPolyTime :
    TM2ComputableInPolyTime encodeVertexCoverInstance
      encodeUnaryFrameMarkedCellAffineRows markedFamily := by
  let joined := fixedPairSameInputConcat_computableInPolyTime
    SelectorClique.encodeUnaryFrameSymPair
    SelectorClique.decodeUnaryFrameSymPair
    SelectorClique.decode_encodeUnaryFrameSymPair
    targetPrefixComputableInPolyTime
    Incidence.Endpoints.computableInPolyTime
  exact
    { tm := joined.tm
      inputAlphabet := joined.inputAlphabet
      outputAlphabet := joined.outputAlphabet
      time := joined.time
      outputsFun := fun I => by
        rw [← markedFamilyInput_eq I]
        simpa only [markedFamilyInput, id_eq] using joined.outputsFun I }

def repeatedRows (I : VertexCoverInstance) : List UnaryFrameSym :=
  unaryFrameMarkedCellAffineRowsStream (markedFamily I)

noncomputable def repeatedRowsComputableInPolyTime :
    TM2ComputableInPolyTime encodeVertexCoverInstance id repeatedRows := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    markedFamilyComputableInPolyTime
    unaryFrameMarkedCellAffineRowsStream_computableInPolyTime
  change TM2ComputableInPolyTime encodeVertexCoverInstance id
    (fun I => unaryFrameMarkedCellAffineRowsStream (markedFamily I))
  simpa only [Function.comp_def] using Classical.choice composed

def baseFieldTyped (I : VertexCoverInstance) : List UnaryFrameSym :=
  SelectorClique.baseField (encodeVertexCoverInstance I)

private noncomputable def baseFieldTypedComputableInPolyTime :
    TM2ComputableInPolyTime encodeVertexCoverInstance id baseFieldTyped := by
  let machine := SelectorClique.baseFieldComputableInPolyTime
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun I => by
        simpa [baseFieldTyped] using
          machine.outputsFun (encodeVertexCoverInstance I) }

private theorem baseFieldTyped_eq (I : VertexCoverInstance) :
    baseFieldTyped I = encodeUnaryFrameBlock (selectorBase I.edges.length) := by
  rw [baseFieldTyped, SelectorClique.baseField_eq]
  have hedge := congrArg List.length
    (WidgetEdges.Source.edgeTicks_encode I)
  rw [WidgetEdges.Source.edgeTicks_eq_replicate_count] at hedge
  have hcount : (encodeVertexCoverInstance I).count CliqueSym.edgeMark =
      I.edges.length := by simpa using hedge
  rw [hcount]

/-- Typed arbitrary-row family consumed by the shared offset formatter. -/
def offsetFamily (I : VertexCoverInstance) : OffsetRowsFamily where
  base := selectorBase I.edges.length
  rows := unaryFrameMarkedCellAffineRowValues (markedFamily I)

def formatInput (I : VertexCoverInstance) : List UnaryFrameSym :=
  baseFieldTyped I ++ repeatedRows I

theorem formatInput_eq (I : VertexCoverInstance) :
    formatInput I = encodeOffsetRowsFamily (offsetFamily I) := by
  rw [formatInput, baseFieldTyped_eq]
  rfl

/-- The whole selector-endpoint formatter source is itself produced by one
fixed polynomial-time TM2 from the original VERTEX-COVER encoding. -/
noncomputable def formatInputComputableInPolyTime :
    TM2ComputableInPolyTime encodeVertexCoverInstance
      encodeOffsetRowsFamily offsetFamily := by
  let joined := fixedPairSameInputConcat_computableInPolyTime
    SelectorClique.encodeUnaryFrameSymPair
    SelectorClique.decodeUnaryFrameSymPair
    SelectorClique.decode_encodeUnaryFrameSymPair
    baseFieldTypedComputableInPolyTime repeatedRowsComputableInPolyTime
  exact
    { tm := joined.tm
      inputAlphabet := joined.inputAlphabet
      outputAlphabet := joined.outputAlphabet
      time := joined.time
      outputsFun := fun I => by
        rw [← formatInput_eq I]
        simpa only [formatInput, id_eq] using joined.outputsFun I }

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.SelectorEndpoints

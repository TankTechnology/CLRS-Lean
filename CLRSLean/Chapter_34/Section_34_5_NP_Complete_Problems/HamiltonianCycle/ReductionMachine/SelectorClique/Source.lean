import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.Header
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.WidgetEdges.Source
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameAffinePrefixRows

/-!
# VERTEX-COVER to HAM-CYCLE machine: selector-clique rows

The selector vertices occupy the consecutive interval beginning at
`12 * edgeCount`.  This module extracts that base and the source target size,
then invokes the reusable affine-prefix row generator.  Row `j` contains the
lower selector endpoints `base, ..., base + j - 1`.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.SelectorClique

open _root_.Turing
open PolyBuilder
open HamiltonianCycleReduction

/-- Expand one source-edge tick to the twelve selector-base ticks and finish
the resulting unary field. -/
def baseFieldSpec : StatefulFlatMapSpec Unit UnaryFrameSym UnaryFrameSym where
  initial := ()
  action _ symbol :=
    (if symbol = .tick then
      List.replicate widgetVertexCount .tick else [], ())
  finish _ := [.separator]

def baseField (input : List CliqueSym) : List UnaryFrameSym :=
  rewriteStatefulFlatMap baseFieldSpec (WidgetEdges.Source.edgeTicks input)

noncomputable def baseFieldComputableInPolyTime :
    TM2ComputableInPolyTime id id baseField := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    WidgetEdges.Source.edgeTicksComputableInPolyTime
    (statefulFlatMap_computableInPolyTime baseFieldSpec)
  change TM2ComputableInPolyTime id id
    (fun input => rewriteStatefulFlatMap baseFieldSpec
      (WidgetEdges.Source.edgeTicks input))
  simpa only [Function.comp_def] using Classical.choice composed

private theorem baseFieldFrom_ticks (count : Nat) :
    rewriteStatefulFlatMapFrom baseFieldSpec ()
        (List.replicate count .tick) =
      List.replicate (widgetVertexCount * count) .tick ++ [.separator] := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.replicate_succ, rewriteStatefulFlatMapFrom.eq_def]
      change List.replicate widgetVertexCount .tick ++
          rewriteStatefulFlatMapFrom baseFieldSpec ()
            (List.replicate count .tick) = _
      rw [ih, Nat.mul_succ, ← List.append_assoc,
        ← List.replicate_add]
      congr 2
      omega

theorem baseField_eq (input : List CliqueSym) :
    baseField input =
      encodeUnaryFrameBlock (selectorBase (input.count .edgeMark)) := by
  rw [baseField, WidgetEdges.Source.edgeTicks_eq_replicate_count]
  rw [show rewriteStatefulFlatMap baseFieldSpec
      (List.replicate (input.count CliqueSym.edgeMark) .tick) =
        rewriteStatefulFlatMapFrom baseFieldSpec ()
          (List.replicate (input.count CliqueSym.edgeMark) .tick) by rfl,
    baseFieldFrom_ticks]
  rfl

/-- Source-field scan used to retain only the unary target-size field. -/
def targetTickSpec : StatefulFlatMapSpec Header.CountMode CliqueSym UnaryFrameSym where
  initial := .vertexCount
  action mode symbol :=
    match mode with
    | .vertexCount =>
        if symbol = .fieldSep then ([], .targetSize) else ([], .vertexCount)
    | .targetSize =>
        if symbol = .fieldSep then ([], .edges)
        else if symbol = .tick then ([.tick], .targetSize)
        else ([], .targetSize)
    | .edges => ([], .edges)
  finish _ := []

@[simp] theorem targetTickSpec_action (mode : Header.CountMode)
    (symbol : CliqueSym) :
    targetTickSpec.action mode symbol =
      match mode with
      | .vertexCount =>
          if symbol = .fieldSep then ([], .targetSize)
          else ([], .vertexCount)
      | .targetSize =>
          if symbol = .fieldSep then ([], .edges)
          else if symbol = .tick then ([.tick], .targetSize)
          else ([], .targetSize)
      | .edges => ([], .edges) := rfl

@[simp] theorem targetTickSpec_action_vertexCount (symbol : CliqueSym) :
    targetTickSpec.action .vertexCount symbol =
      if symbol = .fieldSep then ([], .targetSize) else ([], .vertexCount) :=
  rfl

@[simp] theorem targetTickSpec_action_targetSize (symbol : CliqueSym) :
    targetTickSpec.action .targetSize symbol =
      if symbol = .fieldSep then ([], .edges)
      else if symbol = .tick then ([.tick], .targetSize)
      else ([], .targetSize) := rfl

@[simp] theorem targetTickSpec_action_edges (symbol : CliqueSym) :
    targetTickSpec.action .edges symbol = ([], .edges) := rfl

def targetTicks (input : List CliqueSym) : List UnaryFrameSym :=
  rewriteStatefulFlatMap targetTickSpec input

noncomputable def targetTicksComputableInPolyTime :
    TM2ComputableInPolyTime id id targetTicks :=
  statefulFlatMap_computableInPolyTime targetTickSpec

private theorem targetTicks_edges (input : List CliqueSym) :
    rewriteStatefulFlatMapFrom targetTickSpec .edges input = [] := by
  induction input with
  | nil => rfl
  | cons symbol input ih =>
      rw [rewriteStatefulFlatMapFrom.eq_def]
      change rewriteStatefulFlatMapFrom targetTickSpec .edges input = []
      exact ih

private theorem targetTicks_target (count : Nat) (suffix : List CliqueSym) :
    rewriteStatefulFlatMapFrom targetTickSpec .targetSize
        (prependCliqueTicks count (.fieldSep :: suffix)) =
      List.replicate count .tick := by
  induction count with
  | zero =>
      change rewriteStatefulFlatMapFrom targetTickSpec .edges suffix = []
      exact targetTicks_edges suffix
  | succ count ih =>
      rw [prependCliqueTicks, rewriteStatefulFlatMapFrom.eq_def]
      change .tick :: rewriteStatefulFlatMapFrom targetTickSpec .targetSize
          (prependCliqueTicks count (.fieldSep :: suffix)) =
        List.replicate (count + 1) .tick
      rw [ih, List.replicate_succ]

private theorem targetTicks_vertex (count : Nat) (tail : List CliqueSym) :
    rewriteStatefulFlatMapFrom targetTickSpec .vertexCount
        (prependCliqueTicks count (.fieldSep :: tail)) =
      rewriteStatefulFlatMapFrom targetTickSpec .targetSize tail := by
  induction count with
  | zero =>
      rw [rewriteStatefulFlatMapFrom.eq_def]
      rfl
  | succ count ih =>
      rw [prependCliqueTicks, rewriteStatefulFlatMapFrom.eq_def]
      exact ih

theorem targetTicks_encode (I : VertexCoverInstance) :
    targetTicks (encodeVertexCoverInstance I) =
      List.replicate I.targetSize .tick := by
  simp only [targetTicks, rewriteStatefulFlatMap,
    encodeVertexCoverInstance, encodeCliqueInstance]
  rw [rewriteStatefulFlatMapFrom.eq_def]
  change rewriteStatefulFlatMapFrom targetTickSpec .vertexCount
      (prependCliqueTicks I.vertexCount
        (.fieldSep :: prependCliqueTicks I.targetSize
          (.fieldSep :: I.edges.flatMap encodeCliqueEdge))) = _
  rw [targetTicks_vertex, targetTicks_target]

private theorem targetTicksFrom_all_ticks (mode : Header.CountMode)
    (input : List CliqueSym) :
    rewriteStatefulFlatMapFrom targetTickSpec mode input =
      List.replicate
        (rewriteStatefulFlatMapFrom targetTickSpec mode input).length .tick := by
  induction input generalizing mode with
  | nil => cases mode <;> rfl
  | cons symbol input ih =>
      rw [rewriteStatefulFlatMapFrom.eq_def]
      change (targetTickSpec.action mode symbol).1 ++
          rewriteStatefulFlatMapFrom targetTickSpec
            (targetTickSpec.action mode symbol).2 input =
        List.replicate
          ((targetTickSpec.action mode symbol).1 ++
            rewriteStatefulFlatMapFrom targetTickSpec
              (targetTickSpec.action mode symbol).2 input).length .tick
      cases mode with
      | vertexCount =>
          by_cases hsep : symbol = CliqueSym.fieldSep
          · rw [targetTickSpec_action_vertexCount, if_pos hsep,
              List.nil_append]
            exact ih .targetSize
          · rw [targetTickSpec_action_vertexCount, if_neg hsep,
              List.nil_append]
            exact ih .vertexCount
      | targetSize =>
          by_cases hsep : symbol = CliqueSym.fieldSep
          · rw [targetTickSpec_action_targetSize, if_pos hsep,
              List.nil_append]
            exact ih .edges
          · by_cases htick : symbol = CliqueSym.tick
            · rw [targetTickSpec_action_targetSize, if_neg hsep,
                if_pos htick]
              rw [ih .targetSize]
              simp [List.replicate_succ]
            · rw [targetTickSpec_action_targetSize, if_neg hsep,
                if_neg htick, List.nil_append]
              exact ih .targetSize
      | edges =>
          rw [targetTickSpec_action_edges, List.nil_append]
          exact ih .edges

private theorem targetTicks_all_ticks (input : List CliqueSym) :
    targetTicks input = List.replicate (targetTicks input).length .tick := by
  exact targetTicksFrom_all_ticks .vertexCount input

/-- Terminate the target tick stream as the second family field. -/
def targetFieldSpec : StatefulFlatMapSpec Unit UnaryFrameSym UnaryFrameSym where
  initial := ()
  action _ symbol := ([symbol], ())
  finish _ := [.separator]

def targetField (input : List CliqueSym) : List UnaryFrameSym :=
  rewriteStatefulFlatMap targetFieldSpec (targetTicks input)

private theorem targetFieldFrom (ticks : List UnaryFrameSym) :
    rewriteStatefulFlatMapFrom targetFieldSpec () ticks =
      ticks ++ [.separator] := by
  induction ticks with
  | nil => rfl
  | cons symbol ticks ih =>
      rw [rewriteStatefulFlatMapFrom.eq_def]
      exact congrArg (List.cons symbol) ih

theorem targetField_eq (input : List CliqueSym) :
    targetField input = targetTicks input ++ [.separator] := by
  exact targetFieldFrom (targetTicks input)

noncomputable def targetFieldComputableInPolyTime :
    TM2ComputableInPolyTime id id targetField := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    targetTicksComputableInPolyTime
    (statefulFlatMap_computableInPolyTime targetFieldSpec)
  change TM2ComputableInPolyTime id id
    (fun input => rewriteStatefulFlatMap targetFieldSpec (targetTicks input))
  simpa only [Function.comp_def] using Classical.choice composed

/-- A fixed left-invertible two-symbol code for the three-symbol unary-frame
alphabet, used by same-input concatenation. -/
def encodeUnaryFrameSymPair :
    UnaryFrameSym → UnaryFrameSym × UnaryFrameSym
  | .tick => (.tick, .tick)
  | .separator => (.tick, .separator)
  | .frameEnd => (.separator, .tick)

def decodeUnaryFrameSymPair :
    UnaryFrameSym → UnaryFrameSym → UnaryFrameSym
  | .tick, .tick => .tick
  | .tick, _ => .separator
  | _, _ => .frameEnd

@[simp] theorem decode_encodeUnaryFrameSymPair (symbol : UnaryFrameSym) :
    decodeUnaryFrameSymPair (encodeUnaryFrameSymPair symbol).1
      (encodeUnaryFrameSymPair symbol).2 = symbol := by
  cases symbol <;> rfl

/-- Runtime affine-prefix family extracted from an arbitrary source word. -/
def family (input : List CliqueSym) : UnaryFrameAffinePrefixRows where
  base := selectorBase (input.count .edgeMark)
  count := (targetTicks input).length

def familyStream (input : List CliqueSym) : List UnaryFrameSym :=
  baseField input ++ targetField input

theorem familyStream_eq (input : List CliqueSym) :
    familyStream input = encodeUnaryFrameAffinePrefixRows (family input) := by
  rw [familyStream, baseField_eq, targetField_eq]
  rw [targetTicks_all_ticks]
  simp [family, encodeUnaryFrameAffinePrefixRows, encodeUnaryFrame,
    encodeUnaryFrameBlock, List.append_assoc]

noncomputable def familyComputableInPolyTime :
    TM2ComputableInPolyTime id encodeUnaryFrameAffinePrefixRows family := by
  let joined := fixedPairSameInputConcat_computableInPolyTime
    encodeUnaryFrameSymPair decodeUnaryFrameSymPair
    decode_encodeUnaryFrameSymPair
    baseFieldComputableInPolyTime targetFieldComputableInPolyTime
  exact
    { tm := joined.tm
      inputAlphabet := joined.inputAlphabet
      outputAlphabet := joined.outputAlphabet
      time := joined.time
      outputsFun := fun input => by
        rw [← familyStream_eq input]
        simpa only [familyStream, id_eq] using joined.outputsFun input }

theorem family_encode (I : VertexCoverInstance) :
    family (encodeVertexCoverInstance I) =
      { base := selectorBase I.edges.length, count := I.targetSize } := by
  have hedge := congrArg List.length (WidgetEdges.Source.edgeTicks_encode I)
  rw [WidgetEdges.Source.edgeTicks_eq_replicate_count] at hedge
  have hcount : (encodeVertexCoverInstance I).count CliqueSym.edgeMark =
      I.edges.length := by simpa using hedge
  simp [family, hcount, targetTicks_encode]

/-- Generated triangular rows with shifted lower endpoints. -/
def rows (input : List CliqueSym) : List UnaryFrameSym :=
  unaryFrameAffinePrefixRowsStream (family input)

noncomputable def rowsComputableInPolyTime :
    TM2ComputableInPolyTime id id rows := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    familyComputableInPolyTime
    unaryFrameAffinePrefixRowsStream_computableInPolyTime
  change TM2ComputableInPolyTime id id
    (fun input => unaryFrameAffinePrefixRowsStream (family input))
  simpa only [Function.comp_def] using Classical.choice composed

/-- Input expected by the offset-aware pair formatter: the base field followed
by the generated marked rows. -/
def formatInput (input : List CliqueSym) : List UnaryFrameSym :=
  baseField input ++ rows input

noncomputable def formatInputComputableInPolyTime :
    TM2ComputableInPolyTime id id formatInput :=
  fixedPairSameInputConcat_computableInPolyTime
    encodeUnaryFrameSymPair decodeUnaryFrameSymPair
    decode_encodeUnaryFrameSymPair
    baseFieldComputableInPolyTime rowsComputableInPolyTime

theorem formatInput_encode (I : VertexCoverInstance) :
    formatInput (encodeVertexCoverInstance I) =
      encodeUnaryFrameBlock (selectorBase I.edges.length) ++
        unaryFrameAffinePrefixRowsStream
          { base := selectorBase I.edges.length, count := I.targetSize } := by
  have hfamily := family_encode I
  have hbase :
      selectorBase
          ((encodeVertexCoverInstance I).count CliqueSym.edgeMark) =
        selectorBase I.edges.length := by
    have := congrArg UnaryFrameAffinePrefixRows.base hfamily
    simpa [family] using this
  rw [formatInput, baseField_eq, rows, hfamily, hbase]

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.SelectorClique

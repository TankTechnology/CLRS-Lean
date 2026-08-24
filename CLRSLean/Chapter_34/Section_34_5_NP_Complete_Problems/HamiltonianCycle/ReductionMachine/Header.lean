import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Construction.Instance
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.Header
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.FixedPairSameInputConcat
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.StatefulFlatMap

/-!
# VERTEX-COVER to HAM-CYCLE machine: nondegenerate header

The ordinary CLRS target has `12 * edgeCount + targetSize` vertices and uses
the same number in both unary header fields.  A fixed three-mode transducer
extracts this count directly from a canonical source graph: it copies one tick
for each source-target tick and emits twelve ticks for each edge record.  Two
same-input copies are then formatted as the complete target header.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Header

open _root_.Turing
open PolyBuilder
open HamiltonianCycleReduction

/-- Which canonical source field is currently being scanned. -/
inductive CountMode
  | vertexCount
  | targetSize
  | edges
deriving DecidableEq, Fintype

/-- Twelve unary ticks, one for each vertex of a CLRS edge gadget. -/
def widgetTicks : List CliqueSym :=
  List.replicate widgetVertexCount .tick

/-- Extract the unary target vertex count from a canonical source encoding. -/
def countSpec : StatefulFlatMapSpec CountMode CliqueSym CliqueSym where
  initial := .vertexCount
  action mode symbol :=
    match mode with
    | .vertexCount =>
        if symbol = .fieldSep then ([], .targetSize)
        else ([], .vertexCount)
    | .targetSize =>
        if symbol = .fieldSep then ([], .edges)
        else if symbol = .tick then ([.tick], .targetSize)
        else ([], .targetSize)
    | .edges =>
        if symbol = .edgeMark then (widgetTicks, .edges)
        else ([], .edges)
  finish _ := []

/-- Pure extracted count stream. -/
def countStream (input : List CliqueSym) : List CliqueSym :=
  rewriteStatefulFlatMap countSpec input

/-- A fixed linear-time machine extracts the unary target count. -/
noncomputable def countStreamComputableInPolyTime :
    TM2ComputableInPolyTime id id countStream :=
  statefulFlatMap_computableInPolyTime countSpec

private theorem rewrite_edges_prependTicks (count : Nat)
    (suffix : List CliqueSym) :
    rewriteStatefulFlatMapFrom countSpec .edges
        (prependCliqueTicks count suffix) =
      rewriteStatefulFlatMapFrom countSpec .edges suffix := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [prependCliqueTicks, rewriteStatefulFlatMapFrom.eq_def]
      change rewriteStatefulFlatMapFrom countSpec .edges
          (prependCliqueTicks count suffix) =
        rewriteStatefulFlatMapFrom countSpec .edges suffix
      exact ih

private theorem countSpec_edges_next (symbol : CliqueSym) :
    (countSpec.action .edges symbol).2 = .edges := by
  cases symbol <;> rfl

private theorem rewrite_edges_cons (symbol : CliqueSym)
    (rest : List CliqueSym) :
    rewriteStatefulFlatMapFrom countSpec .edges (symbol :: rest) =
      (countSpec.action .edges symbol).1 ++
        rewriteStatefulFlatMapFrom countSpec .edges rest := by
  change (countSpec.action .edges symbol).1 ++
      rewriteStatefulFlatMapFrom countSpec
        (countSpec.action .edges symbol).2 rest = _
  rw [countSpec_edges_next]

private theorem rewrite_edges_append (left right : List CliqueSym) :
    rewriteStatefulFlatMapFrom countSpec .edges (left ++ right) =
      rewriteStatefulFlatMapFrom countSpec .edges left ++
        rewriteStatefulFlatMapFrom countSpec .edges right := by
  induction left with
  | nil => rfl
  | cons symbol left ih =>
      rw [List.cons_append, rewrite_edges_cons, rewrite_edges_cons,
        ih, List.append_assoc]

private theorem rewrite_edges_encodeEdge (edge : Nat × Nat) :
    rewriteStatefulFlatMapFrom countSpec .edges
        (encodeCliqueEdge edge) = widgetTicks := by
  rcases edge with ⟨left, right⟩
  rw [encodeCliqueEdge, rewriteStatefulFlatMapFrom.eq_def]
  change widgetTicks ++ rewriteStatefulFlatMapFrom countSpec .edges
      (prependCliqueTicks left
        (.pairSep :: prependCliqueTicks right [.recordEnd])) = widgetTicks
  rw [rewrite_edges_prependTicks]
  rw [rewriteStatefulFlatMapFrom.eq_def]
  change widgetTicks ++ rewriteStatefulFlatMapFrom countSpec .edges
      (prependCliqueTicks right [.recordEnd]) = widgetTicks
  rw [rewrite_edges_prependTicks]
  rw [rewriteStatefulFlatMapFrom.eq_def]
  rfl

private theorem rewrite_edges_flatMap (edges : List (Nat × Nat)) :
    rewriteStatefulFlatMapFrom countSpec .edges
        (edges.flatMap encodeCliqueEdge) =
      List.replicate (widgetVertexCount * edges.length) .tick := by
  induction edges with
  | nil => rfl
  | cons edge edges ih =>
      rw [List.flatMap_cons, rewrite_edges_append,
        rewrite_edges_encodeEdge, ih]
      change List.replicate widgetVertexCount CliqueSym.tick ++
          List.replicate (widgetVertexCount * edges.length) CliqueSym.tick =
        List.replicate (widgetVertexCount * (edges.length + 1))
          CliqueSym.tick
      rw [Nat.mul_succ, Nat.add_comm, List.replicate_add]

private theorem rewrite_target_prependTicks (count : Nat)
    (suffix : List CliqueSym) :
    rewriteStatefulFlatMapFrom countSpec .targetSize
        (prependCliqueTicks count (.fieldSep :: suffix)) =
      List.replicate count .tick ++
        rewriteStatefulFlatMapFrom countSpec .edges suffix := by
  induction count with
  | zero =>
      rw [rewriteStatefulFlatMapFrom.eq_def]
      rfl
  | succ count ih =>
      rw [prependCliqueTicks, rewriteStatefulFlatMapFrom.eq_def]
      change .tick :: rewriteStatefulFlatMapFrom countSpec .targetSize
          (prependCliqueTicks count (.fieldSep :: suffix)) =
        List.replicate (count + 1) .tick ++
          rewriteStatefulFlatMapFrom countSpec .edges suffix
      rw [ih, List.replicate_succ]
      rfl

private theorem rewrite_vertex_prependTicks (count : Nat)
    (targetField : List CliqueSym) :
    rewriteStatefulFlatMapFrom countSpec .vertexCount
        (prependCliqueTicks count (.fieldSep :: targetField)) =
      rewriteStatefulFlatMapFrom countSpec .targetSize targetField := by
  induction count with
  | zero =>
      rw [rewriteStatefulFlatMapFrom.eq_def]
      rfl
  | succ count ih =>
      rw [prependCliqueTicks, rewriteStatefulFlatMapFrom.eq_def]
      change rewriteStatefulFlatMapFrom countSpec .vertexCount
          (prependCliqueTicks count (.fieldSep :: targetField)) =
        rewriteStatefulFlatMapFrom countSpec .targetSize targetField
      exact ih

/-- Exact extracted count on every canonical source instance. -/
theorem countStream_encode (I : VertexCoverInstance) :
    countStream (encodeVertexCoverInstance I) =
      List.replicate
        (selectorBase I.edges.length + I.targetSize) .tick := by
  simp only [countStream, rewriteStatefulFlatMap, encodeVertexCoverInstance,
    encodeCliqueInstance]
  rw [rewriteStatefulFlatMapFrom.eq_def]
  change rewriteStatefulFlatMapFrom countSpec .vertexCount
      (prependCliqueTicks I.vertexCount
        (.fieldSep :: prependCliqueTicks I.targetSize
          (.fieldSep :: I.edges.flatMap encodeCliqueEdge))) = _
  rw [rewrite_vertex_prependTicks, rewrite_target_prependTicks,
    rewrite_edges_flatMap]
  change List.replicate I.targetSize CliqueSym.tick ++
      List.replicate (widgetVertexCount * I.edges.length) CliqueSym.tick =
    List.replicate
      (widgetVertexCount * I.edges.length + I.targetSize) CliqueSym.tick
  rw [Nat.add_comm, List.replicate_add]

/-- Prefix the extracted count by the instance marker and terminate its field. -/
def vertexHeaderSpec : StatefulFlatMapSpec Bool CliqueSym CliqueSym where
  initial := false
  action started symbol :=
    if started then ([symbol], true)
    else ([.instanceMark, symbol], true)
  finish started :=
    if started then [.fieldSep] else [.instanceMark, .fieldSep]

/-- Terminate the second copy as the target-size field. -/
def targetHeaderSpec : StatefulFlatMapSpec Unit CliqueSym CliqueSym where
  initial := ()
  action _ symbol := ([symbol], ())
  finish _ := [.fieldSep]

def vertexHeader (ticks : List CliqueSym) : List CliqueSym :=
  rewriteStatefulFlatMap vertexHeaderSpec ticks

def targetHeader (ticks : List CliqueSym) : List CliqueSym :=
  rewriteStatefulFlatMap targetHeaderSpec ticks

private theorem vertexHeader_eq (ticks : List CliqueSym) :
    vertexHeader ticks = .instanceMark :: ticks ++ [.fieldSep] := by
  have fromTrue : ∀ rest : List CliqueSym,
      rewriteStatefulFlatMapFrom vertexHeaderSpec true rest =
        rest ++ [.fieldSep] := by
    intro rest
    induction rest with
    | nil => rfl
    | cons symbol rest ih =>
        rw [rewriteStatefulFlatMapFrom.eq_def]
        change symbol :: rewriteStatefulFlatMapFrom vertexHeaderSpec true rest =
          symbol :: (rest ++ [.fieldSep])
        exact congrArg (List.cons symbol) ih
  cases ticks with
  | nil => rfl
  | cons symbol ticks =>
      rw [vertexHeader, rewriteStatefulFlatMap,
        rewriteStatefulFlatMapFrom.eq_def]
      change [.instanceMark, symbol] ++
          rewriteStatefulFlatMapFrom vertexHeaderSpec true ticks =
        .instanceMark :: symbol :: ticks ++ [.fieldSep]
      rw [fromTrue]
      rfl

private theorem targetHeader_eq (ticks : List CliqueSym) :
    targetHeader ticks = ticks ++ [.fieldSep] := by
  induction ticks with
  | nil => rfl
  | cons symbol ticks ih =>
      rw [targetHeader, rewriteStatefulFlatMap,
        rewriteStatefulFlatMapFrom.eq_def]
      change symbol :: rewriteStatefulFlatMapFrom targetHeaderSpec () ticks =
        symbol :: (ticks ++ [.fieldSep])
      exact congrArg (List.cons symbol)
        (by simpa [targetHeader, rewriteStatefulFlatMap] using ih)

noncomputable def vertexHeaderComputableInPolyTime :
    TM2ComputableInPolyTime id id vertexHeader :=
  statefulFlatMap_computableInPolyTime vertexHeaderSpec

noncomputable def targetHeaderComputableInPolyTime :
    TM2ComputableInPolyTime id id targetHeader :=
  statefulFlatMap_computableInPolyTime targetHeaderSpec

/-- Header over an extracted unary count. -/
def headerFromCount (ticks : List CliqueSym) : List CliqueSym :=
  vertexHeader ticks ++ targetHeader ticks

/-- Same-input composition duplicates and formats the extracted count. -/
noncomputable def headerFromCountComputableInPolyTime :
    TM2ComputableInPolyTime id id headerFromCount := by
  exact fixedPairSameInputConcat_computableInPolyTime
    TMClique.encodeCliqueSymPair TMClique.decodeCliqueSymPair
    TMClique.decode_encodeCliqueSymPair
    vertexHeaderComputableInPolyTime targetHeaderComputableInPolyTime

/-- Complete nondegenerate target header generated from a canonical source. -/
def header (input : List CliqueSym) : List CliqueSym :=
  headerFromCount (countStream input)

/-- One fixed polynomial-time TM2 generates the complete nondegenerate header. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id header := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    countStreamComputableInPolyTime headerFromCountComputableInPolyTime
  change TM2ComputableInPolyTime id id
    (fun input => headerFromCount (countStream input))
  simpa only [Function.comp_def] using Classical.choice composed

private theorem replicate_ticks_append (count : Nat)
    (suffix : List CliqueSym) :
    List.replicate count CliqueSym.tick ++ suffix =
      prependCliqueTicks count suffix := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.replicate_succ, prependCliqueTicks]
      exact congrArg (List.cons .tick) ih

/-- Exact canonical header semantics. -/
theorem header_encode (I : VertexCoverInstance) :
    header (encodeVertexCoverInstance I) =
      .instanceMark ::
        prependCliqueTicks (selectorBase I.edges.length + I.targetSize)
          (.fieldSep ::
            prependCliqueTicks (selectorBase I.edges.length + I.targetSize)
              [.fieldSep]) := by
  rw [header, countStream_encode, headerFromCount,
    vertexHeader_eq, targetHeader_eq]
  change [.instanceMark] ++
      (List.replicate (selectorBase I.edges.length + I.targetSize) .tick ++
        [.fieldSep] ++
        (List.replicate (selectorBase I.edges.length + I.targetSize) .tick ++
          [.fieldSep])) =
    [.instanceMark] ++
      prependCliqueTicks (selectorBase I.edges.length + I.targetSize)
        (.fieldSep ::
          prependCliqueTicks (selectorBase I.edges.length + I.targetSize)
            [.fieldSep])
  refine congrArg
    (fun tail : List CliqueSym => [CliqueSym.instanceMark] ++ tail) ?_
  rw [List.append_assoc, replicate_ticks_append]
  change prependCliqueTicks (selectorBase I.edges.length + I.targetSize)
      (.fieldSep ::
        (List.replicate (selectorBase I.edges.length + I.targetSize) .tick ++
          [.fieldSep])) = _
  rw [replicate_ticks_append]

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Header

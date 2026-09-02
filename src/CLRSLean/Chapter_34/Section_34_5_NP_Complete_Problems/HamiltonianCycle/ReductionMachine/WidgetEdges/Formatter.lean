import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.WidgetEdges.Endpoints

/-!
# VERTEX-COVER to HAM-CYCLE machine: widget-edge formatter

This finite-state pass converts consecutive unary endpoint pairs into the
shared graph edge grammar.  It adds no arithmetic: it only materializes the
fixed `edgeMark`, `pairSep`, and `recordEnd` symbols.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.WidgetEdges

open _root_.Turing
open PolyBuilder
open HamiltonianCycleReduction

/-- Position inside a two-field endpoint record. -/
inductive FormatterMode
  | leftStart
  | leftBody
  | right
deriving DecidableEq, Fintype

/-- Fixed conversion from ordinary unary fields to canonical graph edges. -/
def formatterSpec :
    StatefulFlatMapSpec FormatterMode UnaryFrameSym CliqueSym where
  initial := .leftStart
  action mode symbol :=
    match mode, symbol with
    | .leftStart, .tick => ([.edgeMark, .tick], .leftBody)
    | .leftStart, .separator => ([.edgeMark, .pairSep], .right)
    | .leftStart, .frameEnd => ([], .leftStart)
    | .leftBody, .tick => ([.tick], .leftBody)
    | .leftBody, .separator => ([.pairSep], .right)
    | .leftBody, .frameEnd => ([], .leftStart)
    | .right, .tick => ([.tick], .right)
    | .right, .separator => ([.recordEnd], .leftStart)
    | .right, .frameEnd => ([], .leftStart)
  finish _ := []

/-- Format an arbitrary unary endpoint stream. -/
def formatEndpointStream (input : List UnaryFrameSym) : List CliqueSym :=
  rewriteStatefulFlatMap formatterSpec input

/-- The formatter is a fixed linear-time TM2. -/
noncomputable def formatEndpointStreamComputableInPolyTime :
    TM2ComputableInPolyTime id id formatEndpointStream :=
  statefulFlatMap_computableInPolyTime formatterSpec

private theorem format_leftBody_ticks (count : Nat)
    (tail : List UnaryFrameSym) :
    rewriteStatefulFlatMapFrom formatterSpec .leftBody
        (List.replicate count .tick ++ .separator :: tail) =
      prependCliqueTicks count
        (.pairSep ::
          rewriteStatefulFlatMapFrom formatterSpec .right tail) := by
  induction count with
  | zero =>
      rw [rewriteStatefulFlatMapFrom.eq_def]
      rfl
  | succ count ih =>
      rw [List.replicate_succ, List.cons_append,
        rewriteStatefulFlatMapFrom.eq_def, prependCliqueTicks]
      change .tick :: rewriteStatefulFlatMapFrom formatterSpec .leftBody
          (List.replicate count .tick ++ .separator :: tail) =
        .tick :: prependCliqueTicks count
          (.pairSep :: rewriteStatefulFlatMapFrom formatterSpec .right tail)
      exact congrArg (List.cons CliqueSym.tick) ih

private theorem format_leftStart_ticks (count : Nat)
    (tail : List UnaryFrameSym) :
    rewriteStatefulFlatMapFrom formatterSpec .leftStart
        (List.replicate count .tick ++ .separator :: tail) =
      .edgeMark :: prependCliqueTicks count
        (.pairSep ::
          rewriteStatefulFlatMapFrom formatterSpec .right tail) := by
  cases count with
  | zero =>
      rw [rewriteStatefulFlatMapFrom.eq_def]
      rfl
  | succ count =>
      rw [List.replicate_succ, List.cons_append,
        rewriteStatefulFlatMapFrom.eq_def, prependCliqueTicks]
      change .edgeMark :: .tick ::
          rewriteStatefulFlatMapFrom formatterSpec .leftBody
            (List.replicate count .tick ++ .separator :: tail) =
        .edgeMark :: .tick :: prependCliqueTicks count
          (.pairSep :: rewriteStatefulFlatMapFrom formatterSpec .right tail)
      exact congrArg (List.cons CliqueSym.edgeMark)
        (congrArg (List.cons CliqueSym.tick)
          (format_leftBody_ticks count tail))

private theorem format_right_ticks (count : Nat)
    (tail : List UnaryFrameSym) :
    rewriteStatefulFlatMapFrom formatterSpec .right
        (List.replicate count .tick ++ .separator :: tail) =
      prependCliqueTicks count
        (.recordEnd ::
          rewriteStatefulFlatMapFrom formatterSpec .leftStart tail) := by
  induction count with
  | zero =>
      rw [rewriteStatefulFlatMapFrom.eq_def]
      rfl
  | succ count ih =>
      rw [List.replicate_succ, List.cons_append,
        rewriteStatefulFlatMapFrom.eq_def, prependCliqueTicks]
      change .tick :: rewriteStatefulFlatMapFrom formatterSpec .right
          (List.replicate count .tick ++ .separator :: tail) =
        .tick :: prependCliqueTicks count
          (.recordEnd ::
            rewriteStatefulFlatMapFrom formatterSpec .leftStart tail)
      exact congrArg (List.cons CliqueSym.tick) ih

private theorem format_one_edge (edge : Nat × Nat)
    (tail : List UnaryFrameSym) :
    rewriteStatefulFlatMapFrom formatterSpec .leftStart
        (encodeUnaryFrameBlock edge.1 ++
          encodeUnaryFrameBlock edge.2 ++ tail) =
      encodeCliqueEdge edge ++
        rewriteStatefulFlatMapFrom formatterSpec .leftStart tail := by
  rcases edge with ⟨left, right⟩
  rw [show encodeUnaryFrameBlock left ++ encodeUnaryFrameBlock right ++ tail =
      List.replicate left .tick ++ .separator ::
        (List.replicate right .tick ++ .separator :: tail) by
    simp [encodeUnaryFrameBlock, List.append_assoc]]
  rw [format_leftStart_ticks, format_right_ticks]
  simp [encodeCliqueEdge, prependCliqueTicks_append]

/-- Pair formatting has the exact shared graph-encoding semantics. -/
theorem formatEndpointStream_edges (edges : List (Nat × Nat)) :
    formatEndpointStream
        (encodeUnaryFrame (edges.flatMap fun edge => [edge.1, edge.2])) =
      edges.flatMap encodeCliqueEdge := by
  unfold formatEndpointStream rewriteStatefulFlatMap
  induction edges with
  | nil => rfl
  | cons edge edges ih =>
      rw [show encodeUnaryFrame
            (((edge :: edges).flatMap fun item => [item.1, item.2])) =
          encodeUnaryFrameBlock edge.1 ++ encodeUnaryFrameBlock edge.2 ++
            encodeUnaryFrame
              (edges.flatMap fun item => [item.1, item.2]) by
        simp [encodeUnaryFrame, List.append_assoc]]
      change rewriteStatefulFlatMapFrom formatterSpec .leftStart
          (encodeUnaryFrameBlock edge.1 ++ encodeUnaryFrameBlock edge.2 ++
            encodeUnaryFrame
              (edges.flatMap fun item => [item.1, item.2])) =
        (edge :: edges).flatMap encodeCliqueEdge
      have ih' :
          rewriteStatefulFlatMapFrom formatterSpec .leftStart
              (encodeUnaryFrame
                (edges.flatMap fun item => [item.1, item.2])) =
            edges.flatMap encodeCliqueEdge := by
        simpa [formatterSpec] using ih
      rw [format_one_edge, ih']
      rfl

/-- Complete internal-widget edge stream generated from a raw source string. -/
def widgetEdgeStream (input : List CliqueSym) : List CliqueSym :=
  formatEndpointStream (endpointStream input)

/-- A fixed polynomial-time TM2 generates every internal gadget edge. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id widgetEdgeStream := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    endpointStreamComputableInPolyTime
    formatEndpointStreamComputableInPolyTime
  change TM2ComputableInPolyTime id id
    (fun input => formatEndpointStream (endpointStream input))
  simpa only [Function.comp_def] using Classical.choice composed

/-- Exact canonical edge-family semantics. -/
theorem widgetEdgeStream_encode (I : VertexCoverInstance) :
    widgetEdgeStream (encodeVertexCoverInstance I) =
      (allGlobalWidgetEdges I.edges.length).flatMap encodeCliqueEdge := by
  rw [widgetEdgeStream, endpointStream, endpointValues_encode,
    formatEndpointStream_edges]

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.WidgetEdges

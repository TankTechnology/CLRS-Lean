import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Construction.Instance
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineUnaryTripleProgression
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.StatefulFlatMap

/-!
# VERTEX-COVER to HAM-CYCLE machine: widget-edge source

The fourteen internal edges of gadget occurrence `i` have endpoints affine in
`i`.  This file performs the only source-grammar-dependent part of their
generation: a fixed transducer counts source edge records and produces the
runtime descriptor for the progression `(i, 0, 0)`, for `0 ≤ i < edgeCount`.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.WidgetEdges.Source

open _root_.Turing
open PolyBuilder
open HamiltonianCycleReduction

/-- Retain one unary tick for every source edge marker. -/
def edgeTickSpec : StatefulFlatMapSpec Unit CliqueSym UnaryFrameSym where
  initial := ()
  action _ symbol :=
    (if symbol = .edgeMark then [.tick] else [], ())
  finish _ := []

/-- Unary source-edge count extracted from an arbitrary raw symbol string. -/
def edgeTicks (input : List CliqueSym) : List UnaryFrameSym :=
  rewriteStatefulFlatMap edgeTickSpec input

/-- A fixed linear-time machine extracts the edge-count ticks. -/
noncomputable def edgeTicksComputableInPolyTime :
    TM2ComputableInPolyTime id id edgeTicks :=
  statefulFlatMap_computableInPolyTime edgeTickSpec

/-- The extractor emits no symbols other than the exact number of edge ticks. -/
theorem edgeTicks_eq_replicate_count (input : List CliqueSym) :
    edgeTicks input =
      List.replicate (input.count .edgeMark) UnaryFrameSym.tick := by
  unfold edgeTicks rewriteStatefulFlatMap
  induction input with
  | nil => rfl
  | cons symbol rest ih =>
      rw [rewriteStatefulFlatMapFrom.eq_def]
      by_cases hmark : symbol = CliqueSym.edgeMark
      · subst symbol
        simp only [edgeTickSpec, if_pos, List.cons_append, List.nil_append,
          List.count_cons_self, List.replicate_succ]
        exact congrArg (List.cons UnaryFrameSym.tick) ih
      · simp only [edgeTickSpec, if_neg hmark, List.nil_append,
          List.count_cons_of_ne hmark]
        exact ih

private theorem count_edgeMark_prependCliqueTicks
    (count : Nat) (suffix : List CliqueSym) :
    (prependCliqueTicks count suffix).count .edgeMark =
      suffix.count .edgeMark := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [prependCliqueTicks]
      simpa using ih

private theorem count_edgeMark_encodeCliqueEdge (edge : Nat × Nat) :
    (encodeCliqueEdge edge).count .edgeMark = 1 := by
  rcases edge with ⟨left, right⟩
  simp only [encodeCliqueEdge, List.count_cons_self]
  rw [count_edgeMark_prependCliqueTicks]
  simp only [List.count_cons_of_ne (by decide : CliqueSym.pairSep ≠ .edgeMark)]
  rw [count_edgeMark_prependCliqueTicks]
  decide

private theorem count_edgeMark_flatMap_encodeCliqueEdge
    (edges : List (Nat × Nat)) :
    (edges.flatMap encodeCliqueEdge).count .edgeMark = edges.length := by
  induction edges with
  | nil => rfl
  | cons edge edges ih =>
      rw [List.flatMap_cons, List.count_append,
        count_edgeMark_encodeCliqueEdge, ih]
      simp [Nat.add_comm]

/-- On canonical graph input, the extracted count is exactly the edge-list
length, including repeated stored edge occurrences. -/
theorem edgeTicks_encode (I : VertexCoverInstance) :
    edgeTicks (encodeVertexCoverInstance I) =
      List.replicate I.edges.length UnaryFrameSym.tick := by
  rw [edgeTicks_eq_replicate_count]
  unfold encodeVertexCoverInstance encodeCliqueInstance
  simp only [List.count_cons_of_ne
    (by decide : CliqueSym.instanceMark ≠ .edgeMark)]
  rw [count_edgeMark_prependCliqueTicks]
  simp only [List.count_cons_of_ne
    (by decide : CliqueSym.fieldSep ≠ .edgeMark)]
  rw [count_edgeMark_prependCliqueTicks]
  simp only [List.count_cons_of_ne
    (by decide : CliqueSym.fieldSep ≠ .edgeMark)]
  rw [count_edgeMark_flatMap_encodeCliqueEdge]

/-- Fixed prefix of the seven-field triple-progression descriptor
`(0, 0, 0; 1, 0, 0; count)`. -/
def descriptorPrefix : List UnaryFrameSym :=
  [.separator, .separator, .separator, .tick,
    .separator, .separator, .separator]

/-- Add the fixed affine parameters before unary count ticks and terminate the
last field. -/
def descriptorFrameSpec : StatefulFlatMapSpec Bool UnaryFrameSym UnaryFrameSym where
  initial := false
  action started symbol :=
    if started then ([symbol], true)
    else (descriptorPrefix ++ [symbol], true)
  finish started :=
    if started then [.separator]
    else descriptorPrefix ++ [.separator]

/-- Materialize the full progression descriptor from extracted count ticks. -/
def descriptorFromTicks (ticks : List UnaryFrameSym) : List UnaryFrameSym :=
  rewriteStatefulFlatMap descriptorFrameSpec ticks

noncomputable def descriptorFromTicksComputableInPolyTime :
    TM2ComputableInPolyTime id id descriptorFromTicks :=
  statefulFlatMap_computableInPolyTime descriptorFrameSpec

private theorem descriptorFromTicks_started (ticks : List UnaryFrameSym) :
    rewriteStatefulFlatMapFrom descriptorFrameSpec true ticks =
      ticks ++ [.separator] := by
  induction ticks with
  | nil => rfl
  | cons symbol ticks ih =>
      rw [rewriteStatefulFlatMapFrom.eq_def]
      change symbol :: rewriteStatefulFlatMapFrom descriptorFrameSpec true ticks =
        symbol :: (ticks ++ [.separator])
      exact congrArg (List.cons symbol) ih

/-- Exact framing semantics, including the empty-count case. -/
theorem descriptorFromTicks_eq (ticks : List UnaryFrameSym) :
    descriptorFromTicks ticks =
      descriptorPrefix ++ ticks ++ [.separator] := by
  cases ticks with
  | nil => rfl
  | cons symbol ticks =>
      rw [descriptorFromTicks, rewriteStatefulFlatMap,
        rewriteStatefulFlatMapFrom.eq_def]
      change (descriptorPrefix ++ [symbol]) ++
          rewriteStatefulFlatMapFrom descriptorFrameSpec true ticks =
        descriptorPrefix ++ symbol :: ticks ++ [.separator]
      rw [descriptorFromTicks_started]
      simp [List.append_assoc]

/-- Typed runtime descriptor consumed by the generic triple progression. -/
def progression (input : List CliqueSym) : AffineUnaryTripleProgression where
  base₁ := 0
  base₂ := 0
  base₃ := 0
  step₁ := 1
  step₂ := 0
  step₃ := 0
  count := input.count .edgeMark

/-- The two streaming stages produce the canonical descriptor encoding on all
raw inputs, not merely on well-formed instances. -/
theorem descriptorFromTicks_edgeTicks (input : List CliqueSym) :
    descriptorFromTicks (edgeTicks input) =
      encodeAffineUnaryTripleProgression (progression input) := by
  rw [descriptorFromTicks_eq, edgeTicks_eq_replicate_count]
  simp [descriptorPrefix, progression,
    encodeAffineUnaryTripleProgression, encodeUnaryFrame,
    encodeUnaryFrameBlock]

/-- A fixed polynomial-time TM2 computes the typed progression descriptor
directly from the raw source alphabet. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id encodeAffineUnaryTripleProgression progression := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    edgeTicksComputableInPolyTime descriptorFromTicksComputableInPolyTime
  let raw := Classical.choice composed
  exact
    { tm := raw.tm
      inputAlphabet := raw.inputAlphabet
      outputAlphabet := raw.outputAlphabet
      time := raw.time
      outputsFun := fun input => by
        simpa only [Function.comp_def, descriptorFromTicks_edgeTicks, id_eq] using
          raw.outputsFun input }

/-- Canonical sources select precisely the occurrence range of the stored
edge list. -/
theorem progression_encode (I : VertexCoverInstance) :
    progression (encodeVertexCoverInstance I) =
      { base₁ := 0, base₂ := 0, base₃ := 0,
        step₁ := 1, step₂ := 0, step₃ := 0,
        count := I.edges.length } := by
  have hlength := congrArg List.length (edgeTicks_encode I)
  rw [edgeTicks_eq_replicate_count] at hlength
  have hcount :
      (encodeVertexCoverInstance I).count CliqueSym.edgeMark =
        I.edges.length := by
    simpa using hlength
  simp [progression, hcount]

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.WidgetEdges.Source

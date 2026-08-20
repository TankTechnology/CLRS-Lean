import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineMuxInvocationProgressionControllerSegments
import Mathlib.Tactic

/-!
# Whole-family run of the affine mux invocation controller

The segment theorem is iterated over the complete arithmetic source and then
connected to the controller's pre-halt state.  The resulting theorem is the
exact semantic core needed by the polynomial-time wrapper.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Exact accumulated cost of all complete segments. -/
def affineMuxInvocationProgressionControllerFamilySteps :
    List AffineMuxInvocationProgression → Nat
  | [] => 0
  | segment :: rest =>
      affineMuxInvocationProgressionControllerSegmentSteps segment +
        affineMuxInvocationProgressionControllerFamilySteps rest

/-- The empty family preserves its incoming buffer; a nonempty family ends
immediately after consuming its final `frameEnd` marker. -/
def affineMuxInvocationProgressionControllerFamilyBuffer
    (segments : List AffineMuxInvocationProgression)
    (buffer₁ : Option UnaryFrameSym) : Option UnaryFrameSym :=
  match segments with
  | [] => buffer₁
  | _ :: _ => some .frameEnd

@[simp] theorem affineMuxInvocationProgressionControllerFamilyBuffer_frameEnd
    (segments : List AffineMuxInvocationProgression) :
    affineMuxInvocationProgressionControllerFamilyBuffer segments
      (some .frameEnd) = some .frameEnd := by
  cases segments <;> rfl

/-- Exact execution over a list of complete source segments. -/
def affineMuxInvocationProgressionController_segments_emit
    (segments : List AffineMuxInvocationProgression)
    (buffer₁ : Option UnaryFrameSym) (output : List UnaryFrameSym) :
    EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      (affineMuxInvocationProgressionControllerBoundaryCfg buffer₁
        (segments.flatMap AffineMuxInvocationProgression.sourceFrames) output)
      (some (affineMuxInvocationProgressionControllerBoundaryCfg
        (affineMuxInvocationProgressionControllerFamilyBuffer segments buffer₁)
        [] ((affineMuxInvocationProgressionFamilyFrames segments).reverse ++
          output)))
      (affineMuxInvocationProgressionControllerFamilySteps segments) := by
  induction segments generalizing buffer₁ output with
  | nil => exact ⟨⟨0, rfl⟩, le_rfl⟩
  | cons segment rest ih =>
      let restInput :=
        rest.flatMap AffineMuxInvocationProgression.sourceFrames
      let segmentOutput := (segment.invocationFrames).reverse ++ output
      have hsegment : EvalsToInTime
          (step affineMuxInvocationProgressionControllerRevProgram)
          (affineMuxInvocationProgressionControllerBoundaryCfg buffer₁
            ((segment :: rest).flatMap
              AffineMuxInvocationProgression.sourceFrames) output)
          (some (affineMuxInvocationProgressionControllerBoundaryCfg
            (some .frameEnd) restInput segmentOutput))
          (affineMuxInvocationProgressionControllerSegmentSteps segment) := by
        simpa [restInput, segmentOutput, List.append_assoc] using
          affineMuxInvocationProgressionController_segment_emit
            segment buffer₁ restInput output
      have hrest : EvalsToInTime
          (step affineMuxInvocationProgressionControllerRevProgram)
          (affineMuxInvocationProgressionControllerBoundaryCfg
            (some .frameEnd) restInput segmentOutput)
          (some (affineMuxInvocationProgressionControllerBoundaryCfg
            (affineMuxInvocationProgressionControllerFamilyBuffer rest
              (some .frameEnd))
            [] ((affineMuxInvocationProgressionFamilyFrames rest).reverse ++
              segmentOutput)))
          (affineMuxInvocationProgressionControllerFamilySteps rest) := by
        simpa [restInput] using ih (some .frameEnd) segmentOutput
      let full := EvalsToInTime.trans
        (step affineMuxInvocationProgressionControllerRevProgram)
        (affineMuxInvocationProgressionControllerSegmentSteps segment)
        (affineMuxInvocationProgressionControllerFamilySteps rest)
        _ _ _ hsegment hrest
      convert full using 1
      · simp [affineMuxInvocationProgressionControllerFamilyBuffer,
          affineMuxInvocationProgressionFamilyFrames, segmentOutput,
          List.reverse_append, List.append_assoc]
        cases rest <;> rfl
      · simp [affineMuxInvocationProgressionControllerFamilySteps,
          Nat.add_comm]

/-- An empty-input boundary reaches the public pre-halt configuration in one
step, independently of the stale input-pop buffer. -/
def affineMuxInvocationProgressionController_finish
    (buffer₁ : Option UnaryFrameSym) (output : List UnaryFrameSym) :
    EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      (affineMuxInvocationProgressionControllerBoundaryCfg buffer₁ [] output)
      (some (affineMuxInvocationProgressionControllerFinishCfg output)) 1 :=
  ⟨⟨1, rfl⟩, le_rfl⟩

/-- Complete exact reversed-output run on the source produced by the existing
fixed-group arithmetic generator. -/
def affineMuxInvocationProgressionControllerRev_run
    (segments : List AffineMuxInvocationProgression) :
    EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      (initialCfg affineMuxInvocationProgressionControllerRevProgram
        (affineMuxInvocationProgressionFamilySourceFrames segments))
      (some (affineMuxInvocationProgressionControllerFinishCfg
        (affineMuxInvocationProgressionFamilyFrames segments).reverse))
      (affineMuxInvocationProgressionControllerFamilySteps segments + 1) := by
  have hsegments : EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      (initialCfg affineMuxInvocationProgressionControllerRevProgram
        (affineMuxInvocationProgressionFamilySourceFrames segments))
      (some (affineMuxInvocationProgressionControllerBoundaryCfg
        (affineMuxInvocationProgressionControllerFamilyBuffer segments none)
        [] (affineMuxInvocationProgressionFamilyFrames segments).reverse))
      (affineMuxInvocationProgressionControllerFamilySteps segments) := by
    simpa [affineMuxInvocationProgressionControllerBoundaryCfg,
      affineMuxInvocationProgressionControllerLoopCfg,
      affineMuxInvocationProgressionController_initialCfg_eq_loop,
      affineMuxInvocationProgressionFamilySourceFrames_eq] using
      affineMuxInvocationProgressionController_segments_emit segments none []
  have hfinish := affineMuxInvocationProgressionController_finish
    (affineMuxInvocationProgressionControllerFamilyBuffer segments none)
    (affineMuxInvocationProgressionFamilyFrames segments).reverse
  let full := EvalsToInTime.trans
    (step affineMuxInvocationProgressionControllerRevProgram)
    (affineMuxInvocationProgressionControllerFamilySteps segments) 1
    _ _ _ hsegments hfinish
  convert full using 1
  omega

end CLRS.Chapter34.Turing.PolyBuilder

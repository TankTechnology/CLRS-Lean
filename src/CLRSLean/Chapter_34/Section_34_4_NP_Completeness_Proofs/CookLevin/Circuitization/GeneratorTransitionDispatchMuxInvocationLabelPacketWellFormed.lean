import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelSourceRows

/-!
# Well-formed label packets for dispatch-mux reassembly

The local reassembler zips one coordinate triple with one true-arm and one
false-arm value.  This file proves that every descriptor-derived label packet
has exactly that shape: the three rows have equal length, the reconstructed
frame list retains the full coordinate width, and the physical packet has
exactly four row boundaries.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- The three coordinate-indexed rows of a mux view have the same width. -/
def TransitionDispatchMuxInvocationView.RowAligned
    (view : TransitionDispatchMuxInvocationView) : Prop :=
  view.coordinates.length = view.whenTrue.length ∧
    view.coordinates.length = view.whenFalse.length

/-- `zipWith3` does not truncate an aligned mux view. -/
theorem TransitionDispatchMuxInvocationView.frames_length_of_rowAligned
    (view : TransitionDispatchMuxInvocationView)
    (haligned : view.RowAligned) :
    view.frames.length = view.coordinates.length := by
  rcases view with ⟨selector, coordinates, trueRows, falseRows⟩
  rcases haligned with ⟨htrue, hfalse⟩
  change (List.zipWith3 _ coordinates trueRows falseRows).length =
    coordinates.length
  induction coordinates generalizing trueRows falseRows with
  | nil =>
      have htrueNil : trueRows = [] := by simpa using htrue.symm
      have hfalseNil : falseRows = [] := by simpa using hfalse.symm
      subst trueRows
      subst falseRows
      rfl
  | cons coordinate coordinates ih =>
      cases trueRows with
      | nil => simp at htrue
      | cons whenTrue trueRows =>
          cases falseRows with
          | nil => simp at hfalse
          | cons whenFalse falseRows =>
              simp only [List.length_cons] at htrue hfalse
              have htrue' : coordinates.length = trueRows.length := by omega
              have hfalse' : coordinates.length = falseRows.length := by omega
              simp only [List.zipWith3, List.length_cons]
              rw [ih trueRows falseRows (by simpa using htrue')
                (by simpa using hfalse')]

/-- Every proof-carrying label artifact has aligned coordinate, true-arm, and
false-arm projections. -/
theorem TransitionDispatchLabelArtifact.muxInvocationView_rowAligned
    {tm : _root_.Turing.FinTM2}
    (artifact : TransitionDispatchLabelArtifact tm) :
    artifact.muxInvocationView.RowAligned := by
  simp [TransitionDispatchMuxInvocationView.RowAligned,
    TransitionDispatchLabelArtifact.muxInvocationView,
    TransitionDispatchLabelArtifact.muxFreshLayout,
    TransitionDispatchLabelArtifact.muxTrueInputValues,
    TransitionDispatchLabelArtifact.muxFalseInputValues]

/-- All views reconstructed from one verifier-produced descriptor seed satisfy
the local reassembler's row-alignment precondition. -/
theorem transitionDispatchMuxDescriptorInvocationViews_rowAligned
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed ∈ verifierTransitionRowSeeds W input) :
    ∀ view ∈ transitionDispatchMuxDescriptorInvocationViews W.machine.tm seed,
      view.RowAligned := by
  rw [transitionDispatchMuxDescriptorInvocationViews_eq_artifacts
    W input seed hseed]
  intro view hview
  rw [List.mem_map] at hview
  rcases hview with ⟨artifact, hartifact, rfl⟩
  exact artifact.muxInvocationView_rowAligned

private theorem encodeUnaryFrame_count_frameEnd (values : List Nat) :
    (encodeUnaryFrame values).count .frameEnd = 0 := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp only [encodeUnaryFrame, List.flatMap_cons] at ih ⊢
      rw [List.count_append, ih]
      simp only [encodeUnaryFrameBlock, List.count_append,
        List.count_singleton]
      have hticks :
          (List.replicate value .tick).count UnaryFrameSym.frameEnd = 0 := by
        induction value with
        | zero => rfl
        | succ value ihValue => simp [List.replicate_succ, ihValue]
      rw [hticks]
      decide

private theorem transitionDispatchMuxCoordinateRowFrames_count_frameEnd
    (coordinates : List (Nat × Nat × Nat)) :
    (transitionDispatchMuxCoordinateRowFrames coordinates).count
        .frameEnd = 0 := by
  unfold transitionDispatchMuxCoordinateRowFrames
  induction coordinates with
  | nil => rfl
  | cons coordinate coordinates ih =>
      simp only [List.flatMap_cons, List.count_append]
      rw [encodeUnaryFrame_count_frameEnd, ih]

/-- A label packet has exactly four physical row boundaries, independently of
the unary values and the mux width. -/
theorem TransitionDispatchMuxInvocationView.labelPacketFrames_frameEnd_count
    (view : TransitionDispatchMuxInvocationView) :
    view.labelPacketFrames.count .frameEnd = 4 := by
  simp [TransitionDispatchMuxInvocationView.labelPacketFrames,
    List.count_append, encodeUnaryFrame_count_frameEnd,
    transitionDispatchMuxCoordinateRowFrames_count_frameEnd]

end CLRS.Chapter34.Turing.CookLevin

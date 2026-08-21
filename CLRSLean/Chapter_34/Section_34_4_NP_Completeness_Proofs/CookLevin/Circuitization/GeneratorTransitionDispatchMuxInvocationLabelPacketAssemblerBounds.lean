import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelPacketAssemblerVerifier
import Mathlib.Tactic

/-!
# Polynomial bounds for dispatch-mux packet assembly

The exact execution formulas are bounded here by the literal size of the
prepared four-row packet stream.  In particular, replaying the selector once
per coordinate is charged quadratically to the explicit selector and row
width already present in that stream.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Literal size of one prepared four-row packet. -/
@[simp] theorem
    TransitionDispatchMuxInvocationView.preparedLabelPacketFrames_length
    (view : TransitionDispatchMuxInvocationView) :
    view.preparedLabelPacketFrames.length =
      view.selector +
        (transitionDispatchMuxCoordinateRowFrames
          view.coordinates).length +
        (encodeUnaryFrame view.whenTrue).length +
        (encodeUnaryFrame view.whenFalse).length + 5 := by
  unfold TransitionDispatchMuxInvocationView.preparedLabelPacketFrames
  simp only [List.length_append, List.length_cons, List.length_nil,
    List.length_reverse, encodeUnaryFrame_length]
  simp
  omega

/-- The coordinate zipper and its terminal case are quadratic in the literal
four-row packet measure. -/
theorem transitionDispatchMuxInvocationLabelPacketAssemblerRowsSteps_le
    (selector : Nat) (first : Bool)
    (coordinates : List (Nat × Nat × Nat))
    (whenTrue whenFalse : List Nat)
    (htrue : coordinates.length = whenTrue.length)
    (hfalse : coordinates.length = whenFalse.length) :
    transitionDispatchMuxInvocationLabelPacketAssemblerRowsSteps selector
        first
        (transitionDispatchMuxInvocationLabelPacketAssemblerFrames selector
          coordinates whenTrue whenFalse) ≤
      100 * (selector +
        (transitionDispatchMuxCoordinateRowFrames coordinates).length +
        (encodeUnaryFrame whenTrue).length +
        (encodeUnaryFrame whenFalse).length + 5) ^ 2 := by
  induction coordinates generalizing first whenTrue whenFalse with
  | nil =>
      have htrueNil : whenTrue = [] := by simpa using htrue.symm
      have hfalseNil : whenFalse = [] := by simpa using hfalse.symm
      subst whenTrue
      subst whenFalse
      cases first <;>
        simp [transitionDispatchMuxInvocationLabelPacketAssemblerFrames,
          TransitionDispatchMuxInvocationView.frames,
          transitionDispatchMuxInvocationLabelPacketAssemblerRowsSteps,
          transitionDispatchMuxInvocationLabelPacketAssemblerEmptySteps,
          transitionDispatchMuxInvocationLabelPacketAssemblerFinishSteps,
          transitionDispatchMuxCoordinateRowFrames, encodeUnaryFrame] <;>
        nlinarith
  | cons coordinate coordinates ih =>
      cases whenTrue with
      | nil => simp at htrue
      | cons whenTrue whenTrueTail =>
          cases whenFalse with
          | nil => simp at hfalse
          | cons whenFalse whenFalseTail =>
              have htrueTail : coordinates.length = whenTrueTail.length := by
                simpa using Nat.succ.inj htrue
              have hfalseTail : coordinates.length = whenFalseTail.length := by
                simpa using Nat.succ.inj hfalse
              let frame : AffineMuxFinPairFrame :=
                { whenTrue := whenTrue
                  whenFalse := whenFalse
                  selector := selector
                  selectorNot := coordinate.1
                  trueArm := coordinate.2.1
                  falseArm := coordinate.2.2 }
              let tailMeasure := selector +
                (transitionDispatchMuxCoordinateRowFrames
                  coordinates).length +
                (encodeUnaryFrame whenTrueTail).length +
                (encodeUnaryFrame whenFalseTail).length + 5
              let headMeasure := coordinate.1 + coordinate.2.1 +
                coordinate.2.2 + whenTrue + whenFalse + 5
              have htail := ih (first := false)
                (whenTrue := whenTrueTail) (whenFalse := whenFalseTail)
                htrueTail hfalseTail
              change
                transitionDispatchMuxInvocationLabelPacketAssemblerRowsSteps
                    selector false
                    (transitionDispatchMuxInvocationLabelPacketAssemblerFrames
                      selector coordinates whenTrueTail whenFalseTail) ≤
                  100 * tailMeasure ^ 2 at htail
              have htailPos : 1 ≤ tailMeasure := by
                simp [tailMeasure]
              have hheadPos : 1 ≤ headMeasure := by
                simp [headMeasure]
              have hselector : selector ≤ tailMeasure := by
                dsimp [tailMeasure]
                omega
              have hstep :
                  transitionDispatchMuxInvocationLabelPacketAssemblerCoordinateSteps
                      selector frame ≤
                    10 * headMeasure * tailMeasure := by
                dsimp [frame,
                  headMeasure, tailMeasure,
                  transitionDispatchMuxInvocationLabelPacketAssemblerCoordinateSteps]
                nlinarith
              have hmeasure :
                  selector +
                      (transitionDispatchMuxCoordinateRowFrames
                        (coordinate :: coordinates)).length +
                      (encodeUnaryFrame
                        (whenTrue :: whenTrueTail)).length +
                      (encodeUnaryFrame
                        (whenFalse :: whenFalseTail)).length + 5 =
                    tailMeasure + headMeasure := by
                simp [tailMeasure, headMeasure,
                  transitionDispatchMuxCoordinateRowFrames,
                  encodeUnaryFrame, encodeUnaryFrameBlock]
                omega
              rw [hmeasure]
              simp only [
                transitionDispatchMuxInvocationLabelPacketAssemblerFrames,
                TransitionDispatchMuxInvocationView.frames, List.zipWith3,
                transitionDispatchMuxInvocationLabelPacketAssemblerRowsSteps]
              change
                transitionDispatchMuxInvocationLabelPacketAssemblerCoordinateSteps
                    selector frame +
                    transitionDispatchMuxInvocationLabelPacketAssemblerRowsSteps
                      selector false
                      (transitionDispatchMuxInvocationLabelPacketAssemblerFrames
                        selector coordinates whenTrueTail whenFalseTail) ≤
                  100 * (tailMeasure + headMeasure) ^ 2
              nlinarith [Nat.zero_le tailMeasure, Nat.zero_le headMeasure]

/-- Loading plus assembling one aligned label is quadratic in its prepared
packet length. -/
theorem transitionDispatchMuxInvocationLabelPacketAssemblerLabelSteps_le
    (view : TransitionDispatchMuxInvocationView)
    (haligned : view.RowAligned) :
    transitionDispatchMuxInvocationLabelPacketAssemblerLoadSteps view +
        transitionDispatchMuxInvocationLabelPacketAssemblerRowsSteps
          view.selector true view.frames ≤
      110 * view.preparedLabelPacketFrames.length ^ 2 := by
  rcases haligned with ⟨htrue, hfalse⟩
  have hrows :=
    transitionDispatchMuxInvocationLabelPacketAssemblerRowsSteps_le
      view.selector true view.coordinates view.whenTrue view.whenFalse
      htrue hfalse
  have hframes :
      transitionDispatchMuxInvocationLabelPacketAssemblerFrames view.selector
          view.coordinates view.whenTrue view.whenFalse = view.frames := by
    rcases view
    rfl
  rw [hframes] at hrows
  rw [← view.preparedLabelPacketFrames_length] at hrows
  have hpacket : 5 ≤ view.preparedLabelPacketFrames.length := by
    simp
  have hload :
      transitionDispatchMuxInvocationLabelPacketAssemblerLoadSteps view ≤
        10 * view.preparedLabelPacketFrames.length ^ 2 := by
    unfold transitionDispatchMuxInvocationLabelPacketAssemblerLoadSteps
    have hcoord :
        (transitionDispatchMuxCoordinateRowFrames
          view.coordinates).length ≤
          view.preparedLabelPacketFrames.length := by
      rw [view.preparedLabelPacketFrames_length]
      omega
    have htrueLength :
        (encodeUnaryFrame view.whenTrue).length ≤
          view.preparedLabelPacketFrames.length := by
      rw [view.preparedLabelPacketFrames_length]
      omega
    have hselector :
        view.selector ≤ view.preparedLabelPacketFrames.length := by
      rw [view.preparedLabelPacketFrames_length]
      omega
    nlinarith
  nlinarith

/-- The whole aligned label family is quadratic in the concatenated prepared
packet stream. -/
theorem transitionDispatchMuxInvocationLabelPacketAssemblerFamilySteps_le
    (views : List TransitionDispatchMuxInvocationView)
    (haligned : ∀ view ∈ views, view.RowAligned) :
    transitionDispatchMuxInvocationLabelPacketAssemblerFamilySteps views ≤
      110 * (views.flatMap
        TransitionDispatchMuxInvocationView.preparedLabelPacketFrames
        ).length ^ 2 := by
  induction views with
  | nil => simp [transitionDispatchMuxInvocationLabelPacketAssemblerFamilySteps]
  | cons view views ih =>
      have hview : view.RowAligned := haligned view (by simp)
      have hviews : ∀ other ∈ views, other.RowAligned := by
        intro other hother
        exact haligned other (by simp [hother])
      have hone :=
        transitionDispatchMuxInvocationLabelPacketAssemblerLabelSteps_le
          view hview
      have hrest := ih hviews
      simp only [transitionDispatchMuxInvocationLabelPacketAssemblerFamilySteps]
        at hrest
      simp only [transitionDispatchMuxInvocationLabelPacketAssemblerFamilySteps,
        List.map_cons, List.sum_cons, List.flatMap_cons,
        List.length_append]
      nlinarith [Nat.zero_le view.preparedLabelPacketFrames.length,
        Nat.zero_le (views.flatMap
          TransitionDispatchMuxInvocationView.preparedLabelPacketFrames).length]

/-- On the real verifier stream, the complete assembler execution (including
halt) has a uniform quadratic bound in its literal prepared input length. -/
theorem verifierTransitionDispatchMuxInvocationLabelPacketAssemblerSteps_le
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationLabelPacketAssemblerSteps W input ≤
      110 *
        (verifierTransitionDispatchMuxInvocationDescriptorPreparedLabelPacketFrames
          W input).length ^ 2 + 2 := by
  let views := verifierTransitionDispatchMuxInvocationViews W input
  have haligned : ∀ view ∈ views, view.RowAligned := by
    simpa [views] using
      verifierTransitionDispatchMuxInvocationViews_rowAligned W input
  have hbound :=
    transitionDispatchMuxInvocationLabelPacketAssemblerFamilySteps_le
      views haligned
  have hprepared :=
    verifierTransitionDispatchMuxInvocationDescriptorPreparedLabelPacketFrames_eq
      W input
  change
    transitionDispatchMuxInvocationLabelPacketAssemblerFamilySteps
          (verifierTransitionDispatchMuxInvocationViews W input) + 2 ≤
      110 *
        (verifierTransitionDispatchMuxInvocationDescriptorPreparedLabelPacketFrames
          W input).length ^ 2 + 2
  apply Nat.add_le_add_right
  rw [hprepared]
  simpa [views, verifierTransitionDispatchMuxInvocationViews] using hbound

end CLRS.Chapter34.Turing.CookLevin

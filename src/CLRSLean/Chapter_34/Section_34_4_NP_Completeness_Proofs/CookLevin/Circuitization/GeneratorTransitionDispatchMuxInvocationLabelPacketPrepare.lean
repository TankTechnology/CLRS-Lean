import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelPacketReverse
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFramePeriodicRowContentReverse

/-!
# Concrete stack-ready dispatch-mux label packets

The local mux assembler retains the selector in a counter, loads the coordinate
and true-arm rows into its two work stacks, and then streams the false-arm row.
To make the stack tops line up with that forward false-arm stream, precisely the
coordinate and true-arm payloads must be reversed beforehand.

This file instantiates the generic periodic row-content TM2 with the four-row
mask `false / true / true / false` and proves the exact resulting verifier
packet bytes.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Reverse the coordinate and true-arm positions of every four-row packet. -/
def transitionDispatchMuxInvocationLabelPacketReverseAt
    (position : Fin 4) : Bool :=
  position.val = 1 || position.val = 2

/-- Stack-ready payload rows for one label. -/
def TransitionDispatchMuxInvocationView.preparedLabelPacketRows
    (view : TransitionDispatchMuxInvocationView) :
    List (List UnaryFrameSym) :=
  [encodeUnaryFrame [view.selector],
    (transitionDispatchMuxCoordinateRowFrames view.coordinates).reverse,
    (encodeUnaryFrame view.whenTrue).reverse,
    encodeUnaryFrame view.whenFalse]

/-- Exact bytes of one stack-ready label packet. -/
def TransitionDispatchMuxInvocationView.preparedLabelPacketFrames
    (view : TransitionDispatchMuxInvocationView) : List UnaryFrameSym :=
  encodeUnaryFrame [view.selector] ++ [.frameEnd] ++
    (transitionDispatchMuxCoordinateRowFrames view.coordinates).reverse ++
    [.frameEnd] ++ (encodeUnaryFrame view.whenTrue).reverse ++
    [.frameEnd] ++ encodeUnaryFrame view.whenFalse ++ [.frameEnd]

private theorem transitionDispatchMuxInvocationLabelPacketNext_four
    (position : Fin 4) :
    unaryFramePeriodicRowContentReverseNext 4 (by decide)
        (unaryFramePeriodicRowContentReverseNext 4 (by decide)
          (unaryFramePeriodicRowContentReverseNext 4 (by decide)
            (unaryFramePeriodicRowContentReverseNext 4 (by decide)
              position))) = position := by
  fin_cases position <;>
    rfl

/-- The four-period transform gives exactly the declared stack-ready rows and
returns to cycle position zero after every label. -/
theorem transitionDispatchMuxInvocationLabelPacket_prepare_rows
    (views : List TransitionDispatchMuxInvocationView) :
    unaryFramePeriodicRowContentReverseRowsFrom 4 (by decide)
        transitionDispatchMuxInvocationLabelPacketReverseAt ⟨0, by decide⟩
        (views.flatMap
          TransitionDispatchMuxInvocationView.labelPacketRows) =
      views.flatMap
        TransitionDispatchMuxInvocationView.preparedLabelPacketRows := by
  induction views with
  | nil => rfl
  | cons view views ih =>
      simp only [List.flatMap_cons,
        TransitionDispatchMuxInvocationView.labelPacketRows,
        TransitionDispatchMuxInvocationView.preparedLabelPacketRows]
      change encodeUnaryFrame [view.selector] ::
          (transitionDispatchMuxCoordinateRowFrames
            view.coordinates).reverse ::
          (encodeUnaryFrame view.whenTrue).reverse ::
          encodeUnaryFrame view.whenFalse ::
          unaryFramePeriodicRowContentReverseRowsFrom 4 (by decide)
            transitionDispatchMuxInvocationLabelPacketReverseAt
            ⟨0, by decide⟩
            (views.flatMap
              TransitionDispatchMuxInvocationView.labelPacketRows) = _
      simpa using ih

/-- Exact stack-ready output of the generic periodic row transform. -/
theorem encode_transitionDispatchMuxInvocationLabelPacketFamily_prepare
    (views : List TransitionDispatchMuxInvocationView) :
    encodeUnaryFramePeriodicRowContentReverse 4 (by decide)
        transitionDispatchMuxInvocationLabelPacketReverseAt
        (transitionDispatchMuxInvocationLabelPacketFamily views) =
      views.flatMap
        TransitionDispatchMuxInvocationView.preparedLabelPacketFrames := by
  unfold encodeUnaryFramePeriodicRowContentReverse
    transitionDispatchMuxInvocationLabelPacketFamily
  rw [transitionDispatchMuxInvocationLabelPacket_prepare_rows]
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro view hview
  simp [TransitionDispatchMuxInvocationView.preparedLabelPacketRows,
    TransitionDispatchMuxInvocationView.preparedLabelPacketFrames,
    List.append_assoc]

/-- The stack-ready physical stream for every verifier dispatch label. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorPreparedLabelPacketFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  encodeUnaryFramePeriodicRowContentReverse 4 (by decide)
    transitionDispatchMuxInvocationLabelPacketReverseAt
    (verifierTransitionDispatchMuxInvocationDescriptorLabelPacketFamily
      W input)

/-- Its bytes are a seed-major, label-major concatenation of the explicit
selector / reversed-coordinate / reversed-true / false layout. -/
theorem
    verifierTransitionDispatchMuxInvocationDescriptorPreparedLabelPacketFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorPreparedLabelPacketFrames
        W input =
      ((verifierTransitionRowSeeds W input).flatMap fun seed =>
        transitionDispatchMuxDescriptorInvocationViews
          W.machine.tm seed).flatMap
            TransitionDispatchMuxInvocationView.preparedLabelPacketFrames := by
  exact encode_transitionDispatchMuxInvocationLabelPacketFamily_prepare _

/-- The preprocessing relation itself is realized by one concrete fixed
polynomial-time TM2. -/
noncomputable def
    transitionDispatchMuxInvocationLabelPacketPrepare_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeUnaryFrameMarkedRowFamily id
      (encodeUnaryFramePeriodicRowContentReverse 4 (by decide)
        transitionDispatchMuxInvocationLabelPacketReverseAt) :=
  unaryFramePeriodicRowContentReverse_computableInPolyTime 4 (by decide)
    transitionDispatchMuxInvocationLabelPacketReverseAt

end CLRS.Chapter34.Turing.CookLevin

import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelPacketWellFormed
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowOrderReverse

/-!
# Concrete row-order reversal of dispatch-mux label packets

The final mux-source assembler writes through a prepend-only output stack, so
it consumes labels from last to first.  This file turns the exact four-row
label packet into a `UnaryFrameMarkedRowFamily`, proves that its marked encoding
is byte-for-byte the established packet contract, and instantiates the fixed
linear TM2 which reverses row order without reversing any row payload.

The resulting physical order is explicit: for each label, false arm, true arm,
coordinates, and selector; labels themselves also occur in reverse order.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- The four delimiter-free payload rows carried by one mux label packet. -/
def TransitionDispatchMuxInvocationView.labelPacketRows
    (view : TransitionDispatchMuxInvocationView) :
    List (List UnaryFrameSym) :=
  [encodeUnaryFrame [view.selector],
    transitionDispatchMuxCoordinateRowFrames view.coordinates,
    encodeUnaryFrame view.whenTrue,
    encodeUnaryFrame view.whenFalse]

private theorem labelPacket_encodeUnaryFrame_frameEnd_free
    (values : List Nat) :
    ∀ symbol ∈ encodeUnaryFrame values,
      symbol ≠ UnaryFrameSym.frameEnd := by
  intro symbol hsymbol
  rw [encodeUnaryFrame, List.mem_flatMap] at hsymbol
  rcases hsymbol with ⟨value, _, hblock⟩
  simp [encodeUnaryFrameBlock] at hblock
  rcases hblock with ⟨_, rfl⟩ | rfl <;> simp

private theorem labelPacket_coordinateRow_frameEnd_free
    (coordinates : List (Nat × Nat × Nat)) :
    ∀ symbol ∈ transitionDispatchMuxCoordinateRowFrames coordinates,
      symbol ≠ UnaryFrameSym.frameEnd := by
  intro symbol hsymbol
  rw [transitionDispatchMuxCoordinateRowFrames,
    List.mem_flatMap] at hsymbol
  rcases hsymbol with ⟨coordinate, _, hcoordinate⟩
  exact labelPacket_encodeUnaryFrame_frameEnd_free _ symbol hcoordinate

/-- A list of mux views regarded as one delimiter-bearing row family. -/
def transitionDispatchMuxInvocationLabelPacketFamily
    (views : List TransitionDispatchMuxInvocationView) :
    UnaryFrameMarkedRowFamily where
  rows := views.flatMap
    TransitionDispatchMuxInvocationView.labelPacketRows
  frameEnd_free := by
    intro row hrow symbol hsymbol
    rw [List.mem_flatMap] at hrow
    rcases hrow with ⟨view, _, hrow⟩
    simp only [TransitionDispatchMuxInvocationView.labelPacketRows,
      List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with hrow | hrow | hrow | hrow
    · subst row
      exact labelPacket_encodeUnaryFrame_frameEnd_free _ symbol hsymbol
    · subst row
      exact labelPacket_coordinateRow_frameEnd_free _ symbol hsymbol
    · subst row
      exact labelPacket_encodeUnaryFrame_frameEnd_free _ symbol hsymbol
    · subst row
      exact labelPacket_encodeUnaryFrame_frameEnd_free _ symbol hsymbol

/-- Encoding the typed row family recovers the exact four-row packet bytes. -/
theorem encode_transitionDispatchMuxInvocationLabelPacketFamily
    (views : List TransitionDispatchMuxInvocationView) :
    encodeUnaryFrameMarkedRowFamily
        (transitionDispatchMuxInvocationLabelPacketFamily views) =
      views.flatMap
        TransitionDispatchMuxInvocationView.labelPacketFrames := by
  unfold encodeUnaryFrameMarkedRowFamily
    transitionDispatchMuxInvocationLabelPacketFamily
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro view hview
  simp [TransitionDispatchMuxInvocationView.labelPacketRows,
    TransitionDispatchMuxInvocationView.labelPacketFrames,
    List.append_assoc]

/-- Exact bytes of one label after row-order reversal. -/
def TransitionDispatchMuxInvocationView.reversedLabelPacketFrames
    (view : TransitionDispatchMuxInvocationView) : List UnaryFrameSym :=
  encodeUnaryFrame view.whenFalse ++ [.frameEnd] ++
    encodeUnaryFrame view.whenTrue ++ [.frameEnd] ++
    transitionDispatchMuxCoordinateRowFrames view.coordinates ++
    [.frameEnd] ++ encodeUnaryFrame [view.selector] ++ [.frameEnd]

/-- The generic row-order output has the advertised label-major layout. -/
theorem encode_transitionDispatchMuxInvocationLabelPacketFamily_reverse
    (views : List TransitionDispatchMuxInvocationView) :
    encodeUnaryFrameMarkedRowOrderReverse
        (transitionDispatchMuxInvocationLabelPacketFamily views) =
      views.reverse.flatMap
        TransitionDispatchMuxInvocationView.reversedLabelPacketFrames := by
  unfold encodeUnaryFrameMarkedRowOrderReverse
    transitionDispatchMuxInvocationLabelPacketFamily
  rw [show
      (views.flatMap
        TransitionDispatchMuxInvocationView.labelPacketRows).reverse =
        views.reverse.flatMap
          (List.reverse ∘
            TransitionDispatchMuxInvocationView.labelPacketRows) by
    simp [List.reverse_flatMap]]
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro view hview
  simp [TransitionDispatchMuxInvocationView.labelPacketRows,
    TransitionDispatchMuxInvocationView.reversedLabelPacketFrames,
    List.append_assoc]

/-- All verifier dispatch views, flattened in their canonical seed-major
order, as one typed marked-row family. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFrameMarkedRowFamily :=
  transitionDispatchMuxInvocationLabelPacketFamily
    ((verifierTransitionRowSeeds W input).flatMap fun seed =>
      transitionDispatchMuxDescriptorInvocationViews W.machine.tm seed)

/-- The typed verifier family is exactly the previously established physical
label-packet input contract. -/
theorem
    encode_verifierTransitionDispatchMuxInvocationDescriptorLabelPacketFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeUnaryFrameMarkedRowFamily
        (verifierTransitionDispatchMuxInvocationDescriptorLabelPacketFamily
          W input) =
      verifierTransitionDispatchMuxInvocationDescriptorLabelPacketFrames
        W input := by
  rw [verifierTransitionDispatchMuxInvocationDescriptorLabelPacketFamily,
    encode_transitionDispatchMuxInvocationLabelPacketFamily]
  unfold
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketFrames
  exact List.flatMap_assoc

/-- Concrete exact execution of the fixed row-order TM2 on the real verifier
label-packet contract. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketReverse_run
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    EvalsToInTime (step unaryFrameMarkedRowOrderReverseProgram)
      (initialCfg unaryFrameMarkedRowOrderReverseProgram
        (verifierTransitionDispatchMuxInvocationDescriptorLabelPacketFrames
          W input))
      (some (haltCfg unaryFrameMarkedRowOrderReverseProgram
        (encodeUnaryFrameMarkedRowOrderReverse
          (verifierTransitionDispatchMuxInvocationDescriptorLabelPacketFamily
            W input))))
      (unaryFrameMarkedRowOrderReverseSteps
        (verifierTransitionDispatchMuxInvocationDescriptorLabelPacketFamily
          W input)) := by
  rw [←
    encode_verifierTransitionDispatchMuxInvocationDescriptorLabelPacketFamily]
  exact unaryFrameMarkedRowOrderReverse_run _

/-- The output of that execution is the fully explicit reverse label layout. -/
theorem
    encode_verifierTransitionDispatchMuxInvocationDescriptorLabelPacketFamily_reverse
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeUnaryFrameMarkedRowOrderReverse
        (verifierTransitionDispatchMuxInvocationDescriptorLabelPacketFamily
          W input) =
      ((verifierTransitionRowSeeds W input).flatMap fun seed =>
        transitionDispatchMuxDescriptorInvocationViews
          W.machine.tm seed).reverse.flatMap
            TransitionDispatchMuxInvocationView.reversedLabelPacketFrames := by
  exact encode_transitionDispatchMuxInvocationLabelPacketFamily_reverse _

end CLRS.Chapter34.Turing.CookLevin

import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorPacketNormalize
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameDuplicatedRowRoute
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameAlternatingSuffixDrop

/-!
# Routing unified dispatch-mux descriptors into two physical halves

The unified descriptor packet is duplicated before interpretation.  This
module gives the two copies distinct physical roles without using a semantic
projection: the first copy loses its selector/coordinate prefix and the
second copy is retained, after which an alternating fixed suffix deletion
removes the arm descriptors from the second copy.

For every transition seed the resulting standard rows are therefore

* the true/false arm descriptor row; and
* the selector/fresh-coordinate descriptor row.

Both routing passes are concrete polynomial-time TM2 computations composed
continuously with the raw verifier-input descriptor source.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Verifier-fixed forms for selectors and fresh mux coordinates. -/
def transitionDispatchMuxInvocationDescriptorHeadForms
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  transitionDispatchSelectorForms tm ++
    transitionDispatchMuxDescriptorForms tm

/-- Runtime selector and fresh-coordinate descriptor values. -/
def transitionDispatchMuxInvocationDescriptorHeadValues
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) : List Nat :=
  transitionDispatchSelectors tm seed ++
    transitionDispatchProgressionDescriptorValues
      (transitionDispatchMuxAffineProgressions tm seed)

/-- Verifier-fixed forms for the true and false mux arms. -/
noncomputable def transitionDispatchMuxInvocationDescriptorTailForms
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  transitionDispatchTrueArmSpanDescriptorForms tm ++
    transitionDispatchFalseArmDescriptorForms tm

/-- Runtime true- and false-arm descriptor values. -/
noncomputable def transitionDispatchMuxInvocationDescriptorTailValues
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) : List Nat :=
  transitionDispatchTrueArmSpanDescriptorValues tm seed ++
    transitionDispatchProgressionDescriptorValues
      (transitionDispatchFalseArmProgressions tm seed)

/-- The unified packet is exactly the head section followed by the tail
section. -/
theorem transitionDispatchMuxInvocationDescriptorValues_eq_head_append_tail
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    transitionDispatchMuxInvocationDescriptorValues tm seed =
      transitionDispatchMuxInvocationDescriptorHeadValues tm seed ++
        transitionDispatchMuxInvocationDescriptorTailValues tm seed := by
  simp [transitionDispatchMuxInvocationDescriptorValues,
    transitionDispatchMuxInvocationDescriptorHeadValues,
    transitionDispatchMuxInvocationDescriptorTailValues,
    List.append_assoc]

/-- Evaluating the head form table recovers the runtime head values. -/
theorem transitionDispatchMuxInvocationDescriptorHeadForms_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    affineUnaryTripleMap
        (transitionDispatchMuxInvocationDescriptorHeadForms tm)
        (transitionTailAffineSeed seed) =
      transitionDispatchMuxInvocationDescriptorHeadValues tm seed := by
  unfold transitionDispatchMuxInvocationDescriptorHeadForms
    transitionDispatchMuxInvocationDescriptorHeadValues
    transitionDispatchProgressionDescriptorValues
  rw [show affineUnaryTripleMap
      (transitionDispatchSelectorForms tm ++
        transitionDispatchMuxDescriptorForms tm)
      (transitionTailAffineSeed seed) =
    affineUnaryTripleMap (transitionDispatchSelectorForms tm)
        (transitionTailAffineSeed seed) ++
      affineUnaryTripleMap (transitionDispatchMuxDescriptorForms tm)
        (transitionTailAffineSeed seed) by
      simp [affineUnaryTripleMap, List.map_append]]
  rw [transitionDispatchSelectorForms_value,
    transitionDispatchMuxDescriptorForms_value]

/-- Evaluating the tail form table recovers the runtime tail values. -/
theorem transitionDispatchMuxInvocationDescriptorTailForms_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    affineUnaryTripleMap
        (transitionDispatchMuxInvocationDescriptorTailForms tm)
        (transitionTailAffineSeed seed) =
      transitionDispatchMuxInvocationDescriptorTailValues tm seed := by
  unfold transitionDispatchMuxInvocationDescriptorTailForms
    transitionDispatchMuxInvocationDescriptorTailValues
    transitionDispatchProgressionDescriptorValues
  rw [show affineUnaryTripleMap
      (transitionDispatchTrueArmSpanDescriptorForms tm ++
        transitionDispatchFalseArmDescriptorForms tm)
      (transitionTailAffineSeed seed) =
    affineUnaryTripleMap (transitionDispatchTrueArmSpanDescriptorForms tm)
        (transitionTailAffineSeed seed) ++
      affineUnaryTripleMap (transitionDispatchFalseArmDescriptorForms tm)
        (transitionTailAffineSeed seed) by
      simp [affineUnaryTripleMap, List.map_append]]
  rw [transitionDispatchTrueArmSpanDescriptorForms_value,
    transitionDispatchFalseArmDescriptorForms_value]

/-- The head row has a verifier-fixed width. -/
theorem transitionDispatchMuxInvocationDescriptorHeadValues_length
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (transitionDispatchMuxInvocationDescriptorHeadValues tm seed).length =
      (transitionDispatchMuxInvocationDescriptorHeadForms tm).length := by
  have h := congrArg List.length
    (transitionDispatchMuxInvocationDescriptorHeadForms_value tm seed)
  simpa [affineUnaryTripleMap] using h.symm

/-- The tail row has a verifier-fixed width. -/
theorem transitionDispatchMuxInvocationDescriptorTailValues_length
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (transitionDispatchMuxInvocationDescriptorTailValues tm seed).length =
      (transitionDispatchMuxInvocationDescriptorTailForms tm).length := by
  have h := congrArg List.length
    (transitionDispatchMuxInvocationDescriptorTailForms_value tm seed)
  simpa [affineUnaryTripleMap] using h.symm

/-- At least one program-label selector occurs in every head row. -/
theorem transitionDispatchMuxInvocationDescriptorHeadForms_length_pos
    (tm : _root_.Turing.FinTM2) :
    0 < (transitionDispatchMuxInvocationDescriptorHeadForms tm).length := by
  have hlabels : 0 < (programLabels tm).length :=
    List.length_pos_of_ne_nil (programLabels_nonempty tm)
  simp only [transitionDispatchMuxInvocationDescriptorHeadForms,
    List.length_append, transitionDispatchSelectorForms, List.length_map]
  omega

private theorem encodeUnaryFrame_append_values
    (left right : List Nat) :
    encodeUnaryFrame (left ++ right) =
      encodeUnaryFrame left ++ encodeUnaryFrame right := by
  simp [encodeUnaryFrame]

private theorem encodeUnaryFrame_frameEnd_free (values : List Nat) :
    ∀ symbol ∈ encodeUnaryFrame values,
      symbol ≠ UnaryFrameSym.frameEnd := by
  intro symbol hsymbol
  simp only [encodeUnaryFrame, List.mem_flatMap] at hsymbol
  rcases hsymbol with ⟨value, hvalue, hsymbol⟩
  simp [encodeUnaryFrameBlock] at hsymbol
  rcases hsymbol with (⟨hvalue, rfl⟩ | rfl) <;> simp

/-- Typed input family for the first physical router. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorHalfRouteFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFrameDuplicatedRowRouteFamily
      (transitionDispatchMuxInvocationDescriptorHeadForms W.machine.tm).length :=
  { rows := (verifierTransitionRowSeeds W input).map fun seed =>
      (transitionDispatchMuxInvocationDescriptorHeadValues W.machine.tm seed,
        encodeUnaryFrame
          (transitionDispatchMuxInvocationDescriptorTailValues
            W.machine.tm seed))
    prefix_lengths := by
      intro row hrow
      rw [List.mem_map] at hrow
      rcases hrow with ⟨seed, hseed, rfl⟩
      exact transitionDispatchMuxInvocationDescriptorHeadValues_length
        W.machine.tm seed
    payload_frameEnd_free := by
      intro row hrow symbol hsymbol
      rw [List.mem_map] at hrow
      rcases hrow with ⟨seed, hseed, rfl⟩
      exact encodeUnaryFrame_frameEnd_free _ symbol hsymbol }

/-- The typed router input is byte-for-byte the normalized duplicated packet
stream. -/
theorem
    verifierTransitionDispatchMuxInvocationDescriptorHalfRouteFamily_encoding_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeUnaryFrameDuplicatedRowRouteInput
        (verifierTransitionDispatchMuxInvocationDescriptorHalfRouteFamily
          W input) =
      verifierTransitionDispatchMuxInvocationDescriptorStandardDuplicatedPacketFrames
        W input := by
  rw [
    verifierTransitionDispatchMuxInvocationDescriptorStandardDuplicatedPacketFrames_eq]
  unfold encodeUnaryFrameDuplicatedRowRouteInput
    verifierTransitionDispatchMuxInvocationDescriptorHalfRouteFamily
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro seed hseed
  rw [transitionDispatchMuxInvocationDescriptorValues_eq_head_append_tail]
  rw [encodeUnaryFrame_append_values]
  simp [List.append_assoc]

/-- Physical output after routing the first copy to the arm tail while
retaining the second complete copy. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorRoutedPacketFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFrameDuplicatedRowRoute
    (transitionDispatchMuxInvocationDescriptorHeadForms W.machine.tm).length
    (verifierTransitionDispatchMuxInvocationDescriptorStandardDuplicatedPacketFrames
      W input)

/-- Exact seed-major shape after the first routing pass. -/
theorem
    verifierTransitionDispatchMuxInvocationDescriptorRoutedPacketFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorRoutedPacketFrames
        W input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        encodeUnaryFrame
            (transitionDispatchMuxInvocationDescriptorTailValues
              W.machine.tm seed) ++
          [.frameEnd] ++
          encodeUnaryFrame
            (transitionDispatchMuxInvocationDescriptorHeadValues
              W.machine.tm seed) ++
          encodeUnaryFrame
            (transitionDispatchMuxInvocationDescriptorTailValues
              W.machine.tm seed) ++
          [.frameEnd] := by
  unfold
    verifierTransitionDispatchMuxInvocationDescriptorRoutedPacketFrames
  rw [←
    verifierTransitionDispatchMuxInvocationDescriptorHalfRouteFamily_encoding_eq]
  rw [rewriteUnaryFrameDuplicatedRowRoute_family _
    (transitionDispatchMuxInvocationDescriptorHeadForms_length_pos
      W.machine.tm)]
  unfold encodeUnaryFrameDuplicatedRowRouteOutput
    verifierTransitionDispatchMuxInvocationDescriptorHalfRouteFamily
  rw [List.flatMap_map]

/-- The normalized source and first router form one continuous polynomial-time
TM2 pipeline from the verifier word. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorRoutedPacketFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationDescriptorRoutedPacketFrames
        W) := by
  let source :=
    verifierTransitionDispatchMuxInvocationDescriptorStandardDuplicatedPacketFrames_computableInPolyTime
      W
  let routed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch source
      (unaryFrameDuplicatedRowRoute_computableInPolyTime
        (transitionDispatchMuxInvocationDescriptorHeadForms
          W.machine.tm).length)
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List Γ =>
      rewriteUnaryFrameDuplicatedRowRoute
        (transitionDispatchMuxInvocationDescriptorHeadForms
          W.machine.tm).length
        (verifierTransitionDispatchMuxInvocationDescriptorStandardDuplicatedPacketFrames
          W input))
  simpa [Function.comp_def] using Classical.choice routed

/-- Semantic row pairs accepted by the alternating suffix router. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorHalfRoutePairs
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List (List Nat × List Nat) :=
  (verifierTransitionRowSeeds W input).map fun seed =>
    (transitionDispatchMuxInvocationDescriptorTailValues W.machine.tm seed,
      transitionDispatchMuxInvocationDescriptorHeadValues W.machine.tm seed ++
        transitionDispatchMuxInvocationDescriptorTailValues W.machine.tm seed)

/-- The first routed stream is exactly the input expected by alternating
suffix deletion. -/
theorem
    verifierTransitionDispatchMuxInvocationDescriptorHalfRoutePairs_encoding_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeUnaryFrameAlternatingSuffixDropInput
        (verifierTransitionDispatchMuxInvocationDescriptorHalfRoutePairs
          W input) =
      verifierTransitionDispatchMuxInvocationDescriptorRoutedPacketFrames
        W input := by
  rw [
    verifierTransitionDispatchMuxInvocationDescriptorRoutedPacketFrames_eq]
  unfold encodeUnaryFrameAlternatingSuffixDropInput
    verifierTransitionDispatchMuxInvocationDescriptorHalfRoutePairs
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro seed hseed
  rw [encodeUnaryFrame_append_values]
  simp [List.append_assoc]

/-- Final two-row physical view: arm descriptors first, followed by selector
and coordinate descriptors. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorHalfRows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFrameAlternatingSuffixDrop 0
    (transitionDispatchMuxInvocationDescriptorTailForms W.machine.tm).length
    (verifierTransitionDispatchMuxInvocationDescriptorRoutedPacketFrames
      W input)

/-- Every transition seed now owns two independent standard marked rows with
the exact intended descriptor halves. -/
theorem verifierTransitionDispatchMuxInvocationDescriptorHalfRows_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorHalfRows W input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        encodeUnaryFrame
            (transitionDispatchMuxInvocationDescriptorTailValues
              W.machine.tm seed) ++
          [.frameEnd] ++
          encodeUnaryFrame
            (transitionDispatchMuxInvocationDescriptorHeadValues
              W.machine.tm seed) ++
          [.frameEnd] := by
  unfold verifierTransitionDispatchMuxInvocationDescriptorHalfRows
  rw [←
    verifierTransitionDispatchMuxInvocationDescriptorHalfRoutePairs_encoding_eq]
  rw [rewriteUnaryFrameAlternatingSuffixDrop_pairs]
  unfold encodeUnaryFrameAlternatingSuffixDropOutput
    verifierTransitionDispatchMuxInvocationDescriptorHalfRoutePairs
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro seed hseed
  rw [List.rdrop_zero]
  have htail :=
    transitionDispatchMuxInvocationDescriptorTailValues_length
      W.machine.tm seed
  rw [← htail, List.rdrop_append_length]

/-- The complete packetization, duplication, normalization, and two-stage
routing pipeline is computed by one polynomial-time TM2 from the verifier
word. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorHalfRows_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationDescriptorHalfRows W) := by
  let source :=
    verifierTransitionDispatchMuxInvocationDescriptorRoutedPacketFrames_computableInPolyTime
      W
  let routed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch source
      (unaryFrameAlternatingSuffixDrop_computableInPolyTime 0
        (transitionDispatchMuxInvocationDescriptorTailForms
          W.machine.tm).length)
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List Γ =>
      rewriteUnaryFrameAlternatingSuffixDrop 0
        (transitionDispatchMuxInvocationDescriptorTailForms
          W.machine.tm).length
        (verifierTransitionDispatchMuxInvocationDescriptorRoutedPacketFrames
          W input))
  simpa [Function.comp_def] using Classical.choice routed

end CLRS.Chapter34.Turing.CookLevin

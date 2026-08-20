import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorTrueFrames
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameFixedWidthPacketNormalize
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameFixedPrefixDrop

/-!
# Recovering true-arm progression descriptors from the unified mux source

The true-arm channel of the unified dispatch source consists of adjacent
eight-field blocks.  Each block stores one verifier-fixed prefix-drop amount
followed by the ordinary seven fields of an affine triple progression.  This
module uses only fixed streaming controllers to mark those blocks, restore
canonical row boundaries, delete the first field of every row, and remove the
outer markers again.

The final byte stream is therefore the canonical input of the generic affine
progression executor.  No runtime multiplication or oracle-side parser is
introduced.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- The physical eight-field blocks obtained by pairing a fixed drop table
with its corresponding affine segment table. -/
def transitionDispatchTrueArmSpanDescriptorBlocksFrom
    (seed : TransitionRowSeed) :
    List Nat → List TransitionWidenedFallbackSegment → List (List Nat)
  | amount :: amounts, segment :: segments =>
      transitionDispatchTrueArmSpanDescriptorBlockValues amount
          (transitionWidenedFallbackSegmentProgression seed segment) ::
        transitionDispatchTrueArmSpanDescriptorBlocksFrom seed amounts segments
  | _, _ => []

/-- The unmodified progressions stored after the leading drop amount in each
physical block. -/
def transitionDispatchTrueArmSpanRawProgressionsFrom
    (seed : TransitionRowSeed) :
    List Nat → List TransitionWidenedFallbackSegment →
      List AffineUnaryTripleProgression
  | _ :: amounts, segment :: segments =>
      transitionWidenedFallbackSegmentProgression seed segment ::
        transitionDispatchTrueArmSpanRawProgressionsFrom seed amounts segments
  | _, _ => []

private theorem transitionDispatchTrueArmSpanDescriptorBlocksFrom_flatten
    (seed : TransitionRowSeed) :
    ∀ (amounts : List Nat)
      (segments : List TransitionWidenedFallbackSegment),
      (transitionDispatchTrueArmSpanDescriptorBlocksFrom seed amounts
          segments).flatten =
        transitionDispatchTrueArmSpanDescriptorValuesFrom seed amounts
          segments := by
  intro amounts
  induction amounts with
  | nil =>
      intro segments
      rfl
  | cons amount amounts ih =>
      intro segments
      cases segments with
      | nil => rfl
      | cons segment segments =>
          simp only [transitionDispatchTrueArmSpanDescriptorBlocksFrom,
            transitionDispatchTrueArmSpanDescriptorValuesFrom,
            List.flatten_cons]
          rw [ih]

private theorem transitionDispatchTrueArmSpanDescriptorBlocksFrom_length
    (seed : TransitionRowSeed) :
    ∀ (amounts : List Nat)
      (segments : List TransitionWidenedFallbackSegment)
      (block : List Nat),
      block ∈ transitionDispatchTrueArmSpanDescriptorBlocksFrom seed amounts
        segments →
      block.length = 8 := by
  intro amounts
  induction amounts with
  | nil =>
      intro segments block hblock
      simp [transitionDispatchTrueArmSpanDescriptorBlocksFrom] at hblock
  | cons amount amounts ih =>
      intro segments block hblock
      cases segments with
      | nil =>
          simp [transitionDispatchTrueArmSpanDescriptorBlocksFrom] at hblock
      | cons segment segments =>
          simp only [transitionDispatchTrueArmSpanDescriptorBlocksFrom,
            List.mem_cons] at hblock
          rcases hblock with rfl | hblock
          · rfl
          · exact ih segments block hblock

private theorem transitionDispatchTrueArmSpanDescriptorBlocksFrom_drop
    (seed : TransitionRowSeed) :
    ∀ (amounts : List Nat)
      (segments : List TransitionWidenedFallbackSegment),
      (transitionDispatchTrueArmSpanDescriptorBlocksFrom seed amounts
          segments).map (List.drop 1) =
        (transitionDispatchTrueArmSpanRawProgressionsFrom seed amounts
          segments).map affineUnaryTripleProgressionFields := by
  intro amounts
  induction amounts with
  | nil =>
      intro segments
      rfl
  | cons amount amounts ih =>
      intro segments
      cases segments with
      | nil => rfl
      | cons segment segments =>
          simp only [transitionDispatchTrueArmSpanDescriptorBlocksFrom,
            transitionDispatchTrueArmSpanRawProgressionsFrom, List.map_cons]
          rw [ih]
          rfl

private theorem encodeUnaryFrame_flatten (rows : List (List Nat)) :
    encodeUnaryFrame rows.flatten = rows.flatMap encodeUnaryFrame := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp only [List.flatten_cons, List.flatMap_cons]
      rw [show encodeUnaryFrame (row ++ rows.flatten) =
          encodeUnaryFrame row ++ encodeUnaryFrame rows.flatten by
        simp [encodeUnaryFrame, List.flatMap_append]]
      rw [ih]

/-- All eight-field blocks of one transition seed, in fixed program-label
order. -/
noncomputable def transitionDispatchTrueArmSpanDescriptorBlocks
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List (List Nat) :=
  (transitionDispatchTrueArmNormalizedLayouts tm).flatMap fun layout =>
    transitionDispatchTrueArmSpanDescriptorBlocksFrom seed
      (layout.affineSpanDropAmounts tm) (layout.affineSpanSegments tm)

/-- All raw affine progressions stored by the true-arm blocks of one seed. -/
noncomputable def transitionDispatchTrueArmSpanRawProgressions
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List AffineUnaryTripleProgression :=
  (transitionDispatchTrueArmNormalizedLayouts tm).flatMap fun layout =>
    transitionDispatchTrueArmSpanRawProgressionsFrom seed
      (layout.affineSpanDropAmounts tm) (layout.affineSpanSegments tm)

/-- Flattening the physical block view recovers the value view already
selected from the unified source. -/
theorem transitionDispatchTrueArmSpanDescriptorBlocks_flatten
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (transitionDispatchTrueArmSpanDescriptorBlocks tm seed).flatten =
      transitionDispatchTrueArmSpanDescriptorValues tm seed := by
  unfold transitionDispatchTrueArmSpanDescriptorBlocks
    transitionDispatchTrueArmSpanDescriptorValues
  induction transitionDispatchTrueArmNormalizedLayouts tm with
  | nil => rfl
  | cons layout layouts ih =>
      simp only [List.flatMap_cons, List.flatten_append]
      rw [transitionDispatchTrueArmSpanDescriptorBlocksFrom_flatten, ih]
      rfl

/-- Every physical true-arm descriptor block has the fixed width consumed by
the packet marker. -/
theorem transitionDispatchTrueArmSpanDescriptorBlocks_length
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (block : List Nat)
    (hblock : block ∈ transitionDispatchTrueArmSpanDescriptorBlocks tm seed) :
    block.length = 8 := by
  unfold transitionDispatchTrueArmSpanDescriptorBlocks at hblock
  rw [List.mem_flatMap] at hblock
  rcases hblock with ⟨layout, hlayout, hblock⟩
  exact transitionDispatchTrueArmSpanDescriptorBlocksFrom_length seed
    (layout.affineSpanDropAmounts tm) (layout.affineSpanSegments tm) block
    hblock

/-- Deleting the leading amount from each physical block leaves precisely the
seven ordinary fields of the stored raw progression family. -/
theorem transitionDispatchTrueArmSpanDescriptorBlocks_drop
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (transitionDispatchTrueArmSpanDescriptorBlocks tm seed).map
        (List.drop 1) =
      (transitionDispatchTrueArmSpanRawProgressions tm seed).map
        affineUnaryTripleProgressionFields := by
  unfold transitionDispatchTrueArmSpanDescriptorBlocks
    transitionDispatchTrueArmSpanRawProgressions
  rw [List.map_flatMap, List.map_flatMap]
  apply List.flatMap_congr
  intro layout hlayout
  exact transitionDispatchTrueArmSpanDescriptorBlocksFrom_drop seed
    (layout.affineSpanDropAmounts tm) (layout.affineSpanSegments tm)

/-- Complete physical block family over all transition rows. -/
noncomputable def verifierTransitionDispatchMuxInvocationDescriptorTrueBlocks
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List (List Nat) :=
  (verifierTransitionRowSeeds W input).flatMap
    (transitionDispatchTrueArmSpanDescriptorBlocks W.machine.tm)

/-- Raw true-arm progression family over all transition rows. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorTrueRawProgressions
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List AffineUnaryTripleProgression :=
  (verifierTransitionRowSeeds W input).flatMap
    (transitionDispatchTrueArmSpanRawProgressions W.machine.tm)

/-- Mark every adjacent eight-field block with a physical packet boundary. -/
noncomputable def verifierTransitionDispatchMuxInvocationDescriptorTruePacketFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFrameFixedWidthPackets 8 (by omega)
    (verifierTransitionDispatchMuxInvocationDescriptorTrueFrames W input)

/-- Exact compact-packet semantics of the fixed-width marker. -/
theorem verifierTransitionDispatchMuxInvocationDescriptorTruePacketFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorTruePacketFrames W input =
      (verifierTransitionDispatchMuxInvocationDescriptorTrueBlocks W input).flatMap
        encodeUnaryFrameFixedWidthPacket := by
  unfold verifierTransitionDispatchMuxInvocationDescriptorTruePacketFrames
  rw [verifierTransitionDispatchMuxInvocationDescriptorTrueFrames_eq_values]
  have hvalues :
      ((verifierTransitionRowSeeds W input).flatMap
          (transitionDispatchTrueArmSpanDescriptorValues W.machine.tm)) =
        (verifierTransitionDispatchMuxInvocationDescriptorTrueBlocks W input).flatten := by
    unfold verifierTransitionDispatchMuxInvocationDescriptorTrueBlocks
    induction verifierTransitionRowSeeds W input with
    | nil => rfl
    | cons seed seeds ih =>
        simp only [List.flatMap_cons, List.flatten_append]
        rw [transitionDispatchTrueArmSpanDescriptorBlocks_flatten, ih]
  rw [hvalues]
  rw [encodeUnaryFrame_flatten]
  apply rewriteUnaryFrameFixedWidthPackets_encode
  intro block hblock
  unfold verifierTransitionDispatchMuxInvocationDescriptorTrueBlocks at hblock
  rw [List.mem_flatMap] at hblock
  rcases hblock with ⟨seed, hseed, hblock⟩
  exact transitionDispatchTrueArmSpanDescriptorBlocks_length
    W.machine.tm seed block hblock

/-- Restore canonical row separators before applying row-oriented controllers.
-/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorTrueNormalizedPacketFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  restoreUnaryFrameFixedWidthPacketSeparators
    (verifierTransitionDispatchMuxInvocationDescriptorTruePacketFrames W input)

/-- Delete the first unary value (the fixed prefix-drop amount) from every
normalized eight-field packet. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorTrueDroppedPacketFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFrameFixedPrefixDrop 1
    (verifierTransitionDispatchMuxInvocationDescriptorTrueNormalizedPacketFrames
      W input)

/-- After normalization and deletion, every physical row contains exactly the
seven ordinary progression fields and retains its outer marker. -/
theorem
    verifierTransitionDispatchMuxInvocationDescriptorTrueDroppedPacketFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorTrueDroppedPacketFrames
        W input =
      (verifierTransitionDispatchMuxInvocationDescriptorTrueBlocks W input).flatMap
        fun block => encodeUnaryFrame (block.drop 1) ++ [.frameEnd] := by
  unfold verifierTransitionDispatchMuxInvocationDescriptorTrueDroppedPacketFrames
    verifierTransitionDispatchMuxInvocationDescriptorTrueNormalizedPacketFrames
  rw [verifierTransitionDispatchMuxInvocationDescriptorTruePacketFrames_eq]
  rw [restoreUnaryFrameFixedWidthPacketSeparators_family]
  · exact rewriteUnaryFrameFixedPrefixDrop_rows 1
      (verifierTransitionDispatchMuxInvocationDescriptorTrueBlocks W input)
  · intro block hblock hnil
    have hlength := transitionDispatchTrueArmSpanDescriptorBlocks_length
      W.machine.tm
      (by
        unfold verifierTransitionDispatchMuxInvocationDescriptorTrueBlocks at hblock
        rw [List.mem_flatMap] at hblock
        exact hblock.choose)
      block
      (by
        unfold verifierTransitionDispatchMuxInvocationDescriptorTrueBlocks at hblock
        rw [List.mem_flatMap] at hblock
        exact hblock.choose_spec.2)
    simp [hnil] at hlength

/-- Remove the outer packet markers and expose the canonical adjacent
seven-field progression-family encoding. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorTrueProgressionFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  unmarkAffineUnaryTripleProgressionRows
    (verifierTransitionDispatchMuxInvocationDescriptorTrueDroppedPacketFrames
      W input)

/-- The entire physical interpreter recovers the generic raw progression
family literally. -/
theorem verifierTransitionDispatchMuxInvocationDescriptorTrueProgressionFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorTrueProgressionFrames
        W input =
      encodeAffineUnaryTripleProgressionFamily
        (verifierTransitionDispatchMuxInvocationDescriptorTrueRawProgressions
          W input) := by
  unfold verifierTransitionDispatchMuxInvocationDescriptorTrueProgressionFrames
  rw [verifierTransitionDispatchMuxInvocationDescriptorTrueDroppedPacketFrames_eq]
  rw [show
      (verifierTransitionDispatchMuxInvocationDescriptorTrueBlocks W input).flatMap
          (fun block => encodeUnaryFrame (block.drop 1) ++ [.frameEnd]) =
        ((verifierTransitionDispatchMuxInvocationDescriptorTrueBlocks W input).map
          (List.drop 1)).flatMap
            (fun row => encodeUnaryFrame row ++ [.frameEnd]) by
      simp [List.flatMap_map]]
  rw [unmarkAffineUnaryTripleProgressionRows_markedValues]
  rw [encodeAffineUnaryTripleProgressionFamily_eq_encodeUnaryFrame]
  have hdrop :
      (verifierTransitionDispatchMuxInvocationDescriptorTrueBlocks W input).map
          (List.drop 1) =
        (verifierTransitionDispatchMuxInvocationDescriptorTrueRawProgressions
          W input).map affineUnaryTripleProgressionFields := by
    unfold verifierTransitionDispatchMuxInvocationDescriptorTrueBlocks
      verifierTransitionDispatchMuxInvocationDescriptorTrueRawProgressions
    rw [List.map_flatMap, List.map_flatMap]
    apply List.flatMap_congr
    intro seed hseed
    exact transitionDispatchTrueArmSpanDescriptorBlocks_drop W.machine.tm seed
  rw [hdrop]
  rfl

/-- The raw-input true-arm source followed by fixed-width packet marking is
one concrete polynomial-time TM2. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorTruePacketFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationDescriptorTruePacketFrames W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionDispatchMuxInvocationDescriptorTrueFrames_computableInPolyTime
        W)
      (unaryFrameFixedWidthPacketMark_computableInPolyTime 8 (by omega))
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => rewriteUnaryFrameFixedWidthPackets 8 (by omega)
      (verifierTransitionDispatchMuxInvocationDescriptorTrueFrames W input))
  simpa [Function.comp_def,
    verifierTransitionDispatchMuxInvocationDescriptorTruePacketFrames] using
      Classical.choice composed

/-- Packet normalization preserves polynomial-time computability from the
original verifier input. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorTrueNormalizedPacketFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationDescriptorTrueNormalizedPacketFrames
        W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionDispatchMuxInvocationDescriptorTruePacketFrames_computableInPolyTime
        W)
      restoreUnaryFrameFixedWidthPacketSeparators_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => restoreUnaryFrameFixedWidthPacketSeparators
      (verifierTransitionDispatchMuxInvocationDescriptorTruePacketFrames
        W input))
  simpa [Function.comp_def,
    verifierTransitionDispatchMuxInvocationDescriptorTrueNormalizedPacketFrames]
    using Classical.choice composed

/-- Deleting the leading amount from every normalized packet remains one
concrete polynomial-time TM2. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorTrueDroppedPacketFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationDescriptorTrueDroppedPacketFrames
        W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionDispatchMuxInvocationDescriptorTrueNormalizedPacketFrames_computableInPolyTime
        W)
      (unaryFrameFixedPrefixDrop_computableInPolyTime 1)
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => rewriteUnaryFrameFixedPrefixDrop 1
      (verifierTransitionDispatchMuxInvocationDescriptorTrueNormalizedPacketFrames
        W input))
  simpa [Function.comp_def,
    verifierTransitionDispatchMuxInvocationDescriptorTrueDroppedPacketFrames]
    using Classical.choice composed

set_option maxHeartbeats 600000

/-- The physical eight-to-seven-field interpreter is one concrete
polynomial-time TM2 from the original verifier input. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorTrueProgressionFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationDescriptorTrueProgressionFrames W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionDispatchMuxInvocationDescriptorTrueDroppedPacketFrames_computableInPolyTime
        W)
      unmarkAffineUnaryTripleProgressionRows_computableInPolyTime
  have hfun :
      verifierTransitionDispatchMuxInvocationDescriptorTrueProgressionFrames W =
        fun input => unmarkAffineUnaryTripleProgressionRows
          (verifierTransitionDispatchMuxInvocationDescriptorTrueDroppedPacketFrames
            W input) := by
    funext input
    rfl
  rw [hfun]
  simpa only [Function.comp_def, id_eq] using Classical.choice composed

end CLRS.Chapter34.Turing.CookLevin

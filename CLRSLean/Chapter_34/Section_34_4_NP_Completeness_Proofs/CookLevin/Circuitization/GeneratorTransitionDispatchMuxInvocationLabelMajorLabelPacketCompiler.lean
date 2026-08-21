import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelMajorLabelChannels
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorLabelPacketChannelReassembly
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelPacketPipeline
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowParallelInterleaveRuntime

/-!
# Concrete label-packet compiler from the four label-major channels

The four independently verified channels are first exposed as typed marked-row
families.  Three applications of the reusable same-input interleaver implement
the physical four-way zipper:

`(selector ⊗ true) ⊗ (coordinate ⊗ false)`

which emits `selector / coordinate / true / false` for every label.  The final
encoding is proved byte-for-byte equal to the typed label-packet input expected
by the existing assembler pipeline.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

private theorem labelChannel_encodeUnaryFrame_frameEnd_free
    (values : List Nat) :
    ∀ symbol ∈ encodeUnaryFrame values,
      symbol ≠ UnaryFrameSym.frameEnd := by
  intro symbol hsymbol
  rw [encodeUnaryFrame, List.mem_flatMap] at hsymbol
  rcases hsymbol with ⟨value, _, hblock⟩
  simp [encodeUnaryFrameBlock] at hblock
  rcases hblock with ⟨_, rfl⟩ | rfl <;> simp

private theorem labelChannel_coordinate_frameEnd_free
    (coordinates : List (Nat × Nat × Nat)) :
    ∀ symbol ∈ transitionDispatchMuxCoordinateRowFrames coordinates,
      symbol ≠ UnaryFrameSym.frameEnd := by
  intro symbol hsymbol
  rw [transitionDispatchMuxCoordinateRowFrames,
    List.mem_flatMap] at hsymbol
  rcases hsymbol with ⟨coordinate, _, hcoordinate⟩
  exact labelChannel_encodeUnaryFrame_frameEnd_free _ symbol hcoordinate

/-- Typed selector channel. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorSelectorFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFrameMarkedRowFamily where
  rows :=
    (verifierTransitionDispatchMuxInvocationDescriptorLabelPacketChannelFamily
      W input).selectorRows
  frameEnd_free := by
    intro row hrow symbol hsymbol
    unfold
      verifierTransitionDispatchMuxInvocationDescriptorLabelPacketChannelFamily
      at hrow
    rw [List.mem_map] at hrow
    rcases hrow with ⟨view, _, rfl⟩
    exact labelChannel_encodeUnaryFrame_frameEnd_free _ symbol hsymbol

/-- Typed coordinate channel. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorCoordinateFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFrameMarkedRowFamily where
  rows :=
    (verifierTransitionDispatchMuxInvocationDescriptorLabelPacketChannelFamily
      W input).coordinateRows
  frameEnd_free := by
    intro row hrow symbol hsymbol
    unfold
      verifierTransitionDispatchMuxInvocationDescriptorLabelPacketChannelFamily
      at hrow
    rw [List.mem_map] at hrow
    rcases hrow with ⟨view, _, rfl⟩
    exact labelChannel_coordinate_frameEnd_free _ symbol hsymbol

/-- Typed true-arm channel. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorTrueFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFrameMarkedRowFamily where
  rows :=
    (verifierTransitionDispatchMuxInvocationDescriptorLabelPacketChannelFamily
      W input).trueRows
  frameEnd_free := by
    intro row hrow symbol hsymbol
    unfold
      verifierTransitionDispatchMuxInvocationDescriptorLabelPacketChannelFamily
      at hrow
    rw [List.mem_map] at hrow
    rcases hrow with ⟨view, _, rfl⟩
    exact labelChannel_encodeUnaryFrame_frameEnd_free _ symbol hsymbol

/-- Typed false-arm channel. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorFalseFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFrameMarkedRowFamily where
  rows :=
    (verifierTransitionDispatchMuxInvocationDescriptorLabelPacketChannelFamily
      W input).falseRows
  frameEnd_free := by
    intro row hrow symbol hsymbol
    unfold
      verifierTransitionDispatchMuxInvocationDescriptorLabelPacketChannelFamily
      at hrow
    rw [List.mem_map] at hrow
    rcases hrow with ⟨view, _, rfl⟩
    exact labelChannel_encodeUnaryFrame_frameEnd_free _ symbol hsymbol

theorem
    verifierTransitionDispatchMuxInvocationLabelMajorChannelFamily_encodings
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeUnaryFrameMarkedRowFamily
          (verifierTransitionDispatchMuxInvocationLabelMajorSelectorFamily
            W input) =
        verifierTransitionDispatchMuxInvocationLabelMajorSelectorLabelFrames
          W input ∧
      encodeUnaryFrameMarkedRowFamily
          (verifierTransitionDispatchMuxInvocationLabelMajorCoordinateFamily
            W input) =
        verifierTransitionDispatchMuxInvocationLabelMajorCoordinateLabelFrames
          W input ∧
      encodeUnaryFrameMarkedRowFamily
          (verifierTransitionDispatchMuxInvocationLabelMajorTrueFamily
            W input) =
        verifierTransitionDispatchMuxInvocationLabelMajorTrueLabelFrames
          W input ∧
      encodeUnaryFrameMarkedRowFamily
          (verifierTransitionDispatchMuxInvocationLabelMajorFalseFamily
            W input) =
        verifierTransitionDispatchMuxInvocationLabelMajorFalseLabelFrames
          W input := by
  have hchannels :=
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketChannelFamily_encodings
      W input
  rcases hchannels with ⟨hselector, hcoordinate, htrue, hfalse⟩
  constructor
  · exact hselector.trans
      (verifierTransitionDispatchMuxInvocationLabelMajorSelectorLabelFrames_eq_channel
        W input).symm
  constructor
  · exact hcoordinate.trans
      (verifierTransitionDispatchMuxInvocationLabelMajorCoordinateLabelFrames_eq_channel
        W input).symm
  constructor
  · exact htrue.trans
      (verifierTransitionDispatchMuxInvocationLabelMajorTrueLabelFrames_eq_channel
        W input).symm
  · exact hfalse.trans
      (verifierTransitionDispatchMuxInvocationLabelMajorFalseLabelFrames_eq_channel
        W input).symm

private noncomputable def selectorFamilyCompiler
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (verifierTransitionDispatchMuxInvocationLabelMajorSelectorFamily W) := by
  let base :=
    verifierTransitionDispatchMuxInvocationLabelMajorSelectorLabelFrames_computableInPolyTime
      W
  exact
    { tm := base.tm
      inputAlphabet := base.inputAlphabet
      outputAlphabet := base.outputAlphabet
      time := base.time
      outputsFun := fun input => by
        have run := base.outputsFun input
        simpa only [id_eq,
          (verifierTransitionDispatchMuxInvocationLabelMajorChannelFamily_encodings
            W input).1] using run }

private noncomputable def coordinateFamilyCompiler
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (verifierTransitionDispatchMuxInvocationLabelMajorCoordinateFamily W) := by
  let base :=
    verifierTransitionDispatchMuxInvocationLabelMajorCoordinateLabelFrames_computableInPolyTime
      W
  exact
    { tm := base.tm
      inputAlphabet := base.inputAlphabet
      outputAlphabet := base.outputAlphabet
      time := base.time
      outputsFun := fun input => by
        have run := base.outputsFun input
        simpa only [id_eq,
          (verifierTransitionDispatchMuxInvocationLabelMajorChannelFamily_encodings
            W input).2.1] using run }

private noncomputable def trueFamilyCompiler
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (verifierTransitionDispatchMuxInvocationLabelMajorTrueFamily W) := by
  let base :=
    verifierTransitionDispatchMuxInvocationLabelMajorTrueLabelFrames_computableInPolyTime
      W
  exact
    { tm := base.tm
      inputAlphabet := base.inputAlphabet
      outputAlphabet := base.outputAlphabet
      time := base.time
      outputsFun := fun input => by
        have run := base.outputsFun input
        simpa only [id_eq,
          (verifierTransitionDispatchMuxInvocationLabelMajorChannelFamily_encodings
            W input).2.2.1] using run }

private noncomputable def falseFamilyCompiler
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (verifierTransitionDispatchMuxInvocationLabelMajorFalseFamily W) := by
  let base :=
    verifierTransitionDispatchMuxInvocationLabelMajorFalseLabelFrames_computableInPolyTime
      W
  exact
    { tm := base.tm
      inputAlphabet := base.inputAlphabet
      outputAlphabet := base.outputAlphabet
      time := base.time
      outputsFun := fun input => by
        have run := base.outputsFun input
        simpa only [id_eq,
          (verifierTransitionDispatchMuxInvocationLabelMajorChannelFamily_encodings
            W input).2.2.2] using run }

private theorem selector_true_aligned
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierTransitionDispatchMuxInvocationLabelMajorSelectorFamily
      W input).rows.length =
      (verifierTransitionDispatchMuxInvocationLabelMajorTrueFamily
        W input).rows.length := by
  exact
    (verifierTransitionDispatchMuxInvocationDescriptorLabelPacketChannelFamily_rowAligned
      W input).2.1

private theorem coordinate_false_aligned
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierTransitionDispatchMuxInvocationLabelMajorCoordinateFamily
      W input).rows.length =
      (verifierTransitionDispatchMuxInvocationLabelMajorFalseFamily
        W input).rows.length := by
  have h :=
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketChannelFamily_rowAligned
      W input
  exact h.1.symm.trans h.2.2

private noncomputable def selectorTrueCompiler
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) := by
  letI : Fintype Γ := W.alphabetFintype
  exact
    PolyBuilder.UnaryFrameMarkedRowParallelInterleave.computableInPolyTime
      (selectorFamilyCompiler W) (trueFamilyCompiler W)
      (selector_true_aligned W)

private noncomputable def coordinateFalseCompiler
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) := by
  letI : Fintype Γ := W.alphabetFintype
  exact
    PolyBuilder.UnaryFrameMarkedRowParallelInterleave.computableInPolyTime
      (coordinateFamilyCompiler W) (falseFamilyCompiler W)
      (coordinate_false_aligned W)

private theorem pair_families_aligned
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (PolyBuilder.UnaryFrameMarkedRowParallelInterleave.interleavedFamily
      (selector_true_aligned W) input).rows.length =
      (PolyBuilder.UnaryFrameMarkedRowParallelInterleave.interleavedFamily
        (coordinate_false_aligned W) input).rows.length := by
  have h :=
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketChannelFamily_rowAligned
      W input
  change
    (interleaveUnaryFrameMarkedRows
      (verifierTransitionDispatchMuxInvocationLabelMajorSelectorFamily
        W input).rows
      (verifierTransitionDispatchMuxInvocationLabelMajorTrueFamily
        W input).rows).length =
    (interleaveUnaryFrameMarkedRows
      (verifierTransitionDispatchMuxInvocationLabelMajorCoordinateFamily
        W input).rows
      (verifierTransitionDispatchMuxInvocationLabelMajorFalseFamily
        W input).rows).length
  rw [interleaveUnaryFrameMarkedRows_length_of_aligned _ _
    (selector_true_aligned W input)]
  rw [interleaveUnaryFrameMarkedRows_length_of_aligned _ _
    (coordinate_false_aligned W input)]
  exact congrArg (fun length => 2 * length) h.1

/-- The concrete three-interleaver output family. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorPacketFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFrameMarkedRowFamily :=
  PolyBuilder.UnaryFrameMarkedRowParallelInterleave.interleavedFamily
    (pair_families_aligned W) input

private theorem nested_interleave_eq_four_way
    (selectors coordinates whenTrue whenFalse :
      List (List UnaryFrameSym))
    (hcoordinate : selectors.length = coordinates.length)
    (htrue : selectors.length = whenTrue.length)
    (hfalse : selectors.length = whenFalse.length) :
    interleaveUnaryFrameMarkedRows
        (interleaveUnaryFrameMarkedRows selectors whenTrue)
        (interleaveUnaryFrameMarkedRows coordinates whenFalse) =
      transitionDispatchMuxInvocationLabelPacketRowsFromChannels
        selectors coordinates whenTrue whenFalse := by
  induction selectors generalizing coordinates whenTrue whenFalse with
  | nil =>
      have hc : coordinates = [] :=
        List.eq_nil_of_length_eq_zero hcoordinate.symm
      have ht : whenTrue = [] :=
        List.eq_nil_of_length_eq_zero htrue.symm
      have hf : whenFalse = [] :=
        List.eq_nil_of_length_eq_zero hfalse.symm
      subst coordinates
      subst whenTrue
      subst whenFalse
      rfl
  | cons selector selectors ih =>
      cases coordinates with
      | nil => simp at hcoordinate
      | cons coordinate coordinates =>
          cases whenTrue with
          | nil => simp at htrue
          | cons truth whenTrue =>
              cases whenFalse with
              | nil => simp at hfalse
              | cons falsity whenFalse =>
                  simp only [List.length_cons] at hcoordinate htrue hfalse
                  simp only [interleaveUnaryFrameMarkedRows,
                    transitionDispatchMuxInvocationLabelPacketRowsFromChannels]
                  rw [ih coordinates whenTrue whenFalse (by omega)
                    (by omega) (by omega)]

/-- The three physical interleavers reconstruct the canonical four-row packet
encoding byte for byte. -/
theorem
    verifierTransitionDispatchMuxInvocationLabelMajorPacketFamily_encoding_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeUnaryFrameMarkedRowFamily
        (verifierTransitionDispatchMuxInvocationLabelMajorPacketFamily
          W input) =
      (verifierTransitionDispatchMuxInvocationAlignedViewFamily W input
        ).labelPacketFrames := by
  let channels :=
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketChannelFamily
      W input
  have haligned :=
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketChannelFamily_rowAligned
      W input
  have hrows := nested_interleave_eq_four_way
    channels.selectorRows channels.coordinateRows channels.trueRows
    channels.falseRows haligned.1 haligned.2.1 haligned.2.2
  have hreassembly :=
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketFrames_eq_channelReassembly
      W input
  have hcanonical :
      (verifierTransitionDispatchMuxInvocationAlignedViewFamily W input
        ).labelPacketFrames =
        verifierTransitionDispatchMuxInvocationDescriptorLabelPacketFrames
          W input := by
    unfold AlignedTransitionDispatchMuxInvocationViewFamily.labelPacketFrames
      verifierTransitionDispatchMuxInvocationAlignedViewFamily
      verifierTransitionDispatchMuxInvocationViews
    rw [encode_transitionDispatchMuxInvocationLabelPacketFamily]
    unfold
      verifierTransitionDispatchMuxInvocationDescriptorLabelPacketFrames
    exact List.flatMap_assoc
  rw [hcanonical, hreassembly]
  unfold verifierTransitionDispatchMuxInvocationLabelMajorPacketFamily
    PolyBuilder.UnaryFrameMarkedRowParallelInterleave.interleavedFamily
    UnaryFrameAlignedMarkedRowPair.interleaved
    encodeUnaryFrameMarkedRowFamily
  change
    (interleaveUnaryFrameMarkedRows
      (interleaveUnaryFrameMarkedRows channels.selectorRows channels.trueRows)
      (interleaveUnaryFrameMarkedRows channels.coordinateRows
        channels.falseRows)).flatMap (fun row => row ++ [.frameEnd]) = _
  simpa [encodeTransitionDispatchMuxInvocationLabelPacketChannelRows,
    channels] using congrArg
      (fun rows => rows.flatMap (fun row => row ++ [.frameEnd])) hrows

/-- Concrete raw-input compiler for the typed unprepared label-packet family.
-/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorPacketFamily_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id
      AlignedTransitionDispatchMuxInvocationViewFamily.labelPacketFrames
      (verifierTransitionDispatchMuxInvocationAlignedViewFamily W) := by
  letI : Fintype Γ := W.alphabetFintype
  let pairCompiler :=
    PolyBuilder.UnaryFrameMarkedRowParallelInterleave.computableInPolyTime
      (selectorTrueCompiler W) (coordinateFalseCompiler W)
      (pair_families_aligned W)
  exact
    { tm := pairCompiler.tm
      inputAlphabet := pairCompiler.inputAlphabet
      outputAlphabet := pairCompiler.outputAlphabet
      time := pairCompiler.time
      outputsFun := fun input => by
        have run := pairCompiler.outputsFun input
        have run' : _root_.Turing.TM2OutputsInTime pairCompiler.tm
            (List.map pairCompiler.inputAlphabet.invFun input)
            (some (List.map pairCompiler.outputAlphabet.invFun
              (encodeUnaryFrameMarkedRowFamily
                (verifierTransitionDispatchMuxInvocationLabelMajorPacketFamily
                  W input))))
            (pairCompiler.time.eval input.length) := by
          simpa only [id_eq,
            verifierTransitionDispatchMuxInvocationLabelMajorPacketFamily]
            using run
        rw [
          verifierTransitionDispatchMuxInvocationLabelMajorPacketFamily_encoding_eq
            W input] at run'
        exact run' }

/-- The formerly conditional mux pipeline is now closed from the original
verifier input by the concrete label-major packet compiler. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationFrames_labelMajor_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationFrames W) :=
  verifierTransitionDispatchMuxInvocationFrames_computableInPolyTime_of_labelPacketCompiler
    W
    (verifierTransitionDispatchMuxInvocationLabelMajorPacketFamily_computableInPolyTime
      W)

end CLRS.Chapter34.Turing.CookLevin

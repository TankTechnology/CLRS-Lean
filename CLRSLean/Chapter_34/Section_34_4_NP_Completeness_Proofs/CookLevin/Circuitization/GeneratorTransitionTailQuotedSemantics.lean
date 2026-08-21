import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionTailQuotedRoute
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionTailPhaseAlignment
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionSeedRowSource
import Mathlib.Tactic

/-!
# Canonical semantics of quoted transition tails

The affine tail tables emit every internal symbol in the two-symbol quoted
alphabet, while retaining one literal `frameEnd` as the outer row boundary.
This module identifies the selected router output with the quotation of the
established canonical transition tail.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

private theorem transitionTailQuotedPrefixPhaseRouted_eq
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    encodeUnaryFrameWithFixedDelimiters
        (affineUnaryTripleMap (transitionTailQuotedPrefixPhaseForms tm)
          (transitionEqPrefixSentinelCoordinateSeed seed))
        (transitionTailQuotedPrefixPhaseDelimiters tm) =
      quoteUnaryFrameStream
        (encodeAffineOrThenNotInput
            (transitionScriptFromSeed tm seed
              (seed.rowBase + cfgBitCount tm seed.height)).narrowFrames
            (transitionScriptFromSeed tm seed
              (seed.rowBase + cfgBitCount tm seed.height)).narrowSource ++
          [.tick]) := by
  rw [transitionTailQuotedPrefixPhase_value]
  unfold transitionTailQuotedPrefixPhaseDelimiters
  rw [encodeUnaryFrameWithFixedDelimiters_quote]
  · rw [transitionTailPrefixPhaseRouted_eq tm seed hwork]
  · simpa [affineUnaryTripleMap] using
      transitionTailPrefixPhaseForms_delimiters_length tm

private theorem transitionTailQuotedRealPhaseRouted_eq
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (coordinate : AffineUnaryTripleSeed)
    (hcoordinate : coordinate ∈ transitionEqCoordinateSeeds tm seed)
    (hwork : 0 < workHeight tm seed.height) :
    encodeUnaryFrameWithFixedDelimiters
        (affineUnaryTripleMap transitionTailQuotedEqPhaseForms coordinate)
        transitionTailQuotedEqPhaseDelimiters =
      quoteUnaryFrameStream
        (encodeAffineEqFinPairFrame
          (transitionEqCoordinateFrame coordinate)) := by
  rw [transitionTailQuotedEqPhase_value]
  unfold transitionTailQuotedEqPhaseDelimiters
  rw [encodeUnaryFrameWithFixedDelimiters_quote]
  · have routed := transitionTailRealPhaseRouted_eq
      tm seed coordinate hcoordinate hwork
    have htag := transitionEqCoordinateSeed_first_gt_one tm seed coordinate
      hcoordinate hwork
    have hzero : coordinate.first ≠ 0 := by omega
    have hone : coordinate.first ≠ 1 := by omega
    have original :
        encodeUnaryFrameWithFixedDelimiters
            (affineUnaryTripleMap transitionEqInvocationForms coordinate)
            transitionEqInvocationDelimiterTable =
          encodeAffineEqFinPairFrame
            (transitionEqCoordinateFrame coordinate) := by
      simpa only [encodeUnaryFrameThreeWayTaggedRowOutput,
        transitionTailPhaseTaggedRow, hzero, hone, if_false] using routed
    rw [original]
  · simp [affineUnaryTripleMap, transitionEqInvocationForms,
      transitionEqInvocationDelimiterTable]

private theorem transitionTailSuffixInnerPhase_value
    (tm : _root_.Turing.FinTM2) (coordinate : AffineUnaryTripleSeed) :
    affineUnaryTripleMap (transitionTailSuffixPhaseForms tm) coordinate =
      affineUnaryTripleMap
          (transitionTailSuffixInnerPhaseForms tm) coordinate ++ [0] := by
  simp [transitionTailSuffixPhaseForms,
    transitionTailSuffixInnerPhaseForms, affineUnaryTripleMap,
    List.map_append, transitionZeroForm, affineUnaryTripleFormValue]

private theorem transitionTailQuotedSuffixPhaseRouted_eq
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    encodeUnaryFrameWithFixedDelimiters
        (affineUnaryTripleMap (transitionTailQuotedSuffixPhaseForms tm)
          (transitionEqSuffixSentinelCoordinateSeed seed))
        (transitionTailQuotedSuffixPhaseDelimiters tm) =
      quoteUnaryFrameStream
          ([.tick] ++
            encodeAffineAndFinFrames
              [(transitionScriptFromSeed tm seed
                (seed.rowBase + cfgBitCount tm seed.height)).finalAnd]) ++
        [.frameEnd] := by
  let coordinate := transitionEqSuffixSentinelCoordinateSeed seed
  let innerValues := affineUnaryTripleMap
    (transitionTailSuffixInnerPhaseForms tm) coordinate
  let innerDelimiters := transitionTailSuffixInnerPhaseDelimiters tm
  have hinnerLength : innerValues.length = innerDelimiters.length := by
    rw [show innerValues.length =
        (transitionTailSuffixInnerPhaseForms tm).length by
      simp [innerValues, affineUnaryTripleMap]]
    exact transitionTailSuffixInnerPhase_lengths tm
  have original := transitionTailSuffixPhaseRouted_eq tm seed hwork
  rw [transitionTailSuffixInnerPhase_value tm coordinate] at original
  change encodeUnaryFrameWithFixedDelimiters
      (innerValues ++ [0]) (innerDelimiters ++ [.frameEnd]) = _ at original
  rw [encodeUnaryFrameWithFixedDelimiters_append_of_length
    _ _ _ _ hinnerLength] at original
  simp only [encodeUnaryFrameWithFixedDelimiters, List.replicate_zero,
    List.nil_append, List.append_assoc] at original
  have hinner : encodeUnaryFrameWithFixedDelimiters
      innerValues innerDelimiters =
        [.tick] ++
          encodeAffineAndFinFrames
            [(transitionScriptFromSeed tm seed
              (seed.rowBase + cfgBitCount tm seed.height)).finalAnd] := by
    exact List.append_cancel_right original
  rw [transitionTailQuotedSuffixPhase_value]
  unfold transitionTailQuotedSuffixPhaseDelimiters
  rw [encodeUnaryFrameWithFixedDelimiters_append_of_length]
  · rw [encodeUnaryFrameWithFixedDelimiters_quote _ _ hinnerLength,
      hinner]
    simp [encodeUnaryFrameWithFixedDelimiters, List.append_assoc]
  · simpa [affineUnaryTripleMap] using congrArg (fun n => 2 * n)
      (transitionTailSuffixInnerPhase_lengths tm)

private theorem transitionTailQuotedPrefixTaggedRow_output
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    encodeUnaryFrameThreeWayTaggedRowOutput
        (transitionTailQuotedPrefixPhaseDelimiters tm)
        (transitionTailQuotedSuffixPhaseDelimiters tm)
        transitionTailQuotedEqPhaseDelimiters
        (transitionTailQuotedPhaseTaggedRow tm
          (transitionEqPrefixSentinelCoordinateSeed seed)) =
      quoteUnaryFrameStream
        (encodeAffineOrThenNotInput
            (transitionScriptFromSeed tm seed
              (seed.rowBase + cfgBitCount tm seed.height)).narrowFrames
            (transitionScriptFromSeed tm seed
              (seed.rowBase + cfgBitCount tm seed.height)).narrowSource ++
          [.tick]) := by
  unfold encodeUnaryFrameThreeWayTaggedRowOutput
    transitionTailQuotedPhaseTaggedRow
  simp only [transitionEqPrefixSentinelCoordinateSeed, if_pos]
  exact transitionTailQuotedPrefixPhaseRouted_eq tm seed hwork

private theorem transitionTailQuotedSuffixTaggedRow_output
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    encodeUnaryFrameThreeWayTaggedRowOutput
        (transitionTailQuotedPrefixPhaseDelimiters tm)
        (transitionTailQuotedSuffixPhaseDelimiters tm)
        transitionTailQuotedEqPhaseDelimiters
        (transitionTailQuotedPhaseTaggedRow tm
          (transitionEqSuffixSentinelCoordinateSeed seed)) =
      quoteUnaryFrameStream
          ([.tick] ++
            encodeAffineAndFinFrames
              [(transitionScriptFromSeed tm seed
                (seed.rowBase + cfgBitCount tm seed.height)).finalAnd]) ++
        [.frameEnd] := by
  unfold encodeUnaryFrameThreeWayTaggedRowOutput
    transitionTailQuotedPhaseTaggedRow
  simp only [transitionEqSuffixSentinelCoordinateSeed, Nat.one_ne_zero,
    if_false, if_pos]
  exact transitionTailQuotedSuffixPhaseRouted_eq tm seed hwork

private theorem transitionTailQuotedRealTaggedRow_output
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (coordinate : AffineUnaryTripleSeed)
    (hcoordinate : coordinate ∈ transitionEqCoordinateSeeds tm seed)
    (hwork : 0 < workHeight tm seed.height) :
    encodeUnaryFrameThreeWayTaggedRowOutput
        (transitionTailQuotedPrefixPhaseDelimiters tm)
        (transitionTailQuotedSuffixPhaseDelimiters tm)
        transitionTailQuotedEqPhaseDelimiters
        (transitionTailQuotedPhaseTaggedRow tm coordinate) =
      quoteUnaryFrameStream
        (encodeAffineEqFinPairFrame
          (transitionEqCoordinateFrame coordinate)) := by
  have htag := transitionEqCoordinateSeed_first_gt_one tm seed coordinate
    hcoordinate hwork
  have hzero : coordinate.first ≠ 0 := by omega
  have hone : coordinate.first ≠ 1 := by omega
  unfold encodeUnaryFrameThreeWayTaggedRowOutput
    transitionTailQuotedPhaseTaggedRow
  simp only [hzero, hone, if_false]
  exact transitionTailQuotedRealPhaseRouted_eq tm seed coordinate
    hcoordinate hwork

private theorem transitionTailQuotedRealTaggedRows_output
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    ((transitionEqCoordinateSeeds tm seed).map
        (transitionTailQuotedPhaseTaggedRow tm)).flatMap (fun row =>
          encodeUnaryFrameThreeWayTaggedRowOutput
            (transitionTailQuotedPrefixPhaseDelimiters tm)
            (transitionTailQuotedSuffixPhaseDelimiters tm)
            transitionTailQuotedEqPhaseDelimiters row) =
      quoteUnaryFrameStream
        (encodeAffineEqFinFrames (transitionEqGeneratedFrames tm seed)) := by
  unfold transitionEqGeneratedFrames encodeAffineEqFinFrames
  simp only [List.flatMap_map]
  rw [show quoteUnaryFrameStream
        ((transitionEqCoordinateSeeds tm seed).flatMap
          (fun coordinate =>
            encodeAffineEqFinPairFrame
              (transitionEqCoordinateFrame coordinate))) =
      (transitionEqCoordinateSeeds tm seed).flatMap
        (fun coordinate =>
          quoteUnaryFrameStream
            (encodeAffineEqFinPairFrame
              (transitionEqCoordinateFrame coordinate))) by
    induction transitionEqCoordinateSeeds tm seed with
    | nil => rfl
    | cons coordinate rest ih =>
        simp only [List.flatMap_cons]
        rw [quoteUnaryFrameStream_append, ih]]
  apply List.flatMap_congr
  intro coordinate hcoordinate
  exact transitionTailQuotedRealTaggedRow_output tm seed coordinate
    hcoordinate hwork

/-- The selected quoted coordinates for one transition seed are exactly the
quotation of the canonical tail, followed by one literal outer boundary. -/
theorem transitionTailQuotedPhaseTaggedRowOutput_eq_tail
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    encodeUnaryFrameThreeWayTaggedRowOutputFamily
        (transitionTailQuotedPrefixPhaseDelimiters tm)
        (transitionTailQuotedSuffixPhaseDelimiters tm)
        transitionTailQuotedEqPhaseDelimiters
        ((transitionEqPhaseCoordinateSeeds tm seed).map
          (transitionTailQuotedPhaseTaggedRow tm)) =
      quoteUnaryFrameStream
        (encodeAffineTransitionTail
          (transitionScriptFromSeed tm seed
            (seed.rowBase + cfgBitCount tm seed.height))) ++
        [.frameEnd] := by
  unfold encodeUnaryFrameThreeWayTaggedRowOutputFamily
    transitionEqPhaseCoordinateSeeds
  simp only [List.map_cons, List.map_append,
    List.flatMap_cons, List.flatMap_append]
  rw [transitionTailQuotedPrefixTaggedRow_output tm seed hwork,
    transitionTailQuotedRealTaggedRows_output tm seed hwork,
    transitionEqGeneratedFrames_eq_script tm seed hwork,
    transitionTailQuotedSuffixTaggedRow_output tm seed hwork]
  simp [encodeAffineTransitionTail, quoteUnaryFrameStream_append,
    List.append_assoc]

private theorem transitionTailQuotedPhaseTaggedRows_output
    (tm : _root_.Turing.FinTM2) (seeds : List TransitionRowSeed)
    (hwork : ∀ seed ∈ seeds, 0 < workHeight tm seed.height) :
    encodeUnaryFrameThreeWayTaggedRowOutputFamily
        (transitionTailQuotedPrefixPhaseDelimiters tm)
        (transitionTailQuotedSuffixPhaseDelimiters tm)
        transitionTailQuotedEqPhaseDelimiters
        ((seeds.flatMap (transitionEqPhaseCoordinateSeeds tm)).map
          (transitionTailQuotedPhaseTaggedRow tm)) =
      seeds.flatMap fun seed =>
        quoteUnaryFrameStream
          (encodeAffineTransitionTail
            (transitionScriptFromSeed tm seed
              (seed.rowBase + cfgBitCount tm seed.height))) ++
          [.frameEnd] := by
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      have hseed : 0 < workHeight tm seed.height := hwork seed (by simp)
      have hrest : ∀ item ∈ rest, 0 < workHeight tm item.height := by
        intro item hitem
        exact hwork item (by simp [hitem])
      simp only [List.flatMap_cons, List.map_append]
      have hhead :=
        transitionTailQuotedPhaseTaggedRowOutput_eq_tail tm seed hseed
      have htail := ih hrest
      unfold encodeUnaryFrameThreeWayTaggedRowOutputFamily at hhead htail ⊢
      rw [List.flatMap_append, hhead, htail]

/-- One delimiter-safe quoted tail row for every canonical transition seed. -/
noncomputable def verifierTransitionTailQuotedFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFrameMarkedRowFamily where
  rows := (verifierTransitionRowSeeds W input).map fun seed =>
    quoteUnaryFrameStream
      (encodeAffineTransitionTail
        (transitionScriptFromSeed W.machine.tm seed
          (seed.rowBase + cfgBitCount W.machine.tm seed.height)))
  frameEnd_free := by
    intro row hrow symbol hsymbol
    rcases List.mem_map.mp hrow with ⟨seed, _hseed, rfl⟩
    exact quoteUnaryFrameStream_frameEnd_free _ symbol hsymbol

theorem verifierTransitionTailQuotedFamily_encoding
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeUnaryFrameMarkedRowFamily
        (verifierTransitionTailQuotedFamily W input) =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        quoteUnaryFrameStream
          (encodeAffineTransitionTail
            (transitionScriptFromSeed W.machine.tm seed
              (seed.rowBase + cfgBitCount W.machine.tm seed.height))) ++
          [.frameEnd] := by
  simp [encodeUnaryFrameMarkedRowFamily,
    verifierTransitionTailQuotedFamily, List.flatMap_map]

/-- The concrete quoted router emits exactly the public marked tail family. -/
theorem verifierTransitionTailQuotedRoutedInput_eq_family
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionTailQuotedRoutedInput W input =
      encodeUnaryFrameMarkedRowFamily
        (verifierTransitionTailQuotedFamily W input) := by
  rw [verifierTransitionTailQuotedRoutedInput_eq_rows,
    verifierTransitionTailQuotedFamily_encoding]
  unfold verifierTransitionTailQuotedPhaseTaggedRows
  apply transitionTailQuotedPhaseTaggedRows_output
  intro seed hseed
  rw [verifierTransitionRowSeeds_height_eq W input seed hseed]
  exact Nat.add_pos_left
    (verifierHeight_eval_pos W input.length)
    (maxPushesPerStep W.machine.tm)

/-- A fixed polynomial-time TM2 emits the exact marked quoted-tail family
directly from the raw verifier input. -/
noncomputable def verifierTransitionTailQuotedFamily_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (verifierTransitionTailQuotedFamily W) := by
  let routed :=
    verifierTransitionTailQuotedRoutedInput_computableInPolyTime W
  exact
    { tm := routed.tm
      inputAlphabet := routed.inputAlphabet
      outputAlphabet := routed.outputAlphabet
      time := routed.time
      outputsFun := fun input => by
        have run := routed.outputsFun input
        simpa only [id_eq,
          verifierTransitionTailQuotedRoutedInput_eq_family W input]
          using run }

/-- Reusable seed-indexed source exposing the complete quoted tail row. -/
noncomputable def verifierTransitionTailQuotedSeedRowSource
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    VerifierTransitionSeedRowSource W where
  row := fun seed =>
    quoteUnaryFrameStream
      (encodeAffineTransitionTail
        (transitionScriptFromSeed W.machine.tm seed
          (seed.rowBase + cfgBitCount W.machine.tm seed.height)))
  family := verifierTransitionTailQuotedFamily W
  rows_eq := fun input => rfl
  computableInPolyTime :=
    verifierTransitionTailQuotedFamily_computableInPolyTime W

end CLRS.Chapter34.Turing.CookLevin

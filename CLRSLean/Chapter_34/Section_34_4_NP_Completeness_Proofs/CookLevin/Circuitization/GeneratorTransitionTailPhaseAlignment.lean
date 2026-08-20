import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionTailPhaseRoute
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionEqCanonicalAlignment
import Mathlib.Tactic

/-!
# Canonical alignment of the routed transition tail

The phase router already selects the narrowing prefix, one equality frame for
each genuine coordinate, and the final-conjunction suffix.  This module proves
that the selected bytes are literally the established
`encodeAffineTransitionTail` target, first for one transition row and then for
the complete raw-input verifier family.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

private theorem encodeUnaryFrameWithFixedDelimiters_append
    (left right : List Nat) (leftDelimiters rightDelimiters :
      List UnaryFrameSym)
    (hlength : left.length = leftDelimiters.length) :
    encodeUnaryFrameWithFixedDelimiters (left ++ right)
        (leftDelimiters ++ rightDelimiters) =
      encodeUnaryFrameWithFixedDelimiters left leftDelimiters ++
        encodeUnaryFrameWithFixedDelimiters right rightDelimiters := by
  induction left generalizing leftDelimiters with
  | nil =>
      cases leftDelimiters with
      | nil => rfl
      | cons delimiter delimiters => simp at hlength
  | cons value values ih =>
      cases leftDelimiters with
      | nil => simp at hlength
      | cons delimiter delimiters =>
          simp only [List.length_cons] at hlength
          have hlength' : values.length = delimiters.length :=
            Nat.add_right_cancel hlength
          simp [encodeUnaryFrameWithFixedDelimiters,
            ih delimiters hlength', List.append_assoc]

private theorem transitionNarrowFrames_fixedEncoding
    (frames : List AffineOrFinPairFrame) :
    encodeUnaryFrameWithFixedDelimiters
        (frames.flatMap fun frame =>
          [0, frame.left, 0, frame.right + 1, 0])
        ((List.replicate frames.length
          transitionNarrowInvocationDelimiterTable).flatten) =
      encodeAffineOrFinFrames frames := by
  induction frames with
  | nil => rfl
  | cons frame frames ih =>
      simp only [List.flatMap_cons, List.length_cons,
        List.replicate_succ, List.flatten_cons]
      rw [encodeUnaryFrameWithFixedDelimiters_append]
      · rw [ih]
        simp [transitionNarrowInvocationDelimiterTable,
          encodeUnaryFrameWithFixedDelimiters,
          encodeAffineOrFinFrames, encodeAffineOrFinPairFrame,
          encodeUnaryFrame, encodeUnaryFrameBlock,
          List.append_assoc]
      · simp [transitionNarrowInvocationDelimiterTable]

private theorem transitionNarrowNot_fixedEncoding (source : Nat) :
    encodeUnaryFrameWithFixedDelimiters [0, 0, 0, source, 0]
        transitionNarrowNotInvocationDelimiterTable =
      .tick :: encodeUnaryFrame [0, 0, source] ++ [.frameEnd] := by
  simp [transitionNarrowNotInvocationDelimiterTable,
    encodeUnaryFrameWithFixedDelimiters, encodeUnaryFrame,
    encodeUnaryFrameBlock, List.append_assoc]

private theorem transitionEqFrame_fixedEncoding
    (frame : AffineEqFinPairFrame) :
    encodeUnaryFrameWithFixedDelimiters
        [0, frame.eqStart, frame.left, frame.right, 0,
          frame.matched, 0, frame.previous, 0]
        transitionEqInvocationDelimiterTable =
      encodeAffineEqFinPairFrame frame := by
  simp [transitionEqInvocationDelimiterTable,
    encodeUnaryFrameWithFixedDelimiters, encodeAffineEqFinPairFrame,
    encodeUnaryFrame, encodeUnaryFrameBlock, List.append_assoc]

private theorem transitionFinalAnd_fixedEncoding
    (frame : AffineAndFinPairFrame) :
    encodeUnaryFrameWithFixedDelimiters
        [0, frame.right, 0, frame.left, 0]
        transitionFinalAndInvocationDelimiterTable =
      encodeAffineAndFinPairFrame frame := by
  simp [transitionFinalAndInvocationDelimiterTable,
    encodeUnaryFrameWithFixedDelimiters, encodeAffineAndFinPairFrame,
    encodeUnaryFrame, encodeUnaryFrameBlock, List.append_assoc]

/-- The tag-zero payload is exactly the narrowing phase followed by the
boundary tick that starts the equality phase. -/
theorem transitionTailPrefixPhaseRouted_eq
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    encodeUnaryFrameWithFixedDelimiters
        (affineUnaryTripleMap (transitionTailPrefixPhaseForms tm)
          (transitionEqPrefixSentinelCoordinateSeed seed))
        (transitionTailPrefixPhaseDelimiters tm) =
      encodeAffineOrThenNotInput
          (transitionScriptFromSeed tm seed
            (seed.rowBase + cfgBitCount tm seed.height)).narrowFrames
          (transitionScriptFromSeed tm seed
            (seed.rowBase + cfgBitCount tm seed.height)).narrowSource ++
        [.tick] := by
  rw [transitionTailPrefixPhaseForms_value tm seed hwork]
  unfold transitionTailPrefixPhaseDelimiters
  have hnarrowLength :
      (transitionNarrowInvocationValues tm seed).length =
        ((List.replicate (Fintype.card tm.K * maxPushesPerStep tm)
          transitionNarrowInvocationDelimiterTable).flatten).length := by
    rw [← transitionNarrowInvocationForms_value tm seed hwork]
    rw [show (affineUnaryTripleMap
          (transitionNarrowInvocationForms tm)
          (transitionTailAffineSeed seed)).length =
        (transitionNarrowInvocationForms tm).length by
      simp [affineUnaryTripleMap]]
    rw [transitionNarrowInvocationForms_length]
    simp [transitionNarrowInvocationDelimiterTable]
    omega
  simp only [List.append_assoc]
  rw [encodeUnaryFrameWithFixedDelimiters_append _ _ _ _ hnarrowLength]
  rw [encodeUnaryFrameWithFixedDelimiters_append]
  · let nextRowBase := seed.rowBase + cfgBitCount tm seed.height
    have hscriptLength :
        (transitionScriptFromSeed tm seed nextRowBase).narrowFrames.length =
          Fintype.card tm.K * maxPushesPerStep tm := by
      have hvalues := congrArg List.length
        (transitionNarrowInvocationValues_eq_script tm seed nextRowBase)
      rw [hnarrowLength] at hvalues
      simpa [transitionNarrowInvocationDelimiterTable] using hvalues.symm
    rw [transitionNarrowInvocationValues_eq_script tm seed nextRowBase,
      transitionNarrowNotInvocationValues_eq_script tm seed nextRowBase,
      ← hscriptLength,
      transitionNarrowFrames_fixedEncoding,
      transitionNarrowNot_fixedEncoding]
    simp [encodeUnaryFrameWithFixedDelimiters,
      encodeAffineOrThenNotInput, nextRowBase, List.append_assoc]
  · simp [transitionNarrowNotInvocationValues]

/-- The tag-one payload is exactly the equality boundary, final conjunction,
and local-row terminator. -/
theorem transitionTailSuffixPhaseRouted_eq
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    encodeUnaryFrameWithFixedDelimiters
        (affineUnaryTripleMap (transitionTailSuffixPhaseForms tm)
          (transitionEqSuffixSentinelCoordinateSeed seed))
        (transitionTailSuffixPhaseDelimiters tm) =
      [.tick] ++
        encodeAffineAndFinFrames
          [(transitionScriptFromSeed tm seed
            (seed.rowBase + cfgBitCount tm seed.height)).finalAnd] ++
        [.frameEnd] := by
  rw [transitionTailSuffixPhaseForms_value tm seed hwork,
    transitionFinalAndInvocationValues_eq_script tm seed
      (seed.rowBase + cfgBitCount tm seed.height)]
  simp only [transitionTailSuffixPhaseDelimiters, List.append_assoc]
  rw [encodeUnaryFrameWithFixedDelimiters_append]
  · rw [encodeUnaryFrameWithFixedDelimiters_append]
    · rw [transitionFinalAnd_fixedEncoding]
      simp [encodeUnaryFrameWithFixedDelimiters,
        encodeAffineAndFinFrames]
    · simp
  · simp

/-- Every genuine equality coordinate takes the router's many branch and
materializes one canonical equality frame. -/
theorem transitionTailRealPhaseRouted_eq
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (coordinate : AffineUnaryTripleSeed)
    (hcoordinate : coordinate ∈ transitionEqCoordinateSeeds tm seed)
    (hwork : 0 < workHeight tm seed.height) :
    encodeUnaryFrameThreeWayTaggedRowOutput
        (transitionTailPrefixPhaseDelimiters tm)
        (transitionTailSuffixPhaseDelimiters tm)
        transitionEqInvocationDelimiterTable
        (transitionTailPhaseTaggedRow tm coordinate) =
      encodeAffineEqFinPairFrame (transitionEqCoordinateFrame coordinate) := by
  have htag := transitionEqCoordinateSeed_first_gt_one tm seed coordinate
    hcoordinate hwork
  have hzero : coordinate.first ≠ 0 := by omega
  have hone : coordinate.first ≠ 1 := by omega
  unfold encodeUnaryFrameThreeWayTaggedRowOutput
    transitionTailPhaseTaggedRow
  simp only [hzero, hone, if_false]
  rw [transitionEqInvocationForms_value]
  exact transitionEqFrame_fixedEncoding _

private theorem transitionTailPrefixTaggedRow_output
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    encodeUnaryFrameThreeWayTaggedRowOutput
        (transitionTailPrefixPhaseDelimiters tm)
        (transitionTailSuffixPhaseDelimiters tm)
        transitionEqInvocationDelimiterTable
        (transitionTailPhaseTaggedRow tm
          (transitionEqPrefixSentinelCoordinateSeed seed)) =
      encodeAffineOrThenNotInput
          (transitionScriptFromSeed tm seed
            (seed.rowBase + cfgBitCount tm seed.height)).narrowFrames
          (transitionScriptFromSeed tm seed
            (seed.rowBase + cfgBitCount tm seed.height)).narrowSource ++
        [.tick] := by
  unfold encodeUnaryFrameThreeWayTaggedRowOutput
    transitionTailPhaseTaggedRow
  simp only [transitionEqPrefixSentinelCoordinateSeed, if_pos]
  exact transitionTailPrefixPhaseRouted_eq tm seed hwork

private theorem transitionTailSuffixTaggedRow_output
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    encodeUnaryFrameThreeWayTaggedRowOutput
        (transitionTailPrefixPhaseDelimiters tm)
        (transitionTailSuffixPhaseDelimiters tm)
        transitionEqInvocationDelimiterTable
        (transitionTailPhaseTaggedRow tm
          (transitionEqSuffixSentinelCoordinateSeed seed)) =
      [.tick] ++
        encodeAffineAndFinFrames
          [(transitionScriptFromSeed tm seed
            (seed.rowBase + cfgBitCount tm seed.height)).finalAnd] ++
        [.frameEnd] := by
  unfold encodeUnaryFrameThreeWayTaggedRowOutput
    transitionTailPhaseTaggedRow
  simp only [transitionEqSuffixSentinelCoordinateSeed, Nat.one_ne_zero,
    if_false, if_pos]
  exact transitionTailSuffixPhaseRouted_eq tm seed hwork

private theorem transitionTailRealTaggedRows_output
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    ((transitionEqCoordinateSeeds tm seed).map
        (transitionTailPhaseTaggedRow tm)).flatMap (fun row =>
          encodeUnaryFrameThreeWayTaggedRowOutput
            (transitionTailPrefixPhaseDelimiters tm)
            (transitionTailSuffixPhaseDelimiters tm)
            transitionEqInvocationDelimiterTable row) =
      encodeAffineEqFinFrames (transitionEqGeneratedFrames tm seed) := by
  unfold transitionEqGeneratedFrames encodeAffineEqFinFrames
  simp only [List.flatMap_map]
  apply List.flatMap_congr
  intro coordinate hcoordinate
  exact transitionTailRealPhaseRouted_eq tm seed coordinate hcoordinate hwork

/-- The routed phase family of one transition row is byte-for-byte the
canonical transition tail followed by the local controller terminator. -/
theorem transitionTailPhaseTaggedRowOutput_eq_tail
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    encodeUnaryFrameThreeWayTaggedRowOutputFamily
        (transitionTailPrefixPhaseDelimiters tm)
        (transitionTailSuffixPhaseDelimiters tm)
        transitionEqInvocationDelimiterTable
        ((transitionEqPhaseCoordinateSeeds tm seed).map
          (transitionTailPhaseTaggedRow tm)) =
      encodeAffineTransitionTail
          (transitionScriptFromSeed tm seed
            (seed.rowBase + cfgBitCount tm seed.height)) ++
        [.frameEnd] := by
  unfold encodeUnaryFrameThreeWayTaggedRowOutputFamily
    transitionEqPhaseCoordinateSeeds
  simp only [List.map_cons, List.map_append,
    List.flatMap_cons, List.flatMap_append]
  rw [transitionTailPrefixTaggedRow_output tm seed hwork,
    transitionTailRealTaggedRows_output tm seed hwork,
    transitionEqGeneratedFrames_eq_script tm seed hwork,
    transitionTailSuffixTaggedRow_output tm seed hwork]
  simp [encodeAffineTransitionTail, List.append_assoc]

private theorem transitionTailPhaseTaggedRows_output
    (tm : _root_.Turing.FinTM2) (seeds : List TransitionRowSeed)
    (hwork : ∀ seed ∈ seeds, 0 < workHeight tm seed.height) :
    encodeUnaryFrameThreeWayTaggedRowOutputFamily
        (transitionTailPrefixPhaseDelimiters tm)
        (transitionTailSuffixPhaseDelimiters tm)
        transitionEqInvocationDelimiterTable
        ((seeds.flatMap (transitionEqPhaseCoordinateSeeds tm)).map
          (transitionTailPhaseTaggedRow tm)) =
      seeds.flatMap fun seed =>
        encodeAffineTransitionTail
            (transitionScriptFromSeed tm seed
              (seed.rowBase + cfgBitCount tm seed.height)) ++
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
        transitionTailPhaseTaggedRowOutput_eq_tail tm seed hseed
      have htail := ih hrest
      unfold encodeUnaryFrameThreeWayTaggedRowOutputFamily at hhead htail ⊢
      rw [List.flatMap_append, hhead, htail]

/-- Canonical post-dispatch tail packets for all verifier transition rows. -/
def verifierTransitionTailInputTarget
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  (verifierTransitionRowSeeds W input).flatMap fun seed =>
    encodeAffineTransitionTail
        (transitionScriptFromSeed W.machine.tm seed
          (seed.rowBase + cfgBitCount W.machine.tm seed.height)) ++
      [.frameEnd]

/-- The routed raw-input stream is the canonical transition-tail target for
the complete verifier family, with exact bytes and row order. -/
theorem verifierTransitionTailPhaseRoutedInput_eq_target
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionTailPhaseRoutedInput W input =
      verifierTransitionTailInputTarget W input := by
  rw [verifierTransitionTailPhaseRoutedInput_eq_rows]
  unfold verifierTransitionTailPhaseTaggedRows
    verifierTransitionTailInputTarget
  apply transitionTailPhaseTaggedRows_output
  intro seed hseed
  rw [verifierTransitionRowSeeds_height_eq W input seed hseed]
  exact Nat.add_pos_left
    (verifierHeight_eval_pos W input.length)
    (maxPushesPerStep W.machine.tm)

/-- A fixed polynomial-time TM2 compiles the canonical post-dispatch tail of
every local transition directly from the raw verifier word. -/
noncomputable def verifierTransitionTailInputTarget_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionTailInputTarget W) := by
  let routed :=
    verifierTransitionTailPhaseRoutedInput_computableInPolyTime W
  exact
    { tm := routed.tm
      inputAlphabet := routed.inputAlphabet
      outputAlphabet := routed.outputAlphabet
      time := routed.time
      outputsFun := fun input => by
        have run := routed.outputsFun input
        simpa only [id_eq,
          verifierTransitionTailPhaseRoutedInput_eq_target W input]
          using run }

end CLRS.Chapter34.Turing.CookLevin

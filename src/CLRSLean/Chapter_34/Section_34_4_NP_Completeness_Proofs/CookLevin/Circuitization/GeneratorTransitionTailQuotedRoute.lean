import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionTailQuotedForms
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionTailPhaseRoute

/-!
# Concrete three-way router for quoted transition tails

This is the executable counterpart of the quoted affine form tables.  The
existing phase-coordinate compiler and fixed three-way router are reused;
only their verifier-fixed field and delimiter tables change.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Tag plus the three quoted candidate payload tables. -/
noncomputable def transitionTailQuotedPhaseTaggedForms
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  transitionEqCoordinateTagForm ::
    (transitionTailQuotedPrefixPhaseForms tm ++
      transitionTailQuotedSuffixPhaseForms tm ++
        transitionTailQuotedEqPhaseForms)

@[simp] theorem transitionTailQuotedPhaseTaggedForms_value
    (tm : _root_.Turing.FinTM2) (coordinate : AffineUnaryTripleSeed) :
    affineUnaryTripleMap (transitionTailQuotedPhaseTaggedForms tm)
        coordinate =
      coordinate.first ::
        (affineUnaryTripleMap (transitionTailQuotedPrefixPhaseForms tm)
            coordinate ++
          affineUnaryTripleMap (transitionTailQuotedSuffixPhaseForms tm)
              coordinate ++
            affineUnaryTripleMap transitionTailQuotedEqPhaseForms
              coordinate) := by
  simp [transitionTailQuotedPhaseTaggedForms, transitionEqCoordinateTagForm,
    affineUnaryTripleMap, affineUnaryTripleFormValue, List.map_append,
    List.append_assoc]

theorem transitionTailQuotedPrefixPhaseDelimiters_nonempty
    (tm : _root_.Turing.FinTM2) :
    0 < (transitionTailQuotedPrefixPhaseDelimiters tm).length := by
  simp [transitionTailQuotedPrefixPhaseDelimiters]
  exact transitionTailPrefixPhaseDelimiters_nonempty tm

theorem transitionTailQuotedSuffixPhaseDelimiters_nonempty
    (tm : _root_.Turing.FinTM2) :
    0 < (transitionTailQuotedSuffixPhaseDelimiters tm).length := by
  simp [transitionTailQuotedSuffixPhaseDelimiters]

theorem transitionTailQuotedEqPhaseDelimiters_nonempty :
    0 < transitionTailQuotedEqPhaseDelimiters.length := by
  simp [transitionTailQuotedEqPhaseDelimiters,
    transitionEqInvocationDelimiterTable]

/-- Typed quoted router row denoted by one phase coordinate. -/
noncomputable def transitionTailQuotedPhaseTaggedRow
    (tm : _root_.Turing.FinTM2) (coordinate : AffineUnaryTripleSeed) :
    UnaryFrameThreeWayTaggedRow
      (transitionTailQuotedPrefixPhaseDelimiters tm).length
      (transitionTailQuotedSuffixPhaseDelimiters tm).length
      transitionTailQuotedEqPhaseDelimiters.length :=
  { tag := coordinate.first
    zeroValues := affineUnaryTripleMap
      (transitionTailQuotedPrefixPhaseForms tm) coordinate
    oneValues := affineUnaryTripleMap
      (transitionTailQuotedSuffixPhaseForms tm) coordinate
    manyValues := affineUnaryTripleMap transitionTailQuotedEqPhaseForms
      coordinate
    zero_length := by
      simpa [affineUnaryTripleMap] using
        transitionTailQuotedPrefixPhase_lengths tm
    one_length := by
      simpa [affineUnaryTripleMap] using
        transitionTailQuotedSuffixPhase_lengths tm
    many_length := by
      simpa [affineUnaryTripleMap] using
        transitionTailQuotedEqPhase_lengths }

/-- Quoted router rows for the complete verifier phase-coordinate family. -/
noncomputable def verifierTransitionTailQuotedPhaseTaggedRows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List
      (UnaryFrameThreeWayTaggedRow
        (transitionTailQuotedPrefixPhaseDelimiters W.machine.tm).length
        (transitionTailQuotedSuffixPhaseDelimiters W.machine.tm).length
        transitionTailQuotedEqPhaseDelimiters.length) :=
  ((verifierTransitionRowSeeds W input).flatMap
    (transitionEqPhaseCoordinateSeeds W.machine.tm)).map
      (transitionTailQuotedPhaseTaggedRow W.machine.tm)

/-- Ordinary unary source bytes for all quoted router candidates. -/
noncomputable def verifierTransitionTailQuotedPhaseTaggedValueFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  encodeUnaryFrame
    (affineUnaryTripleMapFamily
      (transitionTailQuotedPhaseTaggedForms W.machine.tm)
      ((verifierTransitionRowSeeds W input).flatMap
        (transitionEqPhaseCoordinateSeeds W.machine.tm)))

private theorem transitionTailQuotedPhaseTaggedValueEncoding
    (tm : _root_.Turing.FinTM2)
    (coordinates : List AffineUnaryTripleSeed) :
    encodeUnaryFrame
        (affineUnaryTripleMapFamily
          (transitionTailQuotedPhaseTaggedForms tm) coordinates) =
      encodeUnaryFrameThreeWayTaggedRowFamily
        (coordinates.map (transitionTailQuotedPhaseTaggedRow tm)) := by
  unfold affineUnaryTripleMapFamily
    encodeUnaryFrameThreeWayTaggedRowFamily
  rw [List.flatMap_map]
  unfold encodeUnaryFrame
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro coordinate _
  rw [transitionTailQuotedPhaseTaggedForms_value]
  rfl

theorem verifierTransitionTailQuotedPhaseTaggedValueFrames_eq_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionTailQuotedPhaseTaggedValueFrames W input =
      encodeUnaryFrameThreeWayTaggedRowFamily
        (verifierTransitionTailQuotedPhaseTaggedRows W input) := by
  unfold verifierTransitionTailQuotedPhaseTaggedValueFrames
    verifierTransitionTailQuotedPhaseTaggedRows
  exact transitionTailQuotedPhaseTaggedValueEncoding W.machine.tm _

/-- A fixed polynomial-time TM2 emits all quoted candidate tables from the
raw verifier word. -/
noncomputable def
    verifierTransitionTailQuotedPhaseTaggedValueFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionTailQuotedPhaseTaggedValueFrames W) := by
  let coordinates :=
    verifierTransitionEqPhaseCoordinateFrameStream_computableInPolyTime W
  let structured : _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineUnaryTripleSeedFamily
      (fun input =>
        (verifierTransitionRowSeeds W input).flatMap
          (transitionEqPhaseCoordinateSeeds W.machine.tm)) :=
    { tm := coordinates.tm
      inputAlphabet := coordinates.inputAlphabet
      outputAlphabet := coordinates.outputAlphabet
      time := coordinates.time
      outputsFun := fun input => by
        have run := coordinates.outputsFun input
        simpa only [id_eq,
          verifierTransitionEqPhaseCoordinateFrameStream_eq_seedEncoding
            W input] using run }
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch structured
      (affineUnaryTripleMapFamily_computableInPolyTime
        (transitionTailQuotedPhaseTaggedForms W.machine.tm))
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [Function.comp_apply, id_eq,
          verifierTransitionTailQuotedPhaseTaggedValueFrames] using run }

/-- Selected quoted tail fields; one literal `frameEnd` remains after every
complete transition row. -/
noncomputable def verifierTransitionTailQuotedRoutedInput
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFrameThreeWayTaggedRows
    (transitionTailQuotedPrefixPhaseDelimiters W.machine.tm)
    (transitionTailQuotedSuffixPhaseDelimiters W.machine.tm)
    transitionTailQuotedEqPhaseDelimiters
    (transitionTailQuotedPrefixPhaseDelimiters_nonempty W.machine.tm)
    (transitionTailQuotedSuffixPhaseDelimiters_nonempty W.machine.tm)
    transitionTailQuotedEqPhaseDelimiters_nonempty
    (verifierTransitionTailQuotedPhaseTaggedValueFrames W input)

theorem verifierTransitionTailQuotedRoutedInput_eq_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionTailQuotedRoutedInput W input =
      encodeUnaryFrameThreeWayTaggedRowOutputFamily
        (transitionTailQuotedPrefixPhaseDelimiters W.machine.tm)
        (transitionTailQuotedSuffixPhaseDelimiters W.machine.tm)
        transitionTailQuotedEqPhaseDelimiters
        (verifierTransitionTailQuotedPhaseTaggedRows W input) := by
  unfold verifierTransitionTailQuotedRoutedInput
  rw [verifierTransitionTailQuotedPhaseTaggedValueFrames_eq_rows]
  exact rewriteUnaryFrameThreeWayTaggedRows_family
    (transitionTailQuotedPrefixPhaseDelimiters W.machine.tm)
    (transitionTailQuotedSuffixPhaseDelimiters W.machine.tm)
    transitionTailQuotedEqPhaseDelimiters
    (transitionTailQuotedPrefixPhaseDelimiters_nonempty W.machine.tm)
    (transitionTailQuotedSuffixPhaseDelimiters_nonempty W.machine.tm)
    transitionTailQuotedEqPhaseDelimiters_nonempty _

/-- The complete selected quoted stream is generated by one fixed
polynomial-time TM2. -/
noncomputable def verifierTransitionTailQuotedRoutedInput_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionTailQuotedRoutedInput W) := by
  let values :=
    verifierTransitionTailQuotedPhaseTaggedValueFrames_computableInPolyTime W
  let router := rewriteUnaryFrameThreeWayTaggedRows_computableInPolyTime
    (transitionTailQuotedPrefixPhaseDelimiters W.machine.tm)
    (transitionTailQuotedSuffixPhaseDelimiters W.machine.tm)
    transitionTailQuotedEqPhaseDelimiters
    (transitionTailQuotedPrefixPhaseDelimiters_nonempty W.machine.tm)
    (transitionTailQuotedSuffixPhaseDelimiters_nonempty W.machine.tm)
    transitionTailQuotedEqPhaseDelimiters_nonempty
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch values router
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [Function.comp_def,
          verifierTransitionTailQuotedRoutedInput] using run }

end CLRS.Chapter34.Turing.CookLevin

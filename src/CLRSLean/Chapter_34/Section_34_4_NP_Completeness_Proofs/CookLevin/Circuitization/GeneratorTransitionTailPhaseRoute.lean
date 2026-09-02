import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionTailPhaseForms
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionEqRowTaggedValues
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameThreeWayTaggedRowRoute
import Mathlib.Tactic

/-!
# Concrete three-way routing of transition-tail phases

Every phase coordinate is expanded to a tag and three fixed-width candidate
payloads.  The reusable router retains the narrowing prefix for tag zero, the
final-conjunction suffix for tag one, and the equality invocation for every
larger tag.  This module connects that finite controller to the raw verifier
input and proves the exact selected-field stream before identifying it with
the canonical transition script in the following module.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- One tag followed by the prefix, suffix, and equality candidate forms. -/
noncomputable def transitionTailPhaseTaggedForms
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  transitionEqCoordinateTagForm ::
    (transitionTailPrefixPhaseForms tm ++
      transitionTailSuffixPhaseForms tm ++ transitionEqInvocationForms)

@[simp] theorem transitionTailPhaseTaggedForms_value
    (tm : _root_.Turing.FinTM2) (coordinate : AffineUnaryTripleSeed) :
    affineUnaryTripleMap (transitionTailPhaseTaggedForms tm) coordinate =
      coordinate.first ::
        (affineUnaryTripleMap (transitionTailPrefixPhaseForms tm) coordinate ++
          affineUnaryTripleMap (transitionTailSuffixPhaseForms tm) coordinate ++
            affineUnaryTripleMap transitionEqInvocationForms coordinate) := by
  simp [transitionTailPhaseTaggedForms, transitionEqCoordinateTagForm,
    affineUnaryTripleMap, affineUnaryTripleFormValue, List.map_append,
    List.append_assoc]

theorem transitionTailPrefixPhaseDelimiters_nonempty
    (tm : _root_.Turing.FinTM2) :
    0 < (transitionTailPrefixPhaseDelimiters tm).length := by
  simp [transitionTailPrefixPhaseDelimiters,
    transitionNarrowNotInvocationDelimiterTable]

theorem transitionTailSuffixPhaseDelimiters_nonempty
    (tm : _root_.Turing.FinTM2) :
    0 < (transitionTailSuffixPhaseDelimiters tm).length := by
  simp [transitionTailSuffixPhaseDelimiters]

/-- Typed router row denoted by one phase coordinate. -/
noncomputable def transitionTailPhaseTaggedRow
    (tm : _root_.Turing.FinTM2) (coordinate : AffineUnaryTripleSeed) :
    UnaryFrameThreeWayTaggedRow
      (transitionTailPrefixPhaseDelimiters tm).length
      (transitionTailSuffixPhaseDelimiters tm).length
      transitionEqInvocationDelimiterTable.length :=
  { tag := coordinate.first
    zeroValues :=
      affineUnaryTripleMap (transitionTailPrefixPhaseForms tm) coordinate
    oneValues :=
      affineUnaryTripleMap (transitionTailSuffixPhaseForms tm) coordinate
    manyValues := affineUnaryTripleMap transitionEqInvocationForms coordinate
    zero_length := by
      rw [show (affineUnaryTripleMap
            (transitionTailPrefixPhaseForms tm) coordinate).length =
          (transitionTailPrefixPhaseForms tm).length by
        simp [affineUnaryTripleMap]]
      exact transitionTailPrefixPhaseForms_delimiters_length tm
    one_length := by
      rw [show (affineUnaryTripleMap
            (transitionTailSuffixPhaseForms tm) coordinate).length =
          (transitionTailSuffixPhaseForms tm).length by
        simp [affineUnaryTripleMap]]
      exact transitionTailSuffixPhaseForms_delimiters_length tm
    many_length := by
      simp [affineUnaryTripleMap] }

/-- Router rows for the complete raw-input phase-coordinate family. -/
noncomputable def verifierTransitionTailPhaseTaggedRows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List
      (UnaryFrameThreeWayTaggedRow
        (transitionTailPrefixPhaseDelimiters W.machine.tm).length
        (transitionTailSuffixPhaseDelimiters W.machine.tm).length
        transitionEqInvocationDelimiterTable.length) :=
  ((verifierTransitionRowSeeds W input).flatMap
    (transitionEqPhaseCoordinateSeeds W.machine.tm)).map
      (transitionTailPhaseTaggedRow W.machine.tm)

/-- Ordinary unary source bytes obtained by applying the complete candidate
form table to every phase coordinate. -/
noncomputable def verifierTransitionTailPhaseTaggedValueFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  encodeUnaryFrame
    (affineUnaryTripleMapFamily
      (transitionTailPhaseTaggedForms W.machine.tm)
      ((verifierTransitionRowSeeds W input).flatMap
        (transitionEqPhaseCoordinateSeeds W.machine.tm)))

private theorem transitionTailPhaseTaggedValueEncoding
    (tm : _root_.Turing.FinTM2)
    (coordinates : List AffineUnaryTripleSeed) :
    encodeUnaryFrame
        (affineUnaryTripleMapFamily (transitionTailPhaseTaggedForms tm)
          coordinates) =
      encodeUnaryFrameThreeWayTaggedRowFamily
        (coordinates.map (transitionTailPhaseTaggedRow tm)) := by
  unfold affineUnaryTripleMapFamily
    encodeUnaryFrameThreeWayTaggedRowFamily
  rw [List.flatMap_map]
  unfold encodeUnaryFrame
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro coordinate _
  rw [transitionTailPhaseTaggedForms_value]
  rfl

/-- The affine-map source is literally the typed family encoding consumed by
the finite router. -/
theorem verifierTransitionTailPhaseTaggedValueFrames_eq_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionTailPhaseTaggedValueFrames W input =
      encodeUnaryFrameThreeWayTaggedRowFamily
        (verifierTransitionTailPhaseTaggedRows W input) := by
  unfold verifierTransitionTailPhaseTaggedValueFrames
    verifierTransitionTailPhaseTaggedRows
  exact transitionTailPhaseTaggedValueEncoding W.machine.tm _

/-- One fixed polynomial-time TM2 emits the three candidate payloads for
every phase coordinate directly from the raw verifier word. -/
noncomputable def
    verifierTransitionTailPhaseTaggedValueFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionTailPhaseTaggedValueFrames W) := by
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
        (transitionTailPhaseTaggedForms W.machine.tm))
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [Function.comp_apply, id_eq,
          verifierTransitionTailPhaseTaggedValueFrames] using run }

/-- Selected transition-tail fields after the concrete three-way router. -/
noncomputable def verifierTransitionTailPhaseRoutedInput
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFrameThreeWayTaggedRows
    (transitionTailPrefixPhaseDelimiters W.machine.tm)
    (transitionTailSuffixPhaseDelimiters W.machine.tm)
    transitionEqInvocationDelimiterTable
    (transitionTailPrefixPhaseDelimiters_nonempty W.machine.tm)
    (transitionTailSuffixPhaseDelimiters_nonempty W.machine.tm)
    transitionEqInvocationDelimiterTable_nonempty
    (verifierTransitionTailPhaseTaggedValueFrames W input)

/-- Exact typed semantics of the routed raw-input stream. -/
theorem verifierTransitionTailPhaseRoutedInput_eq_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionTailPhaseRoutedInput W input =
      encodeUnaryFrameThreeWayTaggedRowOutputFamily
        (transitionTailPrefixPhaseDelimiters W.machine.tm)
        (transitionTailSuffixPhaseDelimiters W.machine.tm)
        transitionEqInvocationDelimiterTable
        (verifierTransitionTailPhaseTaggedRows W input) := by
  unfold verifierTransitionTailPhaseRoutedInput
  rw [verifierTransitionTailPhaseTaggedValueFrames_eq_rows]
  exact rewriteUnaryFrameThreeWayTaggedRows_family
    (transitionTailPrefixPhaseDelimiters W.machine.tm)
    (transitionTailSuffixPhaseDelimiters W.machine.tm)
    transitionEqInvocationDelimiterTable
    (transitionTailPrefixPhaseDelimiters_nonempty W.machine.tm)
    (transitionTailSuffixPhaseDelimiters_nonempty W.machine.tm)
    transitionEqInvocationDelimiterTable_nonempty _

/-- The complete selected phase stream is generated from the raw verifier
word by one fixed polynomial-time TM2. -/
noncomputable def
    verifierTransitionTailPhaseRoutedInput_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionTailPhaseRoutedInput W) := by
  let values :=
    verifierTransitionTailPhaseTaggedValueFrames_computableInPolyTime W
  let router := rewriteUnaryFrameThreeWayTaggedRows_computableInPolyTime
    (transitionTailPrefixPhaseDelimiters W.machine.tm)
    (transitionTailSuffixPhaseDelimiters W.machine.tm)
    transitionEqInvocationDelimiterTable
    (transitionTailPrefixPhaseDelimiters_nonempty W.machine.tm)
    (transitionTailSuffixPhaseDelimiters_nonempty W.machine.tm)
    transitionEqInvocationDelimiterTable_nonempty
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
          verifierTransitionTailPhaseRoutedInput] using run }

end CLRS.Chapter34.Turing.CookLevin

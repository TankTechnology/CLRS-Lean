import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionEqRowSentinel
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionEqSegmentAlignment
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameZeroTagRowDemux
import Mathlib.Tactic

/-!
# Tagged transition equality rows

The marked coordinate source ends every tableau row with the fixed coordinate
`(0, 0, 0)`.  This module prefixes every equality payload by its first
coordinate.  Real equality coordinates have a positive first coordinate,
whereas the sentinel has tag zero.  A reusable finite-state pass can therefore
drop real tags and turn precisely the sentinels into outer `frameEnd`s.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- The first coordinate, used as a zero-versus-positive row tag. -/
def transitionEqCoordinateTagForm : AffineUnaryTripleForm :=
  { constant := 0, first := 1, second := 0, third := 0 }

/-- One tag followed by the nine ordinary equality invocation operands. -/
def transitionEqTaggedInvocationForms : List AffineUnaryTripleForm :=
  transitionEqCoordinateTagForm :: transitionEqInvocationForms

@[simp] theorem transitionEqTaggedInvocationForms_value
    (seed : AffineUnaryTripleSeed) :
    affineUnaryTripleMap transitionEqTaggedInvocationForms seed =
      seed.first ::
        affineUnaryTripleMap transitionEqInvocationForms seed := by
  simp [transitionEqTaggedInvocationForms,
    transitionEqCoordinateTagForm, affineUnaryTripleMap,
    affineUnaryTripleFormValue]

@[simp] theorem transitionEqInvocationForms_length :
    transitionEqInvocationForms.length = 9 := rfl

private theorem encodeUnaryFrame_flatMap {alpha : Type}
    (items : List alpha) (values : alpha → List Nat) :
    encodeUnaryFrame (items.flatMap values) =
      items.flatMap fun item => encodeUnaryFrame (values item) := by
  unfold encodeUnaryFrame
  rw [List.flatMap_assoc]

private theorem transitionEqTaggedValueEncoding
    (coordinates : List AffineUnaryTripleSeed) :
    encodeUnaryFrame
        (affineUnaryTripleMapFamily transitionEqTaggedInvocationForms
          coordinates) =
      (coordinates.map fun coordinate =>
        (coordinate.first,
          affineUnaryTripleMap transitionEqInvocationForms coordinate)).flatMap
        fun row => encodeUnaryFrame (row.1 :: row.2) := by
  unfold affineUnaryTripleMapFamily
  rw [encodeUnaryFrame_flatMap]
  simp only [List.flatMap_map]
  apply List.flatMap_congr
  intro coordinate _
  rw [transitionEqTaggedInvocationForms_value]

/-- Every semantic equality coordinate is distinguishable from the zero
sentinel by its first component. -/
theorem transitionEqCoordinateSeed_first_pos
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (coordinate : AffineUnaryTripleSeed)
    (hcoordinate : coordinate ∈ transitionEqCoordinateSeeds tm seed)
    (hwork : 0 < workHeight tm seed.height) :
    0 < coordinate.first := by
  rw [transitionEqCoordinateSeeds_eq_slots tm seed hwork] at hcoordinate
  simp only [List.mem_map] at hcoordinate
  rcases hcoordinate with ⟨slot, _, rfl⟩
  simp only [transitionEqSlotSeed, transitionEqStart,
    transitionNarrowStart]
  omega

/-- Raw tagged values obtained by applying one fixed affine form table to all
row-marked coordinate seeds. -/
noncomputable def verifierTransitionEqRowTaggedValueFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  encodeUnaryFrame
    (affineUnaryTripleMapFamily transitionEqTaggedInvocationForms
      ((verifierTransitionRowSeeds W input).flatMap
        (transitionEqRowMarkedCoordinateSeeds W.machine.tm)))

/-- Typed tagged-row family consumed by the generic zero-tag demultiplexer. -/
noncomputable def verifierTransitionEqTaggedRowFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFrameZeroTagRowFamily 9 :=
  { rows := (verifierTransitionRowSeeds W input).flatMap fun seed =>
      (transitionEqRowMarkedCoordinateSeeds W.machine.tm seed).map fun
        coordinate =>
          (coordinate.first,
            affineUnaryTripleMap transitionEqInvocationForms coordinate)
    payload_lengths := by
      intro row hrow
      simp only [List.mem_flatMap, List.mem_map] at hrow
      rcases hrow with ⟨seed, _, coordinate, _, rfl⟩
      simp [affineUnaryTripleMap] }

/-- The affine-map output is literally the typed family encoding expected by
the demultiplexer. -/
theorem verifierTransitionEqRowTaggedValueFrames_eq_family
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionEqRowTaggedValueFrames W input =
      encodeUnaryFrameZeroTagRowFamily
        (verifierTransitionEqTaggedRowFamily W input) := by
  unfold verifierTransitionEqRowTaggedValueFrames
    verifierTransitionEqTaggedRowFamily
    encodeUnaryFrameZeroTagRowFamily
  rw [transitionEqTaggedValueEncoding, List.map_flatMap]

/-- One fixed polynomial-time TM2 emits all tagged rows directly from the raw
verifier input. -/
noncomputable def
    verifierTransitionEqRowTaggedValueFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionEqRowTaggedValueFrames W) := by
  let coordinates :=
    verifierTransitionEqRowMarkedCoordinateFrameStream_computableInPolyTime W
  let structured : _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineUnaryTripleSeedFamily
      (fun input =>
        (verifierTransitionRowSeeds W input).flatMap
          (transitionEqRowMarkedCoordinateSeeds W.machine.tm)) :=
    { tm := coordinates.tm
      inputAlphabet := coordinates.inputAlphabet
      outputAlphabet := coordinates.outputAlphabet
      time := coordinates.time
      outputsFun := fun input => by
        have run := coordinates.outputsFun input
        simpa only [id_eq,
          verifierTransitionEqRowMarkedCoordinateFrameStream_eq_seedEncoding
            W input] using run }
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch structured
      (affineUnaryTripleMapFamily_computableInPolyTime
        transitionEqTaggedInvocationForms)
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [Function.comp_apply, id_eq,
          verifierTransitionEqRowTaggedValueFrames] using run }

/-- Drop positive coordinate tags and materialize zero sentinels as outer row
boundaries. -/
noncomputable def verifierTransitionEqRowMarkedValueFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFrameZeroTagRows 9
    (verifierTransitionEqRowTaggedValueFrames W input)

private theorem transitionEqRealTaggedRows_output
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    ((transitionEqCoordinateSeeds tm seed).map fun coordinate =>
        (coordinate.first,
          affineUnaryTripleMap transitionEqInvocationForms coordinate)).flatMap
        (fun row =>
          if row.1 = 0 then [.frameEnd]
          else encodeUnaryFrame row.2) =
      encodeUnaryFrame
        (affineUnaryTripleMapFamily transitionEqInvocationForms
          (transitionEqCoordinateSeeds tm seed)) := by
  unfold affineUnaryTripleMapFamily
  rw [encodeUnaryFrame_flatMap]
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro coordinate hcoordinate
  have hpositive := transitionEqCoordinateSeed_first_pos tm seed coordinate
    hcoordinate hwork
  simp [hpositive.ne']

private theorem transitionEqMarkedTaggedRows_output
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    ((transitionEqRowMarkedCoordinateSeeds tm seed).map fun coordinate =>
        (coordinate.first,
          affineUnaryTripleMap transitionEqInvocationForms coordinate)).flatMap
        (fun row =>
          if row.1 = 0 then [.frameEnd]
          else encodeUnaryFrame row.2) =
      encodeUnaryFrame
          (affineUnaryTripleMapFamily transitionEqInvocationForms
            (transitionEqCoordinateSeeds tm seed)) ++
        [.frameEnd] := by
  unfold transitionEqRowMarkedCoordinateSeeds
  rw [List.map_append, List.flatMap_append,
    transitionEqRealTaggedRows_output tm seed hwork]
  simp [transitionEqSentinelCoordinateSeed]

/-- Exact row-major semantics after demultiplexing: nine ordinary operand
fields per equality frame and one explicit `frameEnd` after every tableau
row. -/
theorem verifierTransitionEqRowMarkedValueFrames_eq_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionEqRowMarkedValueFrames W input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        encodeUnaryFrame
            (affineUnaryTripleMapFamily transitionEqInvocationForms
              (transitionEqCoordinateSeeds W.machine.tm seed)) ++
          [.frameEnd] := by
  unfold verifierTransitionEqRowMarkedValueFrames
  rw [verifierTransitionEqRowTaggedValueFrames_eq_family,
    rewriteUnaryFrameZeroTagRows_family
      (verifierTransitionEqTaggedRowFamily W input) (by omega)]
  unfold encodeUnaryFrameZeroTagRowOutput
    verifierTransitionEqTaggedRowFamily
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro seed hseed
  apply transitionEqMarkedTaggedRows_output
  rw [verifierTransitionRowSeeds_height_eq W input seed hseed]
  exact Nat.add_pos_left
    (verifierHeight_eval_pos W input.length)
    (maxPushesPerStep W.machine.tm)

/-- The row-marked ordinary equality values are generated by one fixed
polynomial-time TM2 from the raw verifier word. -/
noncomputable def
    verifierTransitionEqRowMarkedValueFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionEqRowMarkedValueFrames W) := by
  let tagged :=
    verifierTransitionEqRowTaggedValueFrames_computableInPolyTime W
  let demux := rewriteUnaryFrameZeroTagRows_computableInPolyTime 9
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch tagged demux
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [Function.comp_def,
          verifierTransitionEqRowMarkedValueFrames] using run }

end CLRS.Chapter34.Turing.CookLevin

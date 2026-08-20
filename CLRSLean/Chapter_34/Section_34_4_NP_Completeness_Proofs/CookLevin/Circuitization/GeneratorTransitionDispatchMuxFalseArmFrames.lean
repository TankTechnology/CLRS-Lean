import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxFalseArmAffine

/-!
# Concrete raw-input source for dispatch-mux false arms

This module evaluates and executes the combined widened/preceding-output
progression table.  A final fixed affine projection emits exactly every
`whenFalse` operand of every label-local mux frame, in row-major order.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Coordinate seeds of the complete false-arm progression family. -/
def transitionDispatchFalseArmCoordinateSeeds
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List AffineUnaryTripleSeed :=
  (transitionDispatchFalseArmProgressions tm seed).flatMap fun progression =>
    (affineUnaryTripleProgressionRows progression).map
      transitionWidenedFallbackCoordinateSeed

private theorem transitionDispatchFalseArm_rows_projection
    (rows : List (Nat × Nat × Nat)) :
    (rows.map transitionWidenedFallbackCoordinateSeed).flatMap
        (affineUnaryTripleMap [transitionWidenedFallbackOutputForm]) =
      rows.map fun row => row.1 := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      rcases row with ⟨first, second, third⟩
      simp [transitionWidenedFallbackCoordinateSeed, ih]

/-- Projecting all generated coordinates gives the concatenated first-track
values of the complete false-arm progression family. -/
theorem transitionDispatchFalseArmCoordinateSeeds_projection
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    affineUnaryTripleMapFamily [transitionWidenedFallbackOutputForm]
        (transitionDispatchFalseArmCoordinateSeeds tm seed) =
      (transitionDispatchFalseArmProgressions tm seed).flatMap
        transitionProgressionFirstValues := by
  unfold affineUnaryTripleMapFamily
    transitionDispatchFalseArmCoordinateSeeds
    transitionProgressionFirstValues
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro progression hprogression
  exact transitionDispatchFalseArm_rows_projection
    (affineUnaryTripleProgressionRows progression)

/-- Raw-input descriptors for all false-arm progressions of all rows. -/
noncomputable def verifierTransitionDispatchFalseArmDescriptorFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  verifierTransitionAffineMapFrames W
    (transitionDispatchFalseArmDescriptorForms W.machine.tm) input

theorem verifierTransitionDispatchFalseArmDescriptorFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchFalseArmDescriptorFrames W input =
      encodeAffineUnaryTripleProgressionFamily
        ((verifierTransitionRowSeeds W input).flatMap
          (transitionDispatchFalseArmProgressions W.machine.tm)) := by
  unfold verifierTransitionDispatchFalseArmDescriptorFrames
    verifierTransitionAffineMapFrames verifierTransitionTailAffineSeeds
    affineUnaryTripleMapFamily encodeUnaryFrame
  rw [List.flatMap_map]
  generalize verifierTransitionRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [List.flatMap_cons, List.flatMap_append]
      have hseed := encode_transitionDispatchFalseArmDescriptorForms
        W.machine.tm seed
      unfold encodeUnaryFrame at hseed
      rw [hseed, ih]
      induction transitionDispatchFalseArmProgressions W.machine.tm seed with
      | nil => rfl
      | cons progression progressions progressionIh =>
          simp [encodeAffineUnaryTripleProgressionFamily, progressionIh]

noncomputable def
    verifierTransitionDispatchFalseArmDescriptorFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchFalseArmDescriptorFrames W) := by
  exact verifierTransitionAffineMapFrames_computableInPolyTime W
    (transitionDispatchFalseArmDescriptorForms W.machine.tm)

private theorem falseArm_progressionFrameStream_eq_seedEncoding
    (progression : AffineUnaryTripleProgression) :
    affineUnaryTripleProgressionFrameStream progression =
      encodeAffineUnaryTripleSeedFamily
        ((affineUnaryTripleProgressionRows progression).map
          transitionWidenedFallbackCoordinateSeed) := by
  unfold affineUnaryTripleProgressionFrameStream
  generalize affineUnaryTripleProgressionRows progression = rows
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      rcases row with ⟨first, second, third⟩
      simp only [List.flatMap_cons, List.map_cons,
        encodeAffineUnaryTripleSeedFamily]
      rw [ih]
      rfl

private theorem falseArm_progressionFamilyFrameStream_append
    (left right : List AffineUnaryTripleProgression) :
    affineUnaryTripleProgressionFamilyFrameStream (left ++ right) =
      affineUnaryTripleProgressionFamilyFrameStream left ++
        affineUnaryTripleProgressionFamilyFrameStream right := by
  induction left with
  | nil => rfl
  | cons progression rest ih =>
      simp [affineUnaryTripleProgressionFamilyFrameStream, ih,
        List.append_assoc]

private theorem falseArm_affineSeedFamily_append
    (left right : List AffineUnaryTripleSeed) :
    encodeAffineUnaryTripleSeedFamily (left ++ right) =
      encodeAffineUnaryTripleSeedFamily left ++
        encodeAffineUnaryTripleSeedFamily right := by
  induction left with
  | nil => rfl
  | cons seed rest ih =>
      simp [encodeAffineUnaryTripleSeedFamily, ih, List.append_assoc]

theorem transitionDispatchFalseArmProgressionFrameStream_eq_coordinateSeeds
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    affineUnaryTripleProgressionFamilyFrameStream
        (transitionDispatchFalseArmProgressions tm seed) =
      encodeAffineUnaryTripleSeedFamily
        (transitionDispatchFalseArmCoordinateSeeds tm seed) := by
  unfold transitionDispatchFalseArmCoordinateSeeds
  induction transitionDispatchFalseArmProgressions tm seed with
  | nil => rfl
  | cons progression rest ih =>
      simp only [affineUnaryTripleProgressionFamilyFrameStream,
        List.flatMap_cons]
      rw [falseArm_progressionFrameStream_eq_seedEncoding, ih]
      exact (falseArm_affineSeedFamily_append _ _).symm

noncomputable def verifierTransitionDispatchFalseArmCoordinateFrameStream
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  affineUnaryTripleProgressionFamilyFrameStream
    ((verifierTransitionRowSeeds W input).flatMap
      (transitionDispatchFalseArmProgressions W.machine.tm))

theorem verifierTransitionDispatchFalseArmCoordinateFrameStream_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchFalseArmCoordinateFrameStream W input =
      encodeAffineUnaryTripleSeedFamily
        ((verifierTransitionRowSeeds W input).flatMap
          (transitionDispatchFalseArmCoordinateSeeds W.machine.tm)) := by
  unfold verifierTransitionDispatchFalseArmCoordinateFrameStream
  generalize verifierTransitionRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [List.flatMap_cons]
      rw [falseArm_progressionFamilyFrameStream_append,
        transitionDispatchFalseArmProgressionFrameStream_eq_coordinateSeeds,
        ih, falseArm_affineSeedFamily_append]

noncomputable def
    verifierTransitionDispatchFalseArmCoordinateFrameStream_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchFalseArmCoordinateFrameStream W) := by
  let descriptors :=
    verifierTransitionDispatchFalseArmDescriptorFrames_computableInPolyTime W
  let structured : _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineUnaryTripleProgressionFamily
      (fun input =>
        (verifierTransitionRowSeeds W input).flatMap
          (transitionDispatchFalseArmProgressions W.machine.tm)) :=
    { tm := descriptors.tm
      inputAlphabet := descriptors.inputAlphabet
      outputAlphabet := descriptors.outputAlphabet
      time := descriptors.time
      outputsFun := fun input => by
        have run := descriptors.outputsFun input
        simpa only [id_eq,
          verifierTransitionDispatchFalseArmDescriptorFrames_eq W input]
          using run }
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch structured
      affineUnaryTripleProgressionFamilyFrameStream_computableInPolyTime
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [Function.comp_apply, id_eq,
          verifierTransitionDispatchFalseArmCoordinateFrameStream] using run }

/-- Raw-input unary values for every false arm of every dispatch mux. -/
noncomputable def verifierTransitionDispatchFalseArmValueFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  encodeUnaryFrame
    (affineUnaryTripleMapFamily [transitionWidenedFallbackOutputForm]
      ((verifierTransitionRowSeeds W input).flatMap
        (transitionDispatchFalseArmCoordinateSeeds W.machine.tm)))

/-- Exact semantic artifact contract of the generated false-arm values. -/
theorem verifierTransitionDispatchFalseArmValueFrames_eq_artifacts
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchFalseArmValueFrames W input =
      encodeUnaryFrame
        ((verifierTransitionRowSeeds W input).flatMap fun seed =>
          ((transitionDispatchArtifactsFromSeed W.machine.tm seed).map
            TransitionDispatchLabelArtifact.muxFalseInputValues).flatten) := by
  unfold verifierTransitionDispatchFalseArmValueFrames
    affineUnaryTripleMapFamily
  congr 1
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro seed hseed
  change affineUnaryTripleMapFamily [transitionWidenedFallbackOutputForm]
      (transitionDispatchFalseArmCoordinateSeeds W.machine.tm seed) = _
  rw [transitionDispatchFalseArmCoordinateSeeds_projection]
  rw [transitionDispatchFalseArmProgressions_values]
  · rw [transitionDispatchArtifactsFromSeed_falseArmRows]
  · have hheight := verifierTransitionRowSeeds_height_eq W input seed hseed
    rw [hheight]
    unfold workHeight
    exact Nat.add_pos_left (verifierHeight_eval_pos W input.length) _

/-- A fixed polynomial-time TM2 generates the exact semantic false-arm
operand stream from the raw verifier word. -/
noncomputable def
    verifierTransitionDispatchFalseArmValueFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchFalseArmValueFrames W) := by
  let coordinates :=
    verifierTransitionDispatchFalseArmCoordinateFrameStream_computableInPolyTime W
  let structured : _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineUnaryTripleSeedFamily
      (fun input =>
        (verifierTransitionRowSeeds W input).flatMap
          (transitionDispatchFalseArmCoordinateSeeds W.machine.tm)) :=
    { tm := coordinates.tm
      inputAlphabet := coordinates.inputAlphabet
      outputAlphabet := coordinates.outputAlphabet
      time := coordinates.time
      outputsFun := fun input => by
        have run := coordinates.outputsFun input
        simpa only [id_eq,
          verifierTransitionDispatchFalseArmCoordinateFrameStream_eq W input]
          using run }
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch structured
      (affineUnaryTripleMapFamily_computableInPolyTime
        [transitionWidenedFallbackOutputForm])
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [Function.comp_apply, id_eq,
          verifierTransitionDispatchFalseArmValueFrames] using run }

end CLRS.Chapter34.Turing.CookLevin

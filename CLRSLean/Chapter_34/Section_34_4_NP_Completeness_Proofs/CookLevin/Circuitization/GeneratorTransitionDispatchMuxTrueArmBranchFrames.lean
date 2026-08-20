import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxTrueArmBranchAffine

/-!
# Concrete raw-input source for branch-ending true arms

This module executes the fixed branch-output descriptor table.  From the raw
verifier word, one fixed polynomial-time TM2 emits exactly the flattened
`whenTrue` rows whose statement spine terminates in `branch`.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Coordinate seeds of all branch-ending output progressions in one row. -/
def transitionDispatchBranchOutputCoordinateSeeds
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List AffineUnaryTripleSeed :=
  (transitionDispatchBranchOutputProgressions tm seed).flatMap
    fun progression =>
      (affineUnaryTripleProgressionRows progression).map
        transitionWidenedFallbackCoordinateSeed

private theorem branchOutput_rows_projection
    (rows : List (Nat × Nat × Nat)) :
    (rows.map transitionWidenedFallbackCoordinateSeed).flatMap
        (affineUnaryTripleMap [transitionWidenedFallbackOutputForm]) =
      rows.map fun row => row.1 := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      rcases row with ⟨first, second, third⟩
      simp [transitionWidenedFallbackCoordinateSeed, ih]

/-- Projecting the expanded coordinates recovers the concatenated first
tracks of all branch output progressions. -/
theorem transitionDispatchBranchOutputCoordinateSeeds_projection
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    affineUnaryTripleMapFamily [transitionWidenedFallbackOutputForm]
        (transitionDispatchBranchOutputCoordinateSeeds tm seed) =
      (transitionDispatchBranchOutputProgressions tm seed).flatMap
        transitionProgressionFirstValues := by
  unfold affineUnaryTripleMapFamily
    transitionDispatchBranchOutputCoordinateSeeds
    transitionProgressionFirstValues
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro progression hprogression
  exact branchOutput_rows_projection
    (affineUnaryTripleProgressionRows progression)

/-- Raw-input descriptors for all branch-ending true-arm progressions. -/
noncomputable def verifierTransitionDispatchBranchTrueArmDescriptorFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  verifierTransitionAffineMapFrames W
    (transitionDispatchBranchOutputDescriptorForms W.machine.tm) input

theorem verifierTransitionDispatchBranchTrueArmDescriptorFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchBranchTrueArmDescriptorFrames W input =
      encodeAffineUnaryTripleProgressionFamily
        ((verifierTransitionRowSeeds W input).flatMap
          (transitionDispatchBranchOutputProgressions W.machine.tm)) := by
  unfold verifierTransitionDispatchBranchTrueArmDescriptorFrames
    verifierTransitionAffineMapFrames verifierTransitionTailAffineSeeds
    affineUnaryTripleMapFamily encodeUnaryFrame
  rw [List.flatMap_map]
  generalize verifierTransitionRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [List.flatMap_cons, List.flatMap_append]
      have hseed := encode_transitionDispatchBranchOutputDescriptorForms
        W.machine.tm seed
      unfold encodeUnaryFrame at hseed
      rw [hseed, ih]
      induction transitionDispatchBranchOutputProgressions
          W.machine.tm seed with
      | nil => rfl
      | cons progression progressions progressionIh =>
          simp [encodeAffineUnaryTripleProgressionFamily, progressionIh]

noncomputable def
    verifierTransitionDispatchBranchTrueArmDescriptorFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchBranchTrueArmDescriptorFrames W) := by
  exact verifierTransitionAffineMapFrames_computableInPolyTime W
    (transitionDispatchBranchOutputDescriptorForms W.machine.tm)

private theorem branchOutput_progressionFrameStream_eq_seedEncoding
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

private theorem branchOutput_progressionFamilyFrameStream_append
    (left right : List AffineUnaryTripleProgression) :
    affineUnaryTripleProgressionFamilyFrameStream (left ++ right) =
      affineUnaryTripleProgressionFamilyFrameStream left ++
        affineUnaryTripleProgressionFamilyFrameStream right := by
  induction left with
  | nil => rfl
  | cons progression rest ih =>
      simp [affineUnaryTripleProgressionFamilyFrameStream, ih,
        List.append_assoc]

private theorem branchOutput_affineSeedFamily_append
    (left right : List AffineUnaryTripleSeed) :
    encodeAffineUnaryTripleSeedFamily (left ++ right) =
      encodeAffineUnaryTripleSeedFamily left ++
        encodeAffineUnaryTripleSeedFamily right := by
  induction left with
  | nil => rfl
  | cons seed rest ih =>
      simp [encodeAffineUnaryTripleSeedFamily, ih, List.append_assoc]

theorem transitionDispatchBranchOutputProgressionFrameStream_eq_coordinateSeeds
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    affineUnaryTripleProgressionFamilyFrameStream
        (transitionDispatchBranchOutputProgressions tm seed) =
      encodeAffineUnaryTripleSeedFamily
        (transitionDispatchBranchOutputCoordinateSeeds tm seed) := by
  unfold transitionDispatchBranchOutputCoordinateSeeds
  induction transitionDispatchBranchOutputProgressions tm seed with
  | nil => rfl
  | cons progression rest ih =>
      simp only [affineUnaryTripleProgressionFamilyFrameStream,
        List.flatMap_cons]
      rw [branchOutput_progressionFrameStream_eq_seedEncoding, ih]
      exact (branchOutput_affineSeedFamily_append _ _).symm

/-- Expanded coordinate frames for all branch-ending true arms. -/
noncomputable def verifierTransitionDispatchBranchTrueArmCoordinateFrameStream
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  affineUnaryTripleProgressionFamilyFrameStream
    ((verifierTransitionRowSeeds W input).flatMap
      (transitionDispatchBranchOutputProgressions W.machine.tm))

theorem verifierTransitionDispatchBranchTrueArmCoordinateFrameStream_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchBranchTrueArmCoordinateFrameStream W input =
      encodeAffineUnaryTripleSeedFamily
        ((verifierTransitionRowSeeds W input).flatMap
          (transitionDispatchBranchOutputCoordinateSeeds W.machine.tm)) := by
  unfold verifierTransitionDispatchBranchTrueArmCoordinateFrameStream
  generalize verifierTransitionRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [List.flatMap_cons]
      rw [branchOutput_progressionFamilyFrameStream_append,
        transitionDispatchBranchOutputProgressionFrameStream_eq_coordinateSeeds,
        ih, branchOutput_affineSeedFamily_append]

noncomputable def
    verifierTransitionDispatchBranchTrueArmCoordinateFrameStream_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchBranchTrueArmCoordinateFrameStream W) := by
  let descriptors :=
    verifierTransitionDispatchBranchTrueArmDescriptorFrames_computableInPolyTime W
  let structured : _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineUnaryTripleProgressionFamily
      (fun input =>
        (verifierTransitionRowSeeds W input).flatMap
          (transitionDispatchBranchOutputProgressions W.machine.tm)) :=
    { tm := descriptors.tm
      inputAlphabet := descriptors.inputAlphabet
      outputAlphabet := descriptors.outputAlphabet
      time := descriptors.time
      outputsFun := fun input => by
        have run := descriptors.outputsFun input
        simpa only [id_eq,
          verifierTransitionDispatchBranchTrueArmDescriptorFrames_eq W input]
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
          verifierTransitionDispatchBranchTrueArmCoordinateFrameStream]
          using run }

/-- Raw-input unary values for every branch-ending true arm. -/
noncomputable def verifierTransitionDispatchBranchTrueArmValueFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  encodeUnaryFrame
    (affineUnaryTripleMapFamily [transitionWidenedFallbackOutputForm]
      ((verifierTransitionRowSeeds W input).flatMap
        (transitionDispatchBranchOutputCoordinateSeeds W.machine.tm)))

/-- Exact semantic contract of the generated branch-ending true-arm values. -/
theorem verifierTransitionDispatchBranchTrueArmValueFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchBranchTrueArmValueFrames W input =
      encodeUnaryFrame
        ((verifierTransitionRowSeeds W input).flatMap fun seed =>
          (transitionDispatchBranchTrueArmRows W.machine.tm seed).flatten) := by
  unfold verifierTransitionDispatchBranchTrueArmValueFrames
    affineUnaryTripleMapFamily
  congr 1
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro seed hseed
  change affineUnaryTripleMapFamily [transitionWidenedFallbackOutputForm]
      (transitionDispatchBranchOutputCoordinateSeeds W.machine.tm seed) = _
  rw [transitionDispatchBranchOutputCoordinateSeeds_projection]
  rw [transitionDispatchBranchOutputProgressions_values]
  have hheight := verifierTransitionRowSeeds_height_eq W input seed hseed
  rw [hheight]
  unfold workHeight
  exact Nat.add_pos_left (verifierHeight_eval_pos W input.length) _

/-- A fixed polynomial-time TM2 generates the exact branch-ending true-arm
operand stream from the raw verifier word. -/
noncomputable def
    verifierTransitionDispatchBranchTrueArmValueFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchBranchTrueArmValueFrames W) := by
  let coordinates :=
    verifierTransitionDispatchBranchTrueArmCoordinateFrameStream_computableInPolyTime W
  let structured : _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineUnaryTripleSeedFamily
      (fun input =>
        (verifierTransitionRowSeeds W input).flatMap
          (transitionDispatchBranchOutputCoordinateSeeds W.machine.tm)) :=
    { tm := coordinates.tm
      inputAlphabet := coordinates.inputAlphabet
      outputAlphabet := coordinates.outputAlphabet
      time := coordinates.time
      outputsFun := fun input => by
        have run := coordinates.outputsFun input
        simpa only [id_eq,
          verifierTransitionDispatchBranchTrueArmCoordinateFrameStream_eq W
            input] using run }
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
          verifierTransitionDispatchBranchTrueArmValueFrames] using run }

end CLRS.Chapter34.Turing.CookLevin

import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionWidenedFallbackAffineCorrectness

/-!
# Concrete widened-fallback source from the raw verifier input

The fixed affine table is evaluated over every transition-row seed, executed
by the generic progression-family controller, and projected to its first
track.  The resulting fixed polynomial-time TM2 emits exactly the canonical
widened source row used as the first dispatch label's false arm.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Repackage one progression row for the generic affine map controller. -/
def transitionWidenedFallbackCoordinateSeed
    (row : Nat × Nat × Nat) : AffineUnaryTripleSeed :=
  { first := row.1, second := row.2.1, third := row.2.2 }

/-- Coordinate seeds emitted by all fixed fallback segments of one row. -/
def transitionWidenedFallbackCoordinateSeeds
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List AffineUnaryTripleSeed :=
  (transitionWidenedFallbackProgressions tm seed).flatMap fun progression =>
    (affineUnaryTripleProgressionRows progression).map
      transitionWidenedFallbackCoordinateSeed

/-- Project the first track, which carries the actual fallback wire. -/
def transitionWidenedFallbackOutputForm : AffineUnaryTripleForm :=
  { constant := 0, first := 1, second := 0, third := 0 }

@[simp] theorem transitionWidenedFallbackOutputForm_value
    (seed : AffineUnaryTripleSeed) :
    affineUnaryTripleMap [transitionWidenedFallbackOutputForm] seed =
      [seed.first] := by
  simp [transitionWidenedFallbackOutputForm, affineUnaryTripleMap,
    affineUnaryTripleFormValue]

private theorem transitionWidenedFallback_rows_projection
    (rows : List (Nat × Nat × Nat)) :
    (rows.map transitionWidenedFallbackCoordinateSeed).flatMap
        (affineUnaryTripleMap [transitionWidenedFallbackOutputForm]) =
      rows.map fun row => row.1 := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      rcases row with ⟨first, second, third⟩
      simp [transitionWidenedFallbackCoordinateSeed, ih]

/-- Projecting the generated coordinates of one transition row gives its
byte-value-exact canonical widened fallback. -/
theorem transitionWidenedFallbackCoordinateSeeds_projection
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    affineUnaryTripleMapFamily [transitionWidenedFallbackOutputForm]
        (transitionWidenedFallbackCoordinateSeeds tm seed) =
      transitionWidenedFallbackValues tm seed := by
  calc
    affineUnaryTripleMapFamily [transitionWidenedFallbackOutputForm]
        (transitionWidenedFallbackCoordinateSeeds tm seed) =
        (transitionWidenedFallbackSegments tm).flatMap
          (transitionWidenedFallbackSegmentValues seed) := by
      unfold affineUnaryTripleMapFamily
        transitionWidenedFallbackCoordinateSeeds
        transitionWidenedFallbackProgressions
      rw [List.flatMap_assoc, List.flatMap_map]
      apply List.flatMap_congr
      intro segment hsegment
      exact transitionWidenedFallback_rows_projection
        (affineUnaryTripleProgressionRows
          (transitionWidenedFallbackSegmentProgression seed segment))
    _ = transitionWidenedFallbackValues tm seed :=
      transitionWidenedFallbackSegments_values tm seed

/-- Raw-input descriptors for every fixed fallback segment of every
transition row. -/
noncomputable def verifierTransitionWidenedFallbackDescriptorFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  verifierTransitionAffineMapFrames W
    (transitionWidenedFallbackDescriptorForms W.machine.tm) input

/-- Exact byte semantics of the raw-input descriptor source. -/
theorem verifierTransitionWidenedFallbackDescriptorFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionWidenedFallbackDescriptorFrames W input =
      encodeAffineUnaryTripleProgressionFamily
        ((verifierTransitionRowSeeds W input).flatMap
          (transitionWidenedFallbackProgressions W.machine.tm)) := by
  unfold verifierTransitionWidenedFallbackDescriptorFrames
    verifierTransitionAffineMapFrames verifierTransitionTailAffineSeeds
    affineUnaryTripleMapFamily encodeUnaryFrame
  rw [List.flatMap_map]
  generalize verifierTransitionRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [List.flatMap_cons, List.flatMap_append]
      have hseed := encode_transitionWidenedFallbackDescriptorForms
        W.machine.tm seed
      unfold encodeUnaryFrame at hseed
      rw [hseed, ih]
      induction transitionWidenedFallbackProgressions W.machine.tm seed with
      | nil => rfl
      | cons progression progressions progressionIh =>
          simp [encodeAffineUnaryTripleProgressionFamily, progressionIh]

/-- A fixed polynomial-time TM2 emits every fallback progression descriptor
directly from the raw verifier word. -/
noncomputable def
    verifierTransitionWidenedFallbackDescriptorFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionWidenedFallbackDescriptorFrames W) := by
  exact verifierTransitionAffineMapFrames_computableInPolyTime W
    (transitionWidenedFallbackDescriptorForms W.machine.tm)

private theorem fallback_progressionFrameStream_eq_seedEncoding
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

private theorem fallback_progressionFamilyFrameStream_append
    (left right : List AffineUnaryTripleProgression) :
    affineUnaryTripleProgressionFamilyFrameStream (left ++ right) =
      affineUnaryTripleProgressionFamilyFrameStream left ++
        affineUnaryTripleProgressionFamilyFrameStream right := by
  induction left with
  | nil => rfl
  | cons progression rest ih =>
      simp [affineUnaryTripleProgressionFamilyFrameStream, ih,
        List.append_assoc]

private theorem fallback_affineSeedFamily_append
    (left right : List AffineUnaryTripleSeed) :
    encodeAffineUnaryTripleSeedFamily (left ++ right) =
      encodeAffineUnaryTripleSeedFamily left ++
        encodeAffineUnaryTripleSeedFamily right := by
  induction left with
  | nil => rfl
  | cons seed rest ih =>
      simp [encodeAffineUnaryTripleSeedFamily, ih, List.append_assoc]

/-- Executing one row's progression family gives exactly its coordinate-seed
encoding. -/
theorem transitionWidenedFallbackProgressionFrameStream_eq_coordinateSeeds
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    affineUnaryTripleProgressionFamilyFrameStream
        (transitionWidenedFallbackProgressions tm seed) =
      encodeAffineUnaryTripleSeedFamily
        (transitionWidenedFallbackCoordinateSeeds tm seed) := by
  unfold transitionWidenedFallbackCoordinateSeeds
  induction transitionWidenedFallbackProgressions tm seed with
  | nil => rfl
  | cons progression rest ih =>
      simp only [affineUnaryTripleProgressionFamilyFrameStream,
        List.flatMap_cons]
      rw [fallback_progressionFrameStream_eq_seedEncoding, ih]
      exact (fallback_affineSeedFamily_append _ _).symm

/-- Executed coordinate stream for every transition row. -/
noncomputable def verifierTransitionWidenedFallbackCoordinateFrameStream
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  affineUnaryTripleProgressionFamilyFrameStream
    ((verifierTransitionRowSeeds W input).flatMap
      (transitionWidenedFallbackProgressions W.machine.tm))

/-- The executed source is the row-major coordinate-seed encoding. -/
theorem verifierTransitionWidenedFallbackCoordinateFrameStream_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionWidenedFallbackCoordinateFrameStream W input =
      encodeAffineUnaryTripleSeedFamily
        ((verifierTransitionRowSeeds W input).flatMap
          (transitionWidenedFallbackCoordinateSeeds W.machine.tm)) := by
  unfold verifierTransitionWidenedFallbackCoordinateFrameStream
  generalize verifierTransitionRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [List.flatMap_cons]
      rw [fallback_progressionFamilyFrameStream_append,
        transitionWidenedFallbackProgressionFrameStream_eq_coordinateSeeds,
        ih, fallback_affineSeedFamily_append]

/-- A fixed polynomial-time TM2 executes all fallback progressions from the
raw verifier word. -/
noncomputable def
    verifierTransitionWidenedFallbackCoordinateFrameStream_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionWidenedFallbackCoordinateFrameStream W) := by
  let descriptors :=
    verifierTransitionWidenedFallbackDescriptorFrames_computableInPolyTime W
  let structured : _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineUnaryTripleProgressionFamily
      (fun input =>
        (verifierTransitionRowSeeds W input).flatMap
          (transitionWidenedFallbackProgressions W.machine.tm)) :=
    { tm := descriptors.tm
      inputAlphabet := descriptors.inputAlphabet
      outputAlphabet := descriptors.outputAlphabet
      time := descriptors.time
      outputsFun := fun input => by
        have run := descriptors.outputsFun input
        simpa only [id_eq,
          verifierTransitionWidenedFallbackDescriptorFrames_eq W input]
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
          verifierTransitionWidenedFallbackCoordinateFrameStream] using run }

/-- Raw-input unary values for every canonical widened fallback row. -/
noncomputable def verifierTransitionWidenedFallbackValueFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  encodeUnaryFrame
    (affineUnaryTripleMapFamily [transitionWidenedFallbackOutputForm]
      ((verifierTransitionRowSeeds W input).flatMap
        (transitionWidenedFallbackCoordinateSeeds W.machine.tm)))

/-- The raw-input value source is exactly the semantic widened fallback
family. -/
theorem verifierTransitionWidenedFallbackValueFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionWidenedFallbackValueFrames W input =
      encodeUnaryFrame
        ((verifierTransitionRowSeeds W input).flatMap
          (transitionWidenedFallbackValues W.machine.tm)) := by
  unfold verifierTransitionWidenedFallbackValueFrames
    affineUnaryTripleMapFamily
  congr 1
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro seed hseed
  exact transitionWidenedFallbackCoordinateSeeds_projection W.machine.tm seed

/-- Public acceptance contract: the generated values are the canonical
`Fin` enumeration of the semantic widened wire bundle for every verifier
transition row. -/
theorem verifierTransitionWidenedFallbackValueFrames_eq_canonical
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionWidenedFallbackValueFrames W input =
      encodeUnaryFrame
        ((verifierTransitionRowSeeds W input).flatMap fun seed =>
          List.ofFn fun coordinate : Fin (cfgBitCount W.machine.tm
              (workHeight W.machine.tm seed.height)) =>
            arithmeticWidenedCfgWires W.machine.tm seed.height seed.start
              seed.rowBase
              ((cfgSlotEquivFin W.machine.tm
                (workHeight W.machine.tm seed.height)).symm coordinate)) := by
  rw [verifierTransitionWidenedFallbackValueFrames_eq]
  congr 1
  apply List.flatMap_congr
  intro seed hseed
  exact transitionWidenedFallbackValues_eq_canonical W.machine.tm seed

/-- One fixed polynomial-time TM2 generates the exact widened false-arm row
directly from the raw verifier input. -/
noncomputable def
    verifierTransitionWidenedFallbackValueFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionWidenedFallbackValueFrames W) := by
  let coordinates :=
    verifierTransitionWidenedFallbackCoordinateFrameStream_computableInPolyTime W
  let structured : _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineUnaryTripleSeedFamily
      (fun input =>
        (verifierTransitionRowSeeds W input).flatMap
          (transitionWidenedFallbackCoordinateSeeds W.machine.tm)) :=
    { tm := coordinates.tm
      inputAlphabet := coordinates.inputAlphabet
      outputAlphabet := coordinates.outputAlphabet
      time := coordinates.time
      outputsFun := fun input => by
        have run := coordinates.outputsFun input
        simpa only [id_eq,
          verifierTransitionWidenedFallbackCoordinateFrameStream_eq W input]
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
          verifierTransitionWidenedFallbackValueFrames] using run }

end CLRS.Chapter34.Turing.CookLevin

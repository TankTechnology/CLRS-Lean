import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxSource

/-!
# Executed dispatch-mux fresh-coordinate source

This final thin layer runs the generated progression descriptors and identifies
their output with the semantic whole-row mux layouts.  It is kept separate so
changes to the recursive statement compiler do not force recompilation of the
generic affine source proofs.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Repackage one emitted coordinate triple as a generic affine seed. -/
def transitionDispatchMuxCoordinateSeed
    (row : Nat × Nat × Nat) : AffineUnaryTripleSeed :=
  { first := row.1, second := row.2.1, third := row.2.2 }

/-- All fresh mux coordinate triples for one transition row. -/
def transitionDispatchMuxCoordinateSeeds
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List AffineUnaryTripleSeed :=
  (transitionDispatchMuxAffineProgressions tm seed).flatMap
    fun progression =>
      (affineUnaryTripleProgressionRows progression).map
        transitionDispatchMuxCoordinateSeed

private theorem dispatchMux_progressionFrameStream_eq_seedEncoding
    (progression : AffineUnaryTripleProgression) :
    affineUnaryTripleProgressionFrameStream progression =
      encodeAffineUnaryTripleSeedFamily
        ((affineUnaryTripleProgressionRows progression).map
          transitionDispatchMuxCoordinateSeed) := by
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

private theorem dispatchMux_progressionFamilyFrameStream_append
    (left right : List AffineUnaryTripleProgression) :
    affineUnaryTripleProgressionFamilyFrameStream (left ++ right) =
      affineUnaryTripleProgressionFamilyFrameStream left ++
        affineUnaryTripleProgressionFamilyFrameStream right := by
  induction left with
  | nil => rfl
  | cons progression rest ih =>
      simp [affineUnaryTripleProgressionFamilyFrameStream, ih,
        List.append_assoc]

private theorem dispatchMux_affineSeedFamily_append
    (left right : List AffineUnaryTripleSeed) :
    encodeAffineUnaryTripleSeedFamily (left ++ right) =
      encodeAffineUnaryTripleSeedFamily left ++
        encodeAffineUnaryTripleSeedFamily right := by
  induction left with
  | nil => rfl
  | cons seed rest ih =>
      simp [encodeAffineUnaryTripleSeedFamily, ih, List.append_assoc]

/-- Executing one row's mux progressions yields exactly its coordinate-seed
encoding. -/
theorem transitionDispatchMuxProgressionFrameStream_eq_coordinateSeeds
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    affineUnaryTripleProgressionFamilyFrameStream
        (transitionDispatchMuxAffineProgressions tm seed) =
      encodeAffineUnaryTripleSeedFamily
        (transitionDispatchMuxCoordinateSeeds tm seed) := by
  unfold transitionDispatchMuxCoordinateSeeds
  induction transitionDispatchMuxAffineProgressions tm seed with
  | nil => rfl
  | cons progression rest ih =>
      simp only [affineUnaryTripleProgressionFamilyFrameStream,
        List.flatMap_cons]
      rw [dispatchMux_progressionFrameStream_eq_seedEncoding, ih]
      exact (dispatchMux_affineSeedFamily_append _ _).symm

/-- The generated coordinate triples are exactly the fresh-coordinate fields
of the already verified semantic mux layout. -/
theorem transitionDispatchMuxCoordinateRows_eq_layouts
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    (transitionDispatchMuxAffineProgressions tm seed).flatMap
        affineUnaryTripleProgressionRows =
      (transitionDispatchMuxFreshLayoutsFromSeed tm seed).flatMap
        TransitionDispatchMuxFreshLayout.coordinates := by
  rw [transitionDispatchMuxAffineProgressions_eq_runtimes tm seed hwork]
  have hlayouts := transitionDispatchMuxRuntimes_layouts_eq tm seed
  have hcoordinates := congrArg
    (List.flatMap TransitionDispatchMuxFreshLayout.coordinates) hlayouts
  simpa [TransitionDispatchMuxRuntime.layout, List.flatMap_map] using
    hcoordinates

/-- Coordinate seeds read directly from the semantic seed-only mux layouts. -/
def transitionDispatchMuxLayoutCoordinateSeeds
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List AffineUnaryTripleSeed :=
  (transitionDispatchMuxFreshLayoutsFromSeed tm seed).flatMap fun layout =>
    layout.coordinates.map transitionDispatchMuxCoordinateSeed

/-- Generated coordinate seeds are byte-for-byte the semantic layout
coordinates whenever the statement-cost affine forms are valid. -/
theorem transitionDispatchMuxCoordinateSeeds_eq_layout
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    transitionDispatchMuxCoordinateSeeds tm seed =
      transitionDispatchMuxLayoutCoordinateSeeds tm seed := by
  have hrows := transitionDispatchMuxCoordinateRows_eq_layouts tm seed hwork
  have hmapped := congrArg
    (List.map transitionDispatchMuxCoordinateSeed) hrows
  simpa [transitionDispatchMuxCoordinateSeeds,
    transitionDispatchMuxLayoutCoordinateSeeds, List.map_flatMap] using
    hmapped

/-- Forward fresh-coordinate stream for every verifier transition row. -/
noncomputable def verifierTransitionDispatchMuxCoordinateFrameStream
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  affineUnaryTripleProgressionFamilyFrameStream
    ((verifierTransitionRowSeeds W input).flatMap
      (transitionDispatchMuxAffineProgressions W.machine.tm))

/-- The executed source is exactly the row-major generic seed encoding. -/
theorem verifierTransitionDispatchMuxCoordinateFrameStream_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxCoordinateFrameStream W input =
      encodeAffineUnaryTripleSeedFamily
        ((verifierTransitionRowSeeds W input).flatMap
          (transitionDispatchMuxCoordinateSeeds W.machine.tm)) := by
  unfold verifierTransitionDispatchMuxCoordinateFrameStream
  generalize verifierTransitionRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [List.flatMap_cons]
      rw [dispatchMux_progressionFamilyFrameStream_append,
        transitionDispatchMuxProgressionFrameStream_eq_coordinateSeeds, ih,
        dispatchMux_affineSeedFamily_append]

/-- For verifier-produced rows, the concrete output stream is literally the
semantic fresh-coordinate layout encoding. -/
theorem verifierTransitionDispatchMuxCoordinateFrameStream_eq_layouts
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxCoordinateFrameStream W input =
      encodeAffineUnaryTripleSeedFamily
        ((verifierTransitionRowSeeds W input).flatMap
          (transitionDispatchMuxLayoutCoordinateSeeds W.machine.tm)) := by
  rw [verifierTransitionDispatchMuxCoordinateFrameStream_eq]
  congr 1
  apply List.flatMap_congr
  intro seed hseed
  apply transitionDispatchMuxCoordinateSeeds_eq_layout
  have hheight := verifierTransitionRowSeeds_height_eq W input seed hseed
  rw [hheight]
  unfold workHeight
  exact Nat.add_pos_left (verifierHeight_eval_pos W input.length) _

/-- One fixed polynomial-time TM2 generates every dispatch-mux fresh
coordinate directly from the raw verifier input. -/
noncomputable def
    verifierTransitionDispatchMuxCoordinateFrameStream_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxCoordinateFrameStream W) := by
  let descriptors :=
    verifierTransitionDispatchMuxDescriptorFrames_computableInPolyTime W
  let structured : _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineUnaryTripleProgressionFamily
      (fun input =>
        (verifierTransitionRowSeeds W input).flatMap
          (transitionDispatchMuxAffineProgressions W.machine.tm)) :=
    { tm := descriptors.tm
      inputAlphabet := descriptors.inputAlphabet
      outputAlphabet := descriptors.outputAlphabet
      time := descriptors.time
      outputsFun := fun input => by
        have run := descriptors.outputsFun input
        simpa only [id_eq,
          verifierTransitionDispatchMuxDescriptorFrames_eq W input]
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
          verifierTransitionDispatchMuxCoordinateFrameStream] using run }

end CLRS.Chapter34.Turing.CookLevin

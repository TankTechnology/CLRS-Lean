import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorCoordinateExecute
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorAlignment

/-!
# Label-marked execution of routed dispatch-mux coordinates

The routed coordinate descriptor channel contains exactly one affine triple
progression per fixed program label.  Executing it with the singleton fixed-
group controller therefore retains one physical `frameEnd` after every label,
instead of flattening those boundaries away.  These boundaries are the first
piece of state needed by the final four-channel mux-source assembler.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- A singleton fixed group marks the output of every progression. -/
theorem affineUnaryTripleProgressionFixedGroupZeroFrameStream_eq
    (progressions : List AffineUnaryTripleProgression) :
    affineUnaryTripleProgressionFixedGroupFrameStream 0 progressions =
      progressions.flatMap fun progression =>
        affineUnaryTripleProgressionFrameStream progression ++ [.frameEnd] := by
  induction progressions with
  | nil => rfl
  | cons progression rest ih =>
      simp only [affineUnaryTripleProgressionFixedGroupFrameStream,
        affineUnaryTripleProgressionFixedGroupFrameStreamFrom,
        List.flatMap_cons]
      change affineUnaryTripleProgressionFrameStream progression ++
          .frameEnd ::
            affineUnaryTripleProgressionFixedGroupFrameStream 0 rest = _
      rw [ih]
      simp [List.append_assoc]

/-- Encode one semantic list of fresh-coordinate triples as an ordinary unary
frame row. -/
def transitionDispatchMuxCoordinateRowFrames
    (coordinates : List (Nat × Nat × Nat)) : List UnaryFrameSym :=
  coordinates.flatMap fun coordinate =>
    encodeUnaryFrame
      [coordinate.1, coordinate.2.1, coordinate.2.2]

/-- Execute the physically recovered coordinate descriptors while preserving
one boundary after every dispatch label. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorCoordinateLabelFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  affineUnaryTripleProgressionFixedGroupFrameStream 0
    ((verifierTransitionRowSeeds W input).flatMap
      (transitionDispatchMuxAffineProgressions W.machine.tm))

/-- The physical stream consists of one marked coordinate row per affine
label progression. -/
theorem
    verifierTransitionDispatchMuxInvocationDescriptorCoordinateLabelFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorCoordinateLabelFrames
        W input =
      ((verifierTransitionRowSeeds W input).flatMap
        (transitionDispatchMuxAffineProgressions W.machine.tm)).flatMap
          fun progression =>
            affineUnaryTripleProgressionFrameStream progression ++
              [.frameEnd] := by
  unfold
    verifierTransitionDispatchMuxInvocationDescriptorCoordinateLabelFrames
  exact affineUnaryTripleProgressionFixedGroupZeroFrameStream_eq _

/-- On verifier-produced seeds, every retained physical boundary is exactly a
semantic label boundary of the fresh-coordinate layout. -/
theorem
    verifierTransitionDispatchMuxInvocationDescriptorCoordinateLabelFrames_eq_layouts
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorCoordinateLabelFrames
        W input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        (transitionDispatchMuxFreshLayoutsFromSeed W.machine.tm seed).flatMap
          fun layout =>
            transitionDispatchMuxCoordinateRowFrames layout.coordinates ++
              [.frameEnd] := by
  rw [verifierTransitionDispatchMuxInvocationDescriptorCoordinateLabelFrames_eq]
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro seed hseed
  have hwork : 0 < workHeight W.machine.tm seed.height := by
    have hheight := verifierTransitionRowSeeds_height_eq W input seed hseed
    rw [hheight]
    unfold workHeight
    exact Nat.add_pos_left (verifierHeight_eval_pos W input.length) _
  have hrows := transitionDispatchMuxCoordinateProgressionGroups_values
    W.machine.tm seed hwork
  unfold transitionDispatchMuxCoordinateProgressionGroups at hrows
  simp only [List.map_map] at hrows
  have hencoded := congrArg
    (List.map fun coordinates =>
      transitionDispatchMuxCoordinateRowFrames coordinates ++ [.frameEnd])
    hrows
  have hflattened := congrArg List.flatten hencoded
  rw [List.flatten_eq_flatMap, List.flatMap_map] at hflattened
  simpa [transitionDispatchMuxCoordinateRowFrames,
    affineUnaryTripleProgressionFrameStream,
    affineUnaryTripleRowValues, List.flatten_eq_flatMap,
    List.flatMap_map, Function.comp_def]
    using hflattened

/-- The unified four-way route, coordinate selection, descriptor recovery,
and label-marked execution form one concrete polynomial-time TM2 from the
original verifier word. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorCoordinateLabelFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationDescriptorCoordinateLabelFrames
        W) := by
  let descriptors :=
    verifierTransitionDispatchMuxInvocationDescriptorCoordinateFrames_computableInPolyTime
      W
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
          verifierTransitionDispatchMuxInvocationDescriptorCoordinateFrames_eq
            W input] using run }
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch structured
      (affineUnaryTripleProgressionFixedGroupFrameStream_computableInPolyTime 0)
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [Function.comp_apply, id_eq,
          verifierTransitionDispatchMuxInvocationDescriptorCoordinateLabelFrames]
          using run }

end CLRS.Chapter34.Turing.CookLevin

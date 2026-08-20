import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxCoordinates

/-!
# Concrete output-row source for dispatch muxes

The output of each mux coordinate is one wire after its generated false-arm
AND wire.  This module projects that value from the already compiled fresh
coordinate stream.  These rows are exactly the accumulated `whenFalse` arm of
the following program label; the initial widened row is handled separately.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Project `falseArm + 1`, the final OR output of one mux coordinate. -/
def transitionDispatchMuxOutputForm : AffineUnaryTripleForm :=
  { constant := 1, first := 0, second := 0, third := 1 }

@[simp] theorem transitionDispatchMuxOutputForm_value
    (seed : AffineUnaryTripleSeed) :
    affineUnaryTripleFormValue transitionDispatchMuxOutputForm seed =
      seed.third + 1 := by
  simp [transitionDispatchMuxOutputForm, affineUnaryTripleFormValue]
  omega

/-- Output wires obtained from the generated coordinate seeds of one row. -/
def transitionDispatchMuxOutputValues
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) : List Nat :=
  affineUnaryTripleMapFamily [transitionDispatchMuxOutputForm]
    (transitionDispatchMuxCoordinateSeeds tm seed)

/-- Output wires read directly from a seed-only semantic mux layout. -/
def TransitionDispatchMuxFreshLayout.outputValues
    (layout : TransitionDispatchMuxFreshLayout) : List Nat :=
  layout.coordinates.map fun coordinate => coordinate.2.2 + 1

/-- Semantic output rows of all label muxes in dispatch order. -/
def transitionDispatchMuxLayoutOutputValues
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) : List Nat :=
  (transitionDispatchMuxFreshLayoutsFromSeed tm seed).flatMap
    TransitionDispatchMuxFreshLayout.outputValues

/-- The affine projection yields literally the semantic mux output rows. -/
theorem transitionDispatchMuxOutputValues_eq_layout
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    transitionDispatchMuxOutputValues tm seed =
      transitionDispatchMuxLayoutOutputValues tm seed := by
  unfold transitionDispatchMuxOutputValues
  rw [transitionDispatchMuxCoordinateSeeds_eq_layout tm seed hwork]
  unfold transitionDispatchMuxLayoutOutputValues
    transitionDispatchMuxLayoutCoordinateSeeds
    TransitionDispatchMuxFreshLayout.outputValues
    affineUnaryTripleMapFamily
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro layout hlayout
  induction layout.coordinates with
  | nil => rfl
  | cons coordinate coordinates ih =>
      rcases coordinate with ⟨selectorNot, trueArm, falseArm⟩
      simp only [List.map_cons, List.flatMap_cons, affineUnaryTripleMap,
        transitionDispatchMuxCoordinateSeed]
      rw [transitionDispatchMuxOutputForm_value, ih]
      simp

/-- Output values extracted from an actual proof-carrying label artifact. -/
def TransitionDispatchLabelArtifact.muxOutputValues
    {tm : _root_.Turing.FinTM2}
    (artifact : TransitionDispatchLabelArtifact tm) : List Nat :=
  artifact.muxFrames.map fun frame => frame.falseArm + 1

/-- Projecting output values commutes with erasing a full mux frame to its
fresh layout. -/
theorem TransitionDispatchLabelArtifact.muxOutputValues_eq_layout
    {tm : _root_.Turing.FinTM2}
    (artifact : TransitionDispatchLabelArtifact tm) :
    artifact.muxOutputValues = artifact.muxFreshLayout.outputValues := by
  unfold TransitionDispatchLabelArtifact.muxOutputValues
    TransitionDispatchLabelArtifact.muxFreshLayout
    TransitionDispatchMuxFreshLayout.outputValues
  rw [List.map_map]
  rfl

/-- Actual proof-carrying dispatch artifacts have the same mux output rows as
the seed-only semantic layouts. -/
theorem arithmeticWidening_dispatchArtifact_muxOutputValues_eq
    (tm : _root_.Turing.FinTM2) (height rowBase : Nat)
    (base : CircuitBuilder)
    (hvalid : (arithmeticCfgWires tm height rowBase).ValidIn base) :
    let widened := widenCfg base (arithmeticCfgWires tm height rowBase) hvalid
    (compileDispatchArtifacts tm height widened.builder widened.constants
        widened.wires widened.valid).flatMap
          TransitionDispatchLabelArtifact.muxOutputValues =
      transitionDispatchMuxLayoutOutputValues tm
        { height := height, start := base.gates.length,
          rowBase := rowBase } := by
  dsimp only
  have hlayouts :=
    arithmeticWidening_dispatchArtifact_muxFreshLayouts_eq_seed
      tm height rowBase base hvalid
  have houtputs := congrArg
    (List.flatMap TransitionDispatchMuxFreshLayout.outputValues) hlayouts
  rw [show
      (compileDispatchArtifacts tm height
          (widenCfg base (arithmeticCfgWires tm height rowBase) hvalid).builder
          (widenCfg base (arithmeticCfgWires tm height rowBase) hvalid).constants
          (widenCfg base (arithmeticCfgWires tm height rowBase) hvalid).wires
          (widenCfg base (arithmeticCfgWires tm height rowBase) hvalid).valid).flatMap
            TransitionDispatchLabelArtifact.muxOutputValues =
        (compileDispatchArtifacts tm height
          (widenCfg base (arithmeticCfgWires tm height rowBase) hvalid).builder
          (widenCfg base (arithmeticCfgWires tm height rowBase) hvalid).constants
          (widenCfg base (arithmeticCfgWires tm height rowBase) hvalid).wires
          (widenCfg base (arithmeticCfgWires tm height rowBase) hvalid).valid).flatMap
            (fun artifact => artifact.muxFreshLayout.outputValues) by
      apply List.flatMap_congr
      intro artifact hartifact
      exact TransitionDispatchLabelArtifact.muxOutputValues_eq_layout artifact]
  simpa only [transitionDispatchMuxLayoutOutputValues,
    List.flatMap_map, Function.comp_apply] using houtputs

/-- Raw-input unary values for all dispatch mux output rows. -/
noncomputable def verifierTransitionDispatchMuxOutputValueFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  encodeUnaryFrame
    (affineUnaryTripleMapFamily [transitionDispatchMuxOutputForm]
      ((verifierTransitionRowSeeds W input).flatMap
        (transitionDispatchMuxCoordinateSeeds W.machine.tm)))

/-- The raw-input value source is exactly the semantic mux-output family. -/
theorem verifierTransitionDispatchMuxOutputValueFrames_eq_layouts
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxOutputValueFrames W input =
      encodeUnaryFrame
        ((verifierTransitionRowSeeds W input).flatMap
          (transitionDispatchMuxLayoutOutputValues W.machine.tm)) := by
  unfold verifierTransitionDispatchMuxOutputValueFrames
    affineUnaryTripleMapFamily
  congr 1
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro seed hseed
  change transitionDispatchMuxOutputValues W.machine.tm seed = _
  apply transitionDispatchMuxOutputValues_eq_layout
  have hheight := verifierTransitionRowSeeds_height_eq W input seed hseed
  rw [hheight]
  unfold workHeight
  exact Nat.add_pos_left (verifierHeight_eval_pos W input.length) _

/-- One fixed polynomial-time TM2 generates every dispatch mux output wire
directly from the raw verifier word. -/
noncomputable def
    verifierTransitionDispatchMuxOutputValueFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxOutputValueFrames W) := by
  let coordinates :=
    verifierTransitionDispatchMuxCoordinateFrameStream_computableInPolyTime W
  let structured : _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineUnaryTripleSeedFamily
      (fun input =>
        (verifierTransitionRowSeeds W input).flatMap
          (transitionDispatchMuxCoordinateSeeds W.machine.tm)) :=
    { tm := coordinates.tm
      inputAlphabet := coordinates.inputAlphabet
      outputAlphabet := coordinates.outputAlphabet
      time := coordinates.time
      outputsFun := fun input => by
        have run := coordinates.outputsFun input
        simpa only [id_eq,
          verifierTransitionDispatchMuxCoordinateFrameStream_eq W input]
          using run }
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch structured
      (affineUnaryTripleMapFamily_computableInPolyTime
        [transitionDispatchMuxOutputForm])
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [Function.comp_apply, id_eq,
          verifierTransitionDispatchMuxOutputValueFrames] using run }

end CLRS.Chapter34.Turing.CookLevin

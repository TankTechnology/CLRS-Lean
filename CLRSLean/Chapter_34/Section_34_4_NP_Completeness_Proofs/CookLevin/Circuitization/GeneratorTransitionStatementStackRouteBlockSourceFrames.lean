import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouteBlockDescriptorSelection
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouteSourceFrames
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouteActionFold

/-!
# Concrete complete-stack source rows

The complete selected descriptor block is normalized, executed in one fixed
group per transition seed, and projected to its first coordinates.  The result
is exactly the flattened widened stack block needed as the input of the
sequential selected-action fold.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Complete selected stack progressions in transition-row order. -/
noncomputable def verifierTransitionStackRouteBlockProgressions
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) :
    List AffineUnaryTripleProgression :=
  (verifierTransitionRowSeeds W input).flatMap fun seed =>
    transitionStackRouteBlockProgressions W.machine.tm seed k

/-- Canonical adjacent descriptor stream for the complete selected stack. -/
noncomputable def verifierTransitionStackRouteBlockDescriptorFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) : List UnaryFrameSym :=
  unmarkAffineUnaryTripleProgressionRows
    (verifierTransitionStackRouteBlockMarkedDescriptorFrames W k input)

/-- Removing descriptor-local markers recovers exactly the complete selected
stack progression encoding. -/
theorem verifierTransitionStackRouteBlockDescriptorFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) :
    verifierTransitionStackRouteBlockDescriptorFrames W k input =
      encodeAffineUnaryTripleProgressionFamily
        (verifierTransitionStackRouteBlockProgressions W k input) := by
  unfold verifierTransitionStackRouteBlockDescriptorFrames
    verifierTransitionStackRouteBlockProgressions
  rw [verifierTransitionStackRouteBlockMarkedDescriptorFrames_eq_routeProgressions]
  rw [encodeAffineUnaryTripleProgressionMarkedFamily_flatMap]
  exact unmarkAffineUnaryTripleProgressionRows_encode _

/-- One fixed polynomial-time TM2 emits the canonical complete-stack
descriptor family from the original verifier word. -/
noncomputable def
    verifierTransitionStackRouteBlockDescriptorFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionStackRouteBlockDescriptorFrames W k) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionStackRouteBlockMarkedDescriptorFrames_computableInPolyTime
        W k)
      unmarkAffineUnaryTripleProgressionRows_computableInPolyTime
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [Function.comp_apply, id_eq,
          verifierTransitionStackRouteBlockDescriptorFrames] using run }

/-- One selected stack contributes its machine-fixed complete segment count. -/
theorem transitionStackRouteBlockProgressions_length
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K) :
    (transitionStackRouteBlockProgressions tm seed k).length =
      transitionWidenedFallbackStackSegmentCount tm := by
  simp [transitionStackRouteBlockProgressions,
    transitionWidenedFallbackStackSegments_length]

/-- Group-marked execution of every complete selected stack descriptor row. -/
noncomputable def verifierTransitionStackRouteBlockGroupedFrameStream
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) : List UnaryFrameSym :=
  affineUnaryTripleProgressionFixedGroupFrameStream
    (2 + 2 * maxPushesPerStep W.machine.tm)
    (verifierTransitionStackRouteBlockProgressions W k input)

/-- A fixed polynomial-time TM2 executes each complete selected stack as one
marked descriptor group. -/
noncomputable def
    verifierTransitionStackRouteBlockGroupedFrameStream_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionStackRouteBlockGroupedFrameStream W k) := by
  let descriptors :=
    verifierTransitionStackRouteBlockDescriptorFrames_computableInPolyTime W k
  let structured : _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineUnaryTripleProgressionFamily
      (verifierTransitionStackRouteBlockProgressions W k) :=
    { tm := descriptors.tm
      inputAlphabet := descriptors.inputAlphabet
      outputAlphabet := descriptors.outputAlphabet
      time := descriptors.time
      outputsFun := fun input => by
        have run := descriptors.outputsFun input
        simpa only [id_eq,
          verifierTransitionStackRouteBlockDescriptorFrames_eq W k input]
          using run }
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch structured
      (affineUnaryTripleProgressionFixedGroupFrameStream_computableInPolyTime
        (2 + 2 * maxPushesPerStep W.machine.tm))
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [Function.comp_apply, id_eq,
          verifierTransitionStackRouteBlockGroupedFrameStream] using run }

/-- Projected complete-stack stream produced by the concrete descriptor
pipeline. -/
noncomputable def verifierTransitionStackRouteBlockGeneratedSourceFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) : List UnaryFrameSym :=
  projectUnaryTripleGroupFirst
    (verifierTransitionStackRouteBlockGroupedFrameStream W k input)

/-- The complete stack progression family is the height family followed by
the flattened cell family. -/
theorem transitionStackRouteBlockProgressions_eq_height_append_cell
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K) :
    transitionStackRouteBlockProgressions tm seed k =
      transitionStackRouteHeightProgressions tm seed k ++
        transitionStackRouteCellProgressions tm seed k := by
  unfold transitionStackRouteBlockProgressions
    transitionStackRouteHeightProgressions transitionStackRouteCellProgressions
    transitionWidenedFallbackStackSegments transitionStackRouteHeightSegments
    transitionStackRouteCellSegments
  simp only [List.map_cons, List.map_nil,
    List.cons_append, List.nil_append]

/-- Projecting one complete selected descriptor block gives exactly the
flattened widened stack value block. -/
theorem transitionStackRouteBlockProgressions_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K) :
    transitionStackRouteFirstValues
        (transitionStackRouteBlockProgressions tm seed k) =
      (transitionStackRouteSourceBlock tm seed k).flatten := by
  rw [transitionStackRouteBlockProgressions_eq_height_append_cell]
  unfold transitionStackRouteFirstValues
  simp only [List.flatMap_append, List.map_append]
  rw [transitionStackRouteSourceBlock_eq]
  unfold TransitionStackValueBlock.flatten
  rw [transitionWidenedStackHeightValues_eq_routeSource,
    transitionWidenedStackCellValues_eq_routeSource]
  rfl

/-- Canonical marked-row representation of the complete stack block for every
transition seed. -/
noncomputable def transitionStackRouteBlockSourceFrames
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (seeds : List TransitionRowSeed) : List UnaryFrameSym :=
  encodeUnaryFrameFixedPrefixDropInput
    (seeds.map fun seed => (transitionStackRouteSourceBlock tm seed k).flatten)

/-- The generated stream is literally the complete stack-block source row
family consumed by the future action-fold controller. -/
theorem verifierTransitionStackRouteBlockGeneratedSourceFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) :
    verifierTransitionStackRouteBlockGeneratedSourceFrames W k input =
      transitionStackRouteBlockSourceFrames W.machine.tm k
        (verifierTransitionRowSeeds W input) := by
  unfold verifierTransitionStackRouteBlockGeneratedSourceFrames
    verifierTransitionStackRouteBlockGroupedFrameStream
    verifierTransitionStackRouteBlockProgressions
    transitionStackRouteBlockSourceFrames
  rw [projectUnaryTripleGroupFirst_fixedGroupStream]
  rw [affineUnaryTripleProgressionFixedGroupFirstFrameStream_flatMap
    (2 + 2 * maxPushesPerStep W.machine.tm)
      (verifierTransitionRowSeeds W input)
      (fun seed => transitionStackRouteBlockProgressions W.machine.tm seed k)]
  · congr 1
    apply List.map_congr_left
    intro seed hseed
    exact transitionStackRouteBlockProgressions_values W.machine.tm seed k
  · intro seed hseed
    rw [transitionStackRouteBlockProgressions_length]
    unfold transitionWidenedFallbackStackSegmentCount
    omega

/-- The descriptor pipeline computes its projected complete-stack row stream
in polynomial time. -/
noncomputable def
    verifierTransitionStackRouteBlockGeneratedSourceFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionStackRouteBlockGeneratedSourceFrames W k) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionStackRouteBlockGroupedFrameStream_computableInPolyTime
        W k)
      projectUnaryTripleGroupFirst_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => projectUnaryTripleGroupFirst
      (verifierTransitionStackRouteBlockGroupedFrameStream W k input))
  simpa [Function.comp_def] using Classical.choice composed

/-- Unconditional raw-input machine for the complete selected stack source. -/
noncomputable def
    verifierTransitionStackRouteBlockSourceFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input => transitionStackRouteBlockSourceFrames W.machine.tm k
        (verifierTransitionRowSeeds W input)) := by
  let generated :=
    verifierTransitionStackRouteBlockGeneratedSourceFrames_computableInPolyTime
      W k
  exact
    { tm := generated.tm
      inputAlphabet := generated.inputAlphabet
      outputAlphabet := generated.outputAlphabet
      time := generated.time
      outputsFun := fun input => by
        have run := generated.outputsFun input
        simpa only [id_eq,
          verifierTransitionStackRouteBlockGeneratedSourceFrames_eq W k input]
          using run }

/-- Public semantic equality for the concrete complete-stack source. -/
theorem verifierTransitionStackRouteBlockSourceFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) :
    transitionStackRouteBlockSourceFrames W.machine.tm k
        (verifierTransitionRowSeeds W input) =
      encodeUnaryFrameFixedPrefixDropInput
        ((verifierTransitionRowSeeds W input).map fun seed =>
          (TransitionStackValueBlock.ofWires
            ((arithmeticWidenedCfgWires W.machine.tm seed.height seed.start
              seed.rowBase).stack k)).flatten) := by
  unfold transitionStackRouteBlockSourceFrames
  congr 1
  apply List.map_congr_left
  intro seed hseed
  rw [transitionStackRouteSourceBlock_eq]

end CLRS.Chapter34.Turing.CookLevin

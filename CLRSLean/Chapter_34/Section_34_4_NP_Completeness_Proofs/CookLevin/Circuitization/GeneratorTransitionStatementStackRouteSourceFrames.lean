import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouteDescriptorExecution
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRoutePopSlices
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryTripleGroupFirstProjection

/-!
# Concrete marked sources for transition stack routing

The selected affine descriptors arrive in one fixed-size group per transition
row.  The fixed-group progression controller executes those descriptors, and
the first-coordinate projector turns every triple row into the ordinary unary
value row consumed by the stack-pop controllers.  This closes the former
polynomial-time source assumptions for both height and cell routing.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Fixed-group execution followed by first-coordinate projection agrees with
the row-major marked value encoding whenever every seed contributes exactly
one complete descriptor group. -/
theorem affineUnaryTripleProgressionFixedGroupFirstFrameStream_flatMap
    {α : Type} (groupLast : Nat) (seeds : List α)
    (progressions : α → List AffineUnaryTripleProgression)
    (hlength : ∀ seed ∈ seeds,
      (progressions seed).length = groupLast + 1) :
    affineUnaryTripleProgressionFixedGroupFirstFrameStream groupLast
        (seeds.flatMap progressions) =
      encodeUnaryFrameFixedPrefixDropInput
        (seeds.map fun seed =>
          ((progressions seed).flatMap
            affineUnaryTripleProgressionRows).map fun row => row.1) := by
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      have hhead : (progressions seed).length = groupLast + 1 :=
        hlength seed (by simp)
      have htail : ∀ other ∈ rest,
          (progressions other).length = groupLast + 1 := by
        intro other hother
        exact hlength other (by simp [hother])
      simp only [List.flatMap_cons, List.map_cons]
      rw [affineUnaryTripleProgressionFixedGroupFirstFrameStream_append_group
        groupLast (progressions seed) (rest.flatMap progressions) hhead]
      rw [ih htail]
      simp [encodeUnaryFrameFixedPrefixDropInput, List.append_assoc]

/-- Every transition row contributes exactly the two fixed widened-height
segments. -/
theorem transitionStackRouteHeightProgressions_length
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K) :
    (transitionStackRouteHeightProgressions tm seed k).length = 2 := by
  simp [transitionStackRouteHeightProgressions,
    transitionStackRouteHeightSegments]

/-- Every transition row contributes one public cell segment and two fixed
blank-cell segments for each possible push. -/
theorem transitionStackRouteCellProgressions_length
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K) :
    (transitionStackRouteCellProgressions tm seed k).length =
      1 + 2 * maxPushesPerStep tm := by
  simp [transitionStackRouteCellProgressions, transitionStackRouteCellSegments,
    transitionWidenedFallbackBlankCellSegments]
  omega

/-- Group-marked execution of all selected height descriptors. -/
noncomputable def verifierTransitionStackRouteHeightGroupedFrameStream
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) : List UnaryFrameSym :=
  affineUnaryTripleProgressionFixedGroupFrameStream 1
    (verifierTransitionStackRouteHeightProgressions W k input)

/-- Group-marked execution of all selected cell descriptors. -/
noncomputable def verifierTransitionStackRouteCellGroupedFrameStream
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) : List UnaryFrameSym :=
  affineUnaryTripleProgressionFixedGroupFrameStream
    (2 * maxPushesPerStep W.machine.tm)
    (verifierTransitionStackRouteCellProgressions W k input)

/-- A fixed polynomial-time TM2 executes the selected height descriptor stream
and restores one marker after every transition row. -/
noncomputable def
    verifierTransitionStackRouteHeightGroupedFrameStream_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionStackRouteHeightGroupedFrameStream W k) := by
  let descriptors :=
    verifierTransitionStackRouteHeightDescriptorFrames_computableInPolyTime W k
  let structured : _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineUnaryTripleProgressionFamily
      (verifierTransitionStackRouteHeightProgressions W k) :=
    { tm := descriptors.tm
      inputAlphabet := descriptors.inputAlphabet
      outputAlphabet := descriptors.outputAlphabet
      time := descriptors.time
      outputsFun := fun input => by
        have run := descriptors.outputsFun input
        simpa only [id_eq,
          verifierTransitionStackRouteHeightDescriptorFrames_eq W k input]
          using run }
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch structured
      (affineUnaryTripleProgressionFixedGroupFrameStream_computableInPolyTime 1)
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [Function.comp_apply, id_eq,
          verifierTransitionStackRouteHeightGroupedFrameStream] using run }

/-- A fixed polynomial-time TM2 executes the selected cell descriptor stream
and restores one marker after every transition row. -/
noncomputable def
    verifierTransitionStackRouteCellGroupedFrameStream_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionStackRouteCellGroupedFrameStream W k) := by
  let descriptors :=
    verifierTransitionStackRouteCellDescriptorFrames_computableInPolyTime W k
  let structured : _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineUnaryTripleProgressionFamily
      (verifierTransitionStackRouteCellProgressions W k) :=
    { tm := descriptors.tm
      inputAlphabet := descriptors.inputAlphabet
      outputAlphabet := descriptors.outputAlphabet
      time := descriptors.time
      outputsFun := fun input => by
        have run := descriptors.outputsFun input
        simpa only [id_eq,
          verifierTransitionStackRouteCellDescriptorFrames_eq W k input]
          using run }
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch structured
      (affineUnaryTripleProgressionFixedGroupFrameStream_computableInPolyTime
        (2 * maxPushesPerStep W.machine.tm))
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [Function.comp_apply, id_eq,
          verifierTransitionStackRouteCellGroupedFrameStream] using run }

/-- Projected height stream produced by the concrete descriptor pipeline. -/
noncomputable def verifierTransitionStackRouteHeightGeneratedSourceFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) : List UnaryFrameSym :=
  projectUnaryTripleGroupFirst
    (verifierTransitionStackRouteHeightGroupedFrameStream W k input)

/-- Projected cell stream produced by the concrete descriptor pipeline. -/
noncomputable def verifierTransitionStackRouteCellGeneratedSourceFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) : List UnaryFrameSym :=
  projectUnaryTripleGroupFirst
    (verifierTransitionStackRouteCellGroupedFrameStream W k input)

/-- The generated height stream is literally the marked source consumed by
the existing height pop-slice controller. -/
theorem verifierTransitionStackRouteHeightGeneratedSourceFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) :
    verifierTransitionStackRouteHeightGeneratedSourceFrames W k input =
      transitionStackRouteHeightSourceFrames W.machine.tm k
        (verifierTransitionRowSeeds W input) := by
  unfold verifierTransitionStackRouteHeightGeneratedSourceFrames
    verifierTransitionStackRouteHeightGroupedFrameStream
    verifierTransitionStackRouteHeightProgressions
    transitionStackRouteHeightSourceFrames
    transitionStackRouteFirstValues
  rw [projectUnaryTripleGroupFirst_fixedGroupStream]
  exact affineUnaryTripleProgressionFixedGroupFirstFrameStream_flatMap
    1 (verifierTransitionRowSeeds W input)
      (fun seed => transitionStackRouteHeightProgressions W.machine.tm seed k)
      (by
        intro seed hseed
        simpa using transitionStackRouteHeightProgressions_length
          W.machine.tm seed k)

/-- The generated cell stream is literally the marked source consumed by the
existing cell pop-slice controller. -/
theorem verifierTransitionStackRouteCellGeneratedSourceFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) :
    verifierTransitionStackRouteCellGeneratedSourceFrames W k input =
      transitionStackRouteCellSourceFrames W.machine.tm k
        (verifierTransitionRowSeeds W input) := by
  unfold verifierTransitionStackRouteCellGeneratedSourceFrames
    verifierTransitionStackRouteCellGroupedFrameStream
    verifierTransitionStackRouteCellProgressions
    transitionStackRouteCellSourceFrames
    transitionStackRouteFirstValues
  rw [projectUnaryTripleGroupFirst_fixedGroupStream]
  exact affineUnaryTripleProgressionFixedGroupFirstFrameStream_flatMap
    (2 * maxPushesPerStep W.machine.tm)
      (verifierTransitionRowSeeds W input)
      (fun seed => transitionStackRouteCellProgressions W.machine.tm seed k)
      (by
        intro seed hseed
        simpa [Nat.add_comm] using
          transitionStackRouteCellProgressions_length W.machine.tm seed k)

/-- The complete generated height source is polynomial-time computable from
the original verifier word. -/
noncomputable def
    verifierTransitionStackRouteHeightGeneratedSourceFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionStackRouteHeightGeneratedSourceFrames W k) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionStackRouteHeightGroupedFrameStream_computableInPolyTime
        W k)
      projectUnaryTripleGroupFirst_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => projectUnaryTripleGroupFirst
      (verifierTransitionStackRouteHeightGroupedFrameStream W k input))
  simpa [Function.comp_def] using Classical.choice composed

/-- The complete generated cell source is polynomial-time computable from the
original verifier word. -/
noncomputable def
    verifierTransitionStackRouteCellGeneratedSourceFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionStackRouteCellGeneratedSourceFrames W k) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionStackRouteCellGroupedFrameStream_computableInPolyTime
        W k)
      projectUnaryTripleGroupFirst_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => projectUnaryTripleGroupFirst
      (verifierTransitionStackRouteCellGroupedFrameStream W k input))
  simpa [Function.comp_def] using Classical.choice composed

/-- No source premise remains for the selected height rows. -/
noncomputable def
    verifierTransitionStackRouteHeightSourceFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input => transitionStackRouteHeightSourceFrames W.machine.tm k
        (verifierTransitionRowSeeds W input)) := by
  let generated :=
    verifierTransitionStackRouteHeightGeneratedSourceFrames_computableInPolyTime
      W k
  exact
    { tm := generated.tm
      inputAlphabet := generated.inputAlphabet
      outputAlphabet := generated.outputAlphabet
      time := generated.time
      outputsFun := fun input => by
        have run := generated.outputsFun input
        simpa only [id_eq,
          verifierTransitionStackRouteHeightGeneratedSourceFrames_eq W k input]
          using run }

/-- No source premise remains for the selected cell rows. -/
noncomputable def
    verifierTransitionStackRouteCellSourceFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input => transitionStackRouteCellSourceFrames W.machine.tm k
        (verifierTransitionRowSeeds W input)) := by
  let generated :=
    verifierTransitionStackRouteCellGeneratedSourceFrames_computableInPolyTime
      W k
  exact
    { tm := generated.tm
      inputAlphabet := generated.inputAlphabet
      outputAlphabet := generated.outputAlphabet
      time := generated.time
      outputsFun := fun input => by
        have run := generated.outputsFun input
        simpa only [id_eq,
          verifierTransitionStackRouteCellGeneratedSourceFrames_eq W k input]
          using run }

/-- The height pop slice is now unconditional for the actual verifier row
family. -/
noncomputable def
    verifierTransitionStackRoutePopHeightSliceFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input => transitionStackRoutePopHeightSliceFrames W.machine.tm k
        (verifierTransitionRowSeeds W input)) :=
  transitionStackRoutePopHeightSliceFrames_computableInPolyTime_of_source
    W.machine.tm k (verifierTransitionRowSeeds W)
      (verifierTransitionStackRouteHeightSourceFrames_computableInPolyTime W k)

/-- The cell pop slice is now unconditional for the actual verifier row
family. -/
noncomputable def
    verifierTransitionStackRoutePopCellSliceFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input => transitionStackRoutePopCellSliceFrames W.machine.tm k
        (verifierTransitionRowSeeds W input)) :=
  transitionStackRoutePopCellSliceFrames_computableInPolyTime_of_source
    W.machine.tm k (verifierTransitionRowSeeds W)
      (verifierTransitionStackRouteCellSourceFrames_computableInPolyTime W k)

end CLRS.Chapter34.Turing.CookLevin

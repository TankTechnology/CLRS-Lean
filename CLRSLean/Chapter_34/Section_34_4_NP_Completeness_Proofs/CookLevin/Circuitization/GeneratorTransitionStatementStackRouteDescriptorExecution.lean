import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouteDescriptorSelectionSemantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineUnaryTripleProgressionRowUnmark

/-!
# Executing selected stack-route progression descriptors

The raw verifier input now supplies exactly the marked descriptors belonging
to one selected stack.  This file removes their descriptor-local markers,
repackages the result as the canonical progression-family encoding, and runs
the existing fixed polynomial-time progression controller.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- All selected height progressions in transition-row order. -/
noncomputable def verifierTransitionStackRouteHeightProgressions
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) :
    List AffineUnaryTripleProgression :=
  (verifierTransitionRowSeeds W input).flatMap fun seed =>
    transitionStackRouteHeightProgressions W.machine.tm seed k

/-- All selected cell progressions in transition-row order. -/
noncomputable def verifierTransitionStackRouteCellProgressions
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) :
    List AffineUnaryTripleProgression :=
  (verifierTransitionRowSeeds W input).flatMap fun seed =>
    transitionStackRouteCellProgressions W.machine.tm seed k

/-- Canonical adjacent descriptor stream for the selected height family. -/
noncomputable def verifierTransitionStackRouteHeightDescriptorFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) : List UnaryFrameSym :=
  unmarkAffineUnaryTripleProgressionRows
    (verifierTransitionStackRouteHeightMarkedDescriptorFrames W k input)

/-- Canonical adjacent descriptor stream for the selected cell family. -/
noncomputable def verifierTransitionStackRouteCellDescriptorFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) : List UnaryFrameSym :=
  unmarkAffineUnaryTripleProgressionRows
    (verifierTransitionStackRouteCellMarkedDescriptorFrames W k input)

/-- Marker removal recovers exactly the selected height progression encoding. -/
theorem verifierTransitionStackRouteHeightDescriptorFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) :
    verifierTransitionStackRouteHeightDescriptorFrames W k input =
      encodeAffineUnaryTripleProgressionFamily
        (verifierTransitionStackRouteHeightProgressions W k input) := by
  unfold verifierTransitionStackRouteHeightDescriptorFrames
    verifierTransitionStackRouteHeightProgressions
  rw [verifierTransitionStackRouteHeightMarkedDescriptorFrames_eq_routeProgressions]
  rw [encodeAffineUnaryTripleProgressionMarkedFamily_flatMap]
  exact unmarkAffineUnaryTripleProgressionRows_encode _

/-- Marker removal recovers exactly the selected cell progression encoding. -/
theorem verifierTransitionStackRouteCellDescriptorFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) :
    verifierTransitionStackRouteCellDescriptorFrames W k input =
      encodeAffineUnaryTripleProgressionFamily
        (verifierTransitionStackRouteCellProgressions W k input) := by
  unfold verifierTransitionStackRouteCellDescriptorFrames
    verifierTransitionStackRouteCellProgressions
  rw [verifierTransitionStackRouteCellMarkedDescriptorFrames_eq_routeProgressions]
  rw [encodeAffineUnaryTripleProgressionMarkedFamily_flatMap]
  exact unmarkAffineUnaryTripleProgressionRows_encode _

/-- One fixed polynomial-time TM2 emits the canonical selected height
descriptor family directly from the original verifier word. -/
noncomputable def
    verifierTransitionStackRouteHeightDescriptorFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionStackRouteHeightDescriptorFrames W k) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionStackRouteHeightMarkedDescriptorFrames_computableInPolyTime
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
          verifierTransitionStackRouteHeightDescriptorFrames] using run }

/-- One fixed polynomial-time TM2 emits the canonical selected cell
descriptor family directly from the original verifier word. -/
noncomputable def
    verifierTransitionStackRouteCellDescriptorFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionStackRouteCellDescriptorFrames W k) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionStackRouteCellMarkedDescriptorFrames_computableInPolyTime
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
          verifierTransitionStackRouteCellDescriptorFrames] using run }

/-- Executed triple-row stream of the selected height progressions. -/
noncomputable def verifierTransitionStackRouteHeightProgressionFrameStream
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) : List UnaryFrameSym :=
  affineUnaryTripleProgressionFamilyFrameStream
    (verifierTransitionStackRouteHeightProgressions W k input)

/-- Executed triple-row stream of the selected cell progressions. -/
noncomputable def verifierTransitionStackRouteCellProgressionFrameStream
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) : List UnaryFrameSym :=
  affineUnaryTripleProgressionFamilyFrameStream
    (verifierTransitionStackRouteCellProgressions W k input)

/-- A fixed polynomial-time TM2 executes all selected height progressions
directly from the raw verifier input. -/
noncomputable def
    verifierTransitionStackRouteHeightProgressionFrameStream_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionStackRouteHeightProgressionFrameStream W k) := by
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
          verifierTransitionStackRouteHeightProgressionFrameStream] using run }

/-- A fixed polynomial-time TM2 executes all selected cell progressions
directly from the raw verifier input. -/
noncomputable def
    verifierTransitionStackRouteCellProgressionFrameStream_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionStackRouteCellProgressionFrameStream W k) := by
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
          verifierTransitionStackRouteCellProgressionFrameStream] using run }

end CLRS.Chapter34.Turing.CookLevin

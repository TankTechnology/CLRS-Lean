import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxAffine

/-!
# Concrete raw-input source for dispatch mux skeletons

The fixed affine tables below are evaluated over every verifier transition
seed, then executed by the generic triple-progression family controller.  The
result is a concrete polynomial-time TM2 source for every label selector and
every fresh mux coordinate in row-major order.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Affine progression denoted by one label-local mux offset. -/
def transitionDispatchMuxAffineProgression
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (muxOffset : TransitionAffineNat) : AffineUnaryTripleProgression :=
  let muxStart := seed.start + muxOffset.eval seed.height
  { base₁ := muxStart
    base₂ := muxStart + 1
    base₃ := muxStart + 2
    step₁ := 0
    step₂ := 3
    step₃ := 3
    count := cfgBitCount tm (workHeight tm seed.height) }

/-- Affine mux progressions for a fixed program-label suffix. -/
def transitionDispatchMuxAffineProgressionsForLabels
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    TransitionAffineNat → List tm.Λ → List AffineUnaryTripleProgression
  | _, [] => []
  | offset, label :: labels =>
      let muxOffset := offset.add (transitionDispatchStmtGateAffine tm label)
      transitionDispatchMuxAffineProgression tm seed muxOffset ::
        transitionDispatchMuxAffineProgressionsForLabels tm seed
          (muxOffset.add (transitionDispatchMuxGateAffine tm)) labels

/-- Complete fixed-label progression family for one transition seed. -/
def transitionDispatchMuxAffineProgressions
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List AffineUnaryTripleProgression :=
  transitionDispatchMuxAffineProgressionsForLabels tm seed
    (TransitionAffineNat.const 2) (programLabels tm)

/-- One seven-form block is byte-level descriptor data for precisely one mux
fresh-coordinate progression. -/
theorem transitionDispatchMuxDescriptorBlock_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (muxOffset : TransitionAffineNat) :
    affineUnaryTripleMap (transitionDispatchMuxDescriptorBlock tm muxOffset)
        (transitionTailAffineSeed seed) =
      let progression :=
        transitionDispatchMuxAffineProgression tm seed muxOffset
      [ progression.base₁, progression.base₂, progression.base₃,
        progression.step₁, progression.step₂, progression.step₃,
        progression.count ] := by
  simp [transitionDispatchMuxDescriptorBlock,
    transitionDispatchMuxAffineProgression, affineUnaryTripleMap,
    transitionAbsoluteStartForm_value, TransitionAffineNat.eval_add,
    TransitionAffineNat.eval_shiftInput, workHeight]
  constructor <;> omega

/-- Evaluating the fixed descriptor table yields exactly the concatenated
runtime progression descriptors for one seed. -/
theorem transitionDispatchMuxDescriptorForms_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    affineUnaryTripleMap (transitionDispatchMuxDescriptorForms tm)
        (transitionTailAffineSeed seed) =
      (transitionDispatchMuxAffineProgressions tm seed).flatMap
        fun progression =>
          [ progression.base₁, progression.base₂, progression.base₃,
            progression.step₁, progression.step₂, progression.step₃,
            progression.count ] := by
  unfold transitionDispatchMuxDescriptorForms
    transitionDispatchMuxAffineProgressions
  generalize TransitionAffineNat.const 2 = offset
  generalize programLabels tm = labels
  induction labels generalizing offset with
  | nil => rfl
  | cons label labels ih =>
      rw [transitionDispatchMuxDescriptorFormsForLabels,
        transitionDispatchMuxAffineProgressionsForLabels]
      rw [show affineUnaryTripleMap
          (transitionDispatchMuxDescriptorBlock tm
              (offset.add (transitionDispatchStmtGateAffine tm label)) ++
            transitionDispatchMuxDescriptorFormsForLabels tm
              ((offset.add (transitionDispatchStmtGateAffine tm label)).add
                (transitionDispatchMuxGateAffine tm)) labels)
          (transitionTailAffineSeed seed) =
        affineUnaryTripleMap
            (transitionDispatchMuxDescriptorBlock tm
              (offset.add (transitionDispatchStmtGateAffine tm label)))
            (transitionTailAffineSeed seed) ++
          affineUnaryTripleMap
            (transitionDispatchMuxDescriptorFormsForLabels tm
              ((offset.add (transitionDispatchStmtGateAffine tm label)).add
                (transitionDispatchMuxGateAffine tm)) labels)
            (transitionTailAffineSeed seed) by
          simp [affineUnaryTripleMap, List.map_append]]
      rw [transitionDispatchMuxDescriptorBlock_value, ih]
      rfl

/-- The unary encoding of the fixed form table is exactly the generic
progression-family input. -/
theorem encode_transitionDispatchMuxDescriptorForms
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    encodeUnaryFrame
        (affineUnaryTripleMap (transitionDispatchMuxDescriptorForms tm)
          (transitionTailAffineSeed seed)) =
      encodeAffineUnaryTripleProgressionFamily
        (transitionDispatchMuxAffineProgressions tm seed) := by
  rw [transitionDispatchMuxDescriptorForms_value]
  unfold encodeUnaryFrame
  induction transitionDispatchMuxAffineProgressions tm seed with
  | nil => rfl
  | cons progression rest ih =>
      simp only [List.flatMap_cons,
        encodeAffineUnaryTripleProgressionFamily,
        encodeAffineUnaryTripleProgression, List.flatMap_append]
      rw [ih]
      simp [encodeUnaryFrame, List.append_assoc]

/-- Affine and semantic recursions produce the same progression family at
positive workspace height. -/
theorem transitionDispatchMuxAffineProgressions_eq_runtimes
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    transitionDispatchMuxAffineProgressions tm seed =
      (transitionDispatchMuxRuntimes tm seed).map
        TransitionDispatchMuxRuntime.progression := by
  unfold transitionDispatchMuxAffineProgressions transitionDispatchMuxRuntimes
  have general : ∀ (offset : TransitionAffineNat) (start : Nat)
      (labels : List tm.Λ),
      start = seed.start + offset.eval seed.height →
      transitionDispatchMuxAffineProgressionsForLabels tm seed offset labels =
        (transitionDispatchMuxRuntimesForLabels tm seed start labels).map
          TransitionDispatchMuxRuntime.progression := by
    intro offset start labels hstart
    induction labels generalizing offset start with
    | nil => rfl
    | cons label labels ih =>
        simp only [transitionDispatchMuxAffineProgressionsForLabels,
          transitionDispatchMuxRuntimesForLabels, List.map_cons]
        have hstmt := transitionDispatchStmtGateAffine_eval tm label
          seed.height hwork
        have hmux := transitionDispatchMuxGateAffine_eval tm seed.height
        have hmuxStart :
            seed.start +
                (offset.add
                  (transitionDispatchStmtGateAffine tm label)).eval
                  seed.height =
              start + compileStmtGateCost tm (workHeight tm seed.height)
                (tm.m label) := by
          rw [TransitionAffineNat.eval_add, hstmt, hstart]
          omega
        congr 1
        · unfold transitionDispatchMuxAffineProgression
          dsimp only
          rw [hmuxStart]
        · apply ih
          rw [TransitionAffineNat.eval_add, hmux]
          omega
  apply general
  simp

/-- Exact mux-progression descriptors for every transition row of the raw
verifier input. -/
noncomputable def verifierTransitionDispatchMuxDescriptorFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  verifierTransitionAffineMapFrames W
    (transitionDispatchMuxDescriptorForms W.machine.tm) input

theorem verifierTransitionDispatchMuxDescriptorFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxDescriptorFrames W input =
      encodeAffineUnaryTripleProgressionFamily
        ((verifierTransitionRowSeeds W input).flatMap
          (transitionDispatchMuxAffineProgressions W.machine.tm)) := by
  unfold verifierTransitionDispatchMuxDescriptorFrames
    verifierTransitionAffineMapFrames verifierTransitionTailAffineSeeds
    affineUnaryTripleMapFamily encodeUnaryFrame
  rw [List.flatMap_map]
  generalize verifierTransitionRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [List.flatMap_cons, List.flatMap_append]
      have hseed := encode_transitionDispatchMuxDescriptorForms
        W.machine.tm seed
      unfold encodeUnaryFrame at hseed
      rw [hseed, ih]
      induction transitionDispatchMuxAffineProgressions W.machine.tm seed with
      | nil => rfl
      | cons progression progressions progressionIh =>
          simp [encodeAffineUnaryTripleProgressionFamily, progressionIh]

/-- A fixed polynomial-time TM2 emits all mux progression descriptors from
the raw verifier word. -/
noncomputable def
    verifierTransitionDispatchMuxDescriptorFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxDescriptorFrames W) := by
  exact verifierTransitionAffineMapFrames_computableInPolyTime W
    (transitionDispatchMuxDescriptorForms W.machine.tm)

/-- Raw-input selector source for every row and fixed program label. -/
noncomputable def verifierTransitionDispatchSelectorFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  verifierTransitionAffineMapFrames W
    (transitionDispatchSelectorForms W.machine.tm) input

theorem verifierTransitionDispatchSelectorFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchSelectorFrames W input =
      encodeUnaryFrame
        ((verifierTransitionRowSeeds W input).flatMap
          (transitionDispatchSelectors W.machine.tm)) := by
  unfold verifierTransitionDispatchSelectorFrames
    verifierTransitionAffineMapFrames verifierTransitionTailAffineSeeds
    affineUnaryTripleMapFamily encodeUnaryFrame
  congr 1
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro seed hseed
  exact transitionDispatchSelectorForms_value W.machine.tm seed

/-- A fixed polynomial-time TM2 emits the exact selector family. -/
noncomputable def
    verifierTransitionDispatchSelectorFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchSelectorFrames W) := by
  exact verifierTransitionAffineMapFrames_computableInPolyTime W
    (transitionDispatchSelectorForms W.machine.tm)

end CLRS.Chapter34.Turing.CookLevin

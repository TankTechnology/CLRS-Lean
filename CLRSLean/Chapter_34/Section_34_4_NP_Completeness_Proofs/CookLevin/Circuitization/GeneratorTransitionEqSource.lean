import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionTailAffine
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineUnaryTripleProgressionFamily
import Mathlib.Tactic

/-!
# Runtime source descriptors for transition equality

The public row is not a contiguous prefix of the widened workspace row:
every fixed stack leaves a verifier-dependent gap after its public height and
cell coordinates.  This module records the exact fixed segmentation and
compiles each segment to a runtime triple progression.  The resulting unary
descriptor family is produced directly from the already verified transition
row seeds by one fixed polynomial-time TM2.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- One contiguous public-row segment together with its corresponding
contiguous workspace projection.  All three quantities are affine in the
runtime public height. -/
structure TransitionEqSegment where
  publicBase : TransitionAffineNat
  workspaceBase : TransitionAffineNat
  count : TransitionAffineNat
deriving DecidableEq, Repr

/-- Turn a height-affine natural into a fixed affine form over a transition
row seed. -/
def transitionHeightAffineForm
    (form : TransitionAffineNat) : AffineUnaryTripleForm :=
  { constant := form.constant
    first := form.coefficient
    second := 0
    third := 0 }

@[simp] theorem transitionHeightAffineForm_value
    (form : TransitionAffineNat) (seed : TransitionRowSeed) :
    affineUnaryTripleFormValue (transitionHeightAffineForm form)
        (transitionTailAffineSeed seed) = form.eval seed.height := by
  simp [transitionHeightAffineForm, transitionTailAffineSeed,
    affineUnaryTripleFormValue, TransitionAffineNat.eval]

/-- Affine stack-prefix offset in the public row. -/
noncomputable def transitionStackBitOffsetAffine
    (tm : _root_.Turing.FinTM2) (k : tm.K) : TransitionAffineNat :=
  { constant := arithmeticStackOrdinal tm k
    coefficient := cfgStackBitOffsetHeightCoeff tm k }

@[simp] theorem transitionStackBitOffsetAffine_eval
    (tm : _root_.Turing.FinTM2) (height : Nat) (k : tm.K) :
    (transitionStackBitOffsetAffine tm k).eval height =
      cfgStackBitOffset tm height k := by
  rw [cfgStackBitOffset_eq_affine]
  rfl

/-- Halted, label, and state coordinates preceding all stacks. -/
def transitionEqPrefixWidth (tm : _root_.Turing.FinTM2) : Nat :=
  1 + (labelCount tm + 1) + stateCount tm

/-- Fixed prefix segment, identical in the public and workspace rows. -/
def transitionEqPrefixSegment
    (tm : _root_.Turing.FinTM2) : TransitionEqSegment :=
  { publicBase := TransitionAffineNat.const 0
    workspaceBase := TransitionAffineNat.const 0
    count := TransitionAffineNat.const (transitionEqPrefixWidth tm) }

/-- Public height coordinates of one fixed stack. -/
noncomputable def transitionEqStackHeightSegment
    (tm : _root_.Turing.FinTM2) (k : tm.K) : TransitionEqSegment :=
  let header := TransitionAffineNat.const (transitionEqPrefixWidth tm)
  let stackOffset := transitionStackBitOffsetAffine tm k
  { publicBase := header.add stackOffset
    workspaceBase := header.add
      (stackOffset.shiftInput (maxPushesPerStep tm))
    count := { constant := 1, coefficient := 1 } }

/-- Public cell-symbol coordinates of one fixed stack. -/
noncomputable def transitionEqStackCellSegment
    (tm : _root_.Turing.FinTM2) (k : tm.K) : TransitionEqSegment :=
  let header := TransitionAffineNat.const (transitionEqPrefixWidth tm)
  let publicOffset := transitionStackBitOffsetAffine tm k
  let workspaceOffset :=
    publicOffset.shiftInput (maxPushesPerStep tm)
  let heightSucc : TransitionAffineNat :=
    { constant := 1, coefficient := 1 }
  let width := (reachableAlphabet tm k).card + 1
  { publicBase := (header.add publicOffset).add heightSucc
    workspaceBase := (header.add workspaceOffset).add
      (heightSucc.shiftInput (maxPushesPerStep tm))
    count := { constant := 0, coefficient := width } }

/-- Canonical fixed list of equality segments: common prefix, then height and
cell blocks for every stack in the machine's fixed finite ordering. -/
noncomputable def transitionEqSegments
    (tm : _root_.Turing.FinTM2) : List TransitionEqSegment :=
  transitionEqPrefixSegment tm ::
    (arithmeticRuntimeStackSourceIndices tm).flatMap fun index =>
      let k := (arithmeticStackEquiv tm).symm index
      [transitionEqStackHeightSegment tm k,
        transitionEqStackCellSegment tm k]

@[simp] theorem transitionEqPrefixSegment_eval
    (tm : _root_.Turing.FinTM2) (height : Nat) :
    ((transitionEqPrefixSegment tm).publicBase.eval height,
      (transitionEqPrefixSegment tm).workspaceBase.eval height,
      (transitionEqPrefixSegment tm).count.eval height) =
      (0, 0, transitionEqPrefixWidth tm) := by
  simp [transitionEqPrefixSegment]

@[simp] theorem transitionEqStackHeightSegment_eval
    (tm : _root_.Turing.FinTM2) (height : Nat) (k : tm.K) :
    ((transitionEqStackHeightSegment tm k).publicBase.eval height,
      (transitionEqStackHeightSegment tm k).workspaceBase.eval height,
      (transitionEqStackHeightSegment tm k).count.eval height) =
      (transitionEqPrefixWidth tm + cfgStackBitOffset tm height k,
        transitionEqPrefixWidth tm +
          cfgStackBitOffset tm (workHeight tm height) k,
        height + 1) := by
  simp [transitionEqStackHeightSegment, workHeight]
  simp [TransitionAffineNat.eval]
  omega

@[simp] theorem transitionEqStackCellSegment_eval
    (tm : _root_.Turing.FinTM2) (height : Nat) (k : tm.K) :
    ((transitionEqStackCellSegment tm k).publicBase.eval height,
      (transitionEqStackCellSegment tm k).workspaceBase.eval height,
      (transitionEqStackCellSegment tm k).count.eval height) =
      (transitionEqPrefixWidth tm + cfgStackBitOffset tm height k +
          (height + 1),
        transitionEqPrefixWidth tm +
          cfgStackBitOffset tm (workHeight tm height) k +
          (workHeight tm height + 1),
        height * ((reachableAlphabet tm k).card + 1)) := by
  simp only [transitionEqStackCellSegment,
    TransitionAffineNat.eval_add, TransitionAffineNat.eval_const,
    TransitionAffineNat.eval_shiftInput,
    transitionStackBitOffsetAffine_eval]
  simp [TransitionAffineNat.eval, workHeight]
  constructor
  · ring
  constructor <;> ring

/-- First value of one progression: the preceding equality carry wire. -/
noncomputable def transitionEqPreviousForm
    (tm : _root_.Turing.FinTM2)
    (segment : TransitionEqSegment) : AffineUnaryTripleForm :=
  transitionAbsoluteStartForm
    ((transitionEqStartOffsetAffine tm).add
      (segment.publicBase.scale 6))

/-- Third value of one progression: the corresponding next-row source wire. -/
noncomputable def transitionEqNextRowForm
    (tm : _root_.Turing.FinTM2)
    (segment : TransitionEqSegment) : AffineUnaryTripleForm :=
  { constant :=
      (transitionCfgBitAffine tm).constant + segment.publicBase.constant
    first :=
      (transitionCfgBitAffine tm).coefficient +
        segment.publicBase.coefficient
    second := 0
    third := 1 }

/-- Seven runtime values consumed by the generic triple-progression family
controller for one equality segment. -/
noncomputable def transitionEqSegmentDescriptorForms
    (tm : _root_.Turing.FinTM2)
    (segment : TransitionEqSegment) : List AffineUnaryTripleForm :=
  [ transitionEqPreviousForm tm segment,
    transitionFinalMuxWireForm tm
      segment.workspaceBase.constant segment.workspaceBase.coefficient,
    transitionEqNextRowForm tm segment,
    transitionHeightAffineForm (TransitionAffineNat.const 6),
    transitionHeightAffineForm (TransitionAffineNat.const 3),
    transitionHeightAffineForm (TransitionAffineNat.const 1),
    transitionHeightAffineForm segment.count ]

/-- Complete fixed descriptor-form table for one transition row seed. -/
noncomputable def transitionEqProgressionDescriptorForms
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  (transitionEqSegments tm).flatMap
    (transitionEqSegmentDescriptorForms tm)

/-- Runtime progression denoted by one segment and one transition row seed. -/
noncomputable def transitionEqSegmentProgression
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (segment : TransitionEqSegment) : AffineUnaryTripleProgression :=
  { base₁ := affineUnaryTripleFormValue
      (transitionEqPreviousForm tm segment) (transitionTailAffineSeed seed)
    base₂ := affineUnaryTripleFormValue
      (transitionFinalMuxWireForm tm
        segment.workspaceBase.constant segment.workspaceBase.coefficient)
      (transitionTailAffineSeed seed)
    base₃ := affineUnaryTripleFormValue
      (transitionEqNextRowForm tm segment) (transitionTailAffineSeed seed)
    step₁ := 6
    step₂ := 3
    step₃ := 1
    count := segment.count.eval seed.height }

/-- Runtime progression family for all public/workspace coordinate segments
of one transition row. -/
noncomputable def transitionEqProgressions
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List AffineUnaryTripleProgression :=
  (transitionEqSegments tm).map (transitionEqSegmentProgression tm seed)

/-- The first progression coordinate is the equality carry immediately before
the segment's first public coordinate. -/
theorem transitionEqSegmentProgression_base₁
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (segment : TransitionEqSegment)
    (hwork : 0 < workHeight tm seed.height) :
    (transitionEqSegmentProgression tm seed segment).base₁ =
      transitionEqStart tm seed.height seed.start +
        6 * segment.publicBase.eval seed.height := by
  have hstart : seed.start +
      (transitionEqStartOffsetAffine tm).eval seed.height =
      transitionEqStart tm seed.height seed.start := by
    calc
      seed.start + (transitionEqStartOffsetAffine tm).eval seed.height =
          affineUnaryTripleFormValue (transitionEqStartForm tm)
            (transitionTailAffineSeed seed) := by
        symm
        exact transitionAbsoluteStartForm_value
          (transitionEqStartOffsetAffine tm) seed
      _ = transitionEqStart tm seed.height seed.start :=
        transitionEqStartForm_value tm seed hwork
  unfold transitionEqSegmentProgression transitionEqPreviousForm
  rw [transitionAbsoluteStartForm_value,
    TransitionAffineNat.eval_add, TransitionAffineNat.eval_scale]
  change seed.start +
      ((transitionEqStartOffsetAffine tm).eval seed.height +
        6 * segment.publicBase.eval seed.height) = _
  omega

/-- The second progression coordinate is the exact arithmetic final-mux wire
at the corresponding workspace segment base. -/
theorem transitionEqSegmentProgression_base₂
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (segment : TransitionEqSegment)
    (hwork : 0 < workHeight tm seed.height) :
    (transitionEqSegmentProgression tm seed segment).base₂ =
      seed.start + 2 +
          transitionDispatchListFinalMuxOffset tm seed.height
            (programLabels tm) + 3 +
        3 * segment.workspaceBase.eval seed.height := by
  unfold transitionEqSegmentProgression
  rw [transitionFinalMuxWireForm_value,
    transitionFinalMuxStartForm_value tm seed hwork]
  rfl

/-- The third progression coordinate is the exact source wire in the next
public tableau row. -/
theorem transitionEqSegmentProgression_base₃
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (segment : TransitionEqSegment) :
    (transitionEqSegmentProgression tm seed segment).base₃ =
      seed.rowBase + cfgBitCount tm seed.height +
        segment.publicBase.eval seed.height := by
  unfold transitionEqSegmentProgression transitionEqNextRowForm
    transitionTailAffineSeed affineUnaryTripleFormValue
    TransitionAffineNat.eval
  rw [← transitionCfgBitAffine_eval tm seed.height]
  unfold TransitionAffineNat.eval
  ring

/-- All three fixed strides and the runtime segment length are represented
literally in the progression descriptor. -/
theorem transitionEqSegmentProgression_steps_count
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (segment : TransitionEqSegment) :
    ((transitionEqSegmentProgression tm seed segment).step₁,
      (transitionEqSegmentProgression tm seed segment).step₂,
      (transitionEqSegmentProgression tm seed segment).step₃,
      (transitionEqSegmentProgression tm seed segment).count) =
      (6, 3, 1, segment.count.eval seed.height) := by
  rfl

/-- The fixed seven-form block is byte-for-byte the canonical descriptor of
the runtime progression it denotes. -/
theorem transitionEqSegmentDescriptorForms_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (segment : TransitionEqSegment) :
    affineUnaryTripleMap (transitionEqSegmentDescriptorForms tm segment)
        (transitionTailAffineSeed seed) =
      [ (transitionEqSegmentProgression tm seed segment).base₁,
        (transitionEqSegmentProgression tm seed segment).base₂,
        (transitionEqSegmentProgression tm seed segment).base₃,
        (transitionEqSegmentProgression tm seed segment).step₁,
        (transitionEqSegmentProgression tm seed segment).step₂,
        (transitionEqSegmentProgression tm seed segment).step₃,
        (transitionEqSegmentProgression tm seed segment).count ] := by
  simp [transitionEqSegmentDescriptorForms,
    transitionEqSegmentProgression, affineUnaryTripleMap]

/-- Evaluating the complete fixed form table yields exactly the concatenated
runtime progression descriptors for one row. -/
theorem transitionEqProgressionDescriptorForms_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    affineUnaryTripleMap (transitionEqProgressionDescriptorForms tm)
        (transitionTailAffineSeed seed) =
      (transitionEqProgressions tm seed).flatMap fun progression =>
        [progression.base₁, progression.base₂, progression.base₃,
          progression.step₁, progression.step₂, progression.step₃,
          progression.count] := by
  unfold transitionEqProgressionDescriptorForms transitionEqProgressions
    affineUnaryTripleMap
  rw [List.map_flatMap, List.flatMap_map]
  apply List.flatMap_congr
  intro segment _
  exact transitionEqSegmentDescriptorForms_value tm seed segment

/-- The descriptor bytes for one row are exactly the generic progression
family encoding, not merely a list with the same decoded values. -/
theorem encode_transitionEqProgressionDescriptorForms
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    encodeUnaryFrame
        (affineUnaryTripleMap (transitionEqProgressionDescriptorForms tm)
          (transitionTailAffineSeed seed)) =
      encodeAffineUnaryTripleProgressionFamily
        (transitionEqProgressions tm seed) := by
  rw [transitionEqProgressionDescriptorForms_value]
  unfold encodeUnaryFrame
  induction transitionEqProgressions tm seed with
  | nil => rfl
  | cons progression rest ih =>
      simp only [List.flatMap_cons,
        encodeAffineUnaryTripleProgressionFamily,
        encodeAffineUnaryTripleProgression, List.flatMap_append]
      rw [ih]
      simp [encodeUnaryFrame, List.append_assoc]

/-- Raw-input descriptor stream for all equality segments of all transition
rows. -/
noncomputable def verifierTransitionEqProgressionDescriptorFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  verifierTransitionAffineMapFrames W
    (transitionEqProgressionDescriptorForms W.machine.tm) input

/-- Exact byte semantics of the raw-input descriptor source. -/
theorem verifierTransitionEqProgressionDescriptorFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionEqProgressionDescriptorFrames W input =
      encodeAffineUnaryTripleProgressionFamily
        ((verifierTransitionRowSeeds W input).flatMap
          (transitionEqProgressions W.machine.tm)) := by
  unfold verifierTransitionEqProgressionDescriptorFrames
    verifierTransitionAffineMapFrames verifierTransitionTailAffineSeeds
    affineUnaryTripleMapFamily encodeUnaryFrame
  rw [List.flatMap_map]
  generalize verifierTransitionRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [List.flatMap_cons, List.flatMap_append]
      have hseed := encode_transitionEqProgressionDescriptorForms
        W.machine.tm seed
      unfold encodeUnaryFrame at hseed
      rw [hseed, ih]
      induction transitionEqProgressions W.machine.tm seed with
      | nil => rfl
      | cons progression progressions segmentIh =>
          simp [encodeAffineUnaryTripleProgressionFamily, segmentIh]

/-- One fixed polynomial-time TM2 emits all equality progression descriptors
directly from the raw verifier input. -/
noncomputable def
    verifierTransitionEqProgressionDescriptorFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionEqProgressionDescriptorFrames W) := by
  exact verifierTransitionAffineMapFrames_computableInPolyTime W
    (transitionEqProgressionDescriptorForms W.machine.tm)

end CLRS.Chapter34.Turing.CookLevin

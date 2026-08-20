import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionTailAffine
import Mathlib.Tactic

/-!
# Concrete transition final-conjunction source

This module compiles the last gate of every local Cook--Levin transition
script.  The public equality output and overflow-fit output are affine in the
raw row seed, so a fixed affine source followed by a fixed delimiter map emits
the exact `AffineAndFinPairFrame` protocol.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Five ordinary fields for one final AND invocation.  The delimiter pass
turns them into `tick ; right ; 0 ; left ; frameEnd`. -/
noncomputable def transitionFinalAndInvocationForms
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  [ transitionZeroForm,
    transitionEqWireForm tm,
    transitionZeroForm,
    transitionFitWireForm tm,
    transitionZeroForm ]

/-- Semantic values carried by the final-conjunction invocation of one row. -/
def transitionFinalAndInvocationValues
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) : List Nat :=
  [ 0,
    transitionEqWire tm seed.height seed.start,
    0,
    transitionFitWire tm seed.height seed.start,
    0 ]

/-- The fixed affine form table evaluates to the exact final-conjunction
operands for every positive-workspace row seed. -/
theorem transitionFinalAndInvocationForms_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    affineUnaryTripleMap (transitionFinalAndInvocationForms tm)
        (transitionTailAffineSeed seed) =
      transitionFinalAndInvocationValues tm seed := by
  unfold transitionFinalAndInvocationForms affineUnaryTripleMap
  simp only [List.map_cons, List.map_nil]
  rw [transitionEqWireForm_value tm seed hwork,
    transitionFitWireForm_value tm seed hwork]
  simp [transitionZeroForm, affineUnaryTripleFormValue,
    transitionFinalAndInvocationValues]

/-- Fixed five-position delimiter cycle of one `AffineAndFinPairFrame`. -/
def transitionFinalAndInvocationDelimiterTable : List UnaryFrameSym :=
  [.tick, .separator, .separator, .separator, .frameEnd]

@[simp] theorem transitionFinalAndInvocationDelimiterTable_length :
    transitionFinalAndInvocationDelimiterTable.length = 5 := rfl

theorem transitionFinalAndInvocationDelimiterTable_nonempty :
    0 < transitionFinalAndInvocationDelimiterTable.length := by simp

private theorem transitionFinalAndInvocationDelimiter_frames
    (frames : List AffineAndFinPairFrame) :
    encodeUnaryFrameWithDelimiterCycle
        transitionFinalAndInvocationDelimiterTable
        transitionFinalAndInvocationDelimiterTable_nonempty
        (frames.flatMap fun frame =>
          [0, frame.right, 0, frame.left, 0]) =
      encodeAffineAndFinFrames frames := by
  induction frames with
  | nil => rfl
  | cons frame frames ih =>
      simp [encodeUnaryFrameWithDelimiterCycle,
        encodeUnaryFrameWithDelimiterCycleFrom,
        transitionFinalAndInvocationDelimiterTable,
        unaryFrameDelimiterNext, encodeAffineAndFinFrames,
        encodeAffineAndFinPairFrame, encodeUnaryFrame,
        encodeUnaryFrameBlock, List.append_assoc]
      change encodeUnaryFrameWithDelimiterCycle
          transitionFinalAndInvocationDelimiterTable
          transitionFinalAndInvocationDelimiterTable_nonempty
          (frames.flatMap fun frame =>
            [0, frame.right, 0, frame.left, 0]) =
        encodeAffineAndFinFrames frames
      exact ih

private theorem transitionFinalAndInvocationValues_eq_script
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (nextRowBase : Nat) :
    transitionFinalAndInvocationValues tm seed =
      let frame := (transitionScriptFromSeed tm seed nextRowBase).finalAnd
      [0, frame.right, 0, frame.left, 0] := by
  rfl

/-- Delimiter-exact final-conjunction inputs for all verifier transition rows. -/
noncomputable def verifierTransitionFinalAndInvocationInput
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFrameDelimiters
    transitionFinalAndInvocationDelimiterTable
    transitionFinalAndInvocationDelimiterTable_nonempty
    (verifierTransitionAffineMapFrames W
      (transitionFinalAndInvocationForms W.machine.tm) input)

/-- The concrete source emits exactly the final conjunction stored by every
canonical seed-derived transition script, byte for byte. -/
theorem verifierTransitionFinalAndInvocationInput_eq_scripts
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionFinalAndInvocationInput W input =
      encodeAffineAndFinFrames
        ((verifierTransitionRowSeeds W input).map fun seed =>
          (transitionScriptFromSeed W.machine.tm seed
            (seed.rowBase +
              cfgBitCount W.machine.tm seed.height)).finalAnd) := by
  unfold verifierTransitionFinalAndInvocationInput
    verifierTransitionAffineMapFrames verifierTransitionTailAffineSeeds
    affineUnaryTripleMapFamily
  rw [rewriteUnaryFrameDelimiters_encodeUnaryFrame, List.flatMap_map]
  have hvalues :
      (verifierTransitionRowSeeds W input).flatMap
          (fun seed => affineUnaryTripleMap
            (transitionFinalAndInvocationForms W.machine.tm)
            (transitionTailAffineSeed seed)) =
        (verifierTransitionRowSeeds W input).flatMap
          (transitionFinalAndInvocationValues W.machine.tm) := by
    apply List.flatMap_congr
    intro seed hseed
    apply transitionFinalAndInvocationForms_value
    rw [verifierTransitionRowSeeds_height_eq W input seed hseed]
    exact Nat.add_pos_left
      (verifierHeight_eval_pos W input.length)
      (maxPushesPerStep W.machine.tm)
  rw [hvalues]
  have hscripts :
      (verifierTransitionRowSeeds W input).flatMap
          (transitionFinalAndInvocationValues W.machine.tm) =
        ((verifierTransitionRowSeeds W input).map fun seed =>
          (transitionScriptFromSeed W.machine.tm seed
            (seed.rowBase +
              cfgBitCount W.machine.tm seed.height)).finalAnd).flatMap
            (fun frame => [0, frame.right, 0, frame.left, 0]) := by
    rw [List.flatMap_map]
    apply List.flatMap_congr
    intro seed _
    exact transitionFinalAndInvocationValues_eq_script W.machine.tm seed
      (seed.rowBase + cfgBitCount W.machine.tm seed.height)
  rw [hscripts]
  exact transitionFinalAndInvocationDelimiter_frames _

/-- One fixed polynomial-time TM2 emits every final-conjunction invocation
directly from the raw verifier word. -/
noncomputable def
    verifierTransitionFinalAndInvocationInput_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionFinalAndInvocationInput W) := by
  let values := verifierTransitionAffineMapFrames_computableInPolyTime W
    (transitionFinalAndInvocationForms W.machine.tm)
  let delimiters := unaryFrameDelimiterMap_computableInPolyTime
    transitionFinalAndInvocationDelimiterTable
    transitionFinalAndInvocationDelimiterTable_nonempty
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      values delimiters
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [Function.comp_def,
          verifierTransitionFinalAndInvocationInput] using run }

end CLRS.Chapter34.Turing.CookLevin

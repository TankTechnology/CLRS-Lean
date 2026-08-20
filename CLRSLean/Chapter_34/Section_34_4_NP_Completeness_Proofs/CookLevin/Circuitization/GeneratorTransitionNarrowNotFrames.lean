import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionTailAffine
import Mathlib.Tactic

/-!
# Concrete transition narrowing-negation source

After the overflow OR frames, the continuous narrowing controller consumes a
single NOT invocation.  This module compiles that invocation from every raw
transition row seed and proves literal agreement with the canonical local
transition script.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Five ordinary fields whose delimiters become
`tick ; 0 ; 0 ; source ; frameEnd`. -/
noncomputable def transitionNarrowNotInvocationForms
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  [ transitionZeroForm,
    transitionZeroForm,
    transitionZeroForm,
    transitionNarrowSourceForm tm,
    transitionZeroForm ]

/-- Semantic values of the one-row narrowing NOT protocol. -/
def transitionNarrowNotInvocationValues
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) : List Nat :=
  [0, 0, 0, transitionNarrowSourceWire tm seed.height seed.start, 0]

/-- The fixed affine table computes the exact narrowing source wire. -/
theorem transitionNarrowNotInvocationForms_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    affineUnaryTripleMap (transitionNarrowNotInvocationForms tm)
        (transitionTailAffineSeed seed) =
      transitionNarrowNotInvocationValues tm seed := by
  unfold transitionNarrowNotInvocationForms affineUnaryTripleMap
  simp only [List.map_cons, List.map_nil]
  rw [transitionNarrowSourceForm_value tm seed hwork]
  simp [transitionZeroForm, affineUnaryTripleFormValue,
    transitionNarrowNotInvocationValues]

/-- Fixed delimiter cycle for the post-OR NOT invocation. -/
def transitionNarrowNotInvocationDelimiterTable : List UnaryFrameSym :=
  [.tick, .separator, .separator, .separator, .frameEnd]

@[simp] theorem transitionNarrowNotInvocationDelimiterTable_length :
    transitionNarrowNotInvocationDelimiterTable.length = 5 := rfl

theorem transitionNarrowNotInvocationDelimiterTable_nonempty :
    0 < transitionNarrowNotInvocationDelimiterTable.length := by simp

private theorem transitionNarrowNotInvocationDelimiter_sources
    (sources : List Nat) :
    encodeUnaryFrameWithDelimiterCycle
        transitionNarrowNotInvocationDelimiterTable
        transitionNarrowNotInvocationDelimiterTable_nonempty
        (sources.flatMap fun source => [0, 0, 0, source, 0]) =
      sources.flatMap fun source =>
        .tick :: encodeUnaryFrame [0, 0, source] ++ [.frameEnd] := by
  induction sources with
  | nil => rfl
  | cons source sources ih =>
      simp [encodeUnaryFrameWithDelimiterCycle,
        encodeUnaryFrameWithDelimiterCycleFrom,
        transitionNarrowNotInvocationDelimiterTable,
        unaryFrameDelimiterNext, encodeUnaryFrame,
        encodeUnaryFrameBlock, List.append_assoc]
      simpa [encodeUnaryFrameWithDelimiterCycle,
        transitionNarrowNotInvocationDelimiterTable, encodeUnaryFrame,
        encodeUnaryFrameBlock] using ih

theorem transitionNarrowNotInvocationValues_eq_script
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (nextRowBase : Nat) :
    transitionNarrowNotInvocationValues tm seed =
      let source :=
        (transitionScriptFromSeed tm seed nextRowBase).narrowSource
      [0, 0, 0, source, 0] := by
  rfl

/-- Delimiter-exact NOT invocations for all verifier transition rows. -/
noncomputable def verifierTransitionNarrowNotInvocationInput
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFrameDelimiters
    transitionNarrowNotInvocationDelimiterTable
    transitionNarrowNotInvocationDelimiterTable_nonempty
    (verifierTransitionAffineMapFrames W
      (transitionNarrowNotInvocationForms W.machine.tm) input)

/-- The generated stream is the exact post-OR NOT suffix of every canonical
seed-derived transition script. -/
theorem verifierTransitionNarrowNotInvocationInput_eq_scripts
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionNarrowNotInvocationInput W input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        let source :=
          (transitionScriptFromSeed W.machine.tm seed
            (seed.rowBase +
              cfgBitCount W.machine.tm seed.height)).narrowSource
        .tick :: encodeUnaryFrame [0, 0, source] ++ [.frameEnd] := by
  unfold verifierTransitionNarrowNotInvocationInput
    verifierTransitionAffineMapFrames verifierTransitionTailAffineSeeds
    affineUnaryTripleMapFamily
  rw [rewriteUnaryFrameDelimiters_encodeUnaryFrame, List.flatMap_map]
  have hvalues :
      (verifierTransitionRowSeeds W input).flatMap
          (fun seed => affineUnaryTripleMap
            (transitionNarrowNotInvocationForms W.machine.tm)
            (transitionTailAffineSeed seed)) =
        (verifierTransitionRowSeeds W input).flatMap
          (transitionNarrowNotInvocationValues W.machine.tm) := by
    apply List.flatMap_congr
    intro seed hseed
    apply transitionNarrowNotInvocationForms_value
    rw [verifierTransitionRowSeeds_height_eq W input seed hseed]
    exact Nat.add_pos_left
      (verifierHeight_eval_pos W input.length)
      (maxPushesPerStep W.machine.tm)
  rw [hvalues]
  have hscripts :
      (verifierTransitionRowSeeds W input).flatMap
          (transitionNarrowNotInvocationValues W.machine.tm) =
        ((verifierTransitionRowSeeds W input).map fun seed =>
          (transitionScriptFromSeed W.machine.tm seed
            (seed.rowBase +
              cfgBitCount W.machine.tm seed.height)).narrowSource).flatMap
            (fun source => [0, 0, 0, source, 0]) := by
    rw [List.flatMap_map]
    apply List.flatMap_congr
    intro seed _
    exact transitionNarrowNotInvocationValues_eq_script W.machine.tm seed
      (seed.rowBase + cfgBitCount W.machine.tm seed.height)
  rw [hscripts]
  simpa only [List.flatMap_map] using
    transitionNarrowNotInvocationDelimiter_sources
      ((verifierTransitionRowSeeds W input).map fun seed =>
        (transitionScriptFromSeed W.machine.tm seed
          (seed.rowBase +
            cfgBitCount W.machine.tm seed.height)).narrowSource)

/-- One fixed polynomial-time TM2 compiles every narrowing NOT invocation
directly from the raw verifier word. -/
noncomputable def
    verifierTransitionNarrowNotInvocationInput_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionNarrowNotInvocationInput W) := by
  let values := verifierTransitionAffineMapFrames_computableInPolyTime W
    (transitionNarrowNotInvocationForms W.machine.tm)
  let delimiters := unaryFrameDelimiterMap_computableInPolyTime
    transitionNarrowNotInvocationDelimiterTable
    transitionNarrowNotInvocationDelimiterTable_nonempty
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
          verifierTransitionNarrowNotInvocationInput] using run }

end CLRS.Chapter34.Turing.CookLevin

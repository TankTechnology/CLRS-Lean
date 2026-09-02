import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionEqRowTaggedValues
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionEqCanonicalAlignment
import Mathlib.Tactic

/-!
# Delimiter-exact row-bounded transition equalities

The preceding source emits nine ordinary unary fields for every equality and
one pre-existing `frameEnd` after every transition row.  Here the fixed
nine-position delimiter transducer materializes the canonical equality-frame
delimiters.  Because nine fields return its finite cursor to zero and existing
`frameEnd`s do not advance that cursor, the outer tableau-row boundaries are
preserved byte for byte.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- The nine value fields underlying one canonical equality invocation. -/
def transitionEqFrameInvocationValues
    (frame : AffineEqFinPairFrame) : List Nat :=
  [0, frame.eqStart, frame.left, frame.right, 0,
    frame.matched, 0, frame.previous, 0]

@[simp] theorem transitionEqInvocationForms_value_eq_frameValues
    (seed : AffineUnaryTripleSeed) :
    affineUnaryTripleMap transitionEqInvocationForms seed =
      transitionEqFrameInvocationValues (transitionEqCoordinateFrame seed) := by
  simpa only [transitionEqFrameInvocationValues] using
    transitionEqInvocationForms_value seed

/-- The nine-field affine value source for one row is exactly the flattening
of its generated equality frames. -/
theorem transitionEqInvocationValues_eq_generatedFrames
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    affineUnaryTripleMapFamily transitionEqInvocationForms
        (transitionEqCoordinateSeeds tm seed) =
      (transitionEqGeneratedFrames tm seed).flatMap
        transitionEqFrameInvocationValues := by
  unfold affineUnaryTripleMapFamily transitionEqGeneratedFrames
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro coordinate _
  exact transitionEqInvocationForms_value_eq_frameValues coordinate

private theorem transitionEqDelimiter_ticks
    (index : Fin transitionEqInvocationDelimiterTable.length)
    (count : Nat) (tail : List UnaryFrameSym) :
    rewriteUnaryFrameDelimitersFrom
        transitionEqInvocationDelimiterTable
        transitionEqInvocationDelimiterTable_nonempty index
        (List.replicate count .tick ++ tail) =
      List.replicate count .tick ++
        rewriteUnaryFrameDelimitersFrom
          transitionEqInvocationDelimiterTable
          transitionEqInvocationDelimiterTable_nonempty index tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append,
        rewriteUnaryFrameDelimitersFrom, unaryFrameDelimiterStep]
      exact congrArg (List.cons .tick) ih

private def transitionEqDelimiterIndex (position : Fin 9) :
    Fin transitionEqInvocationDelimiterTable.length :=
  ⟨position.val, by
    rw [transitionEqInvocationDelimiterTable_length]
    exact position.isLt⟩

private theorem transitionEqDelimiterIndex_zero :
    transitionEqDelimiterIndex 0 =
      ⟨0, transitionEqInvocationDelimiterTable_nonempty⟩ := by
  apply Fin.ext
  rfl

private theorem transitionEqDelimiter_separator0
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameDelimitersFrom transitionEqInvocationDelimiterTable
        transitionEqInvocationDelimiterTable_nonempty
        (transitionEqDelimiterIndex 0)
        (.separator :: tail) =
      .frameEnd :: rewriteUnaryFrameDelimitersFrom
        transitionEqInvocationDelimiterTable
        transitionEqInvocationDelimiterTable_nonempty
        (transitionEqDelimiterIndex 1) tail := by rfl

private theorem transitionEqDelimiter_separator1
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameDelimitersFrom transitionEqInvocationDelimiterTable
        transitionEqInvocationDelimiterTable_nonempty
        (transitionEqDelimiterIndex 1)
        (.separator :: tail) =
      .separator :: rewriteUnaryFrameDelimitersFrom
        transitionEqInvocationDelimiterTable
        transitionEqInvocationDelimiterTable_nonempty
        (transitionEqDelimiterIndex 2) tail := by rfl

private theorem transitionEqDelimiter_separator2
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameDelimitersFrom transitionEqInvocationDelimiterTable
        transitionEqInvocationDelimiterTable_nonempty
        (transitionEqDelimiterIndex 2)
        (.separator :: tail) =
      .separator :: rewriteUnaryFrameDelimitersFrom
        transitionEqInvocationDelimiterTable
        transitionEqInvocationDelimiterTable_nonempty
        (transitionEqDelimiterIndex 3) tail := by rfl

private theorem transitionEqDelimiter_separator3
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameDelimitersFrom transitionEqInvocationDelimiterTable
        transitionEqInvocationDelimiterTable_nonempty
        (transitionEqDelimiterIndex 3)
        (.separator :: tail) =
      .separator :: rewriteUnaryFrameDelimitersFrom
        transitionEqInvocationDelimiterTable
        transitionEqInvocationDelimiterTable_nonempty
        (transitionEqDelimiterIndex 4) tail := by rfl

private theorem transitionEqDelimiter_separator4
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameDelimitersFrom transitionEqInvocationDelimiterTable
        transitionEqInvocationDelimiterTable_nonempty
        (transitionEqDelimiterIndex 4)
        (.separator :: tail) =
      .frameEnd :: rewriteUnaryFrameDelimitersFrom
        transitionEqInvocationDelimiterTable
        transitionEqInvocationDelimiterTable_nonempty
        (transitionEqDelimiterIndex 5) tail := by rfl

private theorem transitionEqDelimiter_separator5
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameDelimitersFrom transitionEqInvocationDelimiterTable
        transitionEqInvocationDelimiterTable_nonempty
        (transitionEqDelimiterIndex 5)
        (.separator :: tail) =
      .separator :: rewriteUnaryFrameDelimitersFrom
        transitionEqInvocationDelimiterTable
        transitionEqInvocationDelimiterTable_nonempty
        (transitionEqDelimiterIndex 6) tail := by rfl

private theorem transitionEqDelimiter_separator6
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameDelimitersFrom transitionEqInvocationDelimiterTable
        transitionEqInvocationDelimiterTable_nonempty
        (transitionEqDelimiterIndex 6)
        (.separator :: tail) =
      .separator :: rewriteUnaryFrameDelimitersFrom
        transitionEqInvocationDelimiterTable
        transitionEqInvocationDelimiterTable_nonempty
        (transitionEqDelimiterIndex 7) tail := by rfl

private theorem transitionEqDelimiter_separator7
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameDelimitersFrom transitionEqInvocationDelimiterTable
        transitionEqInvocationDelimiterTable_nonempty
        (transitionEqDelimiterIndex 7)
        (.separator :: tail) =
      .separator :: rewriteUnaryFrameDelimitersFrom
        transitionEqInvocationDelimiterTable
        transitionEqInvocationDelimiterTable_nonempty
        (transitionEqDelimiterIndex 8) tail := by rfl

private theorem transitionEqDelimiter_separator8
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameDelimitersFrom transitionEqInvocationDelimiterTable
        transitionEqInvocationDelimiterTable_nonempty
        (transitionEqDelimiterIndex 8)
        (.separator :: tail) =
      .frameEnd :: rewriteUnaryFrameDelimitersFrom
        transitionEqInvocationDelimiterTable
        transitionEqInvocationDelimiterTable_nonempty
        (transitionEqDelimiterIndex 0) tail := by rfl

private theorem transitionEqDelimiter_one_append
    (frame : AffineEqFinPairFrame) (tail : List UnaryFrameSym) :
    rewriteUnaryFrameDelimitersFrom
        transitionEqInvocationDelimiterTable
        transitionEqInvocationDelimiterTable_nonempty
        (transitionEqDelimiterIndex 0)
        (encodeUnaryFrame (transitionEqFrameInvocationValues frame) ++ tail) =
      encodeAffineEqFinPairFrame frame ++
        rewriteUnaryFrameDelimitersFrom
          transitionEqInvocationDelimiterTable
          transitionEqInvocationDelimiterTable_nonempty
          (transitionEqDelimiterIndex 0) tail := by
  simp only [transitionEqFrameInvocationValues, encodeUnaryFrame,
    List.flatMap_cons, List.flatMap_nil, encodeUnaryFrameBlock,
    List.append_assoc, List.singleton_append, List.replicate_zero,
    List.nil_append, encodeAffineEqFinPairFrame]
  simp only [List.cons_append]
  simp only [List.append_assoc]
  rw [transitionEqDelimiter_separator0, transitionEqDelimiter_ticks]
  try simp only [List.cons_append, List.append_assoc]
  rw [transitionEqDelimiter_separator1, transitionEqDelimiter_ticks]
  try simp only [List.cons_append, List.append_assoc]
  rw [transitionEqDelimiter_separator2, transitionEqDelimiter_ticks]
  try simp only [List.cons_append, List.append_assoc]
  rw [transitionEqDelimiter_separator3, transitionEqDelimiter_separator4,
    transitionEqDelimiter_ticks]
  try simp only [List.cons_append, List.append_assoc]
  rw [transitionEqDelimiter_separator5, transitionEqDelimiter_separator6,
    transitionEqDelimiter_ticks]
  try simp only [List.cons_append, List.append_assoc]
  rw [transitionEqDelimiter_separator7, transitionEqDelimiter_separator8]
  simp only [List.nil_append]

private theorem transitionEqDelimiter_frames_append
    (frames : List AffineEqFinPairFrame) (tail : List UnaryFrameSym) :
    rewriteUnaryFrameDelimitersFrom
        transitionEqInvocationDelimiterTable
        transitionEqInvocationDelimiterTable_nonempty
        (transitionEqDelimiterIndex 0)
        (encodeUnaryFrame
            (frames.flatMap transitionEqFrameInvocationValues) ++ tail) =
      encodeAffineEqFinFrames frames ++
        rewriteUnaryFrameDelimitersFrom
          transitionEqInvocationDelimiterTable
          transitionEqInvocationDelimiterTable_nonempty
          (transitionEqDelimiterIndex 0) tail := by
  induction frames with
  | nil => rfl
  | cons frame frames ih =>
      rw [show encodeUnaryFrame
              ((frame :: frames).flatMap transitionEqFrameInvocationValues) ++
              tail =
            encodeUnaryFrame (transitionEqFrameInvocationValues frame) ++
              (encodeUnaryFrame
                (frames.flatMap transitionEqFrameInvocationValues) ++ tail) by
          simp [encodeUnaryFrame, List.append_assoc]]
      rw [transitionEqDelimiter_one_append, ih]
      simp [encodeAffineEqFinFrames, List.append_assoc]

private theorem transitionEqDelimiter_rowFamilies
    (rows : List (List AffineEqFinPairFrame)) :
    rewriteUnaryFrameDelimiters
        transitionEqInvocationDelimiterTable
        transitionEqInvocationDelimiterTable_nonempty
        (rows.flatMap fun frames =>
          encodeUnaryFrame
              (frames.flatMap transitionEqFrameInvocationValues) ++
            [.frameEnd]) =
      rows.flatMap fun frames =>
        encodeAffineEqFinFrames frames ++ [.frameEnd] := by
  unfold rewriteUnaryFrameDelimiters
  induction rows with
  | nil => rfl
  | cons frames rows ih =>
      simp only [List.flatMap_cons]
      rw [List.append_assoc]
      simp only [List.singleton_append]
      rw [← transitionEqDelimiterIndex_zero]
      let restInput := rows.flatMap fun rest =>
        encodeUnaryFrame
            (rest.flatMap transitionEqFrameInvocationValues) ++ [.frameEnd]
      change rewriteUnaryFrameDelimitersFrom
          transitionEqInvocationDelimiterTable
          transitionEqInvocationDelimiterTable_nonempty
          (transitionEqDelimiterIndex 0)
          (encodeUnaryFrame
              (frames.flatMap transitionEqFrameInvocationValues) ++
            .frameEnd :: restInput) = _
      rw [transitionEqDelimiter_frames_append frames
        (.frameEnd :: restInput)]
      simp only [rewriteUnaryFrameDelimitersFrom,
        unaryFrameDelimiterStep]
      rw [transitionEqDelimiterIndex_zero]
      rw [ih]
      simp [List.append_assoc]

/-- Delimiter-exact equality input with one retained outer marker after every
transition row. -/
noncomputable def verifierTransitionEqRowBoundaryInput
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFrameDelimiters transitionEqInvocationDelimiterTable
    transitionEqInvocationDelimiterTable_nonempty
    (verifierTransitionEqRowMarkedValueFrames W input)

/-- Byte-exact generated-frame semantics, retaining row boundaries. -/
theorem verifierTransitionEqRowBoundaryInput_eq_generatedRows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionEqRowBoundaryInput W input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        encodeAffineEqFinFrames
            (transitionEqGeneratedFrames W.machine.tm seed) ++
          [.frameEnd] := by
  unfold verifierTransitionEqRowBoundaryInput
  rw [verifierTransitionEqRowMarkedValueFrames_eq_rows]
  have hvalues :
      ((verifierTransitionRowSeeds W input).map fun seed =>
        transitionEqGeneratedFrames W.machine.tm seed).flatMap
          (fun frames =>
            encodeUnaryFrame
                (frames.flatMap transitionEqFrameInvocationValues) ++
              [.frameEnd]) =
        (verifierTransitionRowSeeds W input).flatMap (fun seed =>
          encodeUnaryFrame
              (affineUnaryTripleMapFamily transitionEqInvocationForms
                (transitionEqCoordinateSeeds W.machine.tm seed)) ++
            [.frameEnd]) := by
    rw [List.flatMap_map]
    apply List.flatMap_congr
    intro seed _
    rw [transitionEqInvocationValues_eq_generatedFrames]
  rw [← hvalues]
  simpa only [List.flatMap_map] using
    transitionEqDelimiter_rowFamilies
      ((verifierTransitionRowSeeds W input).map fun seed =>
        transitionEqGeneratedFrames W.machine.tm seed)

/-- The row-bounded source is aligned with the equality segment of every
canonical seed-derived transition script. -/
theorem verifierTransitionEqRowBoundaryInput_eq_scripts
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionEqRowBoundaryInput W input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        encodeAffineEqFinFrames
            ((transitionScriptFromSeed W.machine.tm seed
              (seed.rowBase +
                cfgBitCount W.machine.tm seed.height)).eqFrames) ++
          [.frameEnd] := by
  rw [verifierTransitionEqRowBoundaryInput_eq_generatedRows]
  apply List.flatMap_congr
  intro seed hseed
  rw [transitionEqGeneratedFrames_eq_script]
  rw [verifierTransitionRowSeeds_height_eq W input seed hseed]
  exact Nat.add_pos_left
    (verifierHeight_eval_pos W input.length)
    (maxPushesPerStep W.machine.tm)

/-- One fixed polynomial-time TM2 emits the delimiter-exact, row-bounded
equality source directly from the raw verifier word. -/
noncomputable def
    verifierTransitionEqRowBoundaryInput_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionEqRowBoundaryInput W) := by
  let values :=
    verifierTransitionEqRowMarkedValueFrames_computableInPolyTime W
  let delimiters := unaryFrameDelimiterMap_computableInPolyTime
    transitionEqInvocationDelimiterTable
    transitionEqInvocationDelimiterTable_nonempty
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
          verifierTransitionEqRowBoundaryInput] using run }

end CLRS.Chapter34.Turing.CookLevin

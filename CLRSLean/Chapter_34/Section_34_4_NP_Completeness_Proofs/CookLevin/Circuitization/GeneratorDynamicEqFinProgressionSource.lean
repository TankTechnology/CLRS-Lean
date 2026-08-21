import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorEqFinRowProgressionSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactPolynomialUnaryFrameFamily
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameSameInputConcat

/-!
# Equality progressions with a dynamic first coordinate

Canonical equality blocks often start at a wire computed by an earlier
input-dependent phase.  The other six progression fields remain evaluations
of fixed polynomials.  This module combines one verified dynamic unary source
with the exact-polynomial family compiler, then reuses the established triple
progression, affine-map, and delimiter controllers.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- One affine triple progression with a dynamic first base and six exact
polynomial fields. -/
def dynamicFirstAffineUnaryTripleProgression {Γ : Type}
    (first : List Γ → Nat)
    (base₂ base₃ step₁ step₂ step₃ count : Polynomial Nat)
    (input : List Γ) : AffineUnaryTripleProgression :=
  { base₁ := first input
    base₂ := base₂.eval input.length
    base₃ := base₃.eval input.length
    step₁ := step₁.eval input.length
    step₂ := step₂.eval input.length
    step₃ := step₃.eval input.length
    count := count.eval input.length }

/-- Literal same-input source assembled from the dynamic first block and the
six exact-polynomial trailing blocks. -/
def dynamicFirstAffineUnaryTripleProgressionInput {Γ : Type}
    (first : List Γ → Nat)
    (base₂ base₃ step₁ step₂ step₃ count : Polynomial Nat)
    (input : List Γ) : List UnaryFrameSym :=
  encodeUnaryFrameBlock (first input) ++
    exactPolynomialUnaryFrames
      [base₂, base₃, step₁, step₂, step₃, count] input

theorem dynamicFirstAffineUnaryTripleProgression_encode {Γ : Type}
    (first : List Γ → Nat)
    (base₂ base₃ step₁ step₂ step₃ count : Polynomial Nat)
    (input : List Γ) :
    encodeAffineUnaryTripleProgression
        (dynamicFirstAffineUnaryTripleProgression first
          base₂ base₃ step₁ step₂ step₃ count input) =
      dynamicFirstAffineUnaryTripleProgressionInput first
        base₂ base₃ step₁ step₂ step₃ count input := by
  simp [encodeAffineUnaryTripleProgression,
    dynamicFirstAffineUnaryTripleProgression,
    dynamicFirstAffineUnaryTripleProgressionInput,
    exactPolynomialUnaryFrames, encodeUnaryFrame]

/-- Row-major seed stream expanded from the dynamic descriptor. -/
def dynamicFirstAffineUnaryTripleProgressionFrameStream {Γ : Type}
    (first : List Γ → Nat)
    (base₂ base₃ step₁ step₂ step₃ count : Polynomial Nat)
    (input : List Γ) : List UnaryFrameSym :=
  affineUnaryTripleProgressionFrameStream
    (dynamicFirstAffineUnaryTripleProgression first
      base₂ base₃ step₁ step₂ step₃ count input)

/-- A fixed polynomial-time TM2 expands a dynamic-first progression whenever
the dynamic singleton itself has a verified polynomial-time source. -/
noncomputable def
    dynamicFirstAffineUnaryTripleProgressionFrameStream_computableInPolyTime
    {Γ : Type} [Fintype Γ]
    (first : List Γ → Nat)
    (base₂ base₃ step₁ step₂ step₃ count : Polynomial Nat)
    (firstSource : _root_.Turing.TM2ComputableInPolyTime id id
      (fun input => encodeUnaryFrameBlock (first input))) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (dynamicFirstAffineUnaryTripleProgressionFrameStream first
        base₂ base₃ step₁ step₂ step₃ count) := by
  let tail := exactPolynomialUnaryFrames_computableInPolyTime
    (Γ := Γ) [base₂, base₃, step₁, step₂, step₃, count]
  let joined := unaryFrameSameInputConcat_computableInPolyTime
    firstSource tail
  have descriptor : _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineUnaryTripleProgression
      (dynamicFirstAffineUnaryTripleProgression first
        base₂ base₃ step₁ step₂ step₃ count) :=
    { tm := joined.tm
      inputAlphabet := joined.inputAlphabet
      outputAlphabet := joined.outputAlphabet
      time := joined.time
      outputsFun := fun input => by
        have run := joined.outputsFun input
        rw [dynamicFirstAffineUnaryTripleProgression_encode]
        simpa only [id_eq,
          dynamicFirstAffineUnaryTripleProgressionInput] using run }
  let expandedExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch descriptor
      affineUnaryTripleProgressionFrameStream_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => affineUnaryTripleProgressionFrameStream
      (dynamicFirstAffineUnaryTripleProgression first
        base₂ base₃ step₁ step₂ step₃ count input))
  simpa only [Function.comp_def] using Classical.choice expandedExists

/-- Canonical equality frames obtained from a dynamic-first progression. -/
def dynamicFirstAffineEqFinFrames {Γ : Type}
    (first : List Γ → Nat)
    (baseLeft baseRight stepPrevious stepLeft stepRight count : Polynomial Nat)
    (input : List Γ) : List AffineEqFinPairFrame :=
  eqFinProgressionFrames
    (dynamicFirstAffineUnaryTripleProgression first
      baseLeft baseRight stepPrevious stepLeft stepRight count input)

/-- Pointwise closed form of a dynamic-first equality progression. -/
theorem dynamicFirstAffineEqFinFrames_eq_ofFn {Γ : Type}
    (first : List Γ → Nat)
    (baseLeft baseRight stepPrevious stepLeft stepRight count : Polynomial Nat)
    (input : List Γ) :
    dynamicFirstAffineEqFinFrames first
        baseLeft baseRight stepPrevious stepLeft stepRight count input =
      List.ofFn fun index : Fin (count.eval input.length) =>
        { eqStart := first input +
              index.val * stepPrevious.eval input.length + 1
          left := baseLeft.eval input.length +
            index.val * stepLeft.eval input.length
          right := baseRight.eval input.length +
            index.val * stepRight.eval input.length
          matched := first input +
              index.val * stepPrevious.eval input.length + 5
          previous := first input +
            index.val * stepPrevious.eval input.length } := by
  unfold dynamicFirstAffineEqFinFrames eqFinProgressionFrames
    eqFinProgressionSeeds
  rw [affineUnaryTripleProgressionRows_eq_ofFn, List.map_ofFn,
    List.map_ofFn]
  apply List.ofFn_inj.mpr
  funext index
  simp [dynamicFirstAffineUnaryTripleProgression,
    transitionEqCoordinateSeed, transitionEqCoordinateFrame]

/-- Byte-exact equality-controller input for the dynamic-first progression. -/
def dynamicFirstAffineEqFinInput {Γ : Type}
    (first : List Γ → Nat)
    (baseLeft baseRight stepPrevious stepLeft stepRight count : Polynomial Nat)
    (input : List Γ) : List UnaryFrameSym :=
  encodeAffineEqFinFrames
    (dynamicFirstAffineEqFinFrames first
      baseLeft baseRight stepPrevious stepLeft stepRight count input)

/-- A dynamic-first canonical equality progression is compiled by one fixed
polynomial-time TM2. -/
noncomputable def dynamicFirstAffineEqFinInput_computableInPolyTime
    {Γ : Type} [Fintype Γ]
    (first : List Γ → Nat)
    (baseLeft baseRight stepPrevious stepLeft stepRight count : Polynomial Nat)
    (firstSource : _root_.Turing.TM2ComputableInPolyTime id id
      (fun input => encodeUnaryFrameBlock (first input))) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (dynamicFirstAffineEqFinInput first
        baseLeft baseRight stepPrevious stepLeft stepRight count) := by
  let progression :=
    dynamicFirstAffineUnaryTripleProgressionFrameStream_computableInPolyTime
      first baseLeft baseRight stepPrevious stepLeft stepRight count firstSource
  let structured : _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineUnaryTripleSeedFamily
      (fun input : List Γ => eqFinProgressionSeeds
        (dynamicFirstAffineUnaryTripleProgression first
          baseLeft baseRight stepPrevious stepLeft stepRight count input)) :=
    { tm := progression.tm
      inputAlphabet := progression.inputAlphabet
      outputAlphabet := progression.outputAlphabet
      time := progression.time
      outputsFun := fun input => by
        have run := progression.outputsFun input
        simp only [id_eq,
          dynamicFirstAffineUnaryTripleProgressionFrameStream] at run
        rw [affineUnaryTripleProgressionFrameStream_eq_eqFinSeeds] at run
        simpa only [id_eq] using run }
  let mappedExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch structured
      (affineUnaryTripleMapFamily_computableInPolyTime
        transitionEqInvocationForms)
  let delimitedExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (Classical.choice mappedExists)
      (unaryFrameDelimiterMap_computableInPolyTime
        transitionEqInvocationDelimiterTable
        transitionEqInvocationDelimiterTable_nonempty)
  let result := Classical.choice delimitedExists
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simp only [Function.comp_def, id_eq] at run
        rw [eqFinProgression_delimiter_eq_frames] at run
        simpa only [dynamicFirstAffineEqFinInput,
          dynamicFirstAffineEqFinFrames, id_eq] using run }

/-- Dynamic-first row-block equality frames with a fixed affine right table. -/
def dynamicFirstAffineEqFinRowFrames {Γ : Type}
    (rightForms : List AffineUnaryTripleForm)
    (first : List Γ → Nat)
    (baseLeft baseAux stepPrevious stepLeft stepAux count : Polynomial Nat)
    (input : List Γ) : List AffineEqFinPairFrame :=
  eqFinRowProgressionFrames rightForms
    (dynamicFirstAffineUnaryTripleProgression first
      baseLeft baseAux stepPrevious stepLeft stepAux count input)

/-- Row-major closed form of dynamic-first row-block equality frames. -/
theorem dynamicFirstAffineEqFinRowFrames_eq_flatMap_ofFn {Γ : Type}
    (rightForms : List AffineUnaryTripleForm)
    (first : List Γ → Nat)
    (baseLeft baseAux stepPrevious stepLeft stepAux count : Polynomial Nat)
    (input : List Γ) :
    dynamicFirstAffineEqFinRowFrames rightForms first
        baseLeft baseAux stepPrevious stepLeft stepAux count input =
      (List.ofFn fun index : Fin (count.eval input.length) =>
        { first := first input +
              index.val * stepPrevious.eval input.length
          second := baseLeft.eval input.length +
            index.val * stepLeft.eval input.length
          third := baseAux.eval input.length +
            index.val * stepAux.eval input.length }).flatMap
        (affineEqFinRowFrames rightForms) := by
  unfold dynamicFirstAffineEqFinRowFrames eqFinRowProgressionFrames
    eqFinProgressionSeeds
  rw [affineUnaryTripleProgressionRows_eq_ofFn, List.map_ofFn]
  apply congrArg (List.flatMap (affineEqFinRowFrames rightForms))
  apply List.ofFn_inj.mpr
  funext index
  simp [dynamicFirstAffineUnaryTripleProgression,
    transitionEqCoordinateSeed]

/-- Byte-exact row-block input with a dynamic equality-carry base. -/
def dynamicFirstAffineEqFinRowInput {Γ : Type}
    (rightForms : List AffineUnaryTripleForm)
    (first : List Γ → Nat)
    (baseLeft baseAux stepPrevious stepLeft stepAux count : Polynomial Nat)
    (input : List Γ) : List UnaryFrameSym :=
  encodeAffineEqFinFrames
    (dynamicFirstAffineEqFinRowFrames rightForms first
      baseLeft baseAux stepPrevious stepLeft stepAux count input)

/-- A fixed polynomial-time TM2 emits every row-block equality frame with a
dynamic carry base and fixed affine right-target table. -/
noncomputable def dynamicFirstAffineEqFinRowInput_computableInPolyTime
    {Γ : Type} [Fintype Γ]
    (rightForms : List AffineUnaryTripleForm)
    (first : List Γ → Nat)
    (baseLeft baseAux stepPrevious stepLeft stepAux count : Polynomial Nat)
    (firstSource : _root_.Turing.TM2ComputableInPolyTime id id
      (fun input => encodeUnaryFrameBlock (first input))) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (dynamicFirstAffineEqFinRowInput rightForms first
        baseLeft baseAux stepPrevious stepLeft stepAux count) := by
  let progression :=
    dynamicFirstAffineUnaryTripleProgressionFrameStream_computableInPolyTime
      first baseLeft baseAux stepPrevious stepLeft stepAux count firstSource
  let structured : _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineUnaryTripleSeedFamily
      (fun input : List Γ => eqFinProgressionSeeds
        (dynamicFirstAffineUnaryTripleProgression first
          baseLeft baseAux stepPrevious stepLeft stepAux count input)) :=
    { tm := progression.tm
      inputAlphabet := progression.inputAlphabet
      outputAlphabet := progression.outputAlphabet
      time := progression.time
      outputsFun := fun input => by
        have run := progression.outputsFun input
        simp only [id_eq,
          dynamicFirstAffineUnaryTripleProgressionFrameStream] at run
        rw [affineUnaryTripleProgressionFrameStream_eq_eqFinSeeds] at run
        simpa only [id_eq] using run }
  let mappedExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch structured
      (affineUnaryTripleMapFamily_computableInPolyTime
        (affineEqFinRowInvocationForms rightForms))
  let delimitedExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (Classical.choice mappedExists)
      (unaryFrameDelimiterMap_computableInPolyTime
        transitionEqInvocationDelimiterTable
        transitionEqInvocationDelimiterTable_nonempty)
  let result := Classical.choice delimitedExists
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simp only [Function.comp_def, id_eq] at run
        rw [eqFinRowProgression_delimiter_eq_frames] at run
        simpa only [dynamicFirstAffineEqFinRowInput,
          dynamicFirstAffineEqFinRowFrames, id_eq] using run }

end CLRS.Chapter34.Turing.CookLevin

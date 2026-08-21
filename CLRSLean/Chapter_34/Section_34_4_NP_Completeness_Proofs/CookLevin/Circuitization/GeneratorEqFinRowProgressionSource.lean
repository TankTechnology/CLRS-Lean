import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorEqFinProgressionSource

/-!
# Exact-polynomial sources for row blocks of canonical `EqFin` frames

One logical tableau row often compares a consecutive block of left wires
against several verifier-fixed affine right targets.  This module lifts the
single-coordinate progression source to that recurring row-block pattern.

The runtime seed stores the equality carry wire, the first left wire, and an
auxiliary coordinate.  A fixed list of affine forms describes the right
targets.  One fixed affine-map controller expands every seed into all six-gate
equality frames of the row, preserving their canonical adjacency.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Equality frames for the suffix of a logical row beginning at `offset`.
Each coordinate consumes six gates, so the preceding equality carry advances
by six while the left wire advances by one. -/
def affineEqFinRowFramesFrom (offset : Nat) :
    List AffineUnaryTripleForm → AffineUnaryTripleSeed →
      List AffineEqFinPairFrame
  | [], _seed => []
  | rightForm :: rightForms, seed =>
      { eqStart := seed.first + 6 * offset + 1
        left := seed.second + offset
        right := affineUnaryTripleFormValue rightForm seed
        matched := seed.first + 6 * offset + 5
        previous := seed.first + 6 * offset } ::
      affineEqFinRowFramesFrom (offset + 1) rightForms seed

/-- Canonical equality block generated from one logical row seed. -/
def affineEqFinRowFrames (rightForms : List AffineUnaryTripleForm)
    (seed : AffineUnaryTripleSeed) : List AffineEqFinPairFrame :=
  affineEqFinRowFramesFrom 0 rightForms seed

/-- Ordinary affine values needed by the delimiter controller for the suffix
of a logical equality row. -/
def affineEqFinRowInvocationFormsFrom (offset : Nat) :
    List AffineUnaryTripleForm → List AffineUnaryTripleForm
  | [] => []
  | rightForm :: rightForms =>
      [ transitionZeroForm,
        { constant := 6 * offset + 1, first := 1, second := 0, third := 0 },
        { constant := offset, first := 0, second := 1, third := 0 },
        rightForm,
        transitionZeroForm,
        { constant := 6 * offset + 5, first := 1, second := 0, third := 0 },
        transitionZeroForm,
        { constant := 6 * offset, first := 1, second := 0, third := 0 },
        transitionZeroForm ] ++
      affineEqFinRowInvocationFormsFrom (offset + 1) rightForms

/-- Fixed affine expansion table for a complete logical equality row. -/
def affineEqFinRowInvocationForms
    (rightForms : List AffineUnaryTripleForm) :
    List AffineUnaryTripleForm :=
  affineEqFinRowInvocationFormsFrom 0 rightForms

/-- The fixed affine table denotes exactly the flattened invocation values of
all equality frames in one row. -/
theorem affineEqFinRowInvocationFormsFrom_value (offset : Nat)
    (rightForms : List AffineUnaryTripleForm)
    (seed : AffineUnaryTripleSeed) :
    affineUnaryTripleMap
        (affineEqFinRowInvocationFormsFrom offset rightForms) seed =
      (affineEqFinRowFramesFrom offset rightForms seed).flatMap fun frame =>
        [0, frame.eqStart, frame.left, frame.right, 0,
          frame.matched, 0, frame.previous, 0] := by
  induction rightForms generalizing offset with
  | nil => rfl
  | cons rightForm rightForms ih =>
      rw [show affineEqFinRowInvocationFormsFrom offset
          (rightForm :: rightForms) =
          [ transitionZeroForm,
            { constant := 6 * offset + 1,
              first := 1, second := 0, third := 0 },
            { constant := offset,
              first := 0, second := 1, third := 0 },
            rightForm,
            transitionZeroForm,
            { constant := 6 * offset + 5,
              first := 1, second := 0, third := 0 },
            transitionZeroForm,
            { constant := 6 * offset,
              first := 1, second := 0, third := 0 },
            transitionZeroForm ] ++
            affineEqFinRowInvocationFormsFrom (offset + 1) rightForms
          from rfl]
      rw [show affineEqFinRowFramesFrom offset
          (rightForm :: rightForms) seed =
          { eqStart := seed.first + 6 * offset + 1
            left := seed.second + offset
            right := affineUnaryTripleFormValue rightForm seed
            matched := seed.first + 6 * offset + 5
            previous := seed.first + 6 * offset } ::
            affineEqFinRowFramesFrom (offset + 1) rightForms seed
          from rfl]
      rw [show affineUnaryTripleMap
          ([ transitionZeroForm,
             { constant := 6 * offset + 1,
               first := 1, second := 0, third := 0 },
             { constant := offset,
               first := 0, second := 1, third := 0 },
             rightForm,
             transitionZeroForm,
             { constant := 6 * offset + 5,
               first := 1, second := 0, third := 0 },
             transitionZeroForm,
             { constant := 6 * offset,
               first := 1, second := 0, third := 0 },
             transitionZeroForm ] ++
            affineEqFinRowInvocationFormsFrom (offset + 1) rightForms) seed =
          affineUnaryTripleMap
            [ transitionZeroForm,
              { constant := 6 * offset + 1,
                first := 1, second := 0, third := 0 },
              { constant := offset,
                first := 0, second := 1, third := 0 },
              rightForm,
              transitionZeroForm,
              { constant := 6 * offset + 5,
                first := 1, second := 0, third := 0 },
              transitionZeroForm,
              { constant := 6 * offset,
                first := 1, second := 0, third := 0 },
              transitionZeroForm ] seed ++
            affineUnaryTripleMap
              (affineEqFinRowInvocationFormsFrom
                (offset + 1) rightForms) seed by
            simp [affineUnaryTripleMap]]
      rw [ih]
      simp [affineUnaryTripleMap, transitionZeroForm,
        affineUnaryTripleFormValue]
      omega

theorem affineEqFinRowInvocationForms_value
    (rightForms : List AffineUnaryTripleForm)
    (seed : AffineUnaryTripleSeed) :
    affineUnaryTripleMap (affineEqFinRowInvocationForms rightForms) seed =
      (affineEqFinRowFrames rightForms seed).flatMap fun frame =>
        [0, frame.eqStart, frame.left, frame.right, 0,
          frame.matched, 0, frame.previous, 0] := by
  exact affineEqFinRowInvocationFormsFrom_value 0 rightForms seed

/-- Row-major equality frames obtained by expanding every progression seed. -/
def eqFinRowProgressionFrames (rightForms : List AffineUnaryTripleForm)
    (progression : AffineUnaryTripleProgression) :
    List AffineEqFinPairFrame :=
  (eqFinProgressionSeeds progression).flatMap
    (affineEqFinRowFrames rightForms)

/-- Delimiter materialization after row expansion is byte-for-byte the
canonical equality-frame encoding. -/
theorem eqFinRowProgression_delimiter_eq_frames
    (rightForms : List AffineUnaryTripleForm)
    (progression : AffineUnaryTripleProgression) :
    rewriteUnaryFrameDelimiters transitionEqInvocationDelimiterTable
        transitionEqInvocationDelimiterTable_nonempty
        (encodeUnaryFrame
          (affineUnaryTripleMapFamily
            (affineEqFinRowInvocationForms rightForms)
            (eqFinProgressionSeeds progression))) =
      encodeAffineEqFinFrames
        (eqFinRowProgressionFrames rightForms progression) := by
  rw [rewriteUnaryFrameDelimiters_encodeUnaryFrame]
  unfold affineUnaryTripleMapFamily eqFinRowProgressionFrames
  generalize eqFinProgressionSeeds progression = seeds
  have hvalues :
      seeds.flatMap
          (affineUnaryTripleMap
            (affineEqFinRowInvocationForms rightForms)) =
        (seeds.flatMap (affineEqFinRowFrames rightForms)).flatMap fun frame =>
          [0, frame.eqStart, frame.left, frame.right, 0,
            frame.matched, 0, frame.previous, 0] := by
    induction seeds with
    | nil => rfl
    | cons seed seeds ih =>
        simp only [List.flatMap_cons]
        rw [affineEqFinRowInvocationForms_value, List.flatMap_append, ih]
  rw [hvalues]
  exact eqFinInvocationDelimiter_frames
    (seeds.flatMap (affineEqFinRowFrames rightForms))

/-- Exact row-block equality frames whose seed progression is described by
seven fixed natural polynomials. -/
def exactPolynomialAffineEqFinRowFrames {Γ : Type}
    (rightForms : List AffineUnaryTripleForm)
    (basePrevious baseLeft baseAux
      stepPrevious stepLeft stepAux count : Polynomial Nat)
    (input : List Γ) : List AffineEqFinPairFrame :=
  eqFinRowProgressionFrames rightForms
    (exactPolynomialAffineUnaryTripleProgression
      basePrevious baseLeft baseAux
      stepPrevious stepLeft stepAux count input)

/-- Byte-exact input consumed by the established `EqFin` controller. -/
def exactPolynomialAffineEqFinRowInput {Γ : Type}
    (rightForms : List AffineUnaryTripleForm)
    (basePrevious baseLeft baseAux
      stepPrevious stepLeft stepAux count : Polynomial Nat)
    (input : List Γ) : List UnaryFrameSym :=
  encodeAffineEqFinFrames
    (exactPolynomialAffineEqFinRowFrames rightForms
      basePrevious baseLeft baseAux
      stepPrevious stepLeft stepAux count input)

/-- A fixed polynomial-time TM2 emits the complete canonical equality block
for every row of an exact-polynomial seed progression. -/
noncomputable def exactPolynomialAffineEqFinRowInput_computableInPolyTime
    {Γ : Type} [Fintype Γ]
    (rightForms : List AffineUnaryTripleForm)
    (basePrevious baseLeft baseAux
      stepPrevious stepLeft stepAux count : Polynomial Nat) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (@exactPolynomialAffineEqFinRowInput Γ rightForms
        basePrevious baseLeft baseAux
        stepPrevious stepLeft stepAux count) := by
  let progressionSource :=
    exactPolynomialAffineUnaryTripleProgressionFrameStream_computableInPolyTime
      (Γ := Γ) basePrevious baseLeft baseAux
      stepPrevious stepLeft stepAux count
  let progressionStructured : _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineUnaryTripleSeedFamily
      (fun input : List Γ =>
        eqFinProgressionSeeds
          (exactPolynomialAffineUnaryTripleProgression
            basePrevious baseLeft baseAux
            stepPrevious stepLeft stepAux count input)) :=
    { tm := progressionSource.tm
      inputAlphabet := progressionSource.inputAlphabet
      outputAlphabet := progressionSource.outputAlphabet
      time := progressionSource.time
      outputsFun := fun input => by
        have run := progressionSource.outputsFun input
        simp only [id_eq,
          exactPolynomialAffineUnaryTripleProgressionFrameStream] at run
        rw [affineUnaryTripleProgressionFrameStream_eq_eqFinSeeds] at run
        simpa only [id_eq] using run }
  let mappedExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      progressionStructured
      (affineUnaryTripleMapFamily_computableInPolyTime
        (affineEqFinRowInvocationForms rightForms))
  let mapped := Classical.choice mappedExists
  let delimitedExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch mapped
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
        simpa only [id_eq, exactPolynomialAffineEqFinRowInput,
          exactPolynomialAffineEqFinRowFrames] using run }

end CLRS.Chapter34.Turing.CookLevin

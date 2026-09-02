import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorEqFinProgressionSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.NotFamily

/-!
# Exact-polynomial sources for NOT-family operands

One affine unary progression supplies the source wire of every NOT gate.  A
fixed affine map inserts the two zero loader fields, and a four-position
delimiter cycle materializes the exact marker-bearing input expected by the
established NOT-family controller.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Fixed affine values `[0, 0, 0, source, 0]` used by one NOT invocation. -/
def notProgressionInvocationForms : List AffineUnaryTripleForm :=
  [ { constant := 0, first := 0, second := 0, third := 0 },
    { constant := 0, first := 0, second := 0, third := 0 },
    { constant := 0, first := 0, second := 0, third := 0 },
    { constant := 0, first := 1, second := 0, third := 0 },
    { constant := 0, first := 0, second := 0, third := 0 } ]

/-- Fixed delimiter cycle producing `tick`, the two loader separators, and
the local `frameEnd`. -/
def notProgressionInvocationDelimiters : List UnaryFrameSym :=
  [.tick, .separator, .separator, .separator, .frameEnd]

@[simp] theorem notProgressionInvocationDelimiters_length :
    notProgressionInvocationDelimiters.length = 5 := rfl

theorem notProgressionInvocationDelimiters_nonempty :
    0 < notProgressionInvocationDelimiters.length := by simp

@[simp] theorem notProgressionInvocationForms_value
    (seed : AffineUnaryTripleSeed) :
    affineUnaryTripleMap notProgressionInvocationForms seed =
      [0, 0, 0, seed.first, 0] := by
  simp [notProgressionInvocationForms,
    affineUnaryTripleMap, affineUnaryTripleFormValue]

/-- Delimiter materialization agrees exactly with the established NOT-family
encoding for every explicit source list. -/
theorem notProgression_delimiter_eq_sources
    (seeds : List AffineUnaryTripleSeed) :
    rewriteUnaryFrameDelimiters notProgressionInvocationDelimiters
        notProgressionInvocationDelimiters_nonempty
        (encodeUnaryFrame
          (affineUnaryTripleMapFamily notProgressionInvocationForms seeds)) =
      encodeAffineNotFamilySources (seeds.map AffineUnaryTripleSeed.first) := by
  rw [rewriteUnaryFrameDelimiters_encodeUnaryFrame]
  unfold affineUnaryTripleMapFamily
  have hvalues :
      seeds.flatMap (affineUnaryTripleMap notProgressionInvocationForms) =
        seeds.flatMap fun seed => [0, 0, 0, seed.first, 0] := by
    apply List.flatMap_congr
    intro seed _hseed
    exact notProgressionInvocationForms_value seed
  rw [hvalues]
  clear hvalues
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp [encodeUnaryFrameWithDelimiterCycle,
        encodeUnaryFrameWithDelimiterCycleFrom,
        notProgressionInvocationDelimiters,
        unaryFrameDelimiterNext, encodeAffineNotFamilySources,
        encodeAffineNotFamilySource, encodeUnaryFrame,
        encodeUnaryFrameBlock, List.append_assoc]
      change encodeUnaryFrameWithDelimiterCycle
          notProgressionInvocationDelimiters
          notProgressionInvocationDelimiters_nonempty
          (rest.flatMap fun seed => [0, 0, 0, seed.first, 0]) =
        encodeAffineNotFamilySources
          (rest.map AffineUnaryTripleSeed.first)
      exact ih

/-- Source wire values of one exact-polynomial affine progression. -/
def exactPolynomialAffineNotSources {Γ : Type}
    (base step count : Polynomial Nat) (input : List Γ) : List Nat :=
  (eqFinProgressionSeeds
    (exactPolynomialAffineUnaryTripleProgression
      base 0 0 step 0 0 count input)).map
        AffineUnaryTripleSeed.first

/-- Exact marker-bearing NOT-family input generated from the raw word. -/
def exactPolynomialAffineNotFamilyInput {Γ : Type}
    (base step count : Polynomial Nat) (input : List Γ) :
    List UnaryFrameSym :=
  encodeAffineNotFamilySources
    (exactPolynomialAffineNotSources base step count input)

/-- A fixed polynomial-time TM2 emits the exact NOT-family input described by
three fixed natural polynomials. -/
noncomputable def exactPolynomialAffineNotFamilyInput_computableInPolyTime
    {Γ : Type} [Fintype Γ]
    (base step count : Polynomial Nat) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (@exactPolynomialAffineNotFamilyInput Γ base step count) := by
  let progressionSource :=
    exactPolynomialAffineUnaryTripleProgressionFrameStream_computableInPolyTime
      (Γ := Γ) base 0 0 step 0 0 count
  let progressionStructured : _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineUnaryTripleSeedFamily
      (fun input : List Γ =>
        eqFinProgressionSeeds
          (exactPolynomialAffineUnaryTripleProgression
            base 0 0 step 0 0 count input)) :=
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
        notProgressionInvocationForms)
  let mapped := Classical.choice mappedExists
  let delimitedExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch mapped
      (unaryFrameDelimiterMap_computableInPolyTime
        notProgressionInvocationDelimiters
        notProgressionInvocationDelimiters_nonempty)
  let result := Classical.choice delimitedExists
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simp only [Function.comp_def, id_eq] at run
        rw [notProgression_delimiter_eq_sources] at run
        simpa only [id_eq, exactPolynomialAffineNotFamilyInput,
          exactPolynomialAffineNotSources] using run }

end CLRS.Chapter34.Turing.CookLevin

import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineUnaryTripleProgression
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactPolynomialUnaryFrameFamily

/-!
# Exact polynomial affine unary triple progressions

This module connects raw source words to the verified triple-progression
controller.  The existing exact-polynomial compiler emits seven unary
parameters; the fixed triple controller then expands them in row-major order.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Evaluate seven fixed natural polynomials into one runtime triple
progression. -/
def exactPolynomialAffineUnaryTripleProgression {Γ : Type}
    (base₁ base₂ base₃ step₁ step₂ step₃ count : Polynomial Nat)
    (input : List Γ) : AffineUnaryTripleProgression :=
  { base₁ := base₁.eval input.length
    base₂ := base₂.eval input.length
    base₃ := base₃.eval input.length
    step₁ := step₁.eval input.length
    step₂ := step₂.eval input.length
    step₃ := step₃.eval input.length
    count := count.eval input.length }

/-- The structured encoding is byte-for-byte the exact seven-polynomial
unary-frame family. -/
theorem exactPolynomialAffineUnaryTripleProgression_encode {Γ : Type}
    (base₁ base₂ base₃ step₁ step₂ step₃ count : Polynomial Nat)
    (input : List Γ) :
    encodeAffineUnaryTripleProgression
        (exactPolynomialAffineUnaryTripleProgression
          base₁ base₂ base₃ step₁ step₂ step₃ count input) =
      exactPolynomialUnaryFrames
        [base₁, base₂, base₃, step₁, step₂, step₃, count] input := by
  rfl

/-- Public forward expansion from a raw source word. -/
def exactPolynomialAffineUnaryTripleProgressionFrameStream {Γ : Type}
    (base₁ base₂ base₃ step₁ step₂ step₃ count : Polynomial Nat)
    (input : List Γ) : List UnaryFrameSym :=
  affineUnaryTripleProgressionFrameStream
    (exactPolynomialAffineUnaryTripleProgression
      base₁ base₂ base₃ step₁ step₂ step₃ count input)

set_option maxHeartbeats 2000000 in
/-- A fixed polynomial-time TM2 maps the raw word to the exact row-major
triple progression. -/
noncomputable def
    exactPolynomialAffineUnaryTripleProgressionFrameStream_computableInPolyTime
    {Γ : Type} [Fintype Γ]
    (base₁ base₂ base₃ step₁ step₂ step₃ count : Polynomial Nat) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (@exactPolynomialAffineUnaryTripleProgressionFrameStream Γ
        base₁ base₂ base₃ step₁ step₂ step₃ count) := by
  have source : _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineUnaryTripleProgression
      (@exactPolynomialAffineUnaryTripleProgression Γ
        base₁ base₂ base₃ step₁ step₂ step₃ count) := by
    let compiled := exactPolynomialUnaryFrames_computableInPolyTime
      (Γ := Γ) [base₁, base₂, base₃, step₁, step₂, step₃, count]
    exact
      { tm := compiled.tm
        inputAlphabet := compiled.inputAlphabet
        outputAlphabet := compiled.outputAlphabet
        time := compiled.time
        outputsFun := fun input => by
          simpa [exactPolynomialAffineUnaryTripleProgression_encode] using
            compiled.outputsFun input }
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch source
      affineUnaryTripleProgressionFrameStream_computableInPolyTime
  have hfunction :
      (fun input : List Γ =>
        affineUnaryTripleProgressionFrameStream
          (exactPolynomialAffineUnaryTripleProgression
            base₁ base₂ base₃ step₁ step₂ step₃ count input)) =
        @exactPolynomialAffineUnaryTripleProgressionFrameStream Γ
          base₁ base₂ base₃ step₁ step₂ step₃ count := rfl
  rw [← hfunction]
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder

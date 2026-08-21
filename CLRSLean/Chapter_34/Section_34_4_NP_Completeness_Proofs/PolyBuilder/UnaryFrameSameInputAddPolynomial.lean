import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactPolynomialUnaryFrame
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameValueMarkedRows
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowHead

/-!
# Adding an exact polynomial to a dynamic unary singleton

Given a verified raw-input source for one dynamic unary value, this module
adds the value of a fixed natural-number polynomial.  The construction marks
the dynamic value as a full row, marks the polynomial value as a tick-only
row, concatenates the aligned rows, and removes the outer row marker.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

variable {Γ : Type}

/-- The dynamic addend, represented by one complete marked unary row. -/
def unaryFrameDynamicSingletonFullFamily
    (value : List Γ → Nat) (input : List Γ) : UnaryFrameMarkedRowFamily :=
  unaryFrameFullValueMarkedRows [value input]

/-- The exact-polynomial addend, represented by one tick-only marked row. -/
def unaryFramePolynomialSingletonTickFamily
    (p : Polynomial Nat) (input : List Γ) : UnaryFrameMarkedRowFamily :=
  unaryFrameTickValueMarkedRows [p.eval input.length]

theorem unaryFrameSingletonAddFamilies_aligned
    (value : List Γ → Nat) (p : Polynomial Nat) (input : List Γ) :
    (unaryFramePolynomialSingletonTickFamily p input).rows.length =
      (unaryFrameDynamicSingletonFullFamily value input).rows.length := by
  simp [unaryFramePolynomialSingletonTickFamily,
    unaryFrameDynamicSingletonFullFamily]

/-- The marked singleton row containing the pointwise sum. -/
def unaryFrameSameInputAddPolynomialFamily
    (value : List Γ → Nat) (p : Polynomial Nat)
    (input : List Γ) : UnaryFrameMarkedRowFamily :=
  UnaryFrameMarkedRowParallelConcat.concatenatedFamily
    (unaryFrameSingletonAddFamilies_aligned value p) input

theorem unaryFrameSameInputAddPolynomialFamily_rows
    (value : List Γ → Nat) (p : Polynomial Nat)
    (input : List Γ) :
    (unaryFrameSameInputAddPolynomialFamily value p input).rows =
      [encodeUnaryFrame [value input + p.eval input.length]] := by
  change concatUnaryFrameMarkedRows
      (unaryFrameTickValueMarkedRows [p.eval input.length]).rows
      (unaryFrameFullValueMarkedRows [value input]).rows = _
  simpa [Nat.add_comm] using
    (concatUnaryFrameTickFullRows_ofFn
      (count := 1)
      (fun _ => p.eval input.length)
      (fun _ => value input))

/-- Ordinary unary singleton produced by adding the polynomial value. -/
def unaryFrameSameInputAddPolynomial
    (value : List Γ → Nat) (p : Polynomial Nat)
    (input : List Γ) : List UnaryFrameSym :=
  unaryFrameMarkedRowHeadPayload
    (unaryFrameSameInputAddPolynomialFamily value p input)

@[simp] theorem unaryFrameSameInputAddPolynomial_eq
    (value : List Γ → Nat) (p : Polynomial Nat)
    (input : List Γ) :
    unaryFrameSameInputAddPolynomial value p input =
      encodeUnaryFrame [value input + p.eval input.length] := by
  unfold unaryFrameSameInputAddPolynomial unaryFrameMarkedRowHeadPayload
  rw [unaryFrameSameInputAddPolynomialFamily_rows]
  rfl

private noncomputable def
    unaryFrameDynamicSingletonFullFamily_computableInPolyTime
    [Fintype Γ]
    (value : List Γ → Nat)
    (source : _root_.Turing.TM2ComputableInPolyTime id id
      (fun input => encodeUnaryFrame [value input])) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (unaryFrameDynamicSingletonFullFamily value) := by
  let markedExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch source
      (markUnaryFrameFixedFieldRows_computableInPolyTime 1)
  let marked := Classical.choice markedExists
  exact
    { tm := marked.tm
      inputAlphabet := marked.inputAlphabet
      outputAlphabet := marked.outputAlphabet
      time := marked.time
      outputsFun := fun input => by
        have run := marked.outputsFun input
        simp only [Function.comp_def, id_eq] at run
        rw [markUnaryFrameSingleFieldRows_encode] at run
        simpa only [id_eq,
          unaryFrameDynamicSingletonFullFamily] using run }

private noncomputable def
    unaryFramePolynomialSingletonTickFamily_computableInPolyTime
    [Fintype Γ]
    (p : Polynomial Nat) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (unaryFramePolynomialSingletonTickFamily (Γ := Γ) p) := by
  let source := exactPolynomialUnaryFrame_computableInPolyTime
    (Γ := Γ) p
  let markedExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch source
      (unaryFrameDelimiterMap_computableInPolyTime [.frameEnd] (by simp))
  let marked := Classical.choice markedExists
  exact
    { tm := marked.tm
      inputAlphabet := marked.inputAlphabet
      outputAlphabet := marked.outputAlphabet
      time := marked.time
      outputsFun := fun input => by
        have run := marked.outputsFun input
        simp only [Function.comp_def, id_eq] at run
        have hdelimit :
            rewriteUnaryFrameDelimiters [.frameEnd] (by simp)
                (exactPolynomialUnaryFrame p input) =
              encodeUnaryFrameMarkedRowFamily
                (unaryFrameTickValueMarkedRows [p.eval input.length]) := by
          simpa [exactPolynomialUnaryFrame, encodeUnaryFrame] using
            delimitUnaryFrameValuesAsTickRows [p.eval input.length]
        rw [hdelimit] at run
        simpa only [id_eq, exactPolynomialUnaryFrame,
          unaryFramePolynomialSingletonTickFamily] using run }

/-- A fixed polynomial-time TM2 adds a fixed polynomial value to a dynamic
unary singleton produced by another fixed polynomial-time TM2. -/
noncomputable def unaryFrameSameInputAddPolynomial_computableInPolyTime
    [Fintype Γ]
    (value : List Γ → Nat) (p : Polynomial Nat)
    (source : _root_.Turing.TM2ComputableInPolyTime id id
      (fun input => encodeUnaryFrame [value input])) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (unaryFrameSameInputAddPolynomial value p) := by
  let left :=
    unaryFramePolynomialSingletonTickFamily_computableInPolyTime
      (Γ := Γ) p
  let right :=
    unaryFrameDynamicSingletonFullFamily_computableInPolyTime value source
  let joined := UnaryFrameMarkedRowParallelConcat.computableInPolyTime
    left right (unaryFrameSingletonAddFamilies_aligned value p)
  let resultExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch joined
      unaryFrameMarkedRowHeadPayload_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => unaryFrameMarkedRowHeadPayload
      (unaryFrameSameInputAddPolynomialFamily value p input))
  simpa only [Function.comp_def,
    unaryFrameSameInputAddPolynomialFamily] using
      Classical.choice resultExists

end CLRS.Chapter34.Turing.PolyBuilder

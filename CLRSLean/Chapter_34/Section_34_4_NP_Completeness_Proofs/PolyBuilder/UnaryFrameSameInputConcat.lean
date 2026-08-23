import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameQuoteRuntime
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameUnquoteRuntime
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowParallelConcat

/-!
# Concatenating two same-input unary-frame transducers

Arbitrary inner `frameEnd` symbols are first quoted into delimiter-free
singleton rows.  The verified same-input row concatenator joins those rows,
and a fixed total decoder restores the two literal source streams.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Two concrete polynomial-time transducers on the same raw input can be
combined into one concrete polynomial-time transducer for literal append. -/
noncomputable def unaryFrameSameInputConcat_computableInPolyTime
    {α Γ : Type} [Fintype Γ] {encode : α → List Γ}
    {left right : α → List UnaryFrameSym}
    (M₁ : _root_.Turing.TM2ComputableInPolyTime encode id left)
    (M₂ : _root_.Turing.TM2ComputableInPolyTime encode id right) :
    _root_.Turing.TM2ComputableInPolyTime encode id
      (fun input => left input ++ right input) := by
  let leftQuoted := unaryFrameQuoteAfter_computableInPolyTime M₁
  let rightQuoted := unaryFrameQuoteAfter_computableInPolyTime M₂
  let hAligned : ∀ input : α,
      (quotedUnaryFrameSingleton (left input)).rows.length =
        (quotedUnaryFrameSingleton (right input)).rows.length := by
    intro input
    rfl
  let joined := UnaryFrameMarkedRowParallelConcat.computableInPolyTime
    leftQuoted rightQuoted hAligned
  let joinedRaw : _root_.Turing.TM2ComputableInPolyTime encode id
      (fun input => encodeUnaryFrameMarkedRowFamily
        (UnaryFrameMarkedRowParallelConcat.concatenatedFamily hAligned
          input)) :=
    { tm := joined.tm
      inputAlphabet := joined.inputAlphabet
      outputAlphabet := joined.outputAlphabet
      time := joined.time
      outputsFun := fun input => by
        simpa only [id_eq] using joined.outputsFun input }
  let decodedExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch joinedRaw
      unaryFrameUnquote_computableInPolyTime
  let decoded := Classical.choice decodedExists
  exact
    { tm := decoded.tm
      inputAlphabet := decoded.inputAlphabet
      outputAlphabet := decoded.outputAlphabet
      time := decoded.time
      outputsFun := fun input => by
        have run := decoded.outputsFun input
        have hsource :
            encodeUnaryFrameMarkedRowFamily
                (UnaryFrameMarkedRowParallelConcat.concatenatedFamily hAligned
                  input) =
              quoteUnaryFrameStream (left input) ++
                quoteUnaryFrameStream (right input) ++ [.frameEnd] := by
          simp [encodeUnaryFrameMarkedRowFamily,
            quotedUnaryFrameSingleton, concatUnaryFrameMarkedRows]
        have hsemantic :
            unquoteUnaryFrameStream
                (encodeUnaryFrameMarkedRowFamily
                  (UnaryFrameMarkedRowParallelConcat.concatenatedFamily
                    hAligned input)) =
              left input ++ right input := by
          rw [hsource]
          exact unquoteUnaryFrameStream_quote_append_boundary
            (left input) (right input)
        simp only [Function.comp_def, id_eq] at run
        rw [hsemantic] at run
        simpa only [Function.comp_def, id_eq] using run }

end CLRS.Chapter34.Turing.PolyBuilder

import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowParallelInterleaveRuntime

open CLRS.Chapter34.Turing.PolyBuilder
open UnaryFrameMarkedRowParallelInterleave

#check interleavedFamily
#check first_halt_eq_second_start
#check time
#check outputsFun
#check computableInPolyTime

/-- Regression: the physical interleaver also supports the empty input
alphabet; no hidden `Inhabited` premise remains. -/
noncomputable example
    {leftFamily rightFamily : List Empty → UnaryFrameMarkedRowFamily}
    (M₁ : Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily leftFamily)
    (M₂ : Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily rightFamily)
    (hAligned : ∀ input,
      (leftFamily input).rows.length = (rightFamily input).rows.length) :
    Turing.TM2ComputableInPolyTime id encodeUnaryFrameMarkedRowFamily
      (interleavedFamily hAligned) :=
  computableInPolyTime M₁ M₂ hAligned

#print axioms computableInPolyTime

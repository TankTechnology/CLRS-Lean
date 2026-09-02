import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInputBoundaryFinalOrLayout
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInputBoundaryArmStartsSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameValueMarkedRows
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowOrderReverse
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowHead

/-!
# Concrete dynamic source for the verifier-input final-OR start

The final disjunction begins after every candidate-length conjunction arm.
Its coordinate is therefore a dynamic prefix-sum endpoint, rather than the
evaluation of one fixed affine polynomial.  We append a zero increment so
the established prefix-sum controller emits that endpoint, mark and reverse
the value rows, and retain the first reversed row with a fixed streaming TM2.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Prefix-sum instance whose last emitted value is the endpoint after all
input arms. -/
def verifierInputFinalOrStartPrefixSum
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFramePrefixSum :=
  { base := (verifierInputArmsStartPolynomial W).eval input.length
    increments := verifierInputArmCostValues W input ++ [0] }

/-- Compact raw-input encoding accepted by the prefix-sum controller. -/
def verifierInputFinalOrStartPrefixSumInput
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  exactPolynomialUnaryFrame (verifierInputArmsStartPolynomial W) input ++
    exactPolynomialAffineUnaryProgressionFrameStream
      (Polynomial.X + 3) 1 (verifierInputArmCountPolynomial W) input ++
    exactPolynomialUnaryFrame 0 input

/-- The compact source is the canonical structured prefix-sum input. -/
theorem verifierInputFinalOrStartPrefixSum_encode
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeUnaryFramePrefixSum
        (verifierInputFinalOrStartPrefixSum W input) =
      verifierInputFinalOrStartPrefixSumInput W input := by
  simp [encodeUnaryFramePrefixSum,
    verifierInputFinalOrStartPrefixSum,
    verifierInputFinalOrStartPrefixSumInput,
    verifierInputArmCostValues, verifierInputArmCostProgression,
    exactPolynomialAffineUnaryProgressionFrameStream,
    affineUnaryProgressionFrameStream, exactPolynomialUnaryFrame,
    encodeUnaryFrame, List.flatMap_append]

/-- Prefix values followed by a zero increment expose the final accumulator
as their last value. -/
theorem unaryFramePrefixSumValuesFrom_append_zero
    (current : Nat) (increments : List Nat) :
    unaryFramePrefixSumValuesFrom current (increments ++ [0]) =
      unaryFramePrefixSumValuesFrom current increments ++
        [unaryFramePrefixSumFinal current increments] := by
  induction increments generalizing current with
  | nil => rfl
  | cons increment rest ih =>
      simp only [List.cons_append, unaryFramePrefixSumValuesFrom,
        unaryFramePrefixSumFinal]
      rw [ih]

/-- The prefix-sum endpoint is the arithmetic final-disjunction start. -/
theorem verifierInputFinalOrStartPrefixSum_final
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    unaryFramePrefixSumFinal
        (verifierInputFinalOrStartPrefixSum W input).base
        (verifierInputArmCostValues W input) =
      verifierInputFinalOrStart W input := by
  rw [unaryFramePrefixSumFinal_eq_add_sum]
  unfold verifierInputFinalOrStart verifierInputFinalOrStartPrefixSum
  rw [verifierInputArmCostValues_eq_ofFn]
  rw [List.sum_ofFn]
  rfl

/-- Forward stream of all arm starts followed by their final endpoint. -/
def verifierInputFinalOrStartPrefixFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  unaryFramePrefixSumStream (verifierInputFinalOrStartPrefixSum W input)

/-- A fixed polynomial-time TM2 emits every prefix value, including the final
arm endpoint, directly from the raw verifier word. -/
noncomputable def
    verifierInputFinalOrStartPrefixFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierInputFinalOrStartPrefixFrames W) := by
  letI : Fintype Γ := W.alphabetFintype
  let base := exactPolynomialUnaryFrame_computableInPolyTime
    (Γ := Γ) (verifierInputArmsStartPolynomial W)
  let increments :=
    exactPolynomialAffineUnaryProgressionFrameStream_computableInPolyTime
      (Γ := Γ) (Polynomial.X + 3) 1
        (verifierInputArmCountPolynomial W)
  let zero := exactPolynomialUnaryFrame_computableInPolyTime
    (Γ := Γ) 0
  let baseAndIncrements :=
    unaryFrameSameInputConcat_computableInPolyTime base increments
  let joined :=
    unaryFrameSameInputConcat_computableInPolyTime baseAndIncrements zero
  have source : _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFramePrefixSum
      (verifierInputFinalOrStartPrefixSum W) :=
    { tm := joined.tm
      inputAlphabet := joined.inputAlphabet
      outputAlphabet := joined.outputAlphabet
      time := joined.time
      outputsFun := fun input => by
        have run := joined.outputsFun input
        rw [verifierInputFinalOrStartPrefixSum_encode W input]
        simpa only [id_eq, verifierInputFinalOrStartPrefixSumInput,
          List.append_assoc] using run }
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch source
      unaryFramePrefixSumStream_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => unaryFramePrefixSumStream
      (verifierInputFinalOrStartPrefixSum W input))
  simpa only [Function.comp_def] using Classical.choice composed

/-- Mark every emitted prefix value as its own unary row. -/
def verifierInputFinalOrStartValueFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFrameMarkedRowFamily :=
  unaryFrameFullValueMarkedRows
    (unaryFramePrefixSumValues
      (verifierInputFinalOrStartPrefixSum W input))

/-- The marked value family is computed by a fixed polynomial-time TM2. -/
noncomputable def
    verifierInputFinalOrStartValueFamily_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (verifierInputFinalOrStartValueFamily W) := by
  letI : Fintype Γ := W.alphabetFintype
  let values := verifierInputFinalOrStartPrefixFrames_computableInPolyTime W
  let markedExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch values
      (markUnaryFrameFixedFieldRows_computableInPolyTime 1)
  let marked := Classical.choice markedExists
  exact
    { tm := marked.tm
      inputAlphabet := marked.inputAlphabet
      outputAlphabet := marked.outputAlphabet
      time := marked.time
      outputsFun := fun input => by
        have run := marked.outputsFun input
        simp only [Function.comp_def, id_eq,
          verifierInputFinalOrStartPrefixFrames,
          unaryFramePrefixSumStream] at run
        rw [markUnaryFrameSingleFieldRows_encode] at run
        simpa only [id_eq,
          verifierInputFinalOrStartValueFamily] using run }

/-- The same value rows in last-to-first order. -/
def verifierInputFinalOrStartReversedFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFrameMarkedRowFamily :=
  { rows := (verifierInputFinalOrStartValueFamily W input).rows.reverse
    frameEnd_free := by
      intro row hrow symbol hsymbol
      exact (verifierInputFinalOrStartValueFamily W input).frameEnd_free row
        (by simpa using hrow) symbol hsymbol }

/-- Reversing the marked row stream has the typed reversed-family encoding. -/
theorem verifierInputFinalOrStartReversedFamily_encode
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeUnaryFrameMarkedRowOrderReverse
        (verifierInputFinalOrStartValueFamily W input) =
      encodeUnaryFrameMarkedRowFamily
        (verifierInputFinalOrStartReversedFamily W input) := by
  rfl

/-- The value-family rows end in the exact dynamic final-OR start row. -/
theorem verifierInputFinalOrStartValueFamily_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierInputFinalOrStartValueFamily W input).rows =
      (unaryFramePrefixSumValuesFrom
          ((verifierInputArmsStartPolynomial W).eval input.length)
          (verifierInputArmCostValues W input) ++
        [verifierInputFinalOrStart W input]).map
          (fun value => encodeUnaryFrame [value]) := by
  change (unaryFramePrefixSumValuesFrom
      ((verifierInputArmsStartPolynomial W).eval input.length)
      (verifierInputArmCostValues W input ++ [0])).map
        (fun value => encodeUnaryFrame [value]) = _
  rw [unaryFramePrefixSumValuesFrom_append_zero]
  have hfinal := verifierInputFinalOrStartPrefixSum_final W input
  change unaryFramePrefixSumFinal
      ((verifierInputArmsStartPolynomial W).eval input.length)
      (verifierInputArmCostValues W input) =
        verifierInputFinalOrStart W input at hfinal
  rw [hfinal]

/-- Exact ordinary unary block containing only the final-OR start. -/
def verifierInputFinalOrStartFrame
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  unaryFrameMarkedRowHeadPayload
    (verifierInputFinalOrStartReversedFamily W input)

/-- The extracted dynamic endpoint is byte-for-byte its advertised unary
encoding. -/
theorem verifierInputFinalOrStartFrame_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierInputFinalOrStartFrame W input =
      encodeUnaryFrame [verifierInputFinalOrStart W input] := by
  unfold verifierInputFinalOrStartFrame
    unaryFrameMarkedRowHeadPayload
  change (verifierInputFinalOrStartValueFamily W input).rows.reverse.headD [] = _
  rw [verifierInputFinalOrStartValueFamily_rows]
  simp

/-- End-to-end fixed polynomial-time TM2 from the raw verifier word to the
exact final-disjunction start block. -/
noncomputable def verifierInputFinalOrStartFrame_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierInputFinalOrStartFrame W) := by
  letI : Fintype Γ := W.alphabetFintype
  let values := verifierInputFinalOrStartValueFamily_computableInPolyTime W
  let reversedExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch values
      unaryFrameMarkedRowOrderReverse_computableInPolyTime
  let reversedRaw := Classical.choice reversedExists
  have reversed : _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (verifierInputFinalOrStartReversedFamily W) :=
    { tm := reversedRaw.tm
      inputAlphabet := reversedRaw.inputAlphabet
      outputAlphabet := reversedRaw.outputAlphabet
      time := reversedRaw.time
      outputsFun := fun input => by
        have run := reversedRaw.outputsFun input
        simp only [Function.comp_def, id_eq] at run
        rw [verifierInputFinalOrStartReversedFamily_encode W input] at run
        exact run }
  let resultExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch reversed
      unaryFrameMarkedRowHeadPayload_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => unaryFrameMarkedRowHeadPayload
      (verifierInputFinalOrStartReversedFamily W input))
  simpa only [Function.comp_def] using Classical.choice resultExists

end CLRS.Chapter34.Turing.CookLevin

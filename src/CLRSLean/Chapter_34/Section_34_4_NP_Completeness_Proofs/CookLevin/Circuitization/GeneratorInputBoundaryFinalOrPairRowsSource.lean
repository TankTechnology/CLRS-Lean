import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInputBoundaryFinalOrWiresSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowParallelConcat

/-!
# Aligned operand rows for the verifier-input final disjunction

The tail-first OR fold consumes conjunction outputs in reverse order while
its carry wires grow from the dynamic final-OR start.  This module compiles
both marked unary channels and combines them row by row with verified fixed
TM2 combinators.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-! ## Right/carry channel -/

/-- A runtime progression containing one unit increment per OR gate. -/
def verifierInputFinalOrRightIncrementProgression
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : AffineUnaryProgression :=
  exactPolynomialAffineUnaryProgression
    1 0 (verifierInputArmCountPolynomial W) input

def verifierInputFinalOrRightIncrementValues
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List Nat :=
  affineUnaryProgressionValues
    (verifierInputFinalOrRightIncrementProgression W input)

theorem verifierInputFinalOrRightIncrementValues_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierInputFinalOrRightIncrementValues W input =
      List.replicate (W.certificateBound.eval input.length + 1) 1 := by
  unfold verifierInputFinalOrRightIncrementValues
    verifierInputFinalOrRightIncrementProgression
    affineUnaryProgressionValues
    exactPolynomialAffineUnaryProgression
  rw [affineUnaryProgressionValuesFrom_eq_ofFn]
  simp only [verifierInputArmCountPolynomial_eval]
  simp [Nat.add_comm]

/-- Prefix-sum instance for the carry input of each ordered OR gate. -/
def verifierInputFinalOrRightPrefixSum
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFramePrefixSum :=
  { base := verifierInputFinalOrStart W input
    increments := verifierInputFinalOrRightIncrementValues W input }

/-- Concrete same-input concatenation accepted by the carry prefix-sum
controller. -/
def verifierInputFinalOrRightPrefixSumInput
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  verifierInputFinalOrStartFrame W input ++
    exactPolynomialAffineUnaryProgressionFrameStream
      1 0 (verifierInputArmCountPolynomial W) input

theorem verifierInputFinalOrRightPrefixSum_encode
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeUnaryFramePrefixSum
        (verifierInputFinalOrRightPrefixSum W input) =
      verifierInputFinalOrRightPrefixSumInput W input := by
  unfold verifierInputFinalOrRightPrefixSumInput
  rw [verifierInputFinalOrStartFrame_eq]
  simp [encodeUnaryFramePrefixSum,
    verifierInputFinalOrRightPrefixSum,
    verifierInputFinalOrRightIncrementValues,
    verifierInputFinalOrRightIncrementProgression,
    exactPolynomialAffineUnaryProgressionFrameStream,
    affineUnaryProgressionFrameStream,
    encodeUnaryFrame]

/-- Arithmetic carry wires in canonical frame order. -/
def verifierInputFinalOrRightValues
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List Nat :=
  List.ofFn fun offset :
      Fin (W.certificateBound.eval input.length + 1) =>
    verifierInputFinalOrStart W input + offset.val

theorem verifierInputFinalOrRightPrefixSum_values
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    unaryFramePrefixSumValues
        (verifierInputFinalOrRightPrefixSum W input) =
      verifierInputFinalOrRightValues W input := by
  unfold unaryFramePrefixSumValues verifierInputFinalOrRightPrefixSum
    verifierInputFinalOrRightValues
  rw [verifierInputFinalOrRightIncrementValues_eq]
  rw [unaryFramePrefixSumValuesFrom_eq_ofFn]
  simp

def verifierInputFinalOrRightFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  unaryFramePrefixSumStream (verifierInputFinalOrRightPrefixSum W input)

theorem verifierInputFinalOrRightFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierInputFinalOrRightFrames W input =
      encodeUnaryFrame (verifierInputFinalOrRightValues W input) := by
  unfold verifierInputFinalOrRightFrames unaryFramePrefixSumStream
  rw [verifierInputFinalOrRightPrefixSum_values]

noncomputable def verifierInputFinalOrRightFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierInputFinalOrRightFrames W) := by
  letI : Fintype Γ := W.alphabetFintype
  let base := verifierInputFinalOrStartFrame_computableInPolyTime W
  let increments :=
    exactPolynomialAffineUnaryProgressionFrameStream_computableInPolyTime
      (Γ := Γ) 1 0 (verifierInputArmCountPolynomial W)
  let joined := unaryFrameSameInputConcat_computableInPolyTime base increments
  have source : _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFramePrefixSum
      (verifierInputFinalOrRightPrefixSum W) :=
    { tm := joined.tm
      inputAlphabet := joined.inputAlphabet
      outputAlphabet := joined.outputAlphabet
      time := joined.time
      outputsFun := fun input => by
        have run := joined.outputsFun input
        rw [verifierInputFinalOrRightPrefixSum_encode W input]
        simpa only [id_eq,
          verifierInputFinalOrRightPrefixSumInput] using run }
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch source
      unaryFramePrefixSumStream_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => unaryFramePrefixSumStream
      (verifierInputFinalOrRightPrefixSum W input))
  simpa only [Function.comp_def] using Classical.choice composed

/-! ## Marked left and right channels -/

def verifierInputFinalOrLeftForwardFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFrameMarkedRowFamily :=
  unaryFrameFullValueMarkedRows (verifierInputFinalOrWires W input)

noncomputable def
    verifierInputFinalOrLeftForwardFamily_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (verifierInputFinalOrLeftForwardFamily W) := by
  letI : Fintype Γ := W.alphabetFintype
  let wires := verifierInputFinalOrWireFrames_computableInPolyTime W
  let markedExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch wires
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
        rw [verifierInputFinalOrWireFrames_eq W input] at run
        rw [markUnaryFrameSingleFieldRows_encode] at run
        simpa [verifierInputFinalOrLeftForwardFamily] using run }

/-- Left operands in the tail-first order used by canonical OR frames. -/
def verifierInputFinalOrLeftFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFrameMarkedRowFamily :=
  { rows := (verifierInputFinalOrLeftForwardFamily W input).rows.reverse
    frameEnd_free := by
      intro row hrow symbol hsymbol
      exact (verifierInputFinalOrLeftForwardFamily W input).frameEnd_free row
        (by simpa using hrow) symbol hsymbol }

theorem verifierInputFinalOrLeftFamily_encode
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeUnaryFrameMarkedRowOrderReverse
        (verifierInputFinalOrLeftForwardFamily W input) =
      encodeUnaryFrameMarkedRowFamily
        (verifierInputFinalOrLeftFamily W input) := by
  rfl

noncomputable def verifierInputFinalOrLeftFamily_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (verifierInputFinalOrLeftFamily W) := by
  letI : Fintype Γ := W.alphabetFintype
  let forward :=
    verifierInputFinalOrLeftForwardFamily_computableInPolyTime W
  let reversedExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch forward
      unaryFrameMarkedRowOrderReverse_computableInPolyTime
  let reversed := Classical.choice reversedExists
  exact
    { tm := reversed.tm
      inputAlphabet := reversed.inputAlphabet
      outputAlphabet := reversed.outputAlphabet
      time := reversed.time
      outputsFun := fun input => by
        have run := reversed.outputsFun input
        simp only [Function.comp_def, id_eq] at run
        rw [verifierInputFinalOrLeftFamily_encode W input] at run
        exact run }

/-- Right/carry operands as one marked unary field per row. -/
def verifierInputFinalOrRightFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFrameMarkedRowFamily :=
  unaryFrameFullValueMarkedRows (verifierInputFinalOrRightValues W input)

noncomputable def verifierInputFinalOrRightFamily_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (verifierInputFinalOrRightFamily W) := by
  letI : Fintype Γ := W.alphabetFintype
  let rights := verifierInputFinalOrRightFrames_computableInPolyTime W
  let markedExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch rights
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
        rw [verifierInputFinalOrRightFrames_eq W input] at run
        rw [markUnaryFrameSingleFieldRows_encode] at run
        simpa [verifierInputFinalOrRightFamily] using run }

@[simp] theorem verifierInputFinalOrLeftFamily_length
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierInputFinalOrLeftFamily W input).rows.length =
      W.certificateBound.eval input.length + 1 := by
  simp [verifierInputFinalOrLeftFamily,
    verifierInputFinalOrLeftForwardFamily,
    verifierInputFinalOrWires]

@[simp] theorem verifierInputFinalOrRightFamily_length
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierInputFinalOrRightFamily W input).rows.length =
      W.certificateBound.eval input.length + 1 := by
  simp [verifierInputFinalOrRightFamily,
    verifierInputFinalOrRightValues]

def verifierInputFinalOrPairFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFrameMarkedRowFamily :=
  UnaryFrameMarkedRowParallelConcat.concatenatedFamily
    (leftFamily := verifierInputFinalOrLeftFamily W)
    (rightFamily := verifierInputFinalOrRightFamily W)
    (fun word => by simp) input

/-- One fixed polynomial-time TM2 emits aligned `[left,right]` unary rows for
every canonical final-OR frame. -/
noncomputable def verifierInputFinalOrPairFamily_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (verifierInputFinalOrPairFamily W) := by
  letI : Fintype Γ := W.alphabetFintype
  exact UnaryFrameMarkedRowParallelConcat.computableInPolyTime
    (verifierInputFinalOrLeftFamily_computableInPolyTime W)
    (verifierInputFinalOrRightFamily_computableInPolyTime W)
    (fun input => by simp)

end CLRS.Chapter34.Turing.CookLevin

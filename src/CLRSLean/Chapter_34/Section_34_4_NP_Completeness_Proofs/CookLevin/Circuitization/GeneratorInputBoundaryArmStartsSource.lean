import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInputBoundaryArmFrames
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactPolynomialUnaryFrame
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactPolynomialAffineUnaryProgression
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFramePrefixSum
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameSameInputConcat

/-!
# Raw-input source for verifier-input arm starts

Arm costs are affine in the candidate certificate length, but consecutive arm
starts are their prefix sums.  This module composes the affine cost generator
with the verified unary prefix-sum TM2 and identifies every generated value
with the exact circuit-builder coordinate.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Polynomial number of candidate certificate lengths. -/
def verifierInputArmCountPolynomial
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) : Polynomial Nat :=
  W.certificateBound + 1

@[simp] theorem verifierInputArmCountPolynomial_eval
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) (inputLength : Nat) :
    (verifierInputArmCountPolynomial W).eval inputLength =
      W.certificateBound.eval inputLength + 1 := by
  simp [verifierInputArmCountPolynomial]

/-- Runtime affine progression of exact arm gate costs. -/
def verifierInputArmCostProgression
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : AffineUnaryProgression :=
  exactPolynomialAffineUnaryProgression
    (Polynomial.X + 3) 1 (verifierInputArmCountPolynomial W) input

/-- Exact cost list consumed by the prefix-sum controller. -/
def verifierInputArmCostValues
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List Nat :=
  affineUnaryProgressionValues (verifierInputArmCostProgression W input)

/-- The affine source yields precisely the semantic cost of every arm. -/
theorem verifierInputArmCostValues_eq_ofFn
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierInputArmCostValues W input =
      List.ofFn fun arm :
          Fin (W.certificateBound.eval input.length + 1) =>
        verifierInputArmGateCost ((verifierHeight W).eval input.length)
          input.length arm.val := by
  unfold verifierInputArmCostValues verifierInputArmCostProgression
    affineUnaryProgressionValues exactPolynomialAffineUnaryProgression
  rw [affineUnaryProgressionValuesFrom_eq_ofFn]
  simp only [verifierInputArmCountPolynomial_eval]
  apply List.ofFn_inj.mpr
  funext arm
  rw [verifierInputArmGateCost_eq W input arm]
  simp [verifierInputArmCountPolynomial]
  omega

/-- Structured prefix-sum instance for all input arms. -/
def verifierInputArmStartPrefixSum
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFramePrefixSum :=
  { base := (verifierInputArmsStartPolynomial W).eval input.length
    increments := verifierInputArmCostValues W input }

/-- Compact raw-input source accepted by the fixed prefix-sum controller. -/
def verifierInputArmStartPrefixSumInput
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  exactPolynomialUnaryFrame (verifierInputArmsStartPolynomial W) input ++
    exactPolynomialAffineUnaryProgressionFrameStream
      (Polynomial.X + 3) 1 (verifierInputArmCountPolynomial W) input

/-- The compact source is byte-for-byte the canonical structured encoding. -/
theorem verifierInputArmStartPrefixSum_encode
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeUnaryFramePrefixSum (verifierInputArmStartPrefixSum W input) =
      verifierInputArmStartPrefixSumInput W input := by
  rfl

/-- Forward unary frame stream of all exact arm start coordinates. -/
def verifierInputArmStartFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  unaryFramePrefixSumStream (verifierInputArmStartPrefixSum W input)

private theorem sum_take_ofFn_eq_fin_sum {n index : Nat}
    (f : Fin n → Nat) (hindex : index ≤ n) :
    ((List.ofFn f).take index).sum =
      ∑ previous : Fin index,
        f ⟨previous.val, Nat.lt_of_lt_of_le previous.isLt hindex⟩ := by
  induction index with
  | zero => simp
  | succ index ih =>
      have hlt : index < n := by omega
      rw [List.sum_take_succ]
      · rw [Fin.sum_univ_castSucc]
        rw [ih (Nat.le_of_lt hlt)]
        rw [List.getElem_ofFn]
        rfl
      · simpa using hlt

/-- The natural values emitted by the fixed controller are exactly the starts
stored in the builder-free arithmetic arm frames. -/
theorem verifierInputArmStartValues_eq_ofFn
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    unaryFramePrefixSumValues (verifierInputArmStartPrefixSum W input) =
      List.ofFn fun arm :
          Fin (W.certificateBound.eval input.length + 1) =>
        (verifierInputArmArithmeticFrame W input arm).start := by
  unfold unaryFramePrefixSumValues verifierInputArmStartPrefixSum
  rw [verifierInputArmCostValues_eq_ofFn]
  rw [unaryFramePrefixSumValuesFrom_eq_ofFn]
  simp only [List.length_ofFn]
  apply List.ofFn_inj.mpr
  funext arm
  unfold verifierInputArmArithmeticFrame verifierInputArmPrefixCost
  dsimp only
  simp only [Fin.val_cast]
  rw [sum_take_ofFn_eq_fin_sum _ (Nat.le_of_lt arm.isLt)]

/-- Therefore the public stream is the exact encoding of all arithmetic arm
starts in ordinal order. -/
theorem verifierInputArmStartFrames_eq_encode
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierInputArmStartFrames W input =
      encodeUnaryFrame (List.ofFn fun arm :
          Fin (W.certificateBound.eval input.length + 1) =>
        (verifierInputArmArithmeticFrame W input arm).start) := by
  unfold verifierInputArmStartFrames unaryFramePrefixSumStream
  rw [verifierInputArmStartValues_eq_ofFn]

/-- A single fixed polynomial-time TM2 computes all exact arm starts directly
from the raw verifier word. -/
noncomputable def verifierInputArmStartFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierInputArmStartFrames W) := by
  letI : Fintype Γ := W.alphabetFintype
  let base := exactPolynomialUnaryFrame_computableInPolyTime
    (Γ := Γ) (verifierInputArmsStartPolynomial W)
  let increments :=
    exactPolynomialAffineUnaryProgressionFrameStream_computableInPolyTime
      (Γ := Γ) (Polynomial.X + 3) 1
        (verifierInputArmCountPolynomial W)
  let joined := unaryFrameSameInputConcat_computableInPolyTime base increments
  have source : _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFramePrefixSum (verifierInputArmStartPrefixSum W) :=
    { tm := joined.tm
      inputAlphabet := joined.inputAlphabet
      outputAlphabet := joined.outputAlphabet
      time := joined.time
      outputsFun := fun input => by
        have run := joined.outputsFun input
        have sourceRun : _root_.Turing.TM2OutputsInTime joined.tm
            (List.map joined.inputAlphabet.invFun input)
            (some (List.map joined.outputAlphabet.invFun
              (verifierInputArmStartPrefixSumInput W input)))
            (joined.time.eval input.length) := by
          simpa only [id_eq, verifierInputArmStartPrefixSumInput,
            List.map_append] using run
        rw [← verifierInputArmStartPrefixSum_encode W input] at sourceRun
        exact sourceRun }
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch source
      unaryFramePrefixSumStream_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => unaryFramePrefixSumStream
      (verifierInputArmStartPrefixSum W input))
  simpa only [Function.comp_def] using
    Classical.choice composed

end CLRS.Chapter34.Turing.CookLevin

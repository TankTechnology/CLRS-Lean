import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInputBoundaryFinalOrStartSource

/-!
# Concrete source for verifier-input final-OR wires

Consecutive conjunction outputs differ by an affine progression.  A second
verified prefix-sum instance therefore emits the complete ordered source list
of the final disjunction directly from the raw verifier word.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Exact polynomial for the output wire of candidate-length arm zero. -/
def verifierInputFinalOrWireBasePolynomial
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    Polynomial Nat :=
  verifierInputArmsStartPolynomial W + Polynomial.X + 2

@[simp] theorem verifierInputFinalOrWireBasePolynomial_eval
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) (n : Nat) :
    (verifierInputFinalOrWireBasePolynomial W).eval n =
      (verifierInputArmsStartPolynomial W).eval n + n + 2 := by
  simp [verifierInputFinalOrWireBasePolynomial]

/-- Affine differences between consecutive final-OR source wires. -/
def verifierInputFinalOrWireIncrementProgression
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : AffineUnaryProgression :=
  exactPolynomialAffineUnaryProgression
    (Polynomial.X + 4) 1 (verifierInputArmCountPolynomial W) input

/-- Runtime increment list consumed by the wire prefix-sum controller. -/
def verifierInputFinalOrWireIncrementValues
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List Nat :=
  affineUnaryProgressionValues
    (verifierInputFinalOrWireIncrementProgression W input)

/-- Closed positional form of every wire increment. -/
theorem verifierInputFinalOrWireIncrementValues_eq_ofFn
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierInputFinalOrWireIncrementValues W input =
      List.ofFn fun index :
          Fin (W.certificateBound.eval input.length + 1) =>
        input.length + 4 + index.val := by
  unfold verifierInputFinalOrWireIncrementValues
    verifierInputFinalOrWireIncrementProgression
    affineUnaryProgressionValues
    exactPolynomialAffineUnaryProgression
  rw [affineUnaryProgressionValuesFrom_eq_ofFn]
  simp only [verifierInputArmCountPolynomial_eval]
  apply List.ofFn_inj.mpr
  funext index
  simp

/-- Structured prefix-sum instance for every final-OR source wire. -/
def verifierInputFinalOrWirePrefixSum
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFramePrefixSum :=
  { base := (verifierInputFinalOrWireBasePolynomial W).eval input.length
    increments := verifierInputFinalOrWireIncrementValues W input }

/-- Compact raw-input source of the structured wire prefix sum. -/
def verifierInputFinalOrWirePrefixSumInput
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  exactPolynomialUnaryFrame
      (verifierInputFinalOrWireBasePolynomial W) input ++
    exactPolynomialAffineUnaryProgressionFrameStream
      (Polynomial.X + 4) 1 (verifierInputArmCountPolynomial W) input

/-- The compact source is exactly the canonical prefix-sum input. -/
theorem verifierInputFinalOrWirePrefixSum_encode
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeUnaryFramePrefixSum
        (verifierInputFinalOrWirePrefixSum W input) =
      verifierInputFinalOrWirePrefixSumInput W input := by
  rfl

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

/-- Every generated prefix value is exactly the corresponding arithmetic arm
output wire. -/
theorem verifierInputFinalOrWireValues_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    unaryFramePrefixSumValues
        (verifierInputFinalOrWirePrefixSum W input) =
      verifierInputFinalOrWires W input := by
  unfold unaryFramePrefixSumValues verifierInputFinalOrWirePrefixSum
  rw [verifierInputFinalOrWireIncrementValues_eq_ofFn]
  rw [unaryFramePrefixSumValuesFrom_eq_ofFn]
  simp only [List.length_ofFn]
  unfold verifierInputFinalOrWires
  apply List.ofFn_inj.mpr
  funext arm
  simp only [Fin.val_cast]
  rw [sum_take_ofFn_eq_fin_sum _ (Nat.le_of_lt arm.isLt)]
  rw [verifierInputFinalOrWireBasePolynomial_eval]
  unfold verifierInputArmOutputWire verifierInputArmPrefixCost
  have hcost :
      (∑ previous : Fin arm.val,
        verifierInputArmGateCost ((verifierHeight W).eval input.length)
          input.length previous.val) =
      ∑ previous : Fin arm.val,
        (previous.val + input.length + 3) := by
    apply Finset.sum_congr rfl
    intro previous _
    unfold verifierInputArmGateCost
    rw [if_pos]
    rw [verifierHeight_eval, verifierInputBound_eval]
    omega
  rw [hcost]
  have hincrements :
      (∑ previous : Fin arm.val,
        (input.length + 4 + previous.val)) =
      (∑ previous : Fin arm.val,
        (previous.val + input.length + 3)) + arm.val := by
    calc
      _ = ∑ previous : Fin arm.val,
          ((previous.val + input.length + 3) + 1) := by
            apply Finset.sum_congr rfl
            intro previous _
            omega
      _ = (∑ previous : Fin arm.val,
          (previous.val + input.length + 3)) +
            ∑ _previous : Fin arm.val, 1 := by
              rw [Finset.sum_add_distrib]
      _ = _ := by simp
  rw [hincrements]
  omega

/-- Exact forward unary encoding of every final-OR source wire. -/
def verifierInputFinalOrWireFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  unaryFramePrefixSumStream (verifierInputFinalOrWirePrefixSum W input)

theorem verifierInputFinalOrWireFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierInputFinalOrWireFrames W input =
      encodeUnaryFrame (verifierInputFinalOrWires W input) := by
  unfold verifierInputFinalOrWireFrames unaryFramePrefixSumStream
  rw [verifierInputFinalOrWireValues_eq]

/-- One fixed polynomial-time TM2 emits the complete ordered final-OR source
wire stream from the raw verifier word. -/
noncomputable def verifierInputFinalOrWireFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierInputFinalOrWireFrames W) := by
  letI : Fintype Γ := W.alphabetFintype
  let base := exactPolynomialUnaryFrame_computableInPolyTime
    (Γ := Γ) (verifierInputFinalOrWireBasePolynomial W)
  let increments :=
    exactPolynomialAffineUnaryProgressionFrameStream_computableInPolyTime
      (Γ := Γ) (Polynomial.X + 4) 1
        (verifierInputArmCountPolynomial W)
  let joined := unaryFrameSameInputConcat_computableInPolyTime base increments
  have source : _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFramePrefixSum
      (verifierInputFinalOrWirePrefixSum W) :=
    { tm := joined.tm
      inputAlphabet := joined.inputAlphabet
      outputAlphabet := joined.outputAlphabet
      time := joined.time
      outputsFun := fun input => by
        have run := joined.outputsFun input
        rw [verifierInputFinalOrWirePrefixSum_encode W input]
        simpa only [id_eq, verifierInputFinalOrWirePrefixSumInput] using run }
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch source
      unaryFramePrefixSumStream_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => unaryFramePrefixSumStream
      (verifierInputFinalOrWirePrefixSum W input))
  simpa only [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.CookLevin

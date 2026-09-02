import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInputBoundaryInputCodeSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameValueMarkedRows

/-!
# Exact public-input cell wires for the first verifier-input arm

The content-dependent symbol code and the affine physical-cell coordinate are
compiled independently, marked one cell per row, and combined by the verified
same-input row concatenator.  Concatenating unary ticks implements addition,
so the result is the exact cell-wire family for candidate length zero.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Width of one physical input-stack cell's symbol block. -/
def verifierInputStackSymbolWidth
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) : Nat :=
  (reachableAlphabet W.machine.tm W.machine.tm.k₀).card + 1

/-- Affine coordinate of the first public-input cell before adding its actual
finite symbol code. -/
noncomputable def verifierFirstInputArmCellPositionBasePolynomial
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) : Polynomial Nat :=
  let tm := W.machine.tm
  Polynomial.C
      (1 + (labelCount tm + 1) + stateCount tm +
        arithmeticStackOrdinal tm tm.k₀ + 1 +
        verifierInputStackSymbolWidth W) +
    Polynomial.C (cfgStackBitOffsetHeightCoeff tm tm.k₀ + 1) *
      verifierHeight W

@[simp] theorem verifierFirstInputArmCellPositionBasePolynomial_eval
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) (n : Nat) :
    (verifierFirstInputArmCellPositionBasePolynomial W).eval n =
      1 + (labelCount W.machine.tm + 1) + stateCount W.machine.tm +
        cfgStackBitOffset W.machine.tm ((verifierHeight W).eval n)
          W.machine.tm.k₀ +
        (((verifierHeight W).eval n + 1) +
          verifierInputStackSymbolWidth W) := by
  rw [cfgStackBitOffset_eq_affine]
  simp [verifierFirstInputArmCellPositionBasePolynomial,
    Polynomial.eval_add, Polynomial.eval_mul]
  ring

/-- Position-only affine value of every public input cell in arm zero. -/
def verifierFirstInputArmCellPositionValues
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List Nat :=
  List.ofFn fun index : Fin input.length =>
    (verifierFirstInputArmCellPositionBasePolynomial W).eval input.length +
      verifierInputStackSymbolWidth W * index.val

/-- Raw affine unary stream of all position-only values. -/
def verifierFirstInputArmCellPositionFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  exactPolynomialAffineUnaryProgressionFrameStream
    (verifierFirstInputArmCellPositionBasePolynomial W)
    (Polynomial.C (verifierInputStackSymbolWidth W)) Polynomial.X input

theorem verifierFirstInputArmCellPositionFrames_eq_encode
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierFirstInputArmCellPositionFrames W input =
      encodeUnaryFrame (verifierFirstInputArmCellPositionValues W input) := by
  unfold verifierFirstInputArmCellPositionFrames
    verifierFirstInputArmCellPositionValues
    exactPolynomialAffineUnaryProgressionFrameStream
    affineUnaryProgressionFrameStream affineUnaryProgressionValues
    exactPolynomialAffineUnaryProgression
  rw [affineUnaryProgressionValuesFrom_eq_ofFn]
  apply congrArg encodeUnaryFrame
  simp only [Polynomial.eval_X, Polynomial.eval_C]
  apply List.ofFn_inj.mpr
  funext index
  simp only [Fin.val_cast]
  ring

/-- Actual cell coordinate for one public symbol in candidate arm zero. -/
def verifierFirstInputArmCellWire
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (index : Fin input.length) : Nat :=
  1 + (labelCount W.machine.tm + 1) + stateCount W.machine.tm +
    cfgStackBitOffset W.machine.tm
      ((verifierHeight W).eval input.length) W.machine.tm.k₀ +
      (((verifierHeight W).eval input.length + 1) +
        ((verifierInputCode W (some (input.get index))).val +
          verifierInputStackSymbolWidth W * (1 + index.val)))

/-- Tick-only symbol-code contribution, one marked row per raw symbol. -/
def verifierPublicInputCodeTickFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFrameMarkedRowFamily :=
  unaryFrameTickValueMarkedRows
    (input.map (verifierPublicInputCode W))

/-- Full position contribution, one complete unary block per marked row. -/
def verifierFirstInputArmCellPositionFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFrameMarkedRowFamily :=
  unaryFrameFullValueMarkedRows
    (verifierFirstInputArmCellPositionValues W input)

theorem verifierFirstInputArmCellFamilies_aligned
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierPublicInputCodeTickFamily W input).rows.length =
      (verifierFirstInputArmCellPositionFamily W input).rows.length := by
  simp [verifierPublicInputCodeTickFamily,
    verifierFirstInputArmCellPositionFamily,
    verifierFirstInputArmCellPositionValues]

/-- Row-wise unary sum of the actual code and affine cell position. -/
def verifierFirstInputArmCellWireFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFrameMarkedRowFamily :=
  UnaryFrameMarkedRowParallelConcat.concatenatedFamily
    (verifierFirstInputArmCellFamilies_aligned W) input

private theorem verifierPublicInputCodeValues_eq_ofFn
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    input.map (verifierPublicInputCode W) =
      List.ofFn fun index : Fin input.length =>
        verifierPublicInputCode W (input.get index) := by
  calc
    input.map (verifierPublicInputCode W) =
        (List.ofFn input.get).map (verifierPublicInputCode W) := by
      rw [List.ofFn_get]
    _ = List.ofFn
          ((verifierPublicInputCode W) ∘ input.get) := by
      rw [List.map_ofFn]
    _ = _ := by
      apply List.ofFn_inj.mpr
      funext index
      rfl

/-- Every compiled row is exactly the semantic first-arm public-input cell
wire, with no residual builder or oracle-side arithmetic. -/
theorem verifierFirstInputArmCellWireFamily_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierFirstInputArmCellWireFamily W input).rows =
      List.ofFn fun index : Fin input.length =>
        encodeUnaryFrame [verifierFirstInputArmCellWire W input index] := by
  rw [show (verifierFirstInputArmCellWireFamily W input).rows =
      concatUnaryFrameMarkedRows
        (verifierPublicInputCodeTickFamily W input).rows
        (verifierFirstInputArmCellPositionFamily W input).rows by rfl]
  unfold verifierPublicInputCodeTickFamily
    verifierFirstInputArmCellPositionFamily
    verifierFirstInputArmCellPositionValues
  rw [verifierPublicInputCodeValues_eq_ofFn W input]
  rw [concatUnaryFrameTickFullRows_ofFn]
  apply List.ofFn_inj.mpr
  funext index
  apply congrArg encodeUnaryFrame
  congr 1
  unfold verifierPublicInputCode verifierFirstInputArmCellWire
  rw [verifierFirstInputArmCellPositionBasePolynomial_eval]
  ring

/-- Concrete source for the tick-only actual-symbol rows. -/
noncomputable def verifierPublicInputCodeTickFamily_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (verifierPublicInputCodeTickFamily W) := by
  letI : Fintype Γ := W.alphabetFintype
  let source := verifierPublicInputCodeFrames_computableInPolyTime W
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch source
      (unaryFrameDelimiterMap_computableInPolyTime [.frameEnd] (by simp))
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        simpa only [Function.comp_apply, id_eq,
          verifierPublicInputCodeFrames,
          verifierPublicInputCodeTickFamily,
          delimitUnaryFrameValuesAsTickRows] using
          result.outputsFun input }

/-- Concrete source for the full position rows. -/
noncomputable def
    verifierFirstInputArmCellPositionFamily_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (verifierFirstInputArmCellPositionFamily W) := by
  letI : Fintype Γ := W.alphabetFintype
  let source :=
    exactPolynomialAffineUnaryProgressionFrameStream_computableInPolyTime
      (Γ := Γ) (verifierFirstInputArmCellPositionBasePolynomial W)
        (Polynomial.C (verifierInputStackSymbolWidth W)) Polynomial.X
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch source
      (markUnaryFrameFixedFieldRows_computableInPolyTime 1)
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        have hframes :
            exactPolynomialAffineUnaryProgressionFrameStream
                (verifierFirstInputArmCellPositionBasePolynomial W)
                (Polynomial.C (verifierInputStackSymbolWidth W))
                Polynomial.X input =
              encodeUnaryFrame
                (verifierFirstInputArmCellPositionValues W input) := by
          simpa only [verifierFirstInputArmCellPositionFrames] using
            verifierFirstInputArmCellPositionFrames_eq_encode W input
        simp only [Function.comp_apply, id_eq] at run
        rw [hframes, markUnaryFrameSingleFieldRows_encode] at run
        simpa only [id_eq,
          verifierFirstInputArmCellPositionFamily] using run }

/-- One fixed polynomial-time TM2 reads the raw word and emits every exact
public-input cell wire of candidate arm zero as a typed marked family. -/
noncomputable def verifierFirstInputArmCellWireFamily_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (verifierFirstInputArmCellWireFamily W) := by
  letI : Fintype Γ := W.alphabetFintype
  exact UnaryFrameMarkedRowParallelConcat.computableInPolyTime
    (verifierPublicInputCodeTickFamily_computableInPolyTime W)
    (verifierFirstInputArmCellPositionFamily_computableInPolyTime W)
    (verifierFirstInputArmCellFamilies_aligned W)

end CLRS.Chapter34.Turing.CookLevin

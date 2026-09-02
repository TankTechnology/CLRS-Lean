import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInputBoundaryFirstArmCellsSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInputBoundaryArmAffineWiresSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactPolynomialUnaryFrameFamily
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameSameInputConcat
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedCellAffineRowsRuntime

/-!
# Exact public-input cell-wire rows for every candidate arm

The exact content-dependent row for candidate arm zero is already compiled
from the raw word.  One fixed affine marked-cell controller now reuses it for
all candidate lengths, adding one input-stack symbol width at every arm.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Public-input cell wire in an arbitrary candidate-length arm. -/
def verifierInputArmCellWire
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ)
    (arm : Fin (W.certificateBound.eval input.length + 1))
    (index : Fin input.length) : Nat :=
  verifierFirstInputArmCellWire W input index +
    verifierInputStackSymbolWidth W * arm.val

/-- The affine controller parameters derived from the raw verifier word. -/
def verifierInputArmCellRowsParameters
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFrameMarkedCellAffineRows :=
  { step := verifierInputStackSymbolWidth W
    count := W.certificateBound.eval input.length + 1
    cells := List.ofFn fun index : Fin input.length =>
      verifierFirstInputArmCellWire W input index }

private theorem armCellRows_encodeUnaryFrame_frameEnd_free
    (values : List Nat) :
    ∀ symbol ∈ encodeUnaryFrame values,
      symbol ≠ UnaryFrameSym.frameEnd := by
  intro symbol hsymbol
  rw [encodeUnaryFrame, List.mem_flatMap] at hsymbol
  rcases hsymbol with ⟨value, _, hblock⟩
  simp [encodeUnaryFrameBlock] at hblock
  rcases hblock with ⟨_, rfl⟩ | rfl <;> decide

/-- Typed marked-row family of the actual cell-wire block in every arm. -/
def verifierInputArmCellWireRowsFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFrameMarkedRowFamily :=
  { rows := (unaryFrameMarkedCellAffineRowValues
      (verifierInputArmCellRowsParameters W input)).map encodeUnaryFrame
    frameEnd_free := by
      intro row hrow symbol hsymbol
      rw [List.mem_map] at hrow
      rcases hrow with ⟨values, _, rfl⟩
      exact armCellRows_encodeUnaryFrame_frameEnd_free _ symbol hsymbol }

/-- The typed rows expose the closed physical cell-wire coordinates. -/
theorem verifierInputArmCellWireRowsFamily_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierInputArmCellWireRowsFamily W input).rows =
      List.ofFn fun arm :
          Fin (W.certificateBound.eval input.length + 1) =>
        encodeUnaryFrame (List.ofFn fun index : Fin input.length =>
          verifierInputArmCellWire W input arm index) := by
  change (unaryFrameMarkedCellAffineRowValues
      (verifierInputArmCellRowsParameters W input)).map encodeUnaryFrame = _
  unfold unaryFrameMarkedCellAffineRowValues verifierInputArmCellRowsParameters
  rw [List.map_ofFn]
  apply List.ofFn_inj.mpr
  funext arm
  apply congrArg encodeUnaryFrame
  simp [verifierInputArmCellWire]
  funext index
  rfl

/-- The affine definition agrees with the physical stack-cell coordinate in
the verifier-input arithmetic layout. -/
theorem verifierInputArmCellWire_eq_layout
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ)
    (arm : Fin (W.certificateBound.eval input.length + 1))
    (index : Fin input.length) :
    verifierInputArmCellWire W input arm index =
      1 + (labelCount W.machine.tm + 1) + stateCount W.machine.tm +
        cfgStackBitOffset W.machine.tm
          ((verifierHeight W).eval input.length) W.machine.tm.k₀ +
          (((verifierHeight W).eval input.length + 1) +
            ((verifierInputCode W (some (input.get index))).val +
              verifierInputStackSymbolWidth W *
                (arm.val + 1 + index.val))) := by
  unfold verifierInputArmCellWire verifierFirstInputArmCellWire
  ring

/-- The generic controller emits exactly the typed all-arm cell family. -/
theorem verifierInputArmCellRowsStream_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    unaryFrameMarkedCellAffineRowsStream
        (verifierInputArmCellRowsParameters W input) =
      encodeUnaryFrameMarkedRowFamily
        (verifierInputArmCellWireRowsFamily W input) := by
  unfold unaryFrameMarkedCellAffineRowsStream
    encodeUnaryFrameMarkedRowFamily
    verifierInputArmCellWireRowsFamily
  rw [List.flatMap_map]

/-- The concatenated header and first-arm marked family are precisely the
generic affine controller's structured input. -/
theorem verifierInputArmCellRowsParameters_encode
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeUnaryFrameMarkedCellAffineRows
        (verifierInputArmCellRowsParameters W input) =
      exactPolynomialUnaryFrames
          [Polynomial.C (verifierInputStackSymbolWidth W),
            verifierInputArmCountPolynomial W] input ++
        encodeUnaryFrameMarkedRowFamily
          (verifierFirstInputArmCellWireFamily W input) := by
  unfold encodeUnaryFrameMarkedCellAffineRows
    verifierInputArmCellRowsParameters exactPolynomialUnaryFrames
    encodeUnaryFrameMarkedRowFamily
  rw [verifierFirstInputArmCellWireFamily_rows]
  have hrows :
      (List.ofFn fun index : Fin input.length =>
        encodeUnaryFrame [verifierFirstInputArmCellWire W input index]) =
      (List.ofFn fun index : Fin input.length =>
        verifierFirstInputArmCellWire W input index).map
          (fun value => encodeUnaryFrame [value]) := by
    rw [List.map_ofFn]
    rfl
  rw [hrows, List.flatMap_map]
  simp [verifierInputArmCountPolynomial_eval, encodeUnaryFrame,
    encodeUnaryFrameBlock, List.append_assoc]

set_option maxHeartbeats 800000 in
/-- One fixed polynomial-time TM2 reads the raw word and emits every exact
public-input cell-wire row for every candidate certificate length. -/
noncomputable def verifierInputArmCellWireRowsFamily_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (verifierInputArmCellWireRowsFamily W) := by
  letI : Fintype Γ := W.alphabetFintype
  let header := exactPolynomialUnaryFrames_computableInPolyTime (Γ := Γ)
    [Polynomial.C (verifierInputStackSymbolWidth W),
      verifierInputArmCountPolynomial W]
  let firstTyped := verifierFirstInputArmCellWireFamily_computableInPolyTime W
  let firstRaw : _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List Γ => encodeUnaryFrameMarkedRowFamily
        (verifierFirstInputArmCellWireFamily W input)) :=
    { tm := firstTyped.tm
      inputAlphabet := firstTyped.inputAlphabet
      outputAlphabet := firstTyped.outputAlphabet
      time := firstTyped.time
      outputsFun := fun input => by
        simpa only [id_eq] using firstTyped.outputsFun input }
  let joined := unaryFrameSameInputConcat_computableInPolyTime header firstRaw
  have source : _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedCellAffineRows
      (verifierInputArmCellRowsParameters W) :=
    { tm := joined.tm
      inputAlphabet := joined.inputAlphabet
      outputAlphabet := joined.outputAlphabet
      time := joined.time
      outputsFun := fun input => by
        simpa only [id_eq, verifierInputArmCellRowsParameters_encode W input] using
          joined.outputsFun input }
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch source
      unaryFrameMarkedCellAffineRowsStream_computableInPolyTime
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simp only [Function.comp_apply, id_eq] at run
        rw [verifierInputArmCellRowsStream_eq W input] at run
        simpa only [id_eq] using run }

end CLRS.Chapter34.Turing.CookLevin

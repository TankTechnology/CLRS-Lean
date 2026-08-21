import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInputBoundaryArmWireRowsSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowFieldReverseRuntime

/-!
# Tail-first verifier-input arm wire rows

The conjunction serializer consumes source wires in reverse order.  This
module applies the verified field-order reverser to the complete arithmetic
arm rows without reversing any individual unary numeral.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Natural-number view of all complete arm wire rows. -/
def verifierInputArmArithmeticWireValueFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFrameValueRowFamily :=
  { rows := List.ofFn fun arm :
      Fin (W.certificateBound.eval input.length + 1) =>
        verifierInputArmArithmeticWires W input arm }

/-- Its structured encoding is exactly the already compiled marked source. -/
theorem verifierInputArmArithmeticWireValueFamily_encode
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeUnaryFrameValueRowFamily
        (verifierInputArmArithmeticWireValueFamily W input) =
      encodeUnaryFrameMarkedRowFamily
        (verifierInputArmArithmeticWireFamily W input) := by
  change ((List.ofFn fun arm :
      Fin (W.certificateBound.eval input.length + 1) =>
        verifierInputArmArithmeticWires W input arm).map
          encodeUnaryFrame).flatMap
      (fun row => row ++ [UnaryFrameSym.frameEnd]) =
    (verifierInputArmArithmeticWireFamily W input).rows.flatMap
      (fun row => row ++ [UnaryFrameSym.frameEnd])
  rw [verifierInputArmArithmeticWireFamily_rows]
  rw [List.map_ofFn]
  rfl

/-- Repackage the existing source with its stronger natural-row interface. -/
noncomputable def
    verifierInputArmArithmeticWireValueFamily_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameValueRowFamily
      (verifierInputArmArithmeticWireValueFamily W) := by
  let source := verifierInputArmArithmeticWireFamily_computableInPolyTime W
  exact
    { tm := source.tm
      inputAlphabet := source.inputAlphabet
      outputAlphabet := source.outputAlphabet
      time := source.time
      outputsFun := fun input => by
        have run := source.outputsFun input
        rw [verifierInputArmArithmeticWireValueFamily_encode W input]
        simpa only [id_eq] using run }

/-- Typed tail-first rows accepted by the conjunction frame encoder. -/
def verifierInputArmArithmeticWireReversedFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFrameMarkedRowFamily :=
  (verifierInputArmArithmeticWireValueFamily W input).fieldReversed

/-- Every output row contains the exact public wire list in reverse order. -/
theorem verifierInputArmArithmeticWireReversedFamily_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierInputArmArithmeticWireReversedFamily W input).rows =
      List.ofFn fun arm :
          Fin (W.certificateBound.eval input.length + 1) =>
        encodeUnaryFrame
          (verifierInputArmArithmeticWires W input arm).reverse := by
  change (List.ofFn fun arm :
      Fin (W.certificateBound.eval input.length + 1) =>
        verifierInputArmArithmeticWires W input arm).map
          (fun values => encodeUnaryFrame values.reverse) = _
  rw [List.map_ofFn]
  rfl

/-- One fixed polynomial-time TM2 emits all exact tail-first arm rows from
the raw verifier input. -/
noncomputable def
    verifierInputArmArithmeticWireReversedFamily_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (verifierInputArmArithmeticWireReversedFamily W) := by
  let source :=
    verifierInputArmArithmeticWireValueFamily_computableInPolyTime W
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch source
      unaryFrameMarkedRowFieldReverse_computableInPolyTime
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [Function.comp_apply, id_eq,
          unaryFrameMarkedRowFieldReverseStream,
          verifierInputArmArithmeticWireReversedFamily] using run }

end CLRS.Chapter34.Turing.CookLevin

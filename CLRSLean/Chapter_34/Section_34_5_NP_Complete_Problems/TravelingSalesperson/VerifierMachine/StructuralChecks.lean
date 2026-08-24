import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.VerifierMachine.HeaderBits
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.VerifierMachine.SquareCount
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.BoolPairStream
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ListPairEq
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.PairFirstProjection
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.PairSecondProjection

/-!
# Decision-TSP verifier: cardinality and matrix-shape checks

Three fixed branches establish the structural numerical conditions:

* the certificate contains exactly `vertexCount` fields;
* the instance contains exactly the square of that many weight fields;
* the vertex count is at least three.

All comparisons operate on compact canonical binary words.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.TSPVerifier.StructuralChecks

open PolyBuilder

abbrev RawInput := List TSPSym × List TSPSym

def rawEncoding (input : RawInput) : List (Option TSPSym) :=
  pairEncoding input.1 input.2

def cardinalityCheck (input : RawInput) : Bool :=
  decide (FieldCount.certificateCountBits input.1 =
    HeaderBits.vertexCountBits input.2)

def matrixShapeCheck (input : RawInput) : Bool :=
  decide (SquareCount.squareCountBits input.1 =
    FieldCount.weightCountBits input.2)

def minimumVertexCountCheck (input : RawInput) : Bool :=
  Turing.BinaryNat.Comparator.leWords (encodeBinaryNat 3)
    (HeaderBits.vertexCountBits input.2)

private noncomputable def certificateProjection :
    _root_.Turing.TM2ComputableInPolyTime rawEncoding id Prod.fst := by
  let source := PairFirstProjection.computableInPolyTime TSPSym
  exact
    { tm := source.tm
      inputAlphabet := source.inputAlphabet
      outputAlphabet := source.outputAlphabet
      time := source.time
      outputsFun := fun input => by
        simpa [rawEncoding] using source.outputsFun input }

private noncomputable def instanceProjection :
    _root_.Turing.TM2ComputableInPolyTime rawEncoding id Prod.snd := by
  let source := PairSecondProjection.computableInPolyTime TSPSym
  exact
    { tm := source.tm
      inputAlphabet := source.inputAlphabet
      outputAlphabet := source.outputAlphabet
      time := source.time
      outputsFun := fun input => by
        simpa [rawEncoding] using source.outputsFun input }

private noncomputable def certificateCountMachine :
    _root_.Turing.TM2ComputableInPolyTime rawEncoding id
      (fun input => FieldCount.certificateCountBits input.1) := by
  let composed := _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
    certificateProjection FieldCount.certificateCountBitsComputableInPolyTime
  simpa [Function.comp_def] using Classical.choice composed

private noncomputable def squareCountMachine :
    _root_.Turing.TM2ComputableInPolyTime rawEncoding id
      (fun input => SquareCount.squareCountBits input.1) := by
  let composed := _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
    certificateProjection SquareCount.squareCountBitsComputableInPolyTime
  simpa [Function.comp_def] using Classical.choice composed

private noncomputable def vertexCountMachine :
    _root_.Turing.TM2ComputableInPolyTime rawEncoding id
      (fun input => HeaderBits.vertexCountBits input.2) := by
  let composed := _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
    instanceProjection HeaderBits.vertexCountBitsComputableInPolyTime
  simpa [Function.comp_def] using Classical.choice composed

private noncomputable def weightCountMachine :
    _root_.Turing.TM2ComputableInPolyTime rawEncoding id
      (fun input => FieldCount.weightCountBits input.2) := by
  let composed := _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
    instanceProjection FieldCount.weightCountBitsComputableInPolyTime
  simpa [Function.comp_def] using Classical.choice composed

private noncomputable def equalityMachine
    {left right : RawInput → List Bool}
    (leftMachine : _root_.Turing.TM2ComputableInPolyTime rawEncoding id left)
    (rightMachine : _root_.Turing.TM2ComputableInPolyTime rawEncoding id right) :
    _root_.Turing.TM2ComputableInPolyTime rawEncoding
      _root_.Turing.TM2Comp.boolEncoding
      (fun input => decide (left input = right input)) := by
  let paired := BoolPairStream.computableInPolyTime leftMachine rightMachine
  let composed := _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
    paired (ListPairEq.computableInPolyTime Bool)
  simpa [Function.comp_def] using Classical.choice composed

noncomputable def cardinalityCheckComputableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime rawEncoding
      _root_.Turing.TM2Comp.boolEncoding cardinalityCheck := by
  change _root_.Turing.TM2ComputableInPolyTime rawEncoding
    _root_.Turing.TM2Comp.boolEncoding
      (fun input => decide (FieldCount.certificateCountBits input.1 =
        HeaderBits.vertexCountBits input.2))
  exact equalityMachine certificateCountMachine vertexCountMachine

noncomputable def matrixShapeCheckComputableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime rawEncoding
      _root_.Turing.TM2Comp.boolEncoding matrixShapeCheck := by
  change _root_.Turing.TM2ComputableInPolyTime rawEncoding
    _root_.Turing.TM2Comp.boolEncoding
      (fun input => decide (SquareCount.squareCountBits input.1 =
        FieldCount.weightCountBits input.2))
  exact equalityMachine squareCountMachine weightCountMachine

private def constantThree (_ : RawInput) : List Bool := encodeBinaryNat 3

private def constantThreeSpec :
    StatefulFlatMapSpec Unit (Option TSPSym) Bool where
  initial := ()
  action _ _ := ([], ())
  finish _ := encodeBinaryNat 3

private theorem constantThreeRewriteFrom (input : List (Option TSPSym)) :
    rewriteStatefulFlatMapFrom constantThreeSpec () input = encodeBinaryNat 3 := by
  induction input with
  | nil => rfl
  | cons symbol rest ih =>
      rw [rewriteStatefulFlatMapFrom.eq_def]
      simpa [constantThreeSpec] using ih

private noncomputable def constantThreeMachine :
    _root_.Turing.TM2ComputableInPolyTime rawEncoding id constantThree := by
  have machine := statefulFlatMap_computableInPolyTime constantThreeSpec
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have output := machine.outputsFun (rawEncoding input)
        rw [show rewriteStatefulFlatMap constantThreeSpec
              (rawEncoding input) = encodeBinaryNat 3 by
          exact constantThreeRewriteFrom (rawEncoding input)] at output
        simpa [constantThree] using output }

noncomputable def minimumVertexCountCheckComputableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime rawEncoding
      _root_.Turing.TM2Comp.boolEncoding minimumVertexCountCheck := by
  let paired := BoolPairStream.computableInPolyTime
    constantThreeMachine vertexCountMachine
  let composed := _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
    paired Turing.BinaryNat.Comparator.computableInPolyTime
  let machine := Classical.choice composed
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have output := machine.outputsFun input
        simpa [minimumVertexCountCheck, constantThree,
          Function.comp_def] using output }

theorem cardinalityCheck_encode (data : TSPData) (vertices : List Nat) :
    cardinalityCheck
        (encodeTSPCertificate vertices, encodeTSPData data) =
      decide (vertices.length = data.vertexCount) := by
  simp [cardinalityCheck, encodeBinaryNat_injective.eq_iff]

theorem matrixShapeCheck_encode (data : TSPData) (vertices : List Nat) :
    matrixShapeCheck
        (encodeTSPCertificate vertices, encodeTSPData data) =
      decide (vertices.length ^ 2 = data.weights.length) := by
  simp [matrixShapeCheck, encodeBinaryNat_injective.eq_iff]

theorem minimumVertexCountCheck_encode
    (data : TSPData) (vertices : List Nat) :
    minimumVertexCountCheck
        (encodeTSPCertificate vertices, encodeTSPData data) = true ↔
      3 ≤ data.vertexCount := by
  simpa [minimumVertexCountCheck] using
    Turing.BinaryNat.Comparator.leWords_encoded_eq_true_iff
      3 data.vertexCount

end CLRS.Chapter34.Turing.TSPVerifier.StructuralChecks

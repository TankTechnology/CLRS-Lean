import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.VerifierMachine.CostSemantics.Selection
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.VerifierMachine.StructuralChecks
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.BoolPairStream
import CLRSLean.Chapter_34.BinaryNat.Machine.Adder
import CLRSLean.Chapter_34.BinaryNat.Machine.Comparator

/-! # Decision-TSP verifier: selected tour cost against the budget -/

noncomputable section

namespace CLRS.Chapter34.Turing.TSPVerifier.BudgetCheck

open _root_.Turing
open PolyBuilder

abbrev RawInput := UnaryBaseInput.RawInput

def rawEncoding : RawInput → List (Option TSPSym) :=
  UnaryBaseInput.rawEncoding

def budgetBits (input : RawInput) : List Bool :=
  HeaderBits.budgetBits input.2

def doubleBudgetBits (input : RawInput) : List Bool :=
  BinaryNat.Adder.addWords (budgetBits input) (budgetBits input)

def costCheck (input : RawInput) : Bool :=
  BinaryNat.Comparator.leWords
    (SelectedWeightSum.selectedSumBits input)
    (doubleBudgetBits input)

private noncomputable def budgetBitsComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id budgetBits := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    StructuralChecks.instanceProjection
    HeaderBits.budgetBitsComputableInPolyTime
  change TM2ComputableInPolyTime StructuralChecks.rawEncoding id
    (fun input => HeaderBits.budgetBits input.2)
  simpa only [Function.comp_def] using Classical.choice composed

noncomputable def doubleBudgetBitsComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id doubleBudgetBits := by
  let paired := BoolPairStream.computableInPolyTime
    budgetBitsComputableInPolyTime budgetBitsComputableInPolyTime
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    paired BinaryNat.Adder.computableInPolyTime
  change TM2ComputableInPolyTime rawEncoding id
    (fun input => BinaryNat.Adder.addWords
      (budgetBits input) (budgetBits input))
  simpa only [Function.comp_def] using Classical.choice composed

/-- The complete comparison branch is one fixed polynomial-time machine. -/
noncomputable def costCheckComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding costCheck := by
  let paired := BoolPairStream.computableInPolyTime
    SelectedWeightSum.selectedSumBitsComputableInPolyTime
    doubleBudgetBitsComputableInPolyTime
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    paired BinaryNat.Comparator.computableInPolyTime
  change TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
    (fun input => BinaryNat.Comparator.leWords
      (SelectedWeightSum.selectedSumBits input)
      (doubleBudgetBits input))
  simpa only [Function.comp_def, rawEncoding,
    SelectedWeightSum.rawEncoding] using Classical.choice composed

@[simp] theorem binaryNatValue_doubleBudgetBits_encode
    (vertices : List Nat) (data : TSPData) :
    binaryNatValue
        (doubleBudgetBits
          (UnaryCertificate.encode vertices, encodeTSPData data)) =
      2 * data.budget := by
  rw [doubleBudgetBits, budgetBits, HeaderBits.budgetBits_encode,
    BinaryNat.Adder.binaryNatValue_addWords,
    binaryNatValue_encode]
  omega

/-- On inputs that pass the structural, duplicate, range, and symmetry
branches, the concrete doubled-cost comparison is exactly the textbook budget
condition. -/
theorem costCheck_encode_iff (vertices : List Nat) (data : TSPData)
    (hwellFormed : data.WellFormed)
    (hthree : 3 ≤ vertices.length) (hnodup : vertices.Nodup)
    (hcount : vertices.length = data.vertexCount)
    (hbound : ∀ vertex ∈ vertices, vertex < data.vertexCount) :
    costCheck (UnaryCertificate.encode vertices, encodeTSPData data) = true ↔
      data.toInstance.tourCost vertices ≤ data.budget := by
  rw [costCheck, BinaryNat.Comparator.leWords_eq_true_iff,
    CostSemantics.binaryNatValue_selectedSumBits_encode_eq vertices data
      hwellFormed hthree hnodup hcount hbound,
    binaryNatValue_doubleBudgetBits_encode]
  omega

end CLRS.Chapter34.Turing.TSPVerifier.BudgetCheck

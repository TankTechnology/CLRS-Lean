import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.ReductionMachine.Codec
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.ReductionMachine.HeaderFields
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.ReductionMachine.VertexCountBits

/-! # Fixed generation of the HAM-CYCLE to TSP instance header -/

noncomputable section

namespace CLRS.Chapter34.Turing.TSPReduction

open _root_.Turing
open PolyBuilder

def firstHeaderField (I : CliqueInstance) : List TSPSym :=
  HeaderFields.first (vertexCountBits I)

def secondHeaderField (I : CliqueInstance) : List TSPSym :=
  HeaderFields.second (vertexCountBits I)

def header (I : CliqueInstance) : List TSPSym :=
  firstHeaderField I ++ secondHeaderField I

theorem header_eq (I : CliqueInstance) :
    header I = .instanceMark :: encodeTSPField I.vertexCount ++
      encodeTSPField I.vertexCount := by
  rw [header, firstHeaderField, secondHeaderField,
    HeaderFields.first_eq, HeaderFields.second_eq]
  rfl

private noncomputable def firstHeaderFieldComputableInPolyTime :
    TM2ComputableInPolyTime encodeCliqueInstance id firstHeaderField := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    vertexCountBitsComputableInPolyTime
    HeaderFields.firstComputableInPolyTime
  let machine := Classical.choice composed
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun I => by
        have output := machine.outputsFun I
        simpa [Function.comp_def, firstHeaderField] using output }

private noncomputable def secondHeaderFieldComputableInPolyTime :
    TM2ComputableInPolyTime encodeCliqueInstance id secondHeaderField := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    vertexCountBitsComputableInPolyTime
    HeaderFields.secondComputableInPolyTime
  let machine := Classical.choice composed
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun I => by
        have output := machine.outputsFun I
        simpa [Function.comp_def, secondHeaderField] using output }

noncomputable def headerComputableInPolyTime :
    TM2ComputableInPolyTime encodeCliqueInstance id header := by
  exact fixedPairSameInputConcat_computableInPolyTime
    encodeTSPSymPair decodeTSPSymPair decode_encodeTSPSymPair
    firstHeaderFieldComputableInPolyTime secondHeaderFieldComputableInPolyTime

end CLRS.Chapter34.Turing.TSPReduction

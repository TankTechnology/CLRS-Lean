import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.ReductionMachine.CompleteWeights
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.ReductionMachine.Header
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.ReductionMachine.RecordEnd

/-! # Fixed typed HAM-CYCLE to TSP encoder -/

noncomputable section

namespace CLRS.Chapter34.Turing.TSPReduction.Typed

open _root_.Turing
open PolyBuilder

def typedPrefix (I : CliqueInstance) : List TSPSym :=
  header I ++ completeWeightFields I

def stream (I : CliqueInstance) : List TSPSym :=
  typedPrefix I ++ RecordEnd.stream I

theorem stream_eq (I : CliqueInstance) :
    stream I = encodeTSPData
      (CLRS.Chapter34.TSPReduction.hamiltonianTSPData I) := by
  rw [stream, typedPrefix, header_eq, completeWeightFields_eq]
  simp [RecordEnd.stream, encodeTSPData,
    CLRS.Chapter34.TSPReduction.hamiltonianTSPData,
    encodeTSPFields, List.append_assoc]

private noncomputable def typedPrefixComputableInPolyTime :
    TM2ComputableInPolyTime encodeCliqueInstance id typedPrefix := by
  exact fixedPairSameInputConcat_computableInPolyTime
    encodeTSPSymPair decodeTSPSymPair decode_encodeTSPSymPair
    headerComputableInPolyTime completeWeightFieldsComputableInPolyTime

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime encodeCliqueInstance id stream := by
  exact fixedPairSameInputConcat_computableInPolyTime
    encodeTSPSymPair decodeTSPSymPair decode_encodeTSPSymPair
    typedPrefixComputableInPolyTime RecordEnd.computableInPolyTime

end CLRS.Chapter34.Turing.TSPReduction.Typed

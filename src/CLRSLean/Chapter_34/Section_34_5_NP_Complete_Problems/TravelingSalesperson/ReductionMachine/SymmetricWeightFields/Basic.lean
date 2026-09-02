import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.ReductionMachine.WeightFields.Basic

/-! # Formatting both orientations of each TSP pair weight -/

namespace CLRS.Chapter34.Turing.TSPReduction.SymmetricWeightFields

open PolyBuilder

/-- Emit the same compact weight field for both directed orientations of one
undirected source pair. -/
def stream (answers : List Bool) : List TSPSym :=
  answers.flatMap fun answer =>
    encodeTSPField (WeightFields.answerWeight answer) ++
      encodeTSPField (WeightFields.answerWeight answer)

def body : LoopBody Bool TSPSym where
  emit := fun answer =>
    encodeTSPField (WeightFields.answerWeight answer) ++
      encodeTSPField (WeightFields.answerWeight answer)
  cost := fun _ => 10
  emit_length_le_cost := by
    intro answer
    cases answer <;> decide

theorem stream_eq_encoded_duplicate_weights (answers : List Bool) :
    stream answers =
      encodeTSPFields ((answers.map WeightFields.answerWeight).flatMap
        fun weight => [weight, weight]) := by
  simp only [stream, encodeTSPFields, List.flatMap_assoc,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [List.flatMap_map]

end CLRS.Chapter34.Turing.TSPReduction.SymmetricWeightFields

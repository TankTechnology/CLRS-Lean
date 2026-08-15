import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactlyOne

open CLRS.Chapter34
open CLRS.Chapter34.Turing
open CLRS.Chapter34.Turing.PolyBuilder

#check sequentialExactlyOneGateStream
#check sequentialExactlyOneGateStream_eq_trace
#check sequentialExactlyOneRevProgram
#check sequentialExactlyOneRev_run
#check sequentialExactlyOneRev_outputs
#check sequentialExactlyOneRev_computableInPolyTime
#check sequentialExactlyOneGateStream_computableInPolyTime

example (count : Nat) :
    sequentialExactlyOneGateStream count =
      (CookLevin.exactlyOneGateTrace 0 (List.range count)).gates.flatMap
        encodeCircuitGate := by
  exact sequentialExactlyOneGateStream_eq_trace count

example :
    sequentialExactlyOneGateStream 0 =
      [.constFalseMark, .constFalseMark,
       .notMark, .argMark, .endMark,
       .andMark, .endMark, .argMark, .argMark, .endMark] := by
  native_decide

#print axioms sequentialExactlyOneGateStream_eq_trace
#print axioms sequentialExactlyOneRev_run
#print axioms sequentialExactlyOneRev_outputs
#print axioms sequentialExactlyOneRev_computableInPolyTime
#print axioms sequentialExactlyOneGateStream_computableInPolyTime

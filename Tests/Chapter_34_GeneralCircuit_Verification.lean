import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit

namespace CLRS.Chapter34

#check isAssignmentSymbol
#check assignmentSymbolValue
#check assignmentInputs
#check encodeAssignment
#check generalCircuitVerifier
#check generalCircuitVerifier_accepts_iff
#check mem_generalCircuitSAT_iff_exists_certificate

private def identityCircuit : Circuit where
  inputCount := 1
  gates := [.input 0]
  output := 0

example :
    generalCircuitVerifier [.constTrueMark]
      (encodeCircuit identityCircuit) = true := by
  native_decide

example :
    generalCircuitVerifier [.constFalseMark]
      (encodeCircuit identityCircuit) = false := by
  native_decide

example :
    generalCircuitVerifier [.inputMark]
      (encodeCircuit identityCircuit) = false := by
  native_decide

example : generalCircuitVerifier [.constTrueMark] [] = false := by
  native_decide

end CLRS.Chapter34

import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.Validity

open CLRS Chapter34
open CLRS.Chapter34.Turing
open CLRS.Chapter34.Turing.CookLevin

#check CellValidityGateTrace
#check cellValidityGateTrace
#check cellValidityGateTrace_length
#check CellValidityResult
#check buildCellValidity
#check buildCellValidity_gates_eq
#check buildCellValidity_output_eq_trace
#check ExactlyOneFamilyGateTrace
#check exactlyOneFamilyGateTrace
#check exactlyOneFamilyGateTrace_length
#check ExactlyOneFamilyResult
#check exactlyOneFamily
#check exactlyOneFamily_gates_eq
#check exactlyOneFamily_output_eq_trace
#check CfgOneHotGroup
#check cfgOneHotGroupWires
#check RawOneHotGateTrace
#check rawOneHotGateTrace
#check RawOneHotResult
#check buildRawOneHot
#check buildRawOneHot_gates_eq
#check buildRawOneHot_output_eq_trace
#check StackValidityFamilyGateTrace
#check stackValidityFamilyGateTrace
#check stackValidityFamilyGateTrace_length
#check StackValidityFamilyResult
#check buildStackValidityFamily
#check buildStackValidityFamily_gates_eq
#check buildStackValidityFamily_output_eq_trace
#check CanonicalValidityGateTrace
#check canonicalValidityGateTrace
#check canonicalValidityGateTrace_length
#check validCfgCircuit_gates_eq
#check validCfgCircuit_wire_eq_trace

def twoActive : Fin 2 → CircuitBuilder.Wire
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 3

def twoBlank : Fin 2 → CircuitBuilder.Wire
  | ⟨0, _⟩ => 4
  | ⟨1, _⟩ => 5

def twoGroups : Fin 2 → List CircuitBuilder.Wire
  | ⟨0, _⟩ => [2]
  | ⟨1, _⟩ => [3, 4]

example :
    (cellValidityGateTrace 7 2 twoActive twoBlank).gates =
      [.not 4, .not 2, .not 7, .and 2 7, .and 8 9, .or 10 11,
       .not 5, .not 3, .not 13, .and 3 13, .and 14 15, .or 16 17] ∧
    (cellValidityGateTrace 7 2 twoActive twoBlank).outputs 0 = 12 ∧
    (cellValidityGateTrace 7 2 twoActive twoBlank).outputs 1 = 18 := by
  native_decide

example :
    (exactlyOneFamilyGateTrace 7 2 twoGroups).gates.length = 17 ∧
    (exactlyOneFamilyGateTrace 7 2 twoGroups).outputs 0 = 13 ∧
    (exactlyOneFamilyGateTrace 7 2 twoGroups).outputs 1 = 23 := by
  native_decide

#print axioms buildCellValidity_gates_eq
#print axioms buildCellValidity_output_eq_trace
#print axioms exactlyOneFamily_gates_eq
#print axioms exactlyOneFamily_output_eq_trace
#print axioms buildRawOneHot_gates_eq
#print axioms buildRawOneHot_output_eq_trace
#print axioms buildStackValidityFamily_gates_eq
#print axioms buildStackValidityFamily_output_eq_trace
#print axioms validCfgCircuit_gates_eq
#print axioms validCfgCircuit_wire_eq_trace

import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OneHotPairMap

open CLRS.Chapter34
open CLRS.Chapter34.Turing
open CLRS.Chapter34.Turing.CookLevin
open CLRS.Chapter34.Turing.PolyBuilder

#check oneHotPairAndGateTrace
#check oneHotPairOperands
#check oneHotPairMapGateTrace
#check oneHotPairMapFamilies
#check oneHotPairMapGateTrace_gates_eq_phases
#check oneHotPairMap_gates_eq
#check oneHotPairMap_wire_eq_trace
#check affineOneHotPairMapInput
#check affineOneHotPairMapGateStream_eq_trace
#check affineOneHotPairMap_run
#check affineOneHotPairMap_steps_le

def pairLeft : Fin 2 → CircuitBuilder.Wire := fun i => i.val
def pairRight : Fin 2 → CircuitBuilder.Wire := fun i => 2 + i.val
def pairFunction : Fin 2 → Fin 2 → Fin 3 := fun i j =>
  if i = j then 0 else 2

example : affineAndThenOrGateStream
      (affineOneHotPairMapAndFrames pairLeft pairRight)
      (affineOneHotPairMapOrGroups 11 pairLeft pairRight pairFunction) =
    (oneHotPairMapGateTrace 11 pairLeft pairRight pairFunction).gates.flatMap
      encodeCircuitGate := by
  exact affineOneHotPairMapGateStream_eq_trace 11 _ _ _

example : affineAndThenOrRevSteps
      (affineOneHotPairMapAndFrames pairLeft pairRight)
      (affineOneHotPairMapOrGroups 11 pairLeft pairRight pairFunction) ≤
    100 * (affineOneHotPairMapInput 11 pairLeft pairRight
      pairFunction).length + 2 := by
  exact affineOneHotPairMap_steps_le 11 _ _ _

#print axioms oneHotPairMapGateTrace_gates_eq_phases
#print axioms oneHotPairMap_gates_eq
#print axioms oneHotPairMap_wire_eq_trace
#print axioms affineOneHotPairMapGateStream_eq_trace
#print axioms affineOneHotPairMap_run
#print axioms affineOneHotPairMap_steps_le

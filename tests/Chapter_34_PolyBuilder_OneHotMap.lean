import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OneHotMap

open CLRS.Chapter34
open CLRS.Chapter34.Turing
open CLRS.Chapter34.Turing.CookLevin
open CLRS.Chapter34.Turing.PolyBuilder

#check oneHotMapFibers
#check oneHotMapGateTrace_gates_eq_family
#check affineOneHotMapCanonicalGroups
#check affineOneHotMapGateStream_eq_trace
#check affineOneHotMap_run
#check affineOneHotMap_steps_le
#check oneHotMap_gates_eq_disjunctionFamily

def sampleOneHotSource : Fin 4 → CircuitBuilder.Wire := fun i => i.val

def sampleOneHotFunction : Fin 4 → Fin 3 := fun i =>
  if i.val % 2 = 0 then 0 else 2

example : (oneHotMapGateTrace 7 sampleOneHotSource
      sampleOneHotFunction).gates =
    CircuitBuilder.disjunctionFamilyGateTrace 7
      (oneHotMapFibers sampleOneHotSource sampleOneHotFunction) := by
  exact oneHotMapGateTrace_gates_eq_family 7 _ _

example : affineOrFinFamilyGateStream
      (affineOneHotMapCanonicalGroups 7 sampleOneHotSource
        sampleOneHotFunction) =
    (oneHotMapGateTrace 7 sampleOneHotSource
      sampleOneHotFunction).gates.flatMap encodeCircuitGate := by
  exact affineOneHotMapGateStream_eq_trace 7 sampleOneHotSource
    sampleOneHotFunction

example : affineOrFinFamilyRevSteps
      (affineOneHotMapCanonicalGroups 7 sampleOneHotSource
        sampleOneHotFunction) ≤
    100 * (encodeAffineOrFinGroups
      (affineOneHotMapCanonicalGroups 7 sampleOneHotSource
        sampleOneHotFunction)).length + 2 := by
  exact affineOneHotMap_steps_le 7 _ _

#print axioms oneHotMapGateTrace_gates_eq_family
#print axioms affineOneHotMapGateStream_eq_trace
#print axioms affineOneHotMap_run
#print axioms affineOneHotMap_steps_le
#print axioms oneHotMap_gates_eq_disjunctionFamily

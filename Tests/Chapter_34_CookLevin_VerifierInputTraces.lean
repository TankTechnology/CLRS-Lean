import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.VerifierInput.Core

open CLRS.Chapter34.Turing
open CLRS.Chapter34.Turing.CookLevin
open CLRS.Chapter34.Turing.CookLevin.VerifierInput

#check separatorNotsGateTrace
#check buildSeparatorNots_gates_eq
#check inputArmGateTrace
#check inputArmsGateTrace
#check buildInputArms_gates_eq
#check verifierInputShapeGateTrace
#check verifierInputShapeCircuit_gates_eq

#print axioms buildSeparatorNots_gates_eq
#print axioms buildInputArms_gates_eq
#print axioms verifierInputShapeCircuit_gates_eq

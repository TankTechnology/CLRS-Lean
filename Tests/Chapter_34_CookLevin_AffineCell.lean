import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Cell

open StateTransition
open CLRS.Chapter34.Turing.PolyBuilder

#check affineCellGateStream
#check affineCellGateStream_eq_trace
#check affineCellBodyCfg
#check affineCellRevCoreSteps
#check affineCellRev_runToHaltLabel
#check affineCellRevSteps
#check affineCellRev_runFrom
#check affineCellRev_steps_le

#print axioms affineCellGateStream_eq_trace
#print axioms affineCellRev_runToHaltLabel
#print axioms affineCellRev_runFrom
#print axioms affineCellRev_steps_le

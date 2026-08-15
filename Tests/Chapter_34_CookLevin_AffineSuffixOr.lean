import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.SuffixOr

open CLRS.Chapter34
open CLRS.Chapter34.Turing
open CLRS.Chapter34.Turing.CookLevin
open CLRS.Chapter34.Turing.PolyBuilder

#check affineSuffixOrGateStream
#check affineSuffixOrGateStream_eq_trace
#check affineSuffixOrBodyCfg
#check affineSuffixOrRevSteps
#check affineSuffixOrRev_runFrom
#check affineSuffixOrRev_steps_le

#print axioms affineSuffixOrGateStream_eq_trace
#print axioms affineSuffixOrRev_runFrom
#print axioms affineSuffixOrRev_steps_le

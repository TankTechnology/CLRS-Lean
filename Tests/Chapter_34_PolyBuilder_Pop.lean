import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Pop

open CLRS.Chapter34.Turing
open CLRS.Chapter34.Turing.CookLevin
open CLRS.Chapter34.Turing.PolyBuilder

#check affineOrFinNoSeedGateStream
#check affineOrFinNoSeed_run
#check affineOrFinNoSeedRev_steps_le
#check affinePopFrames
#check encodeAffinePopInput
#check affinePopGateStream_eq_trace
#check affinePop_run
#check affinePop_steps_le

#print axioms affineOrFinNoSeed_run
#print axioms affinePopGateStream_eq_trace
#print axioms affinePop_run
#print axioms affinePop_steps_le

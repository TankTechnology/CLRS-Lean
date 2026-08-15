import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Stack

open StateTransition
open CLRS.Chapter34.Turing.PolyBuilder

#check AffineStackFrame
#check encodeAffineStackFrame
#check encodeAffineStackFrame_length
#check affineStackGateStream
#check AffineStackLabel
#check affineStackRevProgram
#check affineStackLoopCfg
#check affineStackMaskReadyCfg
#check affineStackMaskCoreExitCfg
#check affineStackMask_load
#check affineStackMaskCore_run
#check affineStackRevSteps
#check affineStack_run
#check affineStackRev_steps_le

#print axioms affineStackMask_load
#print axioms affineStackMaskCore_run
#print axioms affineStack_run
#print axioms affineStackRev_steps_le

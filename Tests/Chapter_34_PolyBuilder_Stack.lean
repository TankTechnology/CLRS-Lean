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
#check affineStackFrameRevSteps
#check affineStack_runOne
#check encodeAffineStackFamily
#check affineStackFamilyGateStream
#check affineStackFamilyGateStream_eq_flatMap
#check affineStackFamilyRevSteps
#check affineStackFamily_empty_run
#check affineStackFamily_run
#check affineStackFrameRev_steps_le
#check affineStackFamilyRev_steps_le
#check affineStackRevSteps
#check affineStack_run
#check affineStackRev_steps_le

#print axioms affineStackMask_load
#print axioms affineStackMaskCore_run
#print axioms affineStack_runOne
#print axioms affineStackFamily_run
#print axioms affineStackFamilyRev_steps_le
#print axioms affineStack_run
#print axioms affineStackRev_steps_le

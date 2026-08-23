import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.TargetBound.Canonical

open CLRS Chapter34
open CLRS.Chapter34.Turing.GeneralCliqueVerifier.TargetBound

#check targetBound_run
#check targetBoundSteps_le
#check targetBoundPassComputableInPolyTime
#check targetBoundPass_encode_iff

example :
    targetBoundPass []
      (encodeCliqueInstance
        { vertexCount := 4, targetSize := 3, edges := [] }) = true := by
  decide

example :
    targetBoundPass []
      (encodeCliqueInstance
        { vertexCount := 2, targetSize := 3, edges := [] }) = false := by
  decide

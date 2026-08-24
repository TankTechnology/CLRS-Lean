import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.BatchEdgeLookup.Runtime

open CLRS Chapter34 StateTransition
open CLRS.Chapter34.Turing.GeneralCliqueVerifier.BatchEdgeLookup

#check batch_run
#check batchSteps_le
#check batchResults_outputs_in_time
#check batchResultsComputableInPolyTime
#check batchComputableInPolyTime

#print axioms batchResultsComputableInPolyTime
#print axioms batchComputableInPolyTime

private def sampleInstance : CliqueInstance where
  vertexCount := 4
  targetSize := 3
  edges := [(0, 1), (0, 2), (1, 2), (2, 3)]

example : queriesInEdgesBool sampleInstance [(0, 1), (1, 2)] = true := by
  decide

example : queriesInEdgesBool sampleInstance [(0, 1), (1, 3)] = false := by
  decide

example : queryMembershipBits sampleInstance [(0, 1), (1, 3)] =
    [true, false] := by
  decide

example : batchResultStream sampleInstance [(0, 1), (1, 3)] =
    [false, true, false] := by
  decide

/-- A repeated certificate value becomes a loop query and is rejected by a
canonical simple-graph edge table. -/
example : queriesInEdgesBool sampleInstance [(2, 2)] = false := by
  decide

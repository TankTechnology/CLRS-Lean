import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.BaseChecks.Runtime

noncomputable section

open CLRS Chapter34
open CLRS.Chapter34.Turing.GeneralCliqueVerifier
open Turing

#check BaseChecks.baseChecks
#check BaseChecks.cardinalityAndTargetComputableInPolyTime
#check BaseChecks.certificateChecksComputableInPolyTime
#check BaseChecks.graphChecksComputableInPolyTime
#check BaseChecks.typedBaseChecksComputableInPolyTime
#check BaseChecks.baseChecksComputableInPolyTime

example :
    TM2ComputableInPolyTime
      (fun pr : List CliqueSym × List CliqueSym => pairEncoding pr.1 pr.2)
      TM2Comp.boolEncoding
      (fun pr => BaseChecks.baseChecks pr.1 pr.2) :=
  BaseChecks.baseChecksComputableInPolyTime

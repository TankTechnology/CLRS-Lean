import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Conjunction

open StateTransition
open CLRS.Chapter34.Turing.PolyBuilder

#check AffineConjunctionFrame
#check encodeAffineConjunctionFrame
#check encodeAffineConjunctionFrame_length
#check affineConjunctionGateStream
#check affineConjunctionGateStream_eq_trace
#check affineAndRevCoreSteps
#check affineAndRev_runToDoneLabel
#check affineConjunctionRevProgram
#check affineConjunctionLoopCfg
#check affineConjunctionFinishCfg
#check affineConjunctionRevSteps
#check affineConjunction_runToFinish
#check affineConjunction_run
#check affineConjunctionRev_steps_le

/-- A `frameEnd` after at least one tick is a malformed partial wire, not the
end of the source family. -/
example :
    (flip Option.bind (step affineConjunctionRevProgram))^[4]
      (some (affineConjunctionCfg (.load .loadWire) none none false
        [.tick, .frameEnd] [] [] [] [] [] [])) =
      some (affineConjunctionCfg .invalid (some .frameEnd) none true
        [] [] [] [] [] [] []) := by
  rfl

#print axioms affineAndRev_runToDoneLabel
#print axioms affineConjunctionGateStream_eq_trace
#print axioms affineConjunction_runToFinish
#print axioms affineConjunction_run
#print axioms affineConjunctionRev_steps_le

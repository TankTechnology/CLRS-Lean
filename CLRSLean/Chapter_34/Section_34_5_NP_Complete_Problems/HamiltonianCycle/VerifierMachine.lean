import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.VerifierMachine.TargetIncrement

/-!
# HAM-CYCLE fixed verifier machinery

Exports the small fixed-machine components used to realize the serialized
HAM-CYCLE certificate checker.  The first component increments the target
field of a graph encoding, allowing the existing CLIQUE target-bound machine
to distinguish equality from strict inequality.
-/

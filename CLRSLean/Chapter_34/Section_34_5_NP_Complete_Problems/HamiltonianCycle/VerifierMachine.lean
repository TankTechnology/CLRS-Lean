import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.VerifierMachine.CertificateNodup
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.VerifierMachine.MinimumVertexCount
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.VerifierMachine.TargetIncrement

/-!
# HAM-CYCLE fixed verifier machinery

Exports the small fixed-machine components used to realize the serialized
HAM-CYCLE certificate checker.  They currently decide certificate
distinctness, the three-vertex minimum, and transform the target field so the
existing CLIQUE target-bound machine can distinguish equality from strict
inequality.
-/

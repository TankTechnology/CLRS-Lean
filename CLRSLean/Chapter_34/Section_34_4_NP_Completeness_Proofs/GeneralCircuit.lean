import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.Basic
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.Verification
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine

/-!
# General Acyclic Boolean Circuits

Facade for the explicit acyclic Boolean-circuit syntax, well-formedness
predicate, executable gate-order evaluator, total finite-symbol codec,
satisfiability language, and the evaluator's accumulator invariants.
The terminal verification layer gives {lit}`GeneralCircuitSAT` an exact executable
finite-certificate semantics.  The concrete TM2 verifier computes that Boolean
on every input and exposes a quadratic bound for successful canonical runs;
the uniform polynomial bound over every rejecting route remains open.
-/

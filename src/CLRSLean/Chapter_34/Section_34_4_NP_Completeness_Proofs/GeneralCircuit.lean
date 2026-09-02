import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.Basic
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.Verification
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.NP
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT

/-!
# General Acyclic Boolean Circuits

Facade for the explicit acyclic Boolean-circuit syntax, well-formedness
predicate, executable gate-order evaluator, total finite-symbol codec,
satisfiability language, and the evaluator's accumulator invariants.
The terminal verification layer gives {lit}`GeneralCircuitSAT` an exact executable
finite-certificate semantics.  The concrete TM2 verifier computes that Boolean
on every input; all successful, canonical-rejecting, and malformed routes lie
under one explicit quartic polynomial.  The facade also exports polynomial
verifiability and `GeneralCircuitSAT ∈ NP`.
The `ToSAT` layer additionally exports the textbook consistency formula, its
exact raw-language semantics, and its polynomial output-size bound.
-/

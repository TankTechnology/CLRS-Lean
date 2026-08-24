import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Semantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Encoding
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine

/-!
# General CIRCUIT-SAT to SAT

Facade for the textbook consistency-formula bridge from the honest general
acyclic circuit language to SAT.  It exports the semantic equivalence, the
total raw encoding map, exact language preservation, and a polynomial
output-size bound.

It also exports a concrete fixed multitape Turing machine computing the total
map in polynomial time.
-/

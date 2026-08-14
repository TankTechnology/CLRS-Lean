import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.Witness
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.Horizon
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.TableauLayout
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.ReductionMap

/-!
# Cook--Levin circuitization

This facade exports the normalized verifier witness, polynomial execution
envelopes, proof-carrying whole-tableau assembly, and the closed verifier
circuit.  Its principal contracts are well-formedness, exact satisfiability
semantics, fixed-verifier polynomial gate and input bounds, and a polynomial
bound for the complete circuit encoding.
The exported {lit}`cookLevinMap` packages that circuit as an explicit finite-string
map with exact membership semantics and a polynomial output-length bound.
-/

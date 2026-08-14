import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.Witness
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.Horizon
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.TableauLayout
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorClock
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorHeader
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
The generator-clock layer supplies concrete exact unary clocks for every
primary verifier-circuit dimension without adding a source-alphabet finiteness
premise to the universal construction.
The generator-header layer derives the exact tableau arity polynomial, emits
the canonical circuit header and initial input-gate family, and proves that
the latter is byte-for-byte the semantic tableau allocator's gate encoding.
-/

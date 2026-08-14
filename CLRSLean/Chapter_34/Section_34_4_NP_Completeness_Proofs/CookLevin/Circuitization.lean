import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.Witness
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.Horizon
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.TableauLayout
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorClock
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorHeader
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidity
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityOneHot
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityBoolEq
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityStack
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
the canonical circuit header and initial input-gate family, combines them in
one concrete input-preserving run, and proves that the result is a literal
prefix of the complete semantic verifier-circuit encoding.
The generator-validity layer identifies the literal serialized suffix for all
canonical row-validity gates and proves that the resulting stream advances
that prefix through the complete validity phase.  Its concrete construction
now covers every raw one-hot group, the following halted/none-label equality,
every stack's suffix-OR active mask, and every fixed stack-cell XNOR block with
exact contextual runs and closed wire indices.  The leading blank-bit
negations, finite-family iteration, and final conjunction remain the row-local
machine phases.
-/

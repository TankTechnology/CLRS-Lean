import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.ThreeCNF.NPCompleteness

/-!
# Standalone 3-CNF-SAT verification and NP-completeness

This facade exposes the canonical raw assignment format, total checker, exact
all-input acceptance semantics, and linear certificate bound for
{lit}`ThreeCNFSat`.  It also exposes a fixed polynomial-time reduction-backed
verifier and the public {lit}`threeCNFSat_mem_ClassNP` and
{lit}`threeCNFSat_npComplete` theorems.  Compiling the smaller assignment
checker itself to a fixed machine remains an optional implementation
refinement.
-/

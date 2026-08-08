import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CircuitSAT

/-!
# 34.4 NP-Completeness Proofs

The specific polynomial-time reductions of CLRS §34.4: CIRCUIT-SAT poly-reduces
to SAT, SAT to 3-CNF-SAT, and 3-CNF-SAT to CLIQUE.  This facade imports the
reduction constructions.

Current status: the CIRCUIT-SAT → SAT reduction is in progress (`CircuitSAT`);
the semantic equivalence, the list encoding, and the reduction machine are in
place; the machine's `outputsFun` (assembling `PolyTimeReducible`) is pending.
-/

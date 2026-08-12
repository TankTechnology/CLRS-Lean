import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CircuitSAT
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CNFToClique

/-!
# 34.4 NP-Completeness Proofs

The specific polynomial-time reductions of CLRS §34.4: CIRCUIT-SAT poly-reduces
to SAT, SAT to 3-CNF-SAT, and 3-CNF-SAT to CLIQUE.  This facade imports the
reduction constructions.

Current status: CIRCUIT-SAT → SAT is complete (`circuitSAT_reducible_to_SAT`).
The 3-CNF-SAT → CLIQUE semantic core (`CNFToClique`:
`cnfSatisfiable_iff_hasClique`) is in place.  The SAT → 3-CNF-SAT semantic
layer (`SatTo3CNFSat`) and its machine (`SatTo3CNFMachine`) are in progress;
`outputsFun` (assembling `PolyTimeReducible`) is pending.
-/

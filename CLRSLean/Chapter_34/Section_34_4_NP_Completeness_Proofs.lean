import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CircuitSAT
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.SatTo3CNFMachine
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.SAT
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.ThreeCNF
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CNFToCliqueMachine
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin

/-!
# 34.4 NP-Completeness Proofs

The represented polynomial-time reductions around CLRS §34.4: CIRCUIT-SAT
poly-reduces to SAT, SAT to at-most-three-literal 3-CNF-SAT, and 3-CNF-SAT to
both the specialized occurrence language and the honest serialized general
CLIQUE language.  This facade imports the completed semantic constructions and
the machine constructions that have reached their own verification boundary.

Focused implementation status (2026-08-24): CIRCUIT-SAT → SAT is complete
(`circuitSAT_reducible_to_SAT`), and the 3-CNF-SAT occurrence-graph semantic
core (`cnfSatisfiable_iff_hasClique`) and machine reduction are in place.  The
SAT → 3-CNF-SAT semantic layer and concrete machine now assemble
`Turing.TM3CNF.sat_reducible_to_threeCNFSat`.  Focused source and public
interface checks and repository policy checks pass; a full-repository Lean
build is not part of this checkpoint.  General graph-plus-{lit}`k` CLIQUE now
has a unique raw grammar, well-formed graph semantics, exact Boolean
certificate semantics with a quadratic certificate bound, and an indexed
3-CNF occurrence reduction with exact raw-language correctness and a cubic
output-size bound.  Fixed polynomial-time TM2s compute both the reduction and
the exact raw certificate checker, yielding `GeneralCLIQUE ∈ NP`; the public
`CLIQUE` name denotes this honest language.  The bounded-builder core includes
its typed independent semantics, concrete compiler, one-step correctness, and
an exact bounded-run bridge to TM2 output witnesses.  Reusable scan/copy,
symbol-local bounded-loop, and row-major nested-loop macros are verified with
canonical exact independent and compiled runs.  The first Cook--Levin layer
extracts a finite program-support alphabet and proves preservation through
finite execution.  Its bounded-configuration layer is also complete: canonical
finite row codes round-trip through decoding, exact bounded halting is
equivalent to an exact-length stuttering run, and all tableau rows satisfy a
uniform height bound accounting for every push inside a bundled statement.
Fresh two-row transition circuitization is complete for independently allocated
consecutive layouts, including finite satisfying witnesses.  Exact concrete
initial/accepting constraints and the symbolic-input initial form are complete;
fixed-machine affine bounds for row validity, finite-label dispatch, and local
transition circuits are complete, as are well-formed finished-circuit wrappers.
Whole-tableau assembly now closes a well-formed circuit with exact language
semantics and polynomial gate/input/encoding bounds.  The function-level
Cook--Levin map and the exact finite-certificate semantics of
{lit}`GeneralCircuitSAT` are also complete.  The certificate checker now has a
concrete polynomial-time TM2 and yields `GeneralCircuitSAT ∈ NP`.  The explicit
map, its exact semantics, and its polynomial output bound are assembled into
{lit}`cookLevin_textbookCircuitization`.  A fixed polynomial-time TM2 computes
the map from the original input, and {lit}`cookLevin_theorem`,
{lit}`generalCircuitSAT_npHard`, and {lit}`generalCircuitSAT_npComplete` close
the standard Cook--Levin result.

The honest general-circuit language now also has the direct textbook bridge to
SAT.  `generalCircuitToFormula` is semantically exact on well-formed circuits;
the total raw map `generalCircuitToSATMap` preserves membership on every input
string and has an explicit cubic output-length bound.  A concrete fixed TM2
computes this total map in polynomial time, yielding
`generalCircuitSAT_reducible_to_SAT` and `SAT_npHard`.  Together with the
concrete SAT-to-3-CNF and 3-CNF-to-general-CLIQUE machines, this closes the
full hardness chain and proves `CLIQUE_npComplete` for the honest serialized
graph-plus-`k` language.  Standalone SAT and 3-CNF-SAT assignment formats now
have total exact Boolean checkers, malformed-certificate rejection, raw-decoder
index bounds, and linear certificate characterizations.  Their fixed checker
machines and direct NP-completeness wrappers remain an optional final
refinement.  Section 34.5 closes the selected textbook reductions and their
strict serialized layers through `VERTEXCOVER_npComplete`,
`HAMCYCLE_npComplete`, `TSP_npComplete`, and `SUBSETSUM_npComplete`.
-/

import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CircuitSAT
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.SatTo3CNFMachine
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CNFToCliqueMachine
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin

/-!
# 34.4 NP-Completeness Proofs

The represented polynomial-time reductions around CLRS §34.4: CIRCUIT-SAT
poly-reduces to SAT, SAT to at-most-three-literal 3-CNF-SAT, and 3-CNF-SAT to
the specialized occurrence-graph clique language.  This facade imports both
the semantic and machine constructions.

Focused implementation status (2026-08-13): CIRCUIT-SAT → SAT is complete
(`circuitSAT_reducible_to_SAT`), and the 3-CNF-SAT occurrence-graph semantic
core (`cnfSatisfiable_iff_hasClique`) and machine reduction are in place.  The
SAT → 3-CNF-SAT semantic layer and concrete machine now assemble
`Turing.TM3CNF.sat_reducible_to_threeCNFSat`.  Focused source and public
interface checks and repository policy checks pass; a full-repository Lean
build is not part of this checkpoint.  A genuine general graph-plus-`k` CLIQUE
encoding remains a separate gap.  The bounded-builder core now includes
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
string and has an explicit cubic output-length bound.  This closes the semantic
and representation-size layer.  A concrete TM2 implementation of that direct
map and a concrete SAT NP verifier remain explicit refinements; honest general
graph-plus-{lit}`k` CLIQUE and Section 34.5 remain the principal textbook-
coverage gaps.
-/

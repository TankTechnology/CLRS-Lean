import CLRSLean.Chapter_34

/-!
# Chapter 34 — NP-Completeness

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

The current Chapter 34 guide imports {lit}`CLRSLean.Chapter_34`, which supplies
Sections 34.1 (framework and closure properties), 34.2 (verification / `P ⊆ NP`),
34.3 (reducibility / transitivity of `≤_P`), and 34.4 (the specific reductions
`CIRCUIT-SAT ≤_P SAT`, `SAT ≤_P 3-CNF-SAT`, and `3-CNF-SAT ≤_P CLIQUE`).
The last reduction targets an honest serialized graph-plus-`k` language; the
older specialized occurrence-graph language remains available under an
explicit compatibility name.

The Cook--Levin tableau foundation also connects canonical one-hot bounded
stacks to machine-alphabet lists.  Its public contracts identify supported
push, peek, and pop with list cons, head, and tail exactly, and project every
successfully decoded complete row to its decoded machine stacks.
The corresponding circuit layer reuses a shared true/false wire pool, proves
zero-gate push and peek, exact one-gate positive-width pop and capacity costs,
and complete-row frame laws.
The generic lookup layer compiles finite one-hot maps, binary pair maps, and
Boolean predicates with exact gate costs and canonical one-hot semantics.
The structural {lit}`compileStmt` compiler covers all seven
{lit}`TM2.Stmt` constructors—halt, goto, load, push, peek, pop, and branch—and
evaluates complete rows exactly as {lit}`TM2.stepAux` under its explicit prefix
capacity premise.  Its proof-carrying result records the exact structural gate
delta, and a separate theorem gives a fixed-machine/statement affine emitted-
gate bound.  Machine-label dispatch and the local transition circuit complete
Cook--Levin milestone 8E: finite-label dispatch preserves whole-row stuttering
semantics, and {lit}`transitionCircuit_eval_iff` accepts exactly the machine's
stuttering step with a published exact gate delta.  Fresh local two-row
completeness (milestone 8F) is also proved: the offset-parametric constructor
allocates consecutive nonaliasing row layouts, preserves assignments outside
both row intervals, and its canonical wrapper produces the finite assignment
shape used by general-circuit satisfiability.
Exact tableau boundary constraints (milestone 8G) are now proved as complete-
row equalities.  Concrete initial and accepting targets are total and emit an
actual false output when too tall or outside finite support; the separate
symbolic-input-stack form fixes every other initial-row field for later
certificate-linked whole-tableau assembly.
Local polynomial-size accounting (milestone 8H) is now explicit rather than
implicit in exact cost recurrences: canonical row validity, finite-label
dispatch, and complete local transition circuits are bounded by coefficients
depending only on the fixed machine times displayed affine height/row-width
expressions.  The two principal predicate builders also close to well-formed
general circuits with unchanged evaluation.
The whole-tableau core now allocates all rows and conjoins canonical validity,
every stuttering transition, bounded certificate/input shape, and exact
initial/accepting boundaries.  The resulting general circuit is well formed,
is satisfiable exactly for members of the verified language, and has an
explicit fixed-verifier polynomial gate bound.  Its declared input count and
complete finite-string encoding length now have explicit polynomial bounds as
well.  The function-level `cookLevinMap` exposes this encoding with exact
membership semantics and a polynomial output-length theorem.
`GeneralCircuitSAT` independently has an executable Boolean-symbol certificate
checker whose accepted certificates of length at most the instance length
characterize membership exactly, together with a concrete polynomial-time TM2
and the resulting `GeneralCircuitSAT ∈ NP` theorem.  The explicit Cook--Levin
map and its semantic and size contracts are packaged for every NP language by
{lit}`cookLevin_textbookCircuitization`.  A fixed polynomial-time TM2 computes
that map from the original input; {lit}`cookLevin_theorem` and
{lit}`generalCircuitSAT_npComplete` close the standard Cook--Levin theorem.
The honest general-circuit language additionally has a direct consistency-
formula translation to SAT.  `generalCircuitToSATMap_mem_SAT_iff` proves exact
membership preservation on every raw input string, including malformed and
ill-formed inputs, and `generalCircuitToSATMap_length_le` gives a cubic output-
length bound.  A fixed polynomial-time TM2 computes this exact total map, so
`generalCircuitSAT_reducible_to_SAT` and `SAT_npHard` are now proved.
The public `CLIQUE` language now has a unique raw graph-plus-`k` encoding,
exact certificate semantics, a concrete polynomial-time verifier TM2, and the
resulting `GeneralCLIQUE ∈ NP` theorem.  A second concrete polynomial-time TM2
computes the 3-CNF-SAT reduction and proves exact membership preservation on
all raw inputs.  The transported hardness chain now closes
`CLIQUE_npComplete` for this honest language.

## Coverage boundary

Status: partial.  The theorem layer is complete — polytime composition,
`P ⊆ NP`, transitivity of `≤_P`, and the closure of `P` under complement,
union, and intersection — and the §34.4 reductions `CIRCUIT-SAT ≤_P SAT`
(Lemma 34.6), `SAT ≤_P 3-CNF-SAT` (Lemma 34.7), and
`3-CNF-SAT ≤_P CLIQUE` (Lemma 34.10) are proved with concrete machines.  The
public `CLIQUE` target is the honest serialized general graph-plus-`k`
language, not the specialized occurrence language.  Within
Cook--Levin circuitization, the whole-tableau semantic circuit and its
polynomial gate bound are complete; the mathematical reduction map and
finite-certificate semantics are also complete.  The concrete polynomial-time
generator closes the universal reduction, NP-hardness, and
{lit}`NPComplete GeneralCircuitSAT`.  General CLIQUE has exact certificate
semantics, a concrete polynomial-time verifier, membership in NP, and the
concrete 3-CNF-SAT reduction.  The direct general-circuit-to-SAT bridge has a
fixed polynomial-time TM2, and the universal NP-hardness chain reaches SAT,
3-CNF-SAT, and public CLIQUE; general CLIQUE is proved NP-complete.  A
standalone SAT NP verifier remains an optional direct refinement.  Section
34.5 is now partially represented by the typed CLIQUE-to-VERTEX-COVER
complement theorem, its typed reverse, the raw VERTEX-COVER language, and exact
total raw-string semantic maps in both directions.  Both maps have explicit
cubic output-length bounds.  Its Boolean certificate checker is semantically
exact and has a quadratic accepted-certificate bound.  Its first concrete
machine phase is also closed: a fixed linear-time TM2 normalizes raw graph
syntax while preserving parser rejection through an ill-formed sentinel.  The
remaining complement/verifier machines, NP membership/completeness closure,
and the HAM-CYCLE, TSP, and SUBSET-SUM chains remain open; this guide therefore
remains partial.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/

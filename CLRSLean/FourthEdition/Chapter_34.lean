import CLRSLean.Chapter_34

/-!
# Chapter 34 — NP-Completeness

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

The current Chapter 34 guide imports {lit}`CLRSLean.Chapter_34`, which supplies
Sections 34.1 (framework and closure properties), 34.2 (verification / `P ⊆ NP`),
34.3 (reducibility / transitivity of `≤_P`), and 34.4 (the specific reductions
`CIRCUIT-SAT ≤_P SAT`, `SAT ≤_P 3-CNF-SAT`, and
`3-CNF-SAT ≤_P` the specialized occurrence-CLIQUE target).  A general
graph-plus-`k` CLIQUE language is not yet represented.

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
characterize membership exactly.

## Coverage boundary

Status: partial.  The theorem layer is complete — polytime composition,
`P ⊆ NP`, transitivity of `≤_P`, and the closure of `P` under complement,
union, and intersection — and the §34.4 reductions `CIRCUIT-SAT ≤_P SAT`
(Lemma 34.6), `SAT ≤_P 3-CNF-SAT` (Lemma 34.7), and
`3-CNF-SAT ≤_P` the specialized occurrence-CLIQUE target (the represented
semantic core of Lemma 34.10) are proved.  General graph-plus-`k` CLIQUE and
Section 34.5 (NP-complete problems) are not yet represented.  Within
Cook--Levin circuitization, the whole-tableau semantic circuit and its
polynomial gate bound are complete; the mathematical reduction map and
finite-certificate semantics are also complete.  Concrete polynomial-time
TM2 implementations of the circuit generator and certificate checker, and
the final `GeneralCircuitSAT` NP-completeness wrappers, remain downstream.
This guide remains partial and does not claim those later layers.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/

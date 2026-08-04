# Common Proof Infrastructure Consolidation Design

## Goal

Consolidate proof techniques that already recur across CLRS-Lean into small,
stable public APIs without turning the repository into one large generic
framework.  The pass should remove genuine duplicate proof bodies, give the
existing proof-pattern modules real consumers, and document where reusable
infrastructure canonically lives.

The consolidation must preserve all existing public theorem statements and
chapter completion claims.  It must not increase progress counts merely because
a shared helper, compatibility wrapper, alias, or representation bridge becomes
public.

## Current Evidence

The repository already has three different kinds of reusable infrastructure:

1. `CLRSLean/ProofPatterns/` contains lightweight geometric abstractions for
   boundary induction, exchange certificates, key fibers, and natural-number
   intervals.  These modules are imported by the library root, but no chapter
   currently imports or consumes them.
2. Chapter-owned infrastructure is already reused successfully across chapters.
   Chapter 27 imports Chapter 4's all-input recurrence transfer layer, while
   Chapters 19 and 21 import Chapter 17's potential-method framework.
3. `CLRSLean/Probability/FiniteExpectation.lean` is a genuine domain library,
   but `fintypeExpect_mono` is still independently proved in Chapters 5 and 11,
   and `fintypeExpect_neg` remains local to Chapter 11.

Chapter 27 also contains two private generic helpers: one converts monotonicity
of a natural-valued cost into Chapter 4's real-valued `MonotoneAbs` interface,
and one maps the adjacent-power interval through a monotone cost.  Both belong
with Chapter 4's existing all-input transfer API rather than in a Chapter 27
implementation file.

## Design Principles

- Extract only demonstrated proof reuse, not merely similar-looking code.
- Keep shared theorems in the narrowest mathematically natural module.
- Preserve existing public names through wrappers or aliases when moving a
  proof's canonical implementation.
- Prefer exact representation bridges over rewrites of stable chapter proofs.
- Keep chapter-specific semantics in their chapters; shared modules own only
  generic algebra or proof geometry.
- Treat Chapter 4 and Chapter 17 as valid common libraries even though their
  modules are chapter-owned.  Moving a stable API is unnecessary when its
  dependency direction is already correct.

## Consolidation Scope

### 1. Finite expectation algebra

Add the canonical theorems to `CLRS.Probability`:

- `fintypeExpect_mono`: pointwise order implies expectation order, with no
  unnecessary nonnegativity hypotheses;
- `fintypeExpect_neg`: expectation commutes with negation.

Chapter 5 keeps its existing `CLRS.Chapter05.fintypeExpect_mono` statement,
including its currently redundant nonnegativity hypotheses, as a compatibility
wrapper around the canonical theorem.  Its existing root-level alias remains
valid.  Chapter 11 likewise keeps the existing `CLRS.Chapter11` theorem names
and statements as wrappers.  Internal proof sites may call the canonical
theorems directly when that makes ownership clearer.

This change removes duplicate proof bodies without breaking downstream code or
silently strengthening or weakening a chapter-facing declaration.

### 2. All-input recurrence transfer helpers

Promote the two generic Chapter 27 helpers into
`Section_04_6_Master_Theorem_All_Input.lean` under stable Chapter 4 names:

- a theorem converting `Monotone T` for `T : Nat -> Nat` into `MonotoneAbs` for
  `fun n => (T n : Real)`;
- a theorem mapping `powerInterval_of_pos` through a monotone natural-valued
  function to obtain an adjacent-power sandwich.

Chapter 27 removes its private copies and uses these public Chapter 4 results
for all six work/span recurrences.  The six Chapter 27 statements remain public
because they are reader-facing facts about distinct textbook cost functions;
the common transfer proof is nevertheless owned and recorded only once.

No Master-theorem definitions or chapter-specific recurrences move into
`ProofPatterns`.

### 3. Fiber adoption in Chapter 8

Chapter 8 counting sort imports `CLRSLean.ProofPatterns.Fiber` and adds an exact
bridge between its established natural-key `bucket` definition and the generic
`ProofPatterns.fiber` definition.  Core local facts such as append, membership,
constant-key membership, and repeated filtering should delegate to the generic
fiber lemmas where their statements match exactly.

The Chapter 8 `bucket` definition and every existing public bucket theorem name
remain unchanged.  Algorithms and later counting/radix/bucket-sort files
continue to use the chapter-facing vocabulary.

### 4. Interval adoption in Chapter 22

The DFS interval module imports `CLRSLean.ProofPatterns.Interval` and defines a
small projection from a DFS state and vertex to `ProofPatterns.NatInterval`.
Exact equivalence theorems connect:

- `finishesBeforeDiscovered` with `NatInterval.StrictlyBefore`;
- `intervalNestedInside s u v` with vertex `v`'s interval being
  `NatInterval.NestedInside` vertex `u`'s interval.

Only small interval-algebra facts that become strictly clearer should be
rewritten through this bridge.  The DFS parenthesis theorem, ancestor proof,
edge-classification stack, and their public vocabulary remain chapter-owned.

### 5. Patterns deliberately not forced into use

`BoundaryTrace` remains a pedagogical skeleton for now.  Existing loop proofs
carry algorithm-specific state and induction hypotheses, and replacing their
inductions would not yet remove meaningful proof friction.

`ExchangeCertificate` also remains unchanged.  Activity selection uses an
existential, subproblem-specific exchange witness, while the generic structure
stores a total exchange function.  Huffman and MST certificates have still
different local data.  A forced adapter would add classical choice or awkward
packaging without simplifying the chapter proofs.

Chapter 17's potential framework stays in Chapter 17 because it already has
multiple real consumers and a stable public API.

## Theorem-Group Counting Policy

Progress records textbook-facing proof obligations, not the raw number of
public Lean declarations.

- A canonical shared theorem is recorded once at its source.
- Compatibility wrappers, aliases, namespace forwards, and exact
  representation bridges add no progress count.
- Repeated instantiations of one common proof principle do not create new
  infrastructure counts.
- A chapter-specific instance counts only when it expresses a distinct
  textbook obligation.  Several structurally identical instances may be one
  theorem group.
- `docs/proof-map.md` may list every discoverable public theorem name while
  `docs/clrs-proof-progress.csv` records only textbook theorem groups.

This pass documents and follows the policy but does not retroactively recount
all 1676 currently tracked entries.  Historical normalization is a separate
repository-wide audit so that count migration cannot obscure proof-library
changes.

## Public Interface And Tests

Add a focused common-infrastructure interface test that imports the canonical
modules and checks the new shared names and representation bridges.  Existing
chapter interface tests continue to check compatibility names.

The implementation follows a red-green interface loop:

1. add the intended `#check` declarations and confirm the focused test fails
   because the new names are absent;
2. implement the canonical shared theorems and compatibility wrappers;
3. build each changed source module and rerun its immediate chapter interface;
4. run the common-infrastructure interface test and affected Chapter 4, 5, 8,
   11, 22, and 27 interfaces;
5. verify the library root and repository metadata.

The headline shared theorems receive a `#print axioms` audit.  They may depend
only on the standard Lean/Mathlib logical axioms already accepted by the
repository, never `sorryAx` or a project axiom.

## Documentation

Add a common-library decision matrix under `docs/proof-patterns/` with columns
for canonical owner, existing consumers, compatibility surface, progress-count
treatment, and the condition for further extraction.  Update the proof-pattern
atlas and repository architecture so they distinguish:

- canonical domain libraries (`Probability`, Chapter 4 recurrence transfer,
  Chapter 17 amortized analysis);
- geometric proof-pattern modules with demonstrated consumers (`Fiber`,
  `Interval`);
- pedagogical or deferred abstractions (`Boundary`, `Exchange`, local surgery,
  and dynamic-programming grids).

No chapter status, progress CSV number, or completion claim changes in this
pass.

## Verification Boundary

Required verification is:

- focused Lean builds for every changed module;
- affected chapter and common-infrastructure interface tests;
- placeholder scan over changed Lean modules;
- `#print axioms` for the new canonical theorem families;
- `git diff --check`;
- `uv run python scripts/check_repository.py`;
- a final `lake build CLRSLean` or the repository's equivalent fresh root
  aggregate check.

The website/HTML target is not part of this proof-infrastructure pass.  Static
source and navigation consistency remain covered by the repository checker.

## Acceptance Criteria

The consolidation is complete when:

1. the finite-expectation order and negation proofs have one canonical
   implementation while all old public names still compile;
2. Chapter 27 consumes public Chapter 4 transfer helpers instead of private
   generic copies;
3. Chapter 8 and Chapter 22 each consume an existing proof-pattern module
   through an exact, public bridge;
4. no existing public declaration is removed or weakened;
5. no progress count or completion status is inflated by infrastructure;
6. all focused and root Lean checks pass without placeholders or nonstandard
   axioms; and
7. the documentation decision matrix accurately explains what was promoted,
   bridged, retained, and deferred.

## Delivery Shape

Keep the work reviewable as small commits:

1. design specification;
2. red interface checks;
3. finite-expectation consolidation;
4. Chapter 4/27 recurrence-transfer consolidation;
5. Chapter 8/22 proof-pattern adoption;
6. documentation and verification cleanup.

Each code commit must compile at its focused boundary.  The branch is merged
only after the combined root verification succeeds.

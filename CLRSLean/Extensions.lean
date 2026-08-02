/-!
# Extensions beyond the textbook

This area collects results that go **one notch beyond CLRS** without leaving
its orbit: classic structures the book only sketches or leaves to exercises and
problems, natural variants of the verified data structures in the main
chapters, and refinements that exercise the reusable toolkits
({lit}`ProofPatterns`, the finite-probability layer) on new objects.

Extensions are deliberately kept **out of the textbook-coverage ledger**: the
progress CSV counts what the book claims, and this area is where the project
goes further.  A module is only registered in {lit}`literate.toml` (and
therefore rendered in the site sidebar) once it is kernel-clean; prototypes
stay unregistered while their theorem interfaces settle.

Planned extensions:

- **Randomized treap**: an executable randomized binary search tree with
  membership correctness and an expected {lit}`O(log n)` height bound,
  exercising the finite-expectation layer on a new object.
- **Splay tree**: amortized analysis via the potential method of Chapter 17.
- **Persistent dynamic sets**: CLRS Problem 13-1, versioned red-black trees
  with path copying.
- **Edit distance**: sequence alignment as a refinement of the Chapter 15
  longest-common-subsequence dynamic program.

Status: no extension promoted yet; the first prototype (the randomized treap)
lives in {lit}`CLRSLean/Extensions/RandomizedTreap.lean`.
-/

# Local proof progress integration audit — 2026-08-14

This audit compares the surviving local branches, worktrees, and stash against
`main` at `b8977d1`.  It records semantic proof coverage rather than relying on
commit ancestry alone: much of the repository has been squash-merged or moved
into the native fourth-edition source layout.

## Absorbed in this integration

- `codex/ch15-fifo-trace-coupling`, commit `6942b07`: absorbed the exact
  `GeneralCircuitVerifier` checkpoint.  The concrete TM2 computes
  `generalCircuitVerifier` on every input, including malformed and rejecting
  inputs.  The successful canonical route has a quadratic bound.  The stale
  status prose from that branch was not copied.
- `codex/ch`, commit `b652ea6`: absorbed only the reusable
  `ProofPatterns.Optimal` structure and `optimal_of_exchange` kernel.  The old
  Chapter 16 and Chapter 23 source rewrites were not copied because the native
  fourth-edition modules now own those algorithms.
- `codex/ch13-well-formedness`, commit `a7c46cc`: re-expressed the useful idea as
  a small native `RBTree.WellFormed := RedBlackShape ∧ BST` bundle, with
  insertion/deletion correctness wrappers.  The old ordering file was not
  copied because its declarations collide with stronger theorems already on
  `main`.

## Already present or superseded on `main`

- `codex/ch19-extract-min-pr`: all 141 audited declarations are already present
  on `main`; Chapter 19 later landed through the native migration and follow-up
  fixes.
- `codex/ch30fight`: all 263 audited declarations are already present on
  `main`; the Fourier/FFT work has been integrated through the current Chapter
  30 source.
- `codex/ch25-faster-apsp-correctness`: its older six theorem names are absent,
  but their substance is superseded by the current `D_le_simpleWalk` and
  Floyd–Warshall correctness chain.
- `paper-map-recovered`: its old `insert_keys_perm` result is weaker than the
  current top-level B-tree insertion and exact deletion interfaces.
- `worktree-clean-pre15`: its older Chapter 4/5/6/8 cost declarations have been
  replaced by execution-attached cost layers on `main`.
- `codex/clrs4-*`: the useful source-ownership migration landed in `587a05a`
  (the Chapter 15–32 native migration).  The compatibility/export-generator
  experiments are therefore historical scaffolding, not pending proof content.
- The old Chapter 3, Chapter 11, Chapter 15, stable-marriage, Chapter 27,
  Chapter 28, Chapter 29, and Chapter 34 foundation integration worktrees are
  ancestors of, or semantically represented by, current `main`.

## Preserved but not merged

- `paper-map-recovered` has an uncommitted change to
  `Section_18_1_B_Tree_Model.lean`.  It changes the old occupancy model and is
  incompatible with the stronger current Chapter 18 deletion layer.
- `codex/clrs4-native-migration` has an uncommitted Chapter 21 edit and an
  untracked Chapter 19 compatibility test.  These user-owned changes were left
  untouched.
- `stash@{0}` is a partial `composedDelete` checkpoint based on the old Chapter
  18 tree.  Current `main` has the stronger exact B-tree deletion result, so the
  stash was neither applied nor deleted.
- Chapter 19 draft/archive branches were not merged wholesale; their proved
  declarations have already landed, while remaining branch-only artifacts are
  historical layout or work-in-progress material.

No historical worktree, branch, or stash was removed by this audit.

## Known failed or rejected integration routes

1. **Treating `git cherry` or branch-ahead counts as proof coverage.**  Squash
   merges, rebases, file moves, and theorem renames produce many false
   positives.  Compare declarations and theorem strength instead.
2. **Cherry-picking whole pre-migration branches.**  This reintroduces legacy
   files and conflicting ownership after the fourth-edition migration.  Port
   the smallest compatible theorem surface against current native interfaces.
3. **Preferring dirty or stashed drafts over later `main`.**  A draft's unique
   text is not evidence of stronger progress; first compare its semantic
   contract with current headline theorems.
4. **Inferring all-input polynomial time from a successful verifier run.**
   `successfulSteps_le` bounds the canonical valid route only.  Rejecting and
   malformed routes still need a uniform bound before constructing
   `TM2ComputableInPolyTime`.
5. **Using `native_decide` examples as a complexity proof.**  They are useful
   executable regressions, but do not prove a symbolic polynomial step bound.
6. **Calling the specialized occurrence graph general CLIQUE.**  The current
   3-CNF reduction targets occurrence-CLIQUE; a general encoded graph-plus-`k`
   language remains separate work.

## Honest boundary after integration

- Chapter 13 functional correctness is bundled at the shape-plus-BST level.
  Pointer-loop refinement and low-level RAM accounting remain optional deeper
  implementation work.
- Chapter 34's general-circuit checker has total exact TM2 semantics and a
  successful-route quadratic bound.  It does **not** yet establish
  `GeneralCircuitSAT ∈ NP`; the uniform rejecting-route runtime theorem and the
  final complexity-class wrapper remain open.

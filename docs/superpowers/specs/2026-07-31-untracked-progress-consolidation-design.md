# Untracked Progress Consolidation Design

**Status:** Approved for implementation on 2026-07-31.

## Goal

Turn the seven current untracked files into a small, accurate, maintainable
set of repository artifacts. Preserve historical proof-engineering knowledge,
but do not commit obsolete Lean probes, stale completion claims, or unsupported
paper claims.

This pass changes documentation only. It does not change Chapter 18 Lean
definitions, theorem statements, progress counts, or completion status.

## Approaches Considered

### A. Curated integration — selected

Delete superseded scratch files and the unsupported paper draft. Revise the
three Chapter 18 design/research artifacts into honest historical records.
Split the mixed stuck-point document into a dated retrospective and a
current proof-engineering catalog.

This keeps the reusable knowledge while preventing stale claims from entering
`main`.

### B. Archive everything verbatim

Track all seven files with a general historical disclaimer. This preserves the
largest amount of text, but leaves failed Lean files, obsolete theorem counts,
and unsupported research claims searchable as if they were current.

### C. Keep only Chapter 18 materials

Delete both scratch files and both general documents, then retain only the
Chapter 18 design, plan, and AFP comparison. This is clean but discards a
useful cross-chapter proof-engineering retrospective.

## File Disposition

### Remove as superseded local artifacts

- `Scratch_check.lean`: a Mathlib API probe that now fails on the removed
  `List.length_eq_one` name.
- `Scratch_proto.lean`: an early `maxKey`/`minKey` prototype whose useful
  definitions and lemmas were absorbed and strengthened in the formal Chapter
  18 deletion source.
- `docs/research/paper-skeleton-2026-07-27.md`: a research draft whose theorem
  counts, represented-chapter counts, partial-chapter list, CI claims,
  proof-pattern reuse claims, and evaluation readiness have materially drifted.
  A future paper effort should begin from an explicit research contract and
  reproducible evidence rather than patching this draft.

Because these files are untracked, removing them cleans the local workspace;
it does not create Git deletion entries.

### Revise and track as Chapter 18 history

1. `docs/superpowers/specs/2026-07-27-ch18-btree-delete-guard-design.md`
   - Mark the design completed.
   - Convert the original `sorry` and missing-wrapper statements to historical
     context.
   - Record the actual use of generated `composedDelete.induct` instead of the
     proposed strong-recursion proof.
   - Point the later exact deletion semantics to the existing tracked plan and
     the current Chapter 18 page.
   - Keep the five counterexamples and the `NodeWF` / `DeleteReady` /
     `RootDeleteResult` design because they remain accurate.

2. `docs/superpowers/plans/2026-07-30-ch18-btree-delete-proof-completion.md`
   - Add a completed outcome section and the implementation commit.
   - Treat unchecked task boxes as the historical execution plan, not current
     work.
   - Correct the progress CSV path.
   - Record the actual capstone module and induction strategy.
   - Replace the full-site HTML step with the agreed single-chapter gate.

3. `docs/research/afp-btree-deletion-architecture-2026-07-27.md`
   - Preserve the AFP source links and architectural comparison.
   - Mark all former blockers and line-number references as a dated snapshot.
   - Describe AFP's global sorted-inorder invariant as corresponding to the
     combined ordering responsibility of local `Sorted` and `ChildBounded`;
     do not claim AFP omits the ordering obligation.
   - Replace claims of equivalence or complete isomorphism with narrower
     structural comparisons.
   - Add an outcome table mapping the 2026-07-27 recommendations to the final
     Chapter 18 implementation, including merge/rotation repair, bundled
     preservation, generated induction, exact key-bag semantics, and height
     closure.

### Split and track the cross-chapter retrospective

Replace
`docs/proof-patterns/stuck-points-and-reusable-structures.md` with:

- `docs/proof-patterns/stuck-points-retrospective-2026-07-24.md`, containing
  the dated commit-history case studies and later outcome notes; and
- `docs/proof-patterns/proof-engineering-patterns.md`, containing only current
  reusable patterns that are not already covered by
  `geometric-proof-patterns.md` or `clrs-lean-playbook.md`.

The revision must:

- update Chapter 18 from an open blocker to a completed structural, semantic,
  and height proof stack;
- remove Chapter 7 from the list of unresolved mathematical gaps;
- describe `RedBlackShape` accurately and keep the BST invariant separate;
- replace stale source line numbers with theorem or module names;
- repair broken design/plan paths; and
- soften causal claims about workflow changes into evidence-backed
  observations.

## Verification

Before the consolidation commit:

1. Confirm only the five revised/split documentation artifacts and this design
   are tracked; the two Scratch files and paper draft must be absent.
2. Run repository Markdown/link and documentation consistency checks through
   `python3 scripts/check_repository.py`.
3. Run `python3 scripts/check_progress_csv.py` to ensure no progress ledger was
   accidentally changed.
4. Run `git diff --check`.
5. Search the new documents for stale Chapter 18 claims such as remaining
   `sorry`, `111/111`, `partial`, or unfinished exact deletion semantics.
6. Inspect the final diff and commit the documentation separately from any
   future paper work.

Full-site HTML generation is outside this documentation-only, single-chapter
consolidation gate.

## Success Criteria

- The working tree no longer contains obsolete untracked Scratch or paper
  files.
- Every tracked historical claim is explicitly dated or reconciled with the
  current `134/134` Chapter 18 state.
- The repository gains reusable proof-engineering knowledge without adding
  unsupported research claims.
- Existing Lean source, tests, progress ledgers, and generated status pages are
  unchanged.

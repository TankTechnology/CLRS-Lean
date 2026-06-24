# CLRS Chapter Formalization Skill Iteration Log

This log records concrete updates to
`.codex/skills/clrs-chapter-formalization/SKILL.md` after using it on CLRSLean
chapters.

## 2026-06-24 - Initial Skill

- Added the chapter loop: triage, Lean-friendly model choice, theorem interface,
  implementation, site wiring, verification, and post-chapter refinement.
- Added early chapter patterns for functional data structures, lookup tables,
  search trees, and balanced trees.
- Added honesty rules to prevent non-compiler-clean exploration files from being
  presented as finished proofs.

## 2026-06-24 - After Chapter 10

- Added a linked-list pattern: when no imperative memory semantics exists, prove
  search soundness, front-insert membership, and delete-all membership
  characterizations over `List`.
- Confirmed that Chapter 10 can be `proved` only for the functional model;
  pointer updates, free lists, and allocation remain outside the proved status.

## 2026-06-24 - After Chapter 11

- Added a hash-table performance pattern: prove deterministic table-update and
  bucket-search correctness first; keep simple-uniform-hashing expected-time
  theorems separate until a probability model is selected.
- Confirmed that direct addressing is small enough to mark `proved` for the
  functional table model, while chained hashing is currently `partial` because
  the average-case analysis is not formalized.

## 2026-06-24 - After Chapter 12

- Strengthened the tree-chapter pattern: first prove
  `membership after insert ↔ inserted key or old membership`, then use that
  equivalence for upper/lower-bound preservation and the ordered invariant.
- Cleaned unused `simp` arguments after the first successful build; this keeps
  new theorem files quieter without expanding proof scope.

## 2026-06-24 - After Chapter 13

- Strengthened the balanced-tree pattern: prove rotation membership preservation
  and root-recoloring local invariant lemmas before attempting executable
  red-black insertion or deletion.
- Added a warning from practice: doc comments should use `{lit}` for future
  theorem names or textbook pseudocode names; `{name}` should be reserved for
  names that already exist at that point in the file.

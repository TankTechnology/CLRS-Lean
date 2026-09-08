# Chapter audit repair implementation plan

**Goal:** Publish every actionable September 8 chapter finding as a GitHub issue, then repair chapters in fourth-edition order with verified semantic endpoints.

**Architecture:** Keep the dated audit immutable. Maintain issue links and repair evidence in this directory. Preserve existing public algorithms and compatibility names where possible; add actual execution/semantic bridges rather than merely changing completion labels. Each chapter issue owns independent acceptance items; disclosed optional model boundaries receive precise documentation instead of being silently treated as core bugs.

**Tech stack:** Lean 4, Mathlib, Lake, existing Python repository checks, GitHub CLI.

The user approved issue submission and starting repairs on September 8. This executes the remedies already presented in the audit; no additional design approval is needed. Existing website/document changes in the shared checkout are preserved. Work is local until reviewed/pushed; local success alone does not close a remote issue.

## Issue publication

- [x] Create one issue for each chapter with an actionable finding, with severity, source evidence, reviewed scope, and acceptance checklist. All 54 non-MATCH section classifications must be covered; chapter-wide minor notes in otherwise MATCH chapters must also be included.
- [x] Create an umbrella issue with chapter links and global status/publication reconciliation requirements. Preserve completed historical repairs and distinguish new residual findings.
- [x] Read back every issue, verify the body/number/URL, and record the mapping in `issues.csv` and `index.md` here.

## First repair batch: Chapters 1–3

### Chapter 1 reader contract

Modify `src/CLRSLean/FourthEdition/Chapter_01.lean`: point Huffman to Chapter 15 and MST to Chapter 21; describe explicit `Option` failure and hypothesis-constrained totalization accurately. This is a documentation edit; no mirror test is needed. Compile the chapter and run repository reader/metadata checks.

### Chapter 2 actual worst-case comparison interface

Modify `src/CLRSLean/FourthEdition/Chapter_02/Section_02_2_Analyzing_Algorithms.lean`; the existing value/counter definitions remain unchanged.

- [x] Add `tests/Chapter_02_WorstCase_Interface.lean` with missing-name checks and quantified uses of the new interfaces; verify expected failure before implementation.
- [x] Prove `insertSortedComparisons x xs ≤ xs.length` by induction, then `insertionSortComparisons xs ≤ insertionSortWorstComparisons xs.length` using sort permutation/length preservation and the triangular recurrence.
- [x] Define the descending family by `worstInput 0 = []`, `worstInput (n+1) = n :: worstInput n`. Prove length and strict upper bound on members; inserting n into its sorted tail visits every element. Prove this family attains the triangular comparison bound for every n, including 0 and 1.
- [x] Export `IsGreatest` of the set of actual length-n comparison counts and combine it with the existing Θ theorem. Interface checks must use the universal/witness properties, not only numeric toy examples.
- [x] Add flagship axiom checks; update Chapter 2 guide and clarify symbolic t_i line-count inputs. Update canonical evidence notes without treating added helper lemmas as new tracked inventory entries.
- [x] Build changed chapter modules and compatibility import, run focused interface tests and Chapter 2 trust surface, then run full library build and repository checks once after the batch. Record real output and existing warnings.

### Chapter 3 numbering

- [x] Update standard-functions references from legacy §3.2 to canonical §3.3 in `Section_03_2_Standard_Functions/Core.lean` and `TextbookIdentities.lean`, and correct cross-references in `Section_03_1_Asymptotic_Notation/Core.lean`. Keep compatibility filenames and imports unchanged. Chapter build, identity interface and trust file passed.

## Subsequent chapter queue

Continue in chapter order using each issue's checklist. Chapter 3 numbering corrections are in the first batch. Chapter 4 requires actual cost/recurrence proof work; do not mark it fixed after merely explaining a missing proof. Later issues include the verified Ch13/17 data-structure defects and critical Ch27 uninhabited interface. The initial batch does not imply those findings are resolved.

For each mathematical repair: state the intended public contract first, confirm the missing theorem/behavior, prove necessary invariants, attach counters to the actual execution where relevant, verify the changed chapter, and update the repair record. Preserve the original audit snapshot and link new evidence instead of rewriting historical verdicts.

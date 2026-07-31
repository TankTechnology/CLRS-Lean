# Untracked Progress Consolidation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Convert the seven audited untracked files into five accurate,
maintainable documentation artifacts, while removing obsolete Scratch probes
and the unsupported paper draft without changing Lean code or Chapter 18
status.

**Architecture:** Treat the three Chapter 18 documents as dated design and
implementation records, and split the mixed cross-chapter note into a dated
retrospective plus a current proof-pattern catalog. Keep historical claims only
when their date and later outcome are explicit. Make one focused commit per
document family, then verify repository consistency and integrate only after
the exact obsolete paths have been checked.

**Tech Stack:** Markdown, Git, repository Python consistency checks, `rg`, and
the existing Chapter 18 Lean sources as the factual reference.

---

## Preconditions and fixed scope

The approved design is
`docs/superpowers/specs/2026-07-31-untracked-progress-consolidation-design.md`.
The implementation worktree is expected to be based on the local `main` commit
that contains that design.

The four source documents copied into the implementation worktree are:

- `docs/proof-patterns/stuck-points-and-reusable-structures.md`
- `docs/research/afp-btree-deletion-architecture-2026-07-27.md`
- `docs/superpowers/plans/2026-07-30-ch18-btree-delete-proof-completion.md`
- `docs/superpowers/specs/2026-07-27-ch18-btree-delete-guard-design.md`

The following three source files are intentionally not copied because the
approved disposition is deletion:

- `Scratch_check.lean`
- `Scratch_proto.lean`
- `docs/research/paper-skeleton-2026-07-27.md`

This plan must not edit:

- `CLRSLean/**`
- `Tests/**`
- `docs/clrs-proof-progress.csv`
- `README.md`
- `literate.toml`

Full-site HTML generation is out of scope. The documentation and consistency
checks below are the complete gate for this pass.

## Task 1: Reconcile the Chapter 18 guard design with the final implementation

**Files:**

- Modify:
  `docs/superpowers/specs/2026-07-27-ch18-btree-delete-guard-design.md`
- Reference:
  `CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/ComposedPreservation.lean`
- Reference:
  `docs/superpowers/plans/2026-07-30-ch18-exact-deletion-semantics.md`
- Reference: `docs/chapters/chapter-18.md`

- [ ] **Step 1: Record the document's status and time boundary**

Add a status block immediately below the title with this meaning:

```markdown
> **状态：已完成。** 本文记录 2026-07-27 至 2026-07-30 的结构保持
> 设计。结构保持与删除高度闭环由提交 `f3f61b4` 完成；精确删除语义
> 随后完成，2026-07-31 又完成全章最小键数与对数高度界，当前进度为
> `134/134`。
```

Rename present-tense headings such as `目标` to explicitly historical wording
such as `设计目标（历史）`. Any mention of `19` remaining `sorry`s, missing
wrappers, or unproved exact semantics must say that it described the design
starting point rather than the current repository.

- [ ] **Step 2: Preserve the five counterexamples and corrected contract**

Keep the five counterexamples and the definitions/concepts
`NodeWF`, `DeleteReady`, `RootDeleteResult`, and root contraction. Do not
weaken or summarize away the false-contract evidence: it is the main reason
this design remains useful.

Check all descriptions against the current module names instead of relying on
old source line numbers.

- [ ] **Step 3: Add an implementation outcome section**

Add a section named `实施结果与设计偏差` containing a compact table with at
least these rows:

| 设计问题 | 最终实现 |
| --- | --- |
| 主递归归纳 | 使用 Lean 为函数生成的 `composedDelete.induct`，而非设计稿提出的 `Nat.strongRecOn` |
| bundled core | `ComposedPreservation.lean` 中的 `composedDelete_packet` 一次性给出结构保持组件 |
| root normalization | `RootDeleteResult` 与公共根删除接口处理 raw root contraction |
| `splitChild` API | 设计时缺失的独立 wrappers 已恢复并由接口测试固定 |
| 精确语义 | 后续以 `keyBag` / `Multiset.erase` 完成，不属于当时结构里程碑，但已不再是剩余项 |
| 删除高度 | `f3f61b4` 同时完成同深保持与根删除高度不变或减一 |
| 全章高度界 | 2026-07-31 后续里程碑完成最小键数与对数高度界 |

Link exact semantics to
`../plans/2026-07-30-ch18-exact-deletion-semantics.md` and current status to
`../../chapters/chapter-18.md`.

- [ ] **Step 4: Replace the obsolete acceptance gate**

Keep the useful Chapter 18 build and interface checks, but remove full-site
HTML generation from this document's current acceptance requirements. Make
clear that any HTML command shown is historical context rather than a
single-chapter gate.

- [ ] **Step 5: Check the focused diff and commit**

Run:

```bash
git add \
  docs/superpowers/specs/2026-07-27-ch18-btree-delete-guard-design.md
git diff --cached --check -- \
  docs/superpowers/specs/2026-07-27-ch18-btree-delete-guard-design.md
rg -n '状态|134/134|f3f61b4|composedDelete\.induct|精确删除' \
  docs/superpowers/specs/2026-07-27-ch18-btree-delete-guard-design.md
git diff --cached -- \
  docs/superpowers/specs/2026-07-27-ch18-btree-delete-guard-design.md
```

Expected: the status and outcome are explicit; any old count appears only as a
dated starting point; no current full-site gate remains.

Commit only this file:

```bash
git commit -m "docs(ch18): archive deletion guard design"
```

## Task 2: Turn the Chapter 18 proof-completion plan into an outcome record

**Files:**

- Modify:
  `docs/superpowers/plans/2026-07-30-ch18-btree-delete-proof-completion.md`
- Reference:
  `CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/ComposedPreservation.lean`
- Reference:
  `CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/Preservation.lean`
- Reference: `docs/clrs-proof-progress.csv`

- [ ] **Step 1: Add a completed outcome block**

Below the existing plan header, add:

```markdown
## Outcome

**Status:** Completed by `f3f61b4` for the structural deletion milestone.
The task boxes below preserve the original execution plan; they are not
current repository TODOs. That commit also completed same-depth preservation
and root deletion height behavior. Exact deletion semantics was completed in a
subsequent milestone; the 2026-07-31 minimum-key and logarithmic-height work
then brought Chapter 18 to `134/134`.
```

Do not mechanically check every old box. The document is a historical plan,
and the outcome block is the authoritative current status.

- [ ] **Step 2: Correct paths and actual proof architecture**

Make these factual corrections:

- replace `docs/proof-progress.csv` with `docs/clrs-proof-progress.csv`;
- identify
  `CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/ComposedPreservation.lean`
  as the capstone module;
- describe
  `CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/Preservation.lean` as a
  supporting layer rather than the capstone;
- record the actual generated induction principle
  `composedDelete.induct`, not `Nat.strongRecOn`;
- move exact deletion semantics from "future remaining work" to a later
  completed milestone.

- [ ] **Step 3: Replace whole-site verification with the single-chapter gate**

The archived plan may retain historical commands if clearly labeled, but its
current outcome/verification note must use:

```bash
lake build CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion
for f in Tests/Chapter_18_*Interface.lean Tests/Chapter_18_Root_Occupancy.lean; do
  lake env lean -DwarningAsError=true "$f"
done
python3 scripts/check_repository.py
python3 scripts/check_progress_csv.py
```

Do not add full-site HTML generation.

- [ ] **Step 4: Check and commit**

Run:

```bash
git add \
  docs/superpowers/plans/2026-07-30-ch18-btree-delete-proof-completion.md
git diff --cached --check -- \
  docs/superpowers/plans/2026-07-30-ch18-btree-delete-proof-completion.md
rg -n 'Outcome|f3f61b4|134/134|ComposedPreservation|composedDelete\.induct|clrs-proof-progress' \
  docs/superpowers/plans/2026-07-30-ch18-btree-delete-proof-completion.md
git diff --cached -- \
  docs/superpowers/plans/2026-07-30-ch18-btree-delete-proof-completion.md
```

Commit only this file:

```bash
git commit -m "docs(ch18): archive deletion completion plan"
```

## Task 3: Reconcile the AFP architecture research note

**Files:**

- Modify:
  `docs/research/afp-btree-deletion-architecture-2026-07-27.md`
- Reference:
  `CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/ChildBounded.lean`
- Reference:
  `CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/ComposedPreservation.lean`
- Reference:
  `CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/Exact.lean`
- Reference:
  `CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/SameDepthHeight.lean`

- [ ] **Step 1: Mark the note as a dated research snapshot**

Add a status note near the title stating:

- the architectural investigation was performed on 2026-07-27;
- the old blocker count and attack order describe that date only;
- Chapter 18 is now complete at `134/134`;
- the comparison remains useful as architectural provenance, not as a current
  backlog.

Keep the official AFP entry and theory-source links. Correct the title's
existing `(Mündler & Nipkow)` attribution and state the official entry metadata
directly: author Niels Mündler, entry date 2021-02-24. Do not broaden
authorship from memory.

- [ ] **Step 2: Correct the invariant comparison**

Rename the section currently claiming that `ChildBounded` is an invariant AFP
does not have. Use wording with this exact logical boundary:

```markdown
AFP 的全局 `sorted_less (inorder tree)` 与本项目 `Sorted + ChildBounded`
共同承担的排序责任相对应。AFP 没有单独命名的逐子树
`ChildBounded` 谓词，但这不表示 AFP 省略了跨子树顺序义务，也不支持
“CLRS-Lean 的不变量严格更强”这一结论。
```

Replace phrases such as "equivalent" or "completely isomorphic" with
"analogous", "similar strict descent", or a narrower description of the
shared proof shape.

- [ ] **Step 3: Remove stale line-number guidance**

Replace references such as `:1472` and old exact line numbers with theorem or
module names. Convert "the only remaining `sorry`" and the ordered attack list
to historical wording.

- [ ] **Step 4: Add the recommendation-to-outcome table**

Add a section `5. 后续实现结果（截至 2026-07-31）` with at least these
rows:

| 2026-07-27 recommendation/blocker | Current CLRS-Lean outcome |
| --- | --- |
| merge content and bounds | `mem_keysOf_mergeNodes` and merge child-bounded/reassembly lemmas |
| rotation ordering repair | `rotateLeft`/`rotateRight` repair and reassembly layers |
| bundle recursive invariants | `NodeWF` plus `composedDelete_packet` |
| align induction with the function | generated `composedDelete.induct` |
| prove exact deletion content | `keyBag (composedDelete t x tr) = (keyBag tr).erase x` |
| close height behavior | same-depth preservation and root height unchanged-or-minus-one |

End with an explicit statement that there is no remaining core Chapter 18
proof item.

- [ ] **Step 5: Check and commit**

Run:

```bash
git add docs/research/afp-btree-deletion-architecture-2026-07-27.md
git diff --cached --check -- \
  docs/research/afp-btree-deletion-architecture-2026-07-27.md
rg -n '134/134|sorted_less|Sorted \+ ChildBounded|composedDelete\.induct|keyBag|高度' \
  docs/research/afp-btree-deletion-architecture-2026-07-27.md
if rg -n ':[0-9]+' \
  docs/research/afp-btree-deletion-architecture-2026-07-27.md; then
  exit 1
fi
git diff --cached -- \
  docs/research/afp-btree-deletion-architecture-2026-07-27.md
```

Expected: AFP is credited accurately, comparisons are scoped, old blockers
are dated, and the current outcome table is complete.

Commit only this file:

```bash
git commit -m "docs(ch18): reconcile AFP deletion retrospective"
```

## Task 4: Split the mixed stuck-point note into history and current patterns

**Files:**

- Read, then remove from the implementation worktree:
  `docs/proof-patterns/stuck-points-and-reusable-structures.md`
- Create:
  `docs/proof-patterns/stuck-points-retrospective-2026-07-24.md`
- Create: `docs/proof-patterns/proof-engineering-patterns.md`
- Reference: `docs/proof-patterns/geometric-proof-patterns.md`
- Reference: `docs/proof-patterns/clrs-lean-playbook.md`

- [ ] **Step 1: Create the dated retrospective**

Move the seven case studies, the process-collision appendix, the five-category
stuck-point taxonomy, and the commit-timeline rhythm signals into
`stuck-points-retrospective-2026-07-24.md`. Start it with:

```markdown
# 卡壳案例复盘（截至 2026-07-24）

> 本文是提交历史与证明攻坚路径的时间点复盘，不是当前待办清单。
> “后续结果”按 2026-07-31 的仓库状态补记。
```

For each case, preserve verifiable commit-history observations but add a short
`后续结果` paragraph where later work changed the state.

Required corrections:

- Chapter 18 now has search, insertion, structural deletion, exact deletion,
  and height closure at `134/134`;
- Chapter 7's expectation bridge and `Θ(n log n)` result are complete;
- the current partial chapters are 19, 26, 27, and 33;
- the Chapter 20 broken link must use the exact relative targets
  `../superpowers/specs/2026-07-14-ch20-veb-delete-correctness-design.md` and
  `../superpowers/plans/2026-07-14-ch20-veb-delete-correctness-plan.md`;
- source locations use module/theorem names rather than fragile line numbers;
- workflow causality is phrased as evidence or an observed association, not as
  proof that a single incident caused a process change.

Keep the taxonomy and rhythm signals explicitly tied to the 2026-07-24
snapshot. Update any list of unresolved chapters and soften its causal
interpretations using the same rules as the case studies.

- [ ] **Step 2: Create the current proof-pattern catalog**

Move only still-current patterns into `proof-engineering-patterns.md`. Begin
with a scope note that this file complements, rather than duplicates,
`geometric-proof-patterns.md` and `clrs-lean-playbook.md`.

Retain and update the patterns with the strongest distinct value:

- per-field fold preservation;
- enumerated relation lemma families;
- component decomposition for compound invariants;
- bundled induction across invariant and semantic components;
- fuelized recursion and strengthened two-fuel induction;
- weakened invariant plus deficit absorption;
- predicate-wrapped induction conditions;
- definition-shape-aware tactic selection.

Merge or remove duplicate entries for loop-invariant templates, bridge
stacking, and geometric patterns when the existing documents already cover
them.

Correct the red-black description:

```markdown
RedBlackShape = RootBlack ∧ NoRedRed ∧ BalancedBlackHeight
```

State separately that BST ordering is a distinct premise/invariant.

- [ ] **Step 3: Remove the mixed source only after both outputs are complete**

Compare the two new files with the source and confirm every retained historical
case, the five-category taxonomy, the rhythm signals, and every selected
current pattern has a destination. Then remove only the copied worktree input:

```text
docs/proof-patterns/stuck-points-and-reusable-structures.md
```

Do not remove either existing proof-pattern reference document.

- [ ] **Step 4: Check links, stale claims, and commit**

Run:

```bash
git add \
  docs/proof-patterns/stuck-points-retrospective-2026-07-24.md \
  docs/proof-patterns/proof-engineering-patterns.md
git diff --cached --check -- \
  docs/proof-patterns/stuck-points-retrospective-2026-07-24.md \
  docs/proof-patterns/proof-engineering-patterns.md
rg -n '134/134|Chapter 7|19、26、27、33|RedBlackShape|BST|后续结果' \
  docs/proof-patterns/stuck-points-retrospective-2026-07-24.md \
  docs/proof-patterns/proof-engineering-patterns.md
if rg -n ':[0-9]+|\.lean:L[0-9]|L[0-9]+-[0-9]+' \
  docs/proof-patterns/stuck-points-retrospective-2026-07-24.md \
  docs/proof-patterns/proof-engineering-patterns.md; then
  exit 1
fi
python3 scripts/check_repository.py
git diff --cached -- \
  docs/proof-patterns/stuck-points-retrospective-2026-07-24.md \
  docs/proof-patterns/proof-engineering-patterns.md
```

Expected: the repository check passes, the old mixed file is absent, and the
two outputs have non-overlapping purposes.

Commit only the two new files:

```bash
git commit -m "docs(proofs): split stuck-point retrospective and patterns"
```

## Task 5: Verify the complete documentation-only branch

**Files:**

- Verify all five revised/split documents
- Verify the design and implementation plan
- Verify excluded files remain absent

- [ ] **Step 1: Confirm the exact tracked artifact set**

Run:

```bash
git status --short
git diff --name-status main...HEAD
git ls-files \
  docs/superpowers/specs/2026-07-27-ch18-btree-delete-guard-design.md \
  docs/superpowers/plans/2026-07-30-ch18-btree-delete-proof-completion.md \
  docs/research/afp-btree-deletion-architecture-2026-07-27.md \
  docs/proof-patterns/stuck-points-retrospective-2026-07-24.md \
  docs/proof-patterns/proof-engineering-patterns.md
```

Expected: those five files are tracked and the working tree is clean. The
mixed source file should not appear because it was never tracked.

- [ ] **Step 2: Confirm excluded and superseded files are absent**

Run:

```bash
set -e
test ! -e Scratch_check.lean
test ! -e Scratch_proto.lean
test ! -e docs/research/paper-skeleton-2026-07-27.md
test ! -e docs/proof-patterns/stuck-points-and-reusable-structures.md
```

Expected: all four checks exit successfully.

- [ ] **Step 3: Audit historical markers manually**

Run:

```bash
rg -n '11.*sorry|19.*sorry|111/111|未完全收口|唯一.*sorry|尚未证明.*精确|partial' \
  docs/superpowers/specs/2026-07-27-ch18-btree-delete-guard-design.md \
  docs/superpowers/plans/2026-07-30-ch18-btree-delete-proof-completion.md \
  docs/research/afp-btree-deletion-architecture-2026-07-27.md \
  docs/proof-patterns/stuck-points-retrospective-2026-07-24.md \
  docs/proof-patterns/proof-engineering-patterns.md
```

This search may find preserved historical claims. Inspect every hit. Each must
be explicitly attached to its snapshot date and reconciled with the current
`134/134` outcome. There must be no hit presented as the current Chapter 18
state.

- [ ] **Step 4: Run repository verification**

Run:

```bash
python3 scripts/check_repository.py
python3 scripts/check_progress_csv.py
python3 scripts/test_literate_config.py
python3 scripts/check_site_consistency.py
git diff --check main...HEAD
git diff --exit-code main...HEAD -- \
  CLRSLean Tests docs/clrs-proof-progress.csv README.md literate.toml
```

Expected:

- repository checks pass;
- progress remains `35 chapters, 1498 tracked theorem entries, 1498 proved`;
- site structure remains consistent;
- no whitespace errors;
- no Lean source, test, progress, README, or literate configuration change.

- [ ] **Step 5: Review commits and final diff**

Run:

```bash
git log --oneline main..HEAD
git diff --stat main...HEAD
git diff main...HEAD -- \
  docs/proof-patterns \
  docs/research \
  docs/superpowers/plans \
  docs/superpowers/specs
```

Request a proof/documentation review. Resolve all factual issues in new focused
commits, rerun Step 4, and do not squash away the document-family history
unless explicitly requested.

## Task 6: Integrate and clean the original main worktree

Use `superpowers:finishing-a-development-branch` before integration. Do this
task only after Task 5 passes and the user confirms integration.

**Original untracked paths to remove:**

- `Scratch_check.lean`
- `Scratch_proto.lean`
- `docs/proof-patterns/stuck-points-and-reusable-structures.md`
- `docs/research/afp-btree-deletion-architecture-2026-07-27.md`
- `docs/research/paper-skeleton-2026-07-27.md`
- `docs/superpowers/plans/2026-07-30-ch18-btree-delete-proof-completion.md`
- `docs/superpowers/specs/2026-07-27-ch18-btree-delete-guard-design.md`

- [ ] **Step 1: Re-resolve the destructive targets**

In the original `main` worktree, run:

```bash
git status --short --branch
sha256sum --check <<'SHA256'
225ce65a29a41c9025e7f2da3633d06df507656d38f27c76fb4faca1aa6a9a94  Scratch_check.lean
ab9159e487af217e5d3b2b09d2c7e7b4026bde9c18658180a8115deabc1bdea8  Scratch_proto.lean
e476cc9197743c6352755631af01b6646b6f1b4cfd46bc29ef8c8857c5a03a42  docs/proof-patterns/stuck-points-and-reusable-structures.md
c29f55321234a70532867ce523aca3ddb5bb136b50e04befb56c51cc11083e75  docs/research/afp-btree-deletion-architecture-2026-07-27.md
32a2ae7bb241b08d56b579d738ac4fde70187ead2ea8cdcdbdf974294effde94  docs/research/paper-skeleton-2026-07-27.md
cafa161d70441b3c83e253b372d0bb1643e179281ef836a39276593ddac9985f  docs/superpowers/plans/2026-07-30-ch18-btree-delete-proof-completion.md
7cfa9693502245dbedb83116694b9401520e2661a799a35cf2bd535b0871e30a  docs/superpowers/specs/2026-07-27-ch18-btree-delete-guard-design.md
SHA256
```

Expected: exactly the seven audited paths are untracked, apart from any
unrelated user changes that must be preserved. `sha256sum --check` must exit
with status 0 and report success for every digest (`OK` under an English
locale). Stop if a target became tracked, a digest changed, or its role
changed; a hash mismatch means the user may have edited the file after this
plan was written.

- [ ] **Step 2: Ensure every retained artifact exists on the feature branch**

Run:

```bash
git ls-tree -r --name-only codex/untracked-progress-consolidation -- \
  docs/proof-patterns \
  docs/research \
  docs/superpowers/plans \
  docs/superpowers/specs
```

Verify the five intended outputs are listed before removing their old
untracked inputs.

- [ ] **Step 3: Move only the seven audited originals to the desktop trash**

Run the recoverable, exact-path cleanup:

```bash
set -e
gio trash \
  Scratch_check.lean \
  Scratch_proto.lean \
  docs/proof-patterns/stuck-points-and-reusable-structures.md \
  docs/research/afp-btree-deletion-architecture-2026-07-27.md \
  docs/research/paper-skeleton-2026-07-27.md \
  docs/superpowers/plans/2026-07-30-ch18-btree-delete-proof-completion.md \
  docs/superpowers/specs/2026-07-27-ch18-btree-delete-guard-design.md
test ! -e Scratch_check.lean
test ! -e Scratch_proto.lean
test ! -e docs/proof-patterns/stuck-points-and-reusable-structures.md
test ! -e docs/research/afp-btree-deletion-architecture-2026-07-27.md
test ! -e docs/research/paper-skeleton-2026-07-27.md
test ! -e docs/superpowers/plans/2026-07-30-ch18-btree-delete-proof-completion.md
test ! -e docs/superpowers/specs/2026-07-27-ch18-btree-delete-guard-design.md
```

Do not use globs, recursive removal, `gio trash --force`, or a workspace-wide
cleanup command. Report that the originals are recoverable from the desktop
trash and that the four retained subjects now have committed, revised
replacements on the feature branch.

- [ ] **Step 4: Merge and re-verify**

Merge the feature branch into `main` using the completion workflow selected
with the user. Then run:

```bash
python3 scripts/check_repository.py
python3 scripts/check_progress_csv.py
python3 scripts/test_literate_config.py
python3 scripts/check_site_consistency.py
git diff --check HEAD^..HEAD
git status --short --branch
```

Expected: checks pass, `main` contains the five curated artifacts plus the
design and implementation plan, and none of the seven old untracked inputs
remain.

Do not push this new consolidation work without explicit remote-push
authorization.

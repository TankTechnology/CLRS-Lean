# Chapter Completion Audit

This checklist is run whenever we claim a chapter or section is
`main-proof-complete`, `proved`, or ready for a phase milestone.
It is stricter than the normal build loop because it checks that the proof is
*believable* and *documented*, not merely compiler-clean.

Run this before any commit that changes a chapter status.

---

## 1. Correctness Checks

### 1.1 Build

- [ ] `lake build CLRSLean` passes with no errors.
- [ ] `lake build CLRSLean.Chapter_XX.Section_XX_Y_Zzz` passes for every changed section.
- [ ] If the chapter has a `Tests/Chapter_XX_Interface.lean`, it also passes.

### 1.2 No Holes

- [ ] Run `grep -R "sorry\|admit\|axiom" CLRSLean/Chapter_XX/` and confirm the output is empty.
- [ ] For every new public theorem, run `#print axioms TheoremName` and confirm it reports no axioms other than `propext`, `Quot.sound`, and standard Lean/MK4 axioms.
- [ ] No `partial` definitions are used where totality is part of the specification.

### 1.3 Theorem Statements Match the Textbook

- [ ] Each public theorem name is tied to a specific CLRS claim (algorithm, lemma, or theorem number if available).
- [ ] The quantifiers and hypotheses are not stronger than the textbook claim in a misleading way.
- [ ] Any simplification or abstraction is explicitly noted in the module doc (e.g., finite rank-symmetry model, functional list model, power-of-two recurrence).

### 1.4 Definitions are Effective

- [ ] Executable functions terminate. Lean will catch non-termination in most cases, but check that recursive calls are structurally smaller or fuelled.
- [ ] `#eval` examples on small inputs run without error, when applicable.
- [ ] There are no unreachable or contradictory hypotheses in public theorems.

---

## 2. Proof Quality Checks

### 2.1 No Stale Tactics

- [ ] No commented-out `sorry` or `admit` left in the file.
- [ ] No `try` or `all_goals` left over from exploration that accidentally closes a goal by side effect.
- [ ] `simp` calls use explicit lemma lists unless there is a local `attribute [simp]` block with a clear reason.

### 2.2 Helper Lemma Discipline

- [ ] Helper lemmas are `private` or live in a clearly named block unless they are reused by another section.
- [ ] Every helper lemma has a one-line docstring saying what it is for.
- [ ] No duplicate lemmas with nearly identical statements.

### 2.3 Induction and Recursion Alignment

- [ ] The theorem induction structure matches the function recursion structure.
- [ ] Base cases and inductive cases are explicitly separated in long proofs.
- [ ] Invariants are stated as separate `def`s before being used in theorems.

---

## 3. Documentation Checks

### 3.1 Section Module Doc

- [ ] The section `.lean` file opens with a module doc (`/-! ... -/`) that explains:
  - what CLRS section is being formalized;
  - the model choices and simplifications;
  - the main public theorems by name;
  - any remaining gaps.

### 3.2 Chapter Guide

- [ ] `CLRSLean/Chapter_XX.lean` is updated to reflect the new status and theorem list.
- [ ] The chapter guide still accurately describes what is `proved`, `partial`, or `future-work`.

### 3.3 Site Navigation

- [ ] `literate.toml` lists the new section under `[order_children]` for its chapter.
- [ ] `literate.toml` has a `[modules."CLRSLean.Chapter_XX.Section_XX_Y_Zzz"]` title entry.
- [ ] `docs/proof-map.md` has an entry for the new section and its main theorems.
- [ ] `CLRSLean/Status.lean` is updated if the public status board changes.

### 3.4 Role and Header Discipline

- [ ] Inline code in docs uses `{name}` for Lean identifiers and `{lit}` for literal text.
- [ ] Section doc comments use `/-! **Section Title** -/` instead of `/-! ## ... -/` to avoid doc-gen header-nesting errors.
- [ ] Module doc top-level title uses exactly one `#`.

---

## 4. Cross-Cutting Checks

### 4.1 Imports

- [ ] No new cyclic imports introduced.
- [ ] The section imports only what it needs; prefer local imports over importing whole chapters.

### 4.2 Naming Consistency

- [ ] New theorem names follow the existing convention: lowercase after namespace, descriptive, CLRS-facing.
- [ ] No names collide with existing public names in other chapters.

### 4.3 Size and Maintainability

- [ ] Single file is not growing beyond ~1500 lines without a clear split.
- [ ] Long proofs are broken into named `have` steps or helper lemmas.

---

## 5. Sign-Off

When all boxes are checked, record:

```markdown
| Chapter | Section | Auditor | Date | Commit |
|---|---|---|---|---|
| 9 | 9.1-9.3 | Codex | 2026-07-15 | 353ec4a |
| 22 | 22.1-22.5 | Codex | 2026-07-10 | 1aeb257 |
| 13 | 13.1 | (name) | 2026-07-01 | a6c71af |
```

Add the row below the table in this file when the audit is complete.

### Audit Log

| Chapter | Section | Auditor | Date | Commit |
|---|---|---|---|---|

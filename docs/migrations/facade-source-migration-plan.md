# Native source migration for the remaining facade rows

This is the execution plan for issue **#229**: migrate the remaining
fourth-edition **compatibility-facade rows** to native fourth-edition source
locations while preserving the published `1.x` compatibility contract.  It
operationalizes the policy already stated in [`clrs4.md`](clrs4.md); that
document remains the authority on *what* is guaranteed, this one is the *how*.

The facade rows are migration debt, **not** missing theorem coverage.  Every
facade chapter below is already theorem-bearing on `main` under a legacy import
prefix; the only thing missing is native fourth-edition *source ownership*.

## 1. Scope and non-goals

**In scope:** the 47 non-`Ch34` facade rows in
[`docs/clrs-fourth-edition-map.csv`](../clrs-fourth-edition-map.csv)
(`migration_state = facade`), grouped below by legacy import prefix and
declaration namespace.

**Out of scope (explicit):**

- **Chapter 34** (`NP-Completeness`). Its advertised textbook proof boundary
  became `main-proof-complete` on 2026-08-25. Its large theorem and machine
  module tree remains excluded from this 47-row migration batch so that native
  source relocation can be reviewed as a dedicated follow-up, independently of
  the now-closed proof boundary.
- **Online/supplementary material** (`migration_state = online-material`).
  Those rows are retained under `CLRSLean.OnlineMaterial` and are already
  handled by the online-material catalog; they are not facade rows.
- **Already-native chapters** (`migration_state = native`) and their pending
  *declaration-namespace* renames (e.g. `CLRS.Chapter21 → CLRS.Chapter19`).
  Those chapters have migrated their sources; their namespace migration is a
  separate, per-chapter rename tracked in the chapter guides and `clrs4.md`.
  It is deliberately not folded into this plan.

## 2. Inventory of the remaining facade rows (acceptance: inventory + grouping)

Grouped by **legacy import prefix** and **declaration namespace**.  A facade
row means the canonical `CLRSLean.FourthEdition.Chapter_NN` guide currently
sources the section from the legacy `CLRSLean.Chapter_NN` module.

| 4e ch. | Chapter title | Legacy import prefix | Declaration namespace | Facade sections | Legacy section files |
| --- | --- | --- | --- | --- | --- |
| 1 | The Role of Algorithms in Computing | `CLRSLean.Chapter_01` | `CLRS.Chapter01` | 1.1, 1.2 | none — prose-only guide |
| 2 | Getting Started | `CLRSLean.Chapter_02` | `CLRS.Chapter02` | 2.1–2.3 | 3 |
| 3 | Characterizing Running Times | `CLRSLean.Chapter_03` | `CLRS.Chapter03` | 3.1–3.3 | 2 (`3_1`, `3_2`) |
| 4 | Divide-and-Conquer | `CLRSLean.Chapter_04` | `CLRS.Chapter04` | 4.2–4.5 | 4 (`4_2`…`4_5`) |
| 5 | Probabilistic Analysis and Randomized Algorithms | `CLRSLean.Chapter_05` | `CLRS.Chapter05` | 5.1–5.4 | 4 |
| 6 | Heapsort | `CLRSLean.Chapter_06` | `CLRS.Chapter06` | 6.1–6.5 | 5 |
| 7 | Quicksort | `CLRSLean.Chapter_07` | `CLRS.Chapter07` | 7.1–7.4 | 4 |
| 8 | Sorting in Linear Time | `CLRSLean.Chapter_08` | `CLRS.Chapter08` | 8.1–8.4 | 4 |
| 9 | Medians and Order Statistics | `CLRSLean.Chapter_09` | `CLRS.Chapter09` | 9.1–9.3 | 3 |
| 10 | Elementary Data Structures | `CLRSLean.Chapter_10` | `CLRS.Chapter10` | 10.1–10.3 | 3 (`10_1`, `10_2`, `10_4`) |
| 11 | Hash Tables | `CLRSLean.Chapter_11` | `CLRS.Chapter11` | 11.1–11.5 | 5 |
| 12 | Binary Search Trees | `CLRSLean.Chapter_12` | `CLRS.Chapter12` | 12.1–12.3 | 1 |
| 13 | Red-Black Trees | `CLRSLean.Chapter_13` | `CLRS.Chapter13` | 13.1 | 1 |
| 18 | B-Trees | `CLRSLean.Chapter_18` | `CLRS.Chapter18` | 18.1–18.3 | 3 |

Section counts sum to **47** (2+3+3+4+4+5+4+4+3+3+5+3+1+3), matching the
non-`Ch34` facade rows; the 3 `Ch34` facade rows bring the map total to 50.

The primary namespace of every facade chapter is uniformly
`CLRS.ChapterNN`.  Auxiliary namespaces exist (`CLRS.Chapter18.BTree`,
`CLRS.Chapter07.AdjacentSwapTrace`, `CLRS.Chapter04.SubarraySplitTree`,
`CLRS.Chapter12.BSTree`, `CLRS.Chapter13.RBTree`, `CLRS.Chapter02.MergeSortRecurrence`,
`CLRS.Chapter05.OnlineHiring`, `CLRS.Chapter08.MutableOutput`/`ReverseScan`) but
are all nested under `CLRS.ChapterNN`, so they move with it.

## 3. Key observation: no namespace rename is required

For **every** facade chapter the fourth-edition chapter number equals the
third-edition chapter number (1–13, 18).  The canonical declaration namespace
scheme is `CLRS.ChapterNN` where `NN` is the fourth-edition number — the same
scheme the already-migrated chapters use (`CLRS.Chapter15` for 4e Ch.14,
`CLRS.Chapter21` for 4e Ch.19, …).  Therefore the facade chapters' namespace
`CLRS.ChapterNN` is **already the canonical fourth-edition namespace**.

Consequence: the facade migration is a **source-location (module path)
re-homing**, not a declaration rename.  The burden of "namespace migration" in
the issue title falls on the *shifted*, already-native chapters (14–16, 19–27)
and is handled separately.  This makes each facade migration low-risk and
mechanically reversible.

## 4. Replacement imports and namespaces (acceptance: define before moving)

For a facade chapter `N`, the canonical fourth-edition target is:

- **Replacement import:** `CLRSLean.FourthEdition.Chapter_NN` and its section
  modules `CLRSLean.FourthEdition.Chapter_NN.Section_NN_M_*`.
- **Replacement namespace:** `CLRS.ChapterNN` — unchanged (see §3).

Per-section target module paths and titles are defined **only** from the
`section_no` / `section_title` columns of
[`clrs-fourth-edition-map.csv`](../clrs-fourth-edition-map.csv), never assumed
from the legacy filename.  Section numbering is *not* always preserved:

- Ch.10: legacy `Section_10_4_Rooted_Trees` re-homes as 4e **§10.3**
  "Representing rooted trees".
- Ch.4: legacy `Section_04_1_Maximum_Subarray` is **online material**, not a
  4e §4.1 section; it must *not* be re-homed into `FourthEdition.Chapter_04`.
  Legacy `Section_04_6_Master_Theorem_All_Input` is third-edition-only proof
  detail with no 4e §4.6 counterpart (4e §4.6 is the native continuous master
  theorem); it stays in the legacy tree or moves to online material by its own
  decision, not silently.
- Ch.11 §11.5 "Perfect hashing" is already declared at
  `CLRSLean.Chapter_11.Section_11_5_Perfect_Hashing` and promoted to canonical
  §11.5; its re-home target is `FourthEdition.Chapter_11.Section_11_5_Perfect_Hashing`.

Each chapter's plan (the per-chapter follow-up issue) must record the exact
legacy-file → native-module map **before** any file moves, and that map must be
consistent with the edition map.

## 5. Per-chapter migration procedure

For one chapter `N`, in order:

1. **Record the mapping** (§4) in the follow-up issue body.
2. **Add compatibility tests first.**  Create
   `Tests/Chapter_NN_Legacy_Imports.lean` that imports the legacy section
   modules and `#check`s the public declarations, following
   `Tests/Chapter_19_Legacy_Imports.lean`.  Confirm it compiles on the
   *unmigrated* tree.
3. **Create native section modules** under
   `CLRSLean/FourthEdition/Chapter_NN/`.  Move the theorem-bearing body
   (definitions, theorems, proofs) unchanged, keeping `namespace CLRS` /
   `namespace ChapterNN` intact.  Keep `/-!` blocks and Verso markup.
4. **Re-point the facade guide.**  `CLRSLean.FourthEdition.Chapter_NN.lean`
   imports the native sections instead of `CLRSLean.Chapter_NN`; update its
   "Current source" block to name the native sections.
5. **Keep the legacy shims.**  `CLRSLean.Chapter_NN.lean` and its
   `CLRSLean.Chapter_NN/Section_*` modules remain and **forward** to the native
   modules (`import CLRSLean.FourthEdition.Chapter_NN.Section_...`), exactly
   like `CLRSLean.Chapter_21` forwards to `FourthEdition.Chapter_19`.  Public
   declarations stay reachable at `CLRS.ChapterNN`.
6. **Update the edition map atomically** in the same commit that lands the
   source move: flip `migration_state` from `facade` to `native` for the moved
   sections, set `source_modules` to the native module paths, and set
   `legacy_location` to the forwarding note.  No commit may leave a section
   `native` while its source still lives only under the legacy tree, or vice
   versa.
7. **Update ledgers.**  Regenerate `CLRSLean/Progress.lean` only if the
   progress CSV changes (it should not — see §8); keep `literate.toml` module
   entries and titles consistent with the new module paths.
8. **Gate.**  `lake build CLRSLean`, the new legacy-import test,
   `uv run python scripts/check_repository.py`, and the existing
   `FourthEdition_Compatibility.lean` test all pass; `grep` the chapter for
   `sorry`/`admit`; `#print axioms` on a headline theorem is unchanged.

Chapters 4 and 13 are **mixed** (already partly native).  For them the move
targets only their remaining facade sections (4.2–4.5 and 13.1 respectively)
and must not disturb the existing `FourthEdition.Chapter_04` / `_13` native
sections or the online-material re-homing exclusions in §4.

Chapter 1 is **prose-only**: it has no section directory and no
theorem-bearing source.  Its migration is a guide re-point only (the facade
guide already carries the prose; there is nothing to move), so it is the
cheapest chapter and a natural first smoke-test of the procedure.

## 6. Compatibility preservation (acceptance: `1.x` + six-month contract)

The `clrs4.md` "Compatibility and deprecation policy" applies unchanged.  Each
chapter migration must uphold it verbatim:

1. Every existing `CLRSLean.Chapter_NN` import and its public declarations is
   preserved through **all `1.x` releases**.
2. Those imports are preserved for **at least six calendar months** after the
   first published release containing the fourth-edition facades.
3. No legacy import is removed before a **`2.0` or later** release.

Practically: the legacy module paths become *forwarding shims* (§5 step 5), so
third-edition-numbered imports keep compiling with zero downstream changes.
This is the same mechanism already used for Chapters 14–27.

## 7. The `2.0` cleanup checklist and release-note requirements

Eligibility to remove a legacy prefix `CLRSLean.Chapter_NN` at a future major
release requires **all** of (per `clrs4.md`, plus reachability):

- [ ] Its native fourth-edition source **and** declaration-namespace migration
      is complete (for facade chapters the namespace is already canonical; for
      shifted chapters the `CLRS.ChapterNN → CLRS.ChapterNN'` rename is done).
- [ ] The last `1.x` release still passes the legacy-import compatibility tests
      (per-chapter `*_Legacy_Imports.lean` and `FourthEdition_Compatibility.lean`).
- [ ] The six-month minimum since the first facade-bearing release has elapsed.
- [ ] The cleanup release notes name the **exact** removed prefix and its
      replacement import (`CLRSLean.FourthEdition.Chapter_NN`) and declaration
      namespace (`CLRS.ChapterNN`).
- [ ] **Online-material reachability:** no theorem-bearing online/supplementary
      material becomes unreachable through a supported named import.  Run
      `python3 scripts/check_edition_map.py` and confirm it reports no
      "online source module does not exist" — i.e. every `online:*` map row and
      every row of the online ledger still resolves to an importable module
      (either a legacy path or `CLRSLean.OnlineMaterial`).

Removal is **per legacy import prefix**, not all-at-once; a chapter whose gates
have not all passed simply waits, while others proceed.

## 8. Invariants (acceptance: proof labels are not source ownership)

- **Proof-completion labels never change as a side effect of a source move.**
  `docs/clrs-proof-progress.csv` counts, `main-proof-complete` / `partial`
  labels, and `docs/proof-map.md` entries are untouched by a pure re-homing.
  The only ledger column a facade migration edits is the edition map's
  `migration_state` / `source_modules` / `legacy_location` trio.
- A chapter that is `facade` and `main-proof-complete` stays
  `main-proof-complete` after migration; a `facade` chapter that is `partial`
  stays `partial`.  This is what makes the migration debt *separable* from
  coverage debt. Chapter 34 is excluded only because its unusually large source
  relocation is reserved for a dedicated follow-up.

## 9. Phasing and follow-up structure

Recommended order, cheapest-and-clearest first, one follow-up issue per
chapter with the §5 procedure and the §4 mapping table pasted into the body:

1. **Ch.1** (prose-only smoke test of the guide re-point + map flip).
2. **Ch.12** and **Ch.13 §13.1** (single-file facades; §13 is mixed, so §13.2–13.4
   stay untouched).
3. **Ch.18** (well-covered by existing `Tests/Chapter_18_*` interface tests).
4. **Ch.9**, **Ch.10** (small; Ch.10 exercises the §4 renumbering rule).
5. **Ch.2**, **Ch.3**, **Ch.5**, **Ch.6**, **Ch.7**, **Ch.8** (uniform
   same-number chapters).
6. **Ch.4 §4.2–4.5** (mixed; requires disentangling online material).
7. **Ch.11** (includes the promoted §11.5 perfect-hashing section).

No chapter is migrated before its compatibility test and mapping are recorded.
Chapter 34 stays a facade until its own coverage work (separate from this
track) closes.

## 10. Verification

- `lake build CLRSLean` clean.
- Per-chapter `Tests/Chapter_NN_Legacy_Imports.lean` and the shared
  `Tests/FourthEdition_Compatibility.lean` compile.
- `uv run python scripts/check_repository.py` and
  `python3 scripts/check_edition_map.py` pass (the latter enforces the atomic
  `migration_state` ↔ source-location consistency).
- `grep` for `sorry`/`admit` in the moved sources returns nothing;
  `#print axioms` on a headline theorem of each migrated chapter is unchanged
  (`propext` / `Classical.choice` / `Quot.sound`).

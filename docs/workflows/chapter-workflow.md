# CLRS Chapter Workflow

This is the working loop for each CLRS section.

## 1. Textbook Section Map

Record the relevant CLRS section number, title, algorithms, theorem-like claims,
and proof method.  Do not start with Lean code before the section has a clear
target statement.

Separate the map into three tracks:

- main textbook claims for the current pass;
- exercises, marked as future work unless explicitly selected;
- chapter-end Problems, marked as future work with priority and difficulty.

## 2. Algorithm Understanding

Translate the textbook algorithm into a Lean-friendly model.  Prefer a
mathematical version first.  Low-level implementation details such as arrays,
heaps, or union-find can be deferred when they are not needed for the main
correctness theorem.

## 3. Mathematical Proof Plan

Write the human proof in small claims.  For sorting algorithms, this usually
means:

- sortedness;
- preservation of elements, usually via permutation;
- induction or loop invariant.

For graph algorithms, this may mean:

- invariant;
- exchange lemma;
- cut or path certificate;
- final optimality theorem.

## 4. Lean Interface

Write the theorem names first and check that the intended public API is small.
The interface should answer what a future reader would search for:

```lean
#check CLRS.Chapter02.insertionSort_sorted
#check CLRS.Chapter02.insertionSort_perm
```

## 5. Lean Proof

Prove helper lemmas only when they serve the public theorem.  Keep early files
local and readable.  Extract shared abstractions only after at least two sections
need them.

## 6. Verification

Run the narrow file check, the interface check, and the library build when the
environment has Mathlib available:

```bash
lake env lean CLRSLean/Chapter_02/Section_02_1_Insertion_Sort.lean
lake env lean Tests/Chapter_02_Interface.lean
lake build CLRS-Lean
```

## 7. Update The Map

Update:

- `docs/proof-map.md`;
- the relevant `docs/chapters/chapter-XX.md`;
- the relevant `CLRSLean/Chapter_XX.lean` page;
- `CLRSLean/Status.lean` if the status changed;
- **`literate.toml` (REQUIRED for new or renamed sections)**:
  add the module to `[order_children]` and add a `[modules."..."]` title
  entry.  If you skip this, the section will still build but the deployed
  sidebar will show the parent chapter title instead of the section title.

Every section should say whether it is `proved`, `partial`, `statement`,
`blocked-design`, `blocked-mathlib`, `deferred-implementation`,
`future-work`, or `out-of-scope`.

## 8. Verify the deployed navigation

After pushing to `main`, wait for the `Build and deploy Verso site` action to
finish, then open the new section on the live site and confirm that the left
sidebar shows the correct section title (e.g. `15.5. Optimal Binary Search
Trees`), not the parent chapter title.

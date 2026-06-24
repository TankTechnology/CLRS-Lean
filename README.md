# CLRSLean

`CLRSLean` is a Lean 4 companion project for CLRS-style algorithm proofs.  The
deployed site is organized as a small online book: a project landing page,
chapter guide pages, section-level literate Lean proofs, a proof-status ledger,
and a contribution workflow.

The repository is organized by CLRS chapter and section:

```text
CLRSLean.lean
CLRSLean/Chapter_02.lean
CLRSLean/Chapter_10.lean
CLRSLean/Chapter_11.lean
CLRSLean/Chapter_12.lean
CLRSLean/Chapter_13.lean
CLRSLean/Chapter_16.lean
CLRSLean/Chapter_23.lean
CLRSLean/Status.lean
CLRSLean/Workflow.lean
CLRSLean/Chapter_02/Section_02_1_Insertion_Sort.lean
CLRSLean/Chapter_02/Section_02_2_Analyzing_Algorithms.lean
CLRSLean/Chapter_02/Section_02_3_Designing_Algorithms.lean
CLRSLean/Chapter_10/Section_10_1_Stacks_And_Queues.lean
CLRSLean/Chapter_10/Section_10_2_Linked_Lists.lean
CLRSLean/Chapter_11/Section_11_1_Direct_Address_Tables.lean
CLRSLean/Chapter_11/Section_11_2_Chained_Hash_Tables.lean
CLRSLean/Chapter_12/Section_12_1_Binary_Search_Trees.lean
CLRSLean/Chapter_13/Section_13_1_Red_Black_Trees.lean
CLRSLean/Chapter_16/Section_16_1_Activity_Selection.lean
CLRSLean/Chapter_16/Section_16_3_Huffman_Codes.lean
CLRSLean/Chapter_23/Section_23_1_Growing_Minimum_Spanning_Trees.lean
CLRSLean/Chapter_23/Section_23_2_Kruskal_And_Prim.lean
```

The main maintainer documents are:

```text
docs/proof-map.md
docs/workflows/chapter-workflow.md
docs/status/blocked-and-deferred.md
```

Build and verify Lean:

```bash
lake build
```

Generate the Verso website:

```bash
lake build :literateHtml
```

GitHub Actions runs the same Verso build and deploys the generated `_site`
artifact to GitHub Pages.

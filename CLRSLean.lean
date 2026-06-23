import CLRSLean.Chapter_01
import CLRSLean.Chapter_03
import CLRSLean.Chapter_02.Section_02_1_Insertion_Sort
import CLRSLean.Chapter_16.Section_16_3_Huffman_Codes
import CLRSLean.Chapter_23.Section_23_1_Growing_Minimum_Spanning_Trees
import CLRSLean.Chapter_23.Section_23_2_Kruskal_And_Prim

/-!
# CLRS-lean

A Lean 4 companion for *Introduction to Algorithms* (CLRS), formalizing
algorithm correctness proofs chapter by chapter.

## What is this?

Each section in CLRS that presents an algorithm proof is rendered as a
standalone Lean module.  The proofs are faithful to the textbook arguments
but expressed in Lean's dependent type theory, using Mathlib for
mathematical infrastructure.

## Proof status

| Chapter | Section | Status |
|---------|---------|--------|
| 2 | 2.1 Insertion Sort | ✅ proved |
| 16 | 16.3 Huffman Codes | ✅ proved |
| 23 | 23.1 Growing an MST | ⚠️ partial |
| 23 | 23.2 Kruskal and Prim | ⚠️ partial |

## Conventions

- **Zero-indexed**: sequences and lists use 0-based indexing for Mathlib compatibility
- **Total functions**: partial operations return junk values rather than `Option`
- **Unfinished proofs**: marked with `sorry` and an explanatory comment
- **Module = section**: one `.lean` file per CLRS section, rendered as one web page

## Build

* `lake build` — compile Lean sources
* `lake build :literateHtml` — generate website into `_site/`

## Repository

[https://github.com/TankTechnology/CLRSLean](https://github.com/TankTechnology/CLRSLean)
-/

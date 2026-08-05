import CLRSLean.Chapter_19
import CLRSLean.Chapter_20
import CLRSLean.Chapter_33
import CLRSLean.Chapter_04.Section_04_1_Maximum_Subarray
import CLRSLean.Chapter_11.Section_11_5_Perfect_Hashing
import CLRSLean.Chapter_16.Section_16_4_Matroids
import CLRSLean.Chapter_16.Section_16_5_Task_Scheduling
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm
import CLRSLean.Chapter_29.Section_29_5_The_Initial_Basic_Feasible_Solution
import CLRSLean.Chapter_30.Section_30_3_Efficient_FFT_Implementations
import CLRSLean.Chapter_31.Section_31_9_Integer_Factorization

/-!
# CLRS online and supplementary material

This import groups theorem-bearing material that is not part of the primary
CLRS fourth-edition chapter tree. Importing it does not make the legacy chapter
numbers canonical fourth-edition chapter numbers.

## Official fourth-edition online material

The former third-edition chapter guides for Fibonacci heaps
({lit}`CLRSLean.Chapter_19`), van Emde Boas trees
({lit}`CLRSLean.Chapter_20`), and computational geometry
({lit}`CLRSLean.Chapter_33`) correspond to official fourth-edition online
material.

## Moved and project-supplement catalog

CLRS-Lean also retains theorem-bearing developments for maximum subarray,
perfect hashing, matroids, unit-time task scheduling, the detailed simplex
algorithm and its initial basic feasible solution, iterative FFT
implementations, and integer factorization. They are collected here because
they moved out of the corresponding fourth-edition main-text section or remain
useful project supplements. Inclusion in this umbrella is a CLRS-Lean API
classification; it does not claim canonical fourth-edition chapter coverage or
that every project supplement is part of the official online bundle.

The moved section imports are:

* {lit}`CLRSLean.Chapter_04.Section_04_1_Maximum_Subarray`;
* {lit}`CLRSLean.Chapter_11.Section_11_5_Perfect_Hashing`;
* {lit}`CLRSLean.Chapter_16.Section_16_4_Matroids`;
* {lit}`CLRSLean.Chapter_16.Section_16_5_Task_Scheduling`;
* {lit}`CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm`;
* {lit}`CLRSLean.Chapter_29.Section_29_5_The_Initial_Basic_Feasible_Solution`;
* {lit}`CLRSLean.Chapter_30.Section_30_3_Efficient_FFT_Implementations`; and
* {lit}`CLRSLean.Chapter_31.Section_31_9_Integer_Factorization`.

During the compatibility period, declarations keep their existing namespaces.
See {lit}`docs/migrations/clrs4.md` for the import mapping and removal gates.
-/

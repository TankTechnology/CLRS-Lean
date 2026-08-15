/-!
# Progress Dashboard

This page is the public, reader-facing progress dashboard for CLRS-Lean.
The machine-readable source of truth is {lit}`docs/clrs-proof-progress.csv`.
When the CSV changes, regenerate this page with
{lit}`uv run python scripts/check_progress_csv.py --write-dashboard`.

## Fourth-Edition Snapshot

This is the canonical CLRS fourth-edition chapter ledger.  Reused
third-edition theorem sources remain compatibility evidence, not an
alternative chapter-numbering scheme.
Legacy imports remain supported through all 1.x releases and for at
least six months; removal is possible only in 2.0 or later.

* Fourth-edition chapters tracked: 35.
* Chapters represented in Lean: 35.
* Tracked reader-facing theorem entries: 1,578.
* Proved tracked theorem entries: 1,578.
* Online/supplementary theorem entries: 465.
* Remaining edition-coverage units: 2.

Tracked theorem entries form a selected proof inventory of reviewed groups mapped
to represented fourth-edition sections.  A complete proved/tracked count does not
by itself mean that every fourth-edition section obligation is covered.  Moved
subsections and wholly excluded legacy chapters are counted only
in the machine-readable online-material ledger.  This produces disjoint canonical and online-material ledgers;
compatibility imports do not duplicate either count.
An edition-coverage unit is one unresolved section in a represented chapter,
or one whole-chapter unit when no section of that chapter is represented.
The status {lit}`partial` means partial fourth-edition coverage, even when
every theorem already selected for that chapter is proved.

## Status Counts

* {lit}`main-proof-complete`: 29 chapters.
* {lit}`main-proof-complete-for-correctness`: 2 chapters.
* {lit}`selected-section-complete`: 2 chapters.
* {lit}`partial`: 1 chapter.
* {lit}`expository`: 1 chapter.

## Chapter Matrix

```
Ch  Chapter                                                     Status                               Sections                      Tracked  Gap units
--  ----------------------------------------------------------  -----------------------------------  ----------------------------  -------  ---------
 1  1. The Role of Algorithms in Computing                      expository                           Chapter_01                          0        0
 2  2. Getting Started                                          main-proof-complete                  2.1;2.2;2.3                         7        0
 3  3. Characterizing Running Times                             main-proof-complete                  3.1;3.2;3.3                        56        0
 4  4. Divide-and-Conquer                                       main-proof-complete                  4.1;4.2;4.3;4.4;4.5;4.6;4.7        99        0
 5  5. Probabilistic Analysis and Randomized Algorithms         selected-section-complete            5.1;5.2;5.3;5.4                    25        0
 6  6. Heapsort                                                 main-proof-complete                  6.1;6.2;6.3;6.4;6.5                78        0
 7  7. Quicksort                                                main-proof-complete                  7.1;7.2;7.3;7.4                    34        0
 8  8. Sorting in Linear Time                                   main-proof-complete                  8.1;8.2;8.3;8.4                    58        0
 9  9. Medians and Order Statistics                             main-proof-complete                  9.1;9.2;9.3                        72        0
10  10. Elementary Data Structures                              main-proof-complete                  10.1;10.2;10.3                     21        0
11  11. Hash Tables                                             main-proof-complete                  11.1;11.2;11.3;11.4;11.5           59        0
12  12. Binary Search Trees                                     main-proof-complete-for-correctness  12.1;12.2;12.3                     40        0
13  13. Red-Black Trees                                         main-proof-complete                  13.1;13.2;13.3;13.4                40        0
14  14. Dynamic Programming                                     main-proof-complete                  14.1;14.2;14.3;14.4;14.5           90        0
15  15. Greedy Algorithms                                       main-proof-complete                  15.1;15.2;15.3;15.4                27        0
16  16. Amortized Analysis                                      main-proof-complete                  16.1;16.2;16.3;16.4                69        0
17  17. Augmenting Data Structures                              main-proof-complete                  17.1;17.2;17.3                     79        0
18  18. B-Trees                                                 main-proof-complete                  18.1;18.2;18.3                    147        0
19  19. Data Structures for Disjoint Sets                       main-proof-complete                  19.1;19.2;19.3;19.4                84        0
20  20. Elementary Graph Algorithms                             main-proof-complete-for-correctness  20.1;20.2;20.3;20.4;20.5           47        0
21  21. Minimum Spanning Trees                                  main-proof-complete                  21.1;21.2                          52        0
22  22. Single-Source Shortest Paths                            main-proof-complete                  22.1;22.2;22.3;22.4;22.5           31        0
23  23. All-Pairs Shortest Paths                                main-proof-complete                  23.1;23.2;23.3                     29        0
24  24. Maximum Flow                                            main-proof-complete                  24.1;24.2;24.3;24.4;24.5           35        0
25  25. Matchings in Bipartite Graphs                           main-proof-complete                  25.1;25.2;25.3                     18        0
26  26. Parallel Algorithms                                     main-proof-complete                  26.1;26.2;26.3                     95        0
27  27. Online Algorithms                                       main-proof-complete                  27.1;27.2;27.3                     10        0
28  28. Matrix Operations                                       main-proof-complete                  28.1;28.2;28.3                      9        0
29  29. Linear Programming                                      main-proof-complete                  29.1;29.2;29.3                     10        0
30  30. Polynomials and the FFT                                 main-proof-complete                  30.1;30.2;30.3                     34        0
31  31. Number-Theoretic Algorithms                             selected-section-complete            31.1;31.2;31.3;31.4;31.5;31.       17        0
32  32. String Matching                                         main-proof-complete                  32.1;32.2;32.3;32.4;32.5           61        0
33  33. Machine-Learning Algorithms                             main-proof-complete                  33.1; 33.2; 33.3                   15        0
34  34. NP-Completeness                                         partial (edition coverage)           34.1;34.2;34.3;34.4                20        2
35  35. Approximation Algorithms                                main-proof-complete                  35.1;35.2;35.3;35.4;35.5           10        0
```

## Agent Update Rule

Every theorem-producing agent should treat this table as part of the proof
artifact, not as a separate report.  If a contribution adds, removes,
renames, strengthens, or finishes a reader-facing theorem group, update
{lit}`docs/clrs-proof-progress.csv` in the same commit.  If the change
alters the public snapshot or chapter rows, regenerate this page before
building the site.

Minimum maintenance loop:

1. Consult {lit}`docs/clrs-fourth-edition-map.csv`, then update the relevant Lean files and {lit}`docs/clrs-proof-progress.csv`.
2. Run {lit}`uv run python scripts/check_progress_csv.py --write-dashboard`.
3. Run {lit}`lake build CLRSLean`; for explicit website publishing, use the four-shard runbook in {lit}`docs/site-architecture.md`.  The serial {lit}`lake build :literateHtml` target is a diagnostic fallback.
-/

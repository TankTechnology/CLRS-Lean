/-!
# Progress Dashboard

This page is the public, reader-facing progress dashboard for CLRS-Lean.
The machine-readable source of truth is {lit}`docs/clrs-proof-progress.csv`.
When the CSV changes, regenerate this page with
{lit}`uv run python scripts/check_progress_csv.py --write-dashboard`.

## Snapshot

* CLRS chapters tracked: 35.
* Chapters represented in Lean: 23.
* Tracked reader-facing theorem entries: 1022.
* Proved tracked theorem entries: 1022.
* Remaining core theorem groups: 38.

Tracked theorem entries count the public theorem groups currently represented
in Lean.  Remaining core theorem groups count textbook-facing targets that
are not yet represented or not yet complete.

## Status Counts

* {lit}`main-proof-complete`: 3 chapters.
* {lit}`main-proof-complete-for-correctness`: 3 chapters.
* {lit}`selected-section-complete`: 3 chapters.
* {lit}`partial`: 13 chapters.
* {lit}`not-started`: 12 chapters.
* {lit}`expository`: 1 chapter.

## Chapter Matrix

```
Ch  Chapter                                                     Status                               Sections                      Tracked  Missing
--  ----------------------------------------------------------  -----------------------------------  ----------------------------  -------  -------
 1  1. The Role of Algorithms                                   expository                           Chapter_01                          0        0
 2  2. Getting Started                                          main-proof-complete                  2.1;2.2;2.3                         6        0
 3  3. Growth of Functions                                      partial                              3.1;3.2                            23        1
 4  4. Divide-and-Conquer                                       partial                              4.1;4.2;4.3;4.4;4.5;4.6            79        2
 5  5. Probabilistic Analysis and Randomized Algorithms         selected-section-complete            5.1                                 6        1
 6  6. Heapsort                                                 main-proof-complete                  6.1;6.2;6.3;6.4;6.5                60        1
 7  7. Quicksort                                                partial                              7.1;7.2;7.3                        25        3
 8  8. Sorting in Linear Time                                   main-proof-complete-for-correctness  8.2;8.3;8.4                        27        1
 9  9. Medians and Order Statistics                             partial                              9.2;9.3                            43        1
10  10. Elementary Data Structures                              selected-section-complete            10.1;10.2                           6        3
11  11. Hash Tables                                             partial                              11.1;11.2                          20        1
12  12. Binary Search Trees                                     partial                              12.1                               32        1
13  13. Red-Black Trees                                         partial                              13.1                               34        2
14  14. Augmenting Data Structures                              partial                              14.1;14.3                          33        2
15  15. Dynamic Programming                                     partial                              15.1;15.2;15.4;15.5                69        1
16  16. Greedy Algorithms                                       selected-section-complete            16.1;16.3                          21        2
17  17. Amortized Analysis                                      partial                              17.1;17.2;17.4                     66        1
18  18. B-Trees                                                 partial                              18.1;18.2;18.3                     62        1
19  19. Fibonacci Heaps                                         partial                              19.1                               97        1
20  20. van Emde Boas Trees                                     partial                              20.1;20.2                         130        1
21  21. Data Structures for Disjoint Sets                       main-proof-complete                  21.1;21.2;21.3;21.4                84        0
22  22. Elementary Graph Algorithms                             main-proof-complete-for-correctness  22.1;22.2;22.3;22.4;22.5           47        0
23  23. Minimum Spanning Trees                                  main-proof-complete-for-correctness  23.1;23.2                          52        0
24  24. Single-Source Shortest Paths                            not-started                          not represented                     0        1
25  25. All-Pairs Shortest Paths                                not-started                          not represented                     0        1
26  26. Maximum Flow                                            not-started                          not represented                     0        1
27  27. Multithreaded Algorithms                                not-started                          not represented                     0        1
28  28. Matrix Operations                                       not-started                          not represented                     0        1
29  29. Linear Programming                                      not-started                          not represented                     0        1
30  30. Polynomials and the FFT                                 not-started                          not represented                     0        1
31  31. Number-Theoretic Algorithms                             not-started                          not represented                     0        1
32  32. String Matching                                         not-started                          not represented                     0        1
33  33. Computational Geometry                                  not-started                          not represented                     0        1
34  34. NP-Completeness                                         not-started                          not represented                     0        1
35  35. Approximation Algorithms                                not-started                          not represented                     0        1
```

## Agent Update Rule

Every theorem-producing agent should treat this table as part of the proof
artifact, not as a separate report.  If a contribution adds, removes,
renames, strengthens, or finishes a reader-facing theorem group, update
{lit}`docs/clrs-proof-progress.csv` in the same commit.  If the change
alters the public snapshot or chapter rows, regenerate this page before
building the site.

Minimum maintenance loop:

1. Update the relevant chapter/section Lean files and {lit}`docs/clrs-proof-progress.csv`.
2. Run {lit}`uv run python scripts/check_progress_csv.py --write-dashboard`.
3. Run {lit}`lake build CLRSLean` and, for website changes, {lit}`lake build :literateHtml`.
-/

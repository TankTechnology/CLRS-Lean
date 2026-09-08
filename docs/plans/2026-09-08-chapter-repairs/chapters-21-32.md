# Chapters 21–30 and 32 Repair Record

Issues [#363](https://github.com/TankTechnology/CLRS-Lean/issues/363) through
[#372](https://github.com/TankTechnology/CLRS-Lean/issues/372), excluding the
separate Chapter 31 record, and [#374](https://github.com/TankTechnology/CLRS-Lean/issues/374)
were resolved.

| Chapter | Completed repair |
| ---: | --- |
| 21 | Prim execution constructs the final spanning tree and derives its actual queue-operation cost. |
| 22 | Shortest-path execution constructs a source-rooted predecessor tree; detection scope for negative cycles is explicit. |
| 23 | Negative-cycle detection handles the missing direction and negative self-loops; APSP costs attach to actual executions. |
| 24 | Edmonds–Karp uses a sparse support bound and relabel-to-front has a complete scheduler. |
| 25 | Stale matching gaps and the woman-pessimal explanatory direction were corrected. |
| 26 | Parallel matrix interfaces state the dimensions for which execution and work/span theorems apply. |
| 27 | Caching uses an inhabited legal-state interface; competitive theorems and deterministic lower bounds use corrected quantifiers. |
| 28 | Legacy matrix asymptotics agree with the closed LUP execution costs. |
| 29 | The guide accurately separates mathematical real-valued solver contracts from executable polynomial-time claims. |
| 30 | Exact FFT multiplication counts state root-preparation and arithmetic-sharing assumptions. |
| 32 | DFA construction work counts actual transitions; Rabin–Karp includes the precomputed high-order power in its constant update. |

Focused tests cover disconnected graphs, zero-weight cycles, negative self-loops,
sparse flows, scheduler termination, empty caches, LUP failures, LP boundary
models, FFT base cases, DFA tables, and Rabin–Karp windows. Public interface and
axiom checks passed. Chapter 31 is documented in [its dedicated record](chapter-31.md).

# Chapters 17–20 Repair Record

Issues [#359](https://github.com/TankTechnology/CLRS-Lean/issues/359) through
[#362](https://github.com/TankTechnology/CLRS-Lean/issues/362) were resolved.

- **Chapter 17:** interval keys use lexicographic `(low, high)` order, preserving
  distinct equal-low intervals. Update invariants imply the search specification.
  Counted augmented insertion and rotation read cached fields, refine their
  uncounted forms, and have logarithmic maintenance bounds.
- **Chapter 18:** B-tree height and descent counters remain valid; documentation
  limits the count to selected recursive descents and does not equate it with all
  split, merge, predecessor, successor, or physical page-I/O work.
- **Chapter 19:** weighted-list union constructs the actual representative rewrite
  list. Mixed UNION/FIND execution preserves the partition, answers queries
  correctly, and bounds total abstract pointer rewrites.
- **Chapter 20:** topological sort and SCC explicitly include finish-time sorting;
  the DFS `V+E` count no longer stands for the entire algorithm.

The full library, focused regressions, old and new chapter interfaces, axiom
checks, and repository checks passed.

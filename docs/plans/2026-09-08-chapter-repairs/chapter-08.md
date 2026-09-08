# Chapter 8 repair plan — issue #351

- [x] Add a counted comparison-tree interpreter; use truncation and finite maximization to obtain an actual input attaining the lower bound. Preserve structural-height theorems with precise documentation.
- [x] Replace public counting-array execution with one stable indexed distribution and one output traversal. Prove result equality, stability and actual loop counts, including out-of-range behavior; identify this implementation as an indexed stable-bucket refinement.
- [x] Make radix passes consume the same counting execution's returned value and counters.
- [x] Use the shared distributor in public bucket sorting; use instrumented insertion sort per bucket. Prove bucket-content refinement and a bound including bucket initialization/traversal and output writes. Retain the old occupancy expression as an abstract budget, and bound the actual execution's expectation through it.
- [x] Synchronize guides, metadata, interface/trust tests and repair tracking; independently review and run changed-module and full repository checks.

Ownership: root comparison trees, bucket composition and metadata; counting subtask counting execution/mutable API/radix; insertion subtask only generic insertion kernel. No shared file edits. Historical audit remains immutable.

See [verification record](chapter-08-results.md). Full library regression passed with the Chapter10–12 batch (10711 jobs).

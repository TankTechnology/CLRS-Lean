# Chapter 8 Repair Record

Issue [#351](https://github.com/TankTechnology/CLRS-Lean/issues/351) was resolved.

- The comparison-tree interface returns reachable leaves and actual comparison
  counts; a finite maximum supplies a real worst-case input.
- Counting sort performs one input-distribution pass, bucket traversal, and output
  construction while preserving stability and the documented out-of-range-key
  behavior.
- Radix-sort value and cost APIs share one counted execution.
- Bucket sort shares a stable distributor and counted insertion-sort kernel. Its
  work bound includes the bucket count and the expected returned work is linear
  under independent uniform bucket assignment.

The counter excludes persistent copying, array/list view conversions, allocation
internals, and key-function internals. Edge regressions include unreachable tree
branches, duplicate payloads, out-of-range keys, zero buckets, empty input, and
multi-digit radix inputs. The independent review found no actionable defect.

import CLRSLean.Chapter_33.Section_33_1_Line_Segment_Properties
import CLRSLean.Chapter_33.Section_33_2_3_Segment_Intersection_Convex_Hull
import CLRSLean.Chapter_33.Section_33_4_Closest_Pair

/-! # Chapter 33 — Computational Geometry

Chapter 33 of CLRS covers computational-geometry algorithms: line-segment
properties, sweep-line segment intersection, convex-hull construction, and
closest-pair finding.

## Sections

### 33.1 Line-Segment Properties

* `CLRS.Chapter33.Point`, `CLRS.Chapter33.Vector` — 2D point and vector types
* `CLRS.Chapter33.cross` — 2D cross product with antisymmetry, bilinearity, and additivity lemmas
* `CLRS.Chapter33.Orientation` — inductive `Counterclockwise | Clockwise | Collinear`
* `CLRS.Chapter33.Segment` — line-segment structure with bounding-box and intersection predicates

**Status: proved** — cross-product algebra, `orientation_spec`, and
segment-predicate theorems are kernel-checked (7 theorems, 0 sorries).

### 33.2–33.3 Segment Intersection and Convex Hull

* `Section_33_2_3_Segment_Intersection_Convex_Hull`: sweep-line segment
  intersection detection and Graham-scan convex hull.

**Status: partial** — core definitions plus intersection-count and
convex-hull degenerate-case theorems; full sweep-line/Graham correctness
remains future work.

### 33.4 Closest Pair

* `Section_33_4_Closest_Pair`: divide-and-conquer closest-pair algorithm.

**Status: proved** — `closestPair_correct` kernel-checked (the returned
distance is a lower bound on every pairwise distance), 0 axioms.

## Deferred Work

* Remaining correctness theorems in Sections 33.2–33.4 (see section files)
-/

namespace CLRS
namespace Chapter33
end Chapter33
end CLRS

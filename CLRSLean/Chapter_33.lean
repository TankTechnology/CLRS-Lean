import CLRSLean.Chapter_33.Section_33_1_Line_Segment_Properties
import CLRSLean.Chapter_33.Section_33_1_Line_Segment_Properties.SharedEndpoint

/-! # Chapter 33 — Computational Geometry

Chapter 33 of CLRS covers computational-geometry algorithms: line-segment
properties, sweep-line segment intersection, convex-hull construction, and
closest-pair finding.

This chapter currently formalizes Section 33.1 with fully proved
cross-product and orientation theorems.

## Sections

### 33.1 Line-Segment Properties

* `CLRS.Chapter33.Point`, `CLRS.Chapter33.Vector` — 2D point and vector types
* `CLRS.Chapter33.cross` — 2D cross product with antisymmetry, bilinearity, and additivity lemmas
* `CLRS.Chapter33.Orientation` — inductive `Counterclockwise | Clockwise | Collinear`
* `CLRS.Chapter33.Segment` — line-segment structure with bounding-box and intersection predicates
* `CLRS.Chapter33.segmentIntersect_of_sharesEndpoint` — every shared endpoint
  is accepted by the CLRS intersection predicate

**Status: `partial`** — six cross-product algebra theorems,
`orientation_spec`, and the shared-endpoint intersection case are proved.  The
`segmentIntersect` and `bboxIntersect` definitions still need full soundness
and completeness against an independent geometric-intersection specification.

## Deferred Work

* 33.1 general correctness of the line-segment intersection predicate,
  beyond the proved shared-endpoint case
* 33.2–33.3 Sweep-line segment intersection and Graham-scan convex hull
* 33.4 Closest-pair divide-and-conquer
-/

namespace CLRS
namespace Chapter33
end Chapter33
end CLRS

import CLRSLean.Chapter_33.Section_33_1_Line_Segment_Properties

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

**Status: `selected-section-complete`** — Section 33.1 is fully proved (7 theorems, 0 sorries).

## Deferred Work

* 33.2–33.3 Sweep-line segment intersection and Graham-scan convex hull
* 33.4 Closest-pair divide-and-conquer
-/

namespace CLRS
namespace Chapter33
end Chapter33
end CLRS

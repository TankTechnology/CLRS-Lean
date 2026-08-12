import Mathlib

/-!
# CLRS §33.1 — Line-Segment Properties

This section formalizes the foundational primitives of computational geometry:
points, vectors, cross products, orientation determination, and line-segment
intersection testing.  It corresponds to §33.1 "Line-segment properties" of the
third edition of CLRS.

## Main contents

- `Point` / `Vector`: definitions of points and vectors in ℝ²
- `cross`: the 2D cross product `p₁ × p₂ = x₁·y₂ - x₂·y₁`
- `orientation`: determines the orientation of three points from the sign of the
  cross product (counterclockwise / clockwise / collinear)
- `Segment`: a segment defined by its two endpoints
- `onBbox` / `bboxIntersect`: bounding-box quick rejection tests
- `segmentIntersect`: the full line-segment intersection condition (based on
  orientation determination plus the collinear special case)

Status: `partial` — the definitions, the cross-product algebra theorems, and
`orientation_spec` are formalized; the soundness and completeness of
`segmentIntersect` with respect to an independent geometric intersection
specification remain to be proved, including the shared-endpoint and collinear
cases.

## Geometric meaning of the cross product

For vectors `p₁ = (x₁, y₁)` and `p₂ = (x₂, y₂)`:
- `cross p₁ p₂ = x₁·y₂ - x₂·y₁`
- its absolute value is the area of the parallelogram spanned by p₁ and p₂
- its sign: positive means p₂ is counterclockwise from p₁, negative means
  clockwise, zero means collinear

For two segments p₀p₁ and p₀p₂ sharing p₀, the orientation is determined by
`cross (p₁ - p₀) (p₂ - p₀)`.

## Line-segment intersection (CLRS algorithm)

For segments s₁ = (p₁, p₂) and s₂ = (p₃, p₄):
1. compute the four orientations: d1 = orientation(p₁,p₂,p₃), d2 = orientation(p₁,p₂,p₄),
                     d3 = orientation(p₃,p₄,p₁), d4 = orientation(p₃,p₄,p₂)
2. in general, d1 ≠ d2 and d3 ≠ d4 means the segments straddle and intersect
3. when an orientation is collinear, check whether the corresponding endpoint
   lies within the other segment's bounding box

Note: because comparisons on `ℝ` are not computable, `orientation` and the
intersection test are `noncomputable`.  For a computable version one should use
the rationals `ℚ` or a finite-precision approximation.
-/

namespace CLRS
namespace Chapter33

/-! ## Points and vectors -/

/-- A point in the plane, represented as `ℝ × ℝ`. -/
abbrev Point := ℝ × ℝ

/-- A vector in the plane, isomorphic to `Point`. -/
abbrev Vector := ℝ × ℝ

/-- The x component of a vector. -/
def x (p : ℝ × ℝ) : ℝ := p.1

/-- The y component of a vector. -/
def y (p : ℝ × ℝ) : ℝ := p.2

/-- Vector addition. -/
def vadd (p q : ℝ × ℝ) : ℝ × ℝ := (p.1 + q.1, p.2 + q.2)

/-- Vector subtraction. -/
def vsub (p q : ℝ × ℝ) : ℝ × ℝ := (p.1 - q.1, p.2 - q.2)

/-- Scalar multiplication. -/
def smul (c : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (c * p.1, c * p.2)

/-! ## Cross product -/

/--
The 2D cross product: `cross p₁ p₂ = x₁·y₂ - x₂·y₁`.

Geometric meaning: taking the origin as the starting point, the absolute value
of `cross p₁ p₂` is the area of the parallelogram spanned by p₁ and p₂; the sign
indicates the direction of rotating p₁ counterclockwise to p₂
(positive = counterclockwise, negative = clockwise).
-/
def cross (p₁ p₂ : ℝ × ℝ) : ℝ :=
  p₁.1 * p₂.2 - p₂.1 * p₁.2

/-- Antisymmetry of the cross product: `cross p q = -(cross q p)`. -/
theorem cross_antisymm (p q : ℝ × ℝ) : cross p q = - cross q p := by
  simp [cross]

/-- Additivity of the cross product in the first argument. -/
theorem cross_add_left (p q r : ℝ × ℝ) : cross (vadd p q) r = cross p r + cross q r := by
  simp [cross, vadd]
  ring

/-- Homogeneity of the cross product under scalar multiplication in the first argument. -/
theorem cross_smul_left (c : ℝ) (p q : ℝ × ℝ) : cross (smul c p) q = c * cross p q := by
  simp [cross, smul]
  ring

/-- The cross product of a vector with itself is zero: `cross p p = 0`. -/
theorem cross_self (p : ℝ × ℝ) : cross p p = 0 := by
  simp [cross]

/-- The cross product of collinear vectors is zero: if `q = c · p`, then `cross p q = 0`. -/
theorem cross_smul_self (c : ℝ) (p : ℝ × ℝ) : cross p (smul c p) = 0 := by
  simp [cross, smul]
  ring

/-- Additivity of the cross product in the second argument (follows from antisymmetry). -/
theorem cross_add_right (p q r : ℝ × ℝ) : cross p (vadd q r) = cross p q + cross p r := by
  simp [cross, vadd]
  ring

/-! ## Orientation -/

/--
The orientation type of three points `(p₀, p₁, p₂)`.

- `Counterclockwise` (counterclockwise / left turn): going from the directed
  segment p₀→p₁ to p₀→p₂ requires a left turn
- `Clockwise` (clockwise / right turn): going from p₀→p₁ to p₀→p₂ requires a right
  turn
- `Collinear` (collinear): the three points lie on a single line
-/
inductive Orientation : Type where
  | Counterclockwise
  | Clockwise
  | Collinear
  deriving DecidableEq, Inhabited

/--
Computes the orientation of three points `(p₀, p₁, p₂)`.

The orientation is determined by the cross product `(p₁ - p₀) × (p₂ - p₀)`:
- `> 0` → `Counterclockwise`
- `< 0` → `Clockwise`
- `= 0` → `Collinear`

Since `>` is not computable on `ℝ`, this definition is `noncomputable`.
-/
noncomputable def orientation (p₀ p₁ p₂ : ℝ × ℝ) : Orientation :=
  let cp := cross (vsub p₁ p₀) (vsub p₂ p₀)
  if h : cp > 0 then Orientation.Counterclockwise
  else if h : cp < 0 then Orientation.Clockwise
  else Orientation.Collinear

/-- The correspondence between an orientation result and the sign of its cross product. -/
theorem orientation_spec (p₀ p₁ p₂ : ℝ × ℝ) :
    let cp := cross (vsub p₁ p₀) (vsub p₂ p₀)
    match orientation p₀ p₁ p₂ with
    | Orientation.Counterclockwise => cp > 0
    | Orientation.Clockwise => cp < 0
    | Orientation.Collinear => cp = 0 := by
  intro cp
  have h_cp : cp = cross (vsub p₁ p₀) (vsub p₂ p₀) := rfl
  rw [h_cp]
  unfold orientation
  by_cases h : cross (vsub p₁ p₀) (vsub p₂ p₀) > 0
  · simp [h]
  · by_cases h' : cross (vsub p₁ p₀) (vsub p₂ p₀) < 0
    · simp [h, h']
    · have : cross (vsub p₁ p₀) (vsub p₂ p₀) = 0 := by linarith
      simp [h, h', this]

/-! ## Line segments -/

/-- A segment is defined by its two endpoints: the start `p` and the end `q`. -/
structure Segment where
  /-- The start of the segment -/
  p : ℝ × ℝ
  /-- The end of the segment -/
  q : ℝ × ℝ
  deriving Inhabited

/-- Creates a segment. -/
def mkSegment (p q : ℝ × ℝ) : Segment := ⟨p, q⟩

/--
Determines whether the point `r` lies in the bounding box of the segment `(p, q)`.

The bounding box is the axis-aligned rectangle with the segment's endpoints as
opposite corners.  This predicate is used in the intersection test to handle
the case where a collinear endpoint lies on the segment.
-/
noncomputable def onBbox (r p q : ℝ × ℝ) : Prop :=
  min p.1 q.1 ≤ r.1 ∧ r.1 ≤ max p.1 q.1 ∧
  min p.2 q.2 ≤ r.2 ∧ r.2 ≤ max p.2 q.2

/-- The bounding box of segment `s`, returned as `(xmin, xmax, ymin, ymax)`. -/
def bbox (s : Segment) : ℝ × ℝ × ℝ × ℝ :=
  (min s.p.1 s.q.1, max s.p.1 s.q.1, min s.p.2 s.q.2, max s.p.2 s.q.2)

/--
Determines whether the bounding boxes of two segments `s1` and `s2` intersect
(a projection overlap test).

This is the quick rejection step of the line-segment intersection test: if the
bounding boxes do not intersect, the segments certainly do not intersect.
-/
noncomputable def bboxIntersect (s1 s2 : Segment) : Prop :=
  let (xmin1, xmax1, ymin1, ymax1) := bbox s1
  let (xmin2, xmax2, ymin2, ymax2) := bbox s2
  (xmin1 ≤ xmax2 ∧ xmin2 ≤ xmax1) ∧ (ymin1 ≤ ymax2 ∧ ymin2 ≤ ymax1)

/-! ## Segment intersection -/

/--
The CLRS §33.1 line-segment intersection test.

Based on orientation determination and bounding-box tests:
1. compute `d1 = orientation(p₁, p₂, p₃)`, `d2 = orientation(p₁, p₂, p₄)`
2. compute `d3 = orientation(p₃, p₄, p₁)`, `d4 = orientation(p₃, p₄, p₂)`
3. in general, `d1 ≠ d2` and `d3 ≠ d4` means the segments straddle and intersect
4. if some orientation is `Collinear`, check whether the corresponding endpoint
   lies in the other segment's bounding box

This is the mathematical formalization of the `SEGMENTS-INTERSECT` algorithm of
CLRS Fig 33.2.
-/
noncomputable def segmentIntersect (s1 s2 : Segment) : Prop :=
  let d1 := orientation s1.p s1.q s2.p
  let d2 := orientation s1.p s1.q s2.q
  let d3 := orientation s2.p s2.q s1.p
  let d4 := orientation s2.p s2.q s1.q
  (d1 ≠ d2 ∧ d3 ≠ d4) ∨
  (d1 = Orientation.Collinear ∧ onBbox s2.p s1.p s1.q) ∨
  (d2 = Orientation.Collinear ∧ onBbox s2.q s1.p s1.q) ∨
  (d3 = Orientation.Collinear ∧ onBbox s1.p s2.p s2.q) ∨
  (d4 = Orientation.Collinear ∧ onBbox s1.q s2.p s2.q)

/--
Determines whether two segments share an endpoint.

This is a special case of intersection: if they share an endpoint, some of the
intersection test's orientations are collinear.

**TODO:** Two segments sharing an endpoint must satisfy `segmentIntersect`.
Proof sketch: a shared endpoint means at least one of the four orientations is
`Collinear`, and the shared endpoint always lies in the other segment's bounding
box.
-/
noncomputable def sharesEndpoint (s1 s2 : Segment) : Prop :=
  s1.p = s2.p ∨ s1.p = s2.q ∨ s1.q = s2.p ∨ s1.q = s2.q

/-! ## Appendix: convenient aliases -/

/-- The point (0, 0) — the origin. -/
def origin : ℝ × ℝ := (0, 0)

/-- The vector from point `p` to `q`. -/
def toVector (p q : ℝ × ℝ) : ℝ × ℝ := vsub q p

end Chapter33
end CLRS

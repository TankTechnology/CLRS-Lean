import CLRSLean.Chapter_33.Section_33_1_Line_Segment_Properties

/-!
# Shared endpoints imply segment intersection

This focused companion closes the endpoint special case of the CLRS
`SEGMENTS-INTERSECT` predicate.  It is supplementary computational-geometry
material and does not belong to the canonical fourth-edition Chapter 33.
-/

namespace CLRS
namespace Chapter33

/-- The start endpoint is in the segment's axis-aligned bounding box. -/
theorem onBbox_left (p q : Point) : onBbox p p q := by
  exact ⟨min_le_left _ _, le_max_left _ _, min_le_left _ _, le_max_left _ _⟩

/-- The end endpoint is in the segment's axis-aligned bounding box. -/
theorem onBbox_right (p q : Point) : onBbox q p q := by
  exact ⟨min_le_right _ _, le_max_right _ _, min_le_right _ _, le_max_right _ _⟩

/-- Repeating the first point makes an orientation collinear. -/
theorem orientation_last_eq_first (p q : Point) :
    orientation p q p = Orientation.Collinear := by
  simp [orientation, cross, vsub]

/-- Repeating the second point makes an orientation collinear. -/
theorem orientation_last_eq_second (p q : Point) :
    orientation p q q = Orientation.Collinear := by
  simp [orientation, cross, vsub]

/-- Two segments that share any endpoint satisfy the CLRS segment-intersection
predicate. -/
theorem segmentIntersect_of_sharesEndpoint {s₁ s₂ : Segment}
    (h : sharesEndpoint s₁ s₂) : segmentIntersect s₁ s₂ := by
  rcases h with hpp | hpq | hqp | hqq
  · unfold segmentIntersect
    right
    right
    right
    left
    exact ⟨by simpa [hpp] using orientation_last_eq_first s₂.p s₂.q,
      by simpa [hpp] using onBbox_left s₂.p s₂.q⟩
  · unfold segmentIntersect
    right
    right
    right
    left
    exact ⟨by simpa [hpq] using orientation_last_eq_second s₂.p s₂.q,
      by simpa [hpq] using onBbox_right s₂.p s₂.q⟩
  · unfold segmentIntersect
    right
    left
    exact ⟨by simpa [hqp] using orientation_last_eq_second s₁.p s₁.q,
      by simpa [hqp] using onBbox_right s₁.p s₁.q⟩
  · unfold segmentIntersect
    right
    right
    left
    exact ⟨by simpa [hqq] using orientation_last_eq_second s₁.p s₁.q,
      by simpa [hqq] using onBbox_right s₁.p s₁.q⟩

end Chapter33
end CLRS

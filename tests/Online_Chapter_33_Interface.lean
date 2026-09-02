import CLRSLean.Chapter_33

/-! # Online computational-geometry shared-endpoint interface -/

namespace CLRS
namespace Chapter33

#check segmentIntersect_of_sharesEndpoint

example :
    segmentIntersect
      (mkSegment ((0 : Real), 0) (2, 0))
      (mkSegment (0, 0) (0, 3)) := by
  apply segmentIntersect_of_sharesEndpoint
  simp [sharesEndpoint, mkSegment]

example :
    segmentIntersect
      (mkSegment ((-2 : Real), 1) (1, 1))
      (mkSegment (1, 1) (1, 4)) := by
  apply segmentIntersect_of_sharesEndpoint
  simp [sharesEndpoint, mkSegment]

end Chapter33
end CLRS

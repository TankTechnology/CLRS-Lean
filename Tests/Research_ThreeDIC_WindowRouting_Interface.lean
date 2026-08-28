import CLRSLean.Research.ThreeDIC.WindowRouting

/-!
# Research interface: local geometry of adjacent repair windows

This interface isolates the geometric bridge from perfect local color diversity
to bounded-hop repair routing.  The first public result bounds the squared grid
distance between arbitrary representatives of adjacent sliding windows.
-/

open CLRS.Research.ThreeDIC

#check inWindow
#check gridDistSq
#check gridDistSq_horizontal_adjacent_windows_le
#check gridDistSq_vertical_adjacent_windows_le
#check windowAdjacent
#check gridDistSq_adjacent_windows_le
#check windowPath_representatives_bounded

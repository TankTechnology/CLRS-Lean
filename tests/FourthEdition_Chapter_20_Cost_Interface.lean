import CLRSLean.FourthEdition.Chapter_20.Section_20_2_BFS
import CLRSLean.FourthEdition.Chapter_20.Section_20_3_DFS.Cost

/-!
# Fourth-edition Chapter 20 cost interface checks

These checks pin the textbook `O(V + E)` work bounds for the native
fourth-edition breadth-first and depth-first search implementations.
-/

namespace CLRS
namespace Chapter22
namespace Graph

#check bfsStateWithCost_cost_le
#check dfsWithCost_result
#check dfsWithCost_cost_eq
#check dfsWithCost_cost_le

end Graph
end Chapter22
end CLRS

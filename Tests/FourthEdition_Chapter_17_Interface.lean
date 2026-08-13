import CLRSLean.FourthEdition.Chapter_17

/-!
# Fourth-edition Chapter 17 interface checks

These checks pin the public theorem interface of the fourth-edition sections
§17.1 (dynamic order statistics), §17.2 (augmenting a data structure), and
§17.3 (interval trees).
-/

namespace CLRS
namespace Chapter14

-- §17.1 dynamic order statistics (OS-RANK)
#check OSRBTree.rankOf
#check OSRBTree.osRank
#check OSRBTree.osRankCost
#check OSRBTree.osRank_eq_rankOf_of_wellSized
#check OSRBTree.toRB_size
#check OSRBTree.osRankCost_le_height
#check OSRBTree.osRankCost_log_bound

-- §17.2 how to augment a data structure
#check augmentationUpdateCost
#check augmentation_update_bound

-- §17.3 interval trees (dynamic/static bridge)
#check IntervalTree.intervalHeight
#check IntervalTree.intervalSearchCost
#check IntervalTree.intervalSearchCost_le_height
#check AugmentedRBTree.toIntervalTree
#check AugmentedRBTree.realAug_toIntervalTree
#check AugmentedRBTree.wellAugmented_toIntervalTree
#check intervalSearch_after_update

/-! The headline theorems must not carry `sorryAx` or any project axiom. -/
#print axioms OSRBTree.osRank_eq_rankOf_of_wellSized
#print axioms OSRBTree.osRankCost_log_bound
#print axioms augmentation_update_bound
#print axioms intervalSearch_after_update

end Chapter14
end CLRS

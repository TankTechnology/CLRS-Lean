import CLRSLean.Chapter_26

/-!
# Chapter 26 Augmentation Interface Test

Protects the public Ford-Fulkerson augmentation, residual-reachability bridge,
and Max-Flow Min-Cut interface.
-/

#check CLRS.Chapter26.Flow.ResidualPath
#check CLRS.Chapter26.Flow.AugmentingPath
#check CLRS.Chapter26.Flow.ResidualPath.edges
#check CLRS.Chapter26.Flow.ResidualPath.residualEdge_of_mem_edges
#check CLRS.Chapter26.Flow.AugmentingPath.edges_nonempty
#check CLRS.Chapter26.Flow.AugmentingPath.bottleneck
#check CLRS.Chapter26.Flow.AugmentingPath.bottleneck_pos
#check CLRS.Chapter26.Flow.AugmentingPath.bottleneck_le_residualCapacity
#check CLRS.Chapter26.Flow.augmentBy
#check CLRS.Chapter26.Flow.augment
#check CLRS.Chapter26.Flow.augmentBy_value
#check CLRS.Chapter26.Flow.augment_value
#check CLRS.Chapter26.Flow.value_lt_augment
#check CLRS.Chapter26.Flow.hasAugmentingPath_iff_nonempty_augmentingPath
#check CLRS.Chapter26.Flow.not_maximal_of_augmentingPath
#check CLRS.Chapter26.Flow.not_maximal_of_hasAugmentingPath
#check CLRS.Chapter26.Flow.exists_cut_value_eq_of_noAugmentingPath
#check CLRS.Chapter26.Flow.maximal_iff_noAugmentingPath
#check CLRS.Chapter26.Flow.maximal_iff_exists_cut_value_eq

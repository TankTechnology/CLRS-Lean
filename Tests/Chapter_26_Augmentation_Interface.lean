import CLRSLean.Chapter_26

/-!
# Chapter 26 Augmentation Interface Test

Protects the public Ford-Fulkerson augmentation surface.  This test is added
before the implementation so its initial unknown-identifier failure records the
intended interface.
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

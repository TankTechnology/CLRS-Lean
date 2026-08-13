import CLRSLean.Chapter_26

/-!
# Chapter 26 Push-Relabel Interface Test

Verifies the public declarations of the §26.4 push-relabel formalization.
-/

-- Preflow model
#check CLRS.Chapter26.Preflow
#check CLRS.Chapter26.Preflow.excess
#check CLRS.Chapter26.Preflow.isOverflowing
#check CLRS.Chapter26.Preflow.residualCapacity
#check CLRS.Chapter26.Preflow.residualEdge
#check CLRS.Chapter26.Preflow.hasAugmentingPath
#check CLRS.Chapter26.Preflow.toFlow

-- Height functions and admissible edges
#check CLRS.Chapter26.IsValidHeight
#check CLRS.Chapter26.admissibleEdge

-- Operations
#check CLRS.Chapter26.Preflow.pushBy
#check CLRS.Chapter26.Preflow.push
#check CLRS.Chapter26.relabel
#check CLRS.Chapter26.Preflow.pushBy_validHeight
#check CLRS.Chapter26.relabel_validHeight

-- Height bound
#check CLRS.Chapter26.exists_residualEdge_of_overflowing
#check CLRS.Chapter26.exists_residualPath_to_source_of_overflowing
#check CLRS.Chapter26.height_le_of_overflowing

-- Correctness
#check CLRS.Chapter26.maximal_of_no_overflow

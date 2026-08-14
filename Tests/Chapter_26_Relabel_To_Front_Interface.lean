import CLRSLean.Chapter_26

/-!
# Chapter 26 Relabel-to-Front Interface Test

Verifies the public declarations of the §26.5 relabel-to-front / generic
push-relabel counting formalization.
-/

-- The number of edges
#check CLRS.Chapter26.numEdges

-- Basic operations and runs
#check CLRS.Chapter26.BasicOp
#check CLRS.Chapter26.BasicOp.isRelabel
#check CLRS.Chapter26.BasicOp.isSaturatingPush
#check CLRS.Chapter26.BasicOp.isNonsaturatingPush
#check CLRS.Chapter26.BasicOp.classification
#check CLRS.Chapter26.BasicOp.opVertex
#check CLRS.Chapter26.Run

-- Counting bounds
#check CLRS.Chapter26.Run.height_mono
#check CLRS.Chapter26.Run.relabel_count_bound
#check CLRS.Chapter26.Run.saturating_push_count_bound
#check CLRS.Chapter26.Run.nonsaturating_push_count_bound
#check CLRS.Chapter26.Run.generic_step_count_bound

-- The relabel-to-front discharge order (O(V^3) bound)
#check CLRS.Chapter26.numEdges_le_card_mul_card
#check CLRS.Chapter26.RelabelToFrontRun
#check CLRS.Chapter26.RelabelToFrontRun.relabelsBefore
#check CLRS.Chapter26.RelabelToFrontRun.relabelsBefore_le_numRelabels
#check CLRS.Chapter26.RelabelToFrontRun.nonsaturating_push_count_bound
#check CLRS.Chapter26.RelabelToFrontRun.step_count_bound
#check CLRS.Chapter26.RelabelToFrontRun.step_count_bound_V3

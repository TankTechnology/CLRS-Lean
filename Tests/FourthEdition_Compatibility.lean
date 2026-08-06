import CLRSLean.OnlineMaterial
import CLRSLean.FourthEdition.Chapter_14
import CLRSLean.FourthEdition.Chapter_17
import CLRSLean.FourthEdition.Chapter_19
import CLRSLean.FourthEdition.Chapter_24
import CLRSLean.FourthEdition.Chapter_26
import CLRSLean.Chapter_14
import CLRSLean.Chapter_15
import CLRSLean.Chapter_21
import CLRSLean.Chapter_26
import CLRSLean.Chapter_27

/-!
# CLRS fourth-edition compatibility checks

These checks protect representative third-edition-numbered imports, their
shifted fourth-edition facades, and public declarations retained as online or
supplementary material.
-/

-- Representative declarations reached through shifted legacy and facade paths.
#check CLRS.Chapter15.matrixChain_correct
#check CLRS.Chapter14.IntervalTree.intervalSearch?_spec
#check CLRS.Chapter21.Forest.singletonForest
#check CLRS.Chapter26.Flow.maximal_of_noAugmentingPath
#check CLRS.Chapter27.CompDAG.greedySchedule

-- Third-edition-only or moved content collected by `CLRSLean.OnlineMaterial`.
#check CLRS.Chapter19.FH.extractMin_correct
#check CLRS.Chapter20.VEBTreeMM.delete_correct
#check CLRS.Chapter33.orientation_spec
#check CLRS.Chapter04.maxSubarrayDivideCosted_correct
#check CLRS.Chapter11.perfectSearch_iff_mem
#check CLRS.Matroid16.greedy_optimal
#check CLRS.SchedulingMatroid.minPenaltySchedule_correct
#check CLRS.Chapter29.Dictionary.simplex_optimal_or_unbounded
#check CLRS.Chapter29.StandardLP.initializedSimplex_complete
#check CLRS.Chapter30.iterativeRadix2FFT_eq_dft
#check CLRS.Chapter31.rho_collision_factor

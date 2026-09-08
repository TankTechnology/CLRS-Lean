import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_24

/-! # Chapter 24 flagship trust surface -/

#check CLRS.Chapter26.edmondsKarp_maximal
#check CLRS.Chapter26.augmentation_count_bound
#check CLRS.Chapter26.Flow.maximal_iff_exists_cut_value_eq

#assert_axioms CLRS.Chapter26.edmondsKarp_maximal
#assert_axioms CLRS.Chapter26.augmentation_count_bound
#assert_axioms CLRS.Chapter26.Flow.maximal_iff_exists_cut_value_eq

example :
    let G : CLRS.Chapter26.FlowNetwork Bool :=
      { c := fun _ _ => 0
        s := false
        t := true
        hc_nonneg := by simp
        hc_self := by simp
        hs_ne_t := by decide }
    let φ : CLRS.Chapter26.Flow Bool G :=
      { f := fun _ _ => 0
        hcapacity := by simp [G]
        hskew_symm := by simp
        hconservation := by simp }
    φ.value = 0 := by
  simp [CLRS.Chapter26.Flow.value]

#assert_axioms CLRS.Chapter26.SparseEK.execute_maximal
#assert_axioms CLRS.Chapter26.SparseEK.execute_augmentations_le
#assert_axioms CLRS.Chapter26.SparseEK.execute_work_bound
#assert_axioms CLRS.Chapter26.SparseEK.execute_work_empty

#assert_axioms CLRS.Chapter26.RelabelExecution.initial_valid
#assert_axioms CLRS.Chapter26.RelabelExecution.Trace.toRelabelToFrontRun
#assert_axioms CLRS.Chapter26.RelabelExecution.execute_terminal
#assert_axioms CLRS.Chapter26.RelabelExecution.initialized_maximum_flow
#assert_axioms CLRS.Chapter26.RelabelExecution.initialized_work_le_cubic
#assert_axioms CLRS.Chapter26.RelabelExecution.initialized_correct_and_cost
#assert_axioms CLRS.Chapter26.SparseEK.execute_work_uniform

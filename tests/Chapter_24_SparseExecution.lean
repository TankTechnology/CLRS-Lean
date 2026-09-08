import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_24.Section_24_2_Edmonds_Karp.S5_SparseExecution
open CLRS.Chapter26 CLRS.Chapter26.SparseEK Finset
noncomputable section

#assert_axioms residual_mem_support
#assert_axioms CapacityInput.prepare_storage
#assert_axioms bfs_work_le
#assert_axioms Timeline.augmentation_count_sparse
#assert_axioms recoverParents_spec
#assert_axioms search_none_iff
#assert_axioms augmentWithCost_refines
#assert_axioms augmentWithCost_work
#assert_axioms execute_maximal
#assert_axioms execute_augmentations_le
#assert_axioms execute_work_bound
#assert_axioms execute_work_empty
#assert_axioms execute_work_uniform

-- Actual stored-parent traversal, including the root and absent-parent boundaries.
example : (recoverParents (fun v : Nat => if v=2 then some 1 else if v=1 then some 0 else none)
    2 2).vertices = [0,1,2] := by decide
example : (recoverParents (fun v : Nat => if v=2 then some 1 else if v=1 then some 0 else none)
    2 2).work = 8 := by decide
example : (recoverParents (fun _ : Nat => none) 0 7).vertices = [7] := by decide
example : (recoverParents (fun _ : Nat => none) 3 7).work = 3 := by decide
example : (edgesWithCost ([0,1,2] : List Nat)).1 = [(0,1),(1,2)] := by decide
example : (edgesWithCost ([] : List Nat)).2 = 0 := by decide

-- Both flow directions update, and unrelated entries remain unchanged.
example : (updateAll (fun _ : Nat × Nat => 0) 3 [(0,1),(1,2)]).cells (1,0) = -3 := by
  norm_num [updateAll,pushPair,bump,Function.update]
example : (updateAll (fun _ : Nat × Nat => 0) 3 [(0,1),(1,2)]).cells (0,2) = 0 := by
  norm_num [updateAll,pushPair,bump,Function.update]
example : (updateAll (fun _ : Nat × Nat => 0) 3 [(0,1),(1,2)]).work = 8 := by
  simp [updateAll_work]

-- Arbitrarily many isolated vertices do not reintroduce V into each BFS bound.
private def oneArc (n : Nat) : FlowNetwork (Fin (n+2)) where
  c u v := if u=0 ∧ v=1 then 1 else 0
  s := 0
  t := 1
  hc_nonneg u v := by split <;> norm_num
  hc_self u := by
    split
    · rename_i h
      have : (0 : Fin (n+2)) = 1 := h.1.symm.trans h.2
      have := congrArg Fin.val this
      simp at this
    · rfl
  hs_ne_t := by intro h; have := congrArg Fin.val h; simp at this

private def oneArcInput (n : Nat) : CapacityInput (oneArc n) where
  arcs := [(0,1)]
  nodup := by simp
  mem_iff u v := by simp [oneArc]; split <;> simp_all

private theorem oneArc_card (n : Nat) : (positiveArcs (oneArc n)).card = 1 := by
  simpa [oneArcInput] using (oneArcInput n).length_eq.symm

example (n : Nat) : (execute (oneArcInput n)).flow.isMaximal := execute_maximal _
example (n : Nat) : (execute (oneArcInput n)).augmentations ≤ 2*(n+2) := by
  simpa [oneArc_card] using execute_augmentations_le (oneArcInput n)
example (n : Nat) : (execute (oneArcInput n)).work ≤ 130*(n+2) := by
  simpa [oneArc_card] using execute_work_bound (oneArcInput n) (by rw [oneArc_card]; omega)
example (n : Nat) : (costedResidualBFS (prepare (oneArcInput n).arcs).adjacency
    (zeroFlow (oneArc n))).work ≤ 11 := by
  have hb := bfs_work_le (oneArcInput n) (zeroFlow (oneArc n))
  have hs := support_card_le (oneArc n)
  rw [oneArc_card] at hs
  omega

private def noArcs : FlowNetwork (Fin 2) where
  c _ _ := 0
  s := 0
  t := 1
  hc_nonneg _ _ := le_rfl
  hc_self _ := rfl
  hs_ne_t := by decide
private def noArcsInput : CapacityInput noArcs where
  arcs := []
  nodup := by simp
  mem_iff _ _ := by simp [noArcs]
private theorem noArcs_card : (positiveArcs noArcs).card = 0 := by
  simpa [noArcsInput] using noArcsInput.length_eq.symm
example : (execute noArcsInput).flow.isMaximal := execute_maximal _
example : (execute noArcsInput).augmentations = 0 := by
  have := execute_augmentations_le noArcsInput
  simpa [noArcs_card] using this
example : (execute noArcsInput).work ≤ 4 := by
  simpa using execute_work_empty noArcsInput noArcs_card

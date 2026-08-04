import CLRSLean.Chapter_27.Section_27_1_Multithreading_Model.S3_GreedyAccounting

/-!
# 27.1 S4. Executable scheduler

Deterministic ready-set selection and the resulting certified greedy step.

The scheduler chooses the first ready vertices in increasing vertex order, up
to the processor count.  The resulting finite set carries the readiness and
maximal-cardinality proofs required by the certified schedule-step structure.
-/

namespace CLRS
namespace Chapter27
namespace CompDAG

/-- The first `processors` ready vertices in increasing vertex order. -/
def readyRun (G : CompDAG) (remaining : ℕ → ℕ) (processors : ℕ) : Finset ℕ :=
  (((G.ready remaining).sort (· ≤ ·)).take processors).toFinset

/-- Every vertex selected by {name}`readyRun` is ready in the current state. -/
theorem readyRun_subset_ready (G : CompDAG) (remaining : ℕ → ℕ)
    (processors : ℕ) :
    G.readyRun remaining processors ⊆ G.ready remaining := by
  intro v hv
  simp only [readyRun, List.mem_toFinset] at hv
  exact (Finset.mem_sort (· ≤ ·)).mp (List.mem_of_mem_take hv)

/-- {name}`readyRun` fills every processor unless fewer ready vertices exist. -/
theorem readyRun_card (G : CompDAG) (remaining : ℕ → ℕ)
    (processors : ℕ) :
    (G.readyRun remaining processors).card =
      min processors (G.ready remaining).card := by
  rw [readyRun, List.toFinset_card_of_nodup]
  · simp
  · exact (List.take_sublist processors _).nodup
      (Finset.sort_nodup (G.ready remaining) (· ≤ ·))

/-- Positive residual work guarantees that at least one vertex is ready. -/
theorem ready_nonempty_of_remainingWork_pos (G : CompDAG)
    (remaining : ℕ → ℕ) (hwork : 0 < G.remainingWork remaining) :
    (G.ready remaining).Nonempty := by
  by_contra hready
  have hempty : G.ready remaining = ∅ := Finset.not_nonempty_iff_eq_empty.mp hready
  have hexecute_empty : G.execute remaining ∅ = remaining := by
    funext v
    simp [execute]
  have hdrop := G.remainingSpan_execute_ready_add_one_le remaining hwork
  rw [hempty, hexecute_empty] at hdrop
  omega

/-- The deterministic ready prefix packaged as one certified greedy step. -/
def greedyStep (G : CompDAG) (remaining : ℕ → ℕ) (processors : ℕ) :
    DAGScheduleStep G processors where
  remaining := remaining
  run := G.readyRun remaining processors
  run_subset_ready := G.readyRun_subset_ready remaining processors
  run_card_eq_min := G.readyRun_card remaining processors

end CompDAG

end Chapter27
end CLRS

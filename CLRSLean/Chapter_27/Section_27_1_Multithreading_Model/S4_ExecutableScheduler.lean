import CLRSLean.Chapter_27.Section_27_1_Multithreading_Model.S3_GreedyAccounting

/-!
# 27.1 S4. Executable scheduler

Deterministic ready-set selection and the resulting certified greedy step.

The scheduler chooses the first ready vertices in increasing vertex order, up
to the processor count.  The resulting finite set carries the readiness and
maximal-cardinality proofs required by the certified schedule-step structure.
Positive residual work therefore yields a nonempty run and strictly decreases
the residual-work measure.  Recursing on that measure constructs a total,
deterministic greedy schedule and exposes the CLRS Graham--Brent bound.
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

/-- With at least one processor, positive residual work makes the deterministic
ready prefix nonempty.  This is the progress fact used by the total scheduler. -/
theorem readyRun_nonempty (G : CompDAG) (remaining : ℕ → ℕ)
    (processors : ℕ) (hp : 0 < processors)
    (hwork : 0 < G.remainingWork remaining) :
    (G.readyRun remaining processors).Nonempty := by
  have hready : (G.ready remaining).Nonempty :=
    G.ready_nonempty_of_remainingWork_pos remaining hwork
  have hready_card : 0 < (G.ready remaining).card := Finset.card_pos.mpr hready
  apply Finset.card_pos.mp
  rw [G.readyRun_card remaining processors]
  exact lt_min hp hready_card

/-- The deterministic ready prefix packaged as one certified greedy step. -/
def greedyStep (G : CompDAG) (remaining : ℕ → ℕ) (processors : ℕ) :
    DAGScheduleStep G processors where
  remaining := remaining
  run := G.readyRun remaining processors
  run_subset_ready := G.readyRun_subset_ready remaining processors
  run_card_eq_min := G.readyRun_card remaining processors

/-- Every active deterministic greedy step strictly decreases residual work
when at least one processor is available. -/
theorem remainingWork_greedyStep_after_lt (G : CompDAG)
    (remaining : ℕ → ℕ) (processors : ℕ) (hp : 0 < processors)
    (hwork : 0 < G.remainingWork remaining) :
    G.remainingWork (G.greedyStep remaining processors).after <
      G.remainingWork remaining := by
  have hrun : (G.readyRun remaining processors).Nonempty :=
    G.readyRun_nonempty remaining processors hp hwork
  have hcard : 0 < (G.readyRun remaining processors).card :=
    Finset.card_pos.mpr hrun
  have hbalance :
      G.remainingWork (G.greedyStep remaining processors).after +
          (G.readyRun remaining processors).card =
        G.remainingWork remaining :=
    (G.greedyStep remaining processors).remainingWork_after_add_card
  omega

/-- Construct the terminating deterministic greedy schedule from any residual
state.  Recursion is well-founded because each active step strictly decreases
the finite residual-work measure. -/
def greedyScheduleFrom (G : CompDAG) (processors : ℕ) (hp : 0 < processors) :
    (remaining : ℕ → ℕ) → DAGSchedule G processors remaining :=
  fun remaining =>
    if hcomplete : G.remainingWork remaining = 0 then
      DAGSchedule.done remaining hcomplete
    else
      have hactive : 0 < G.remainingWork remaining := Nat.pos_of_ne_zero hcomplete
      DAGSchedule.step (G.greedyStep remaining processors) hactive
        (G.greedyScheduleFrom processors hp
          (G.greedyStep remaining processors).after)
termination_by remaining => G.remainingWork remaining
decreasing_by
  exact G.remainingWork_greedyStep_after_lt remaining processors hp hactive

/-- The terminating deterministic greedy schedule from the DAG's initial node
work. -/
def greedySchedule (G : CompDAG) (processors : ℕ) (hp : 0 < processors) :
    DAGSchedule G processors G.node_work :=
  G.greedyScheduleFrom processors hp G.node_work

/-- The constructed greedy schedule terminates only at a zero-work residual
state. -/
theorem greedySchedule_final_work_eq_zero (G : CompDAG) (processors : ℕ)
    (hp : 0 < processors) :
    G.remainingWork (G.greedySchedule processors hp).finalState = 0 :=
  (G.greedySchedule processors hp).final_work_eq_zero

/-- The constructed deterministic greedy schedule satisfies the CLRS
Graham--Brent bound `Tₚ ≤ T₁ / p + T∞`. -/
theorem greedySchedule_time_le_work_div_add_span (G : CompDAG)
    (processors : ℕ) (hp : 0 < processors) :
    (G.greedySchedule processors hp).time ≤
      G.work / processors + G.span :=
  (G.greedySchedule processors hp).time_le_work_div_add_span hp

end CompDAG

end Chapter27
end CLRS

import CLRSLean.Chapter_27

namespace CLRS.Chapter27

#check CompDAG.readyRun
#check CompDAG.readyRun_subset_ready
#check CompDAG.readyRun_card
#check CompDAG.ready_nonempty_of_remainingWork_pos
#check CompDAG.readyRun_nonempty
#check CompDAG.greedyStep
#check CompDAG.remainingWork_greedyStep_after_lt
#check CompDAG.greedyScheduleFrom
#check CompDAG.greedySchedule
#check CompDAG.greedySchedule_final_work_eq_zero
#check CompDAG.greedySchedule_time_le_work_div_add_span

/-- An initially complete DAG exercises the scheduler's immediate done branch. -/
def schedulerZeroDAG : CompDAG where
  n := 1
  node_work := fun _ => 0
  edges := []
  h_edges_in_bounds := by decide
  h_edges_forward := by decide

/-- The zero-step two-processor schedule for {name}`schedulerZeroDAG`. -/
def schedulerZeroSchedule : DAGSchedule schedulerZeroDAG 2 schedulerZeroDAG.node_work :=
  schedulerZeroDAG.greedySchedule 2 (by decide)

example : schedulerZeroSchedule.time = 0 := by native_decide

example : schedulerZeroDAG.remainingWork schedulerZeroSchedule.finalState = 0 := by
  native_decide

example : schedulerZeroSchedule.finalState 0 = 0 := by native_decide

/-- A single unit-work node exercises the scheduler's active and done branches. -/
def schedulerUnitDAG : CompDAG where
  n := 1
  node_work := fun i => if i = 0 then 1 else 0
  edges := []
  h_edges_in_bounds := by decide
  h_edges_forward := by decide

/-- The deterministic one-processor schedule for {name}`schedulerUnitDAG`. -/
def schedulerUnitSchedule : DAGSchedule schedulerUnitDAG 1 schedulerUnitDAG.node_work :=
  schedulerUnitDAG.greedySchedule 1 (by decide)

example : schedulerUnitSchedule.time = 1 := by native_decide

example : schedulerUnitDAG.remainingWork schedulerUnitSchedule.finalState = 0 := by
  native_decide

example : schedulerUnitSchedule.time ≤
    schedulerUnitDAG.work / 1 + schedulerUnitDAG.span :=
  schedulerUnitDAG.greedySchedule_time_le_work_div_add_span 1 (by decide)

/-- A single node with three work units stays ready across three executions. -/
def schedulerWorkThreeDAG : CompDAG where
  n := 1
  node_work := fun i => if i = 0 then 3 else 0
  edges := []
  h_edges_in_bounds := by decide
  h_edges_forward := by decide

/-- The one-processor schedule that revisits the still-active node three times. -/
def schedulerWorkThreeSchedule :
    DAGSchedule schedulerWorkThreeDAG 1 schedulerWorkThreeDAG.node_work :=
  schedulerWorkThreeDAG.greedySchedule 1 (by decide)

example : schedulerWorkThreeSchedule.time = 3 := by native_decide

example :
    schedulerWorkThreeDAG.remainingWork schedulerWorkThreeSchedule.finalState = 0 := by
  native_decide

/-- A unit-work fork whose two children become ready together after node zero. -/
def schedulerForkDAG : CompDAG where
  n := 3
  node_work := fun i => if i < 3 then 1 else 0
  edges := [(0, 1), (0, 2)]
  h_edges_in_bounds := by decide
  h_edges_forward := by decide

/-- Residual fork state after its root has executed once. -/
def schedulerForkAfterRoot : ℕ → ℕ :=
  schedulerForkDAG.execute schedulerForkDAG.node_work {0}

example : schedulerForkDAG.readyRun schedulerForkAfterRoot 1 = {1} := by
  native_decide

example : schedulerForkDAG.readyRun schedulerForkAfterRoot 2 = {1, 2} := by
  native_decide

/-- The deterministic serial schedule for {name}`schedulerForkDAG`. -/
def schedulerForkScheduleOne :
    DAGSchedule schedulerForkDAG 1 schedulerForkDAG.node_work :=
  schedulerForkDAG.greedySchedule 1 (by decide)

/-- The deterministic two-processor schedule for {name}`schedulerForkDAG`. -/
def schedulerForkScheduleTwo :
    DAGSchedule schedulerForkDAG 2 schedulerForkDAG.node_work :=
  schedulerForkDAG.greedySchedule 2 (by decide)

example : schedulerForkScheduleOne.time = 3 := by native_decide

example : schedulerForkScheduleTwo.time = 2 := by native_decide

example : schedulerForkDAG.remainingWork schedulerForkScheduleOne.finalState = 0 := by
  native_decide

example : schedulerForkDAG.remainingWork schedulerForkScheduleTwo.finalState = 0 := by
  native_decide

example : schedulerForkScheduleOne.time ≤
    schedulerForkDAG.work / 1 + schedulerForkDAG.span :=
  schedulerForkDAG.greedySchedule_time_le_work_div_add_span 1 (by decide)

example : schedulerForkScheduleTwo.time ≤
    schedulerForkDAG.work / 2 + schedulerForkDAG.span :=
  schedulerForkDAG.greedySchedule_time_le_work_div_add_span 2 (by decide)

#check parallelLoopDepth_le_log
#check parallelLoop_span_le_log

end CLRS.Chapter27

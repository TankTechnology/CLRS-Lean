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

/-- A unit-work fork whose two children become ready together after node zero. -/
def schedulerForkDAG : CompDAG where
  n := 3
  node_work := fun i => if i < 3 then 1 else 0
  edges := [(0, 1), (0, 2)]
  h_edges_in_bounds := by decide
  h_edges_forward := by decide

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

end CLRS.Chapter27

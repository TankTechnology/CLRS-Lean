import CLRSLean.FourthEdition.Chapter_26.Section_26_1_Multithreading_Model.S2_ReadyExecution

/-!
# 26.1 S3. Greedy accounting

Greedy-schedule accounting certificates, traces, concrete DAG steps, and the
CLRS work/span running-time bound.
-/

namespace CLRS
namespace Chapter27

/-! ## Greedy-scheduler accounting

CLRS partitions a greedy execution into complete steps, which execute one
strand on every processor, and incomplete steps, which execute every ready
strand.  Complete steps are paid for by total work; incomplete steps are paid
for by a unit decrease in the remaining span.  This structure records exactly
the two obligations needed by that argument, independently of the concrete DAG
execution representation that produces them. -/

/-- The accounting certificate extracted from a greedy schedule.

`completeSteps` steps each consume `processors` units of work, while the number
of `incompleteSteps` is bounded by the initial span. -/
structure GreedyScheduleAccounting where
  /-- Number of processors used by the schedule. -/
  processors : ℕ
  /-- Total work `T₁` of the computation. -/
  totalWork : ℕ
  /-- Initial span `T∞` of the computation. -/
  totalSpan : ℕ
  /-- Number of time steps that use every processor. -/
  completeSteps : ℕ
  /-- Number of time steps that execute fewer than all processors. -/
  incompleteSteps : ℕ
  /-- A schedule has at least one processor. -/
  processors_pos : 0 < processors
  /-- Complete steps cannot consume more than the available total work. -/
  complete_work_bound : completeSteps * processors ≤ totalWork
  /-- Every incomplete step consumes at least one unit of remaining span. -/
  incomplete_span_bound : incompleteSteps ≤ totalSpan

namespace GreedyScheduleAccounting

/-- Parallel running time is the number of complete plus incomplete steps. -/
def time (A : GreedyScheduleAccounting) : ℕ :=
  A.completeSteps + A.incompleteSteps

/-- CLRS Theorems 26.1/26.2 at the accounting boundary:
`Tₚ ≤ T₁ / p + T∞`. -/
theorem time_le_work_div_add_span (A : GreedyScheduleAccounting) :
    A.time ≤ A.totalWork / A.processors + A.totalSpan := by
  have hcomplete : A.completeSteps ≤ A.totalWork / A.processors :=
    (Nat.le_div_iff_mul_le A.processors_pos).2 A.complete_work_bound
  exact Nat.add_le_add hcomplete A.incomplete_span_bound

end GreedyScheduleAccounting

/-! ## Greedy-schedule traces -/

/-- Whether a greedy-schedule step keeps every processor busy or exhausts the
currently ready strands before doing so. -/
inductive GreedyStepKind where
  | complete
  | incomplete
deriving Repr, DecidableEq

/-- A finite greedy-schedule trace together with the two global bounds that
justify its complete and incomplete steps.  Unlike
`GreedyScheduleAccounting`, this representation retains the order of steps. -/
structure GreedyScheduleTrace where
  /-- Number of processors used by the schedule. -/
  processors : ℕ
  /-- Total work `T₁` of the computation. -/
  totalWork : ℕ
  /-- Initial span `T∞` of the computation. -/
  totalSpan : ℕ
  /-- Complete and incomplete steps, in execution order. -/
  steps : List GreedyStepKind
  /-- A schedule has at least one processor. -/
  processors_pos : 0 < processors
  /-- The complete steps cannot consume more than the available work. -/
  complete_work_bound : steps.count .complete * processors ≤ totalWork
  /-- The incomplete steps cannot outnumber the initial span. -/
  incomplete_span_bound : steps.count .incomplete ≤ totalSpan

namespace GreedyScheduleTrace

/-- Parallel running time is the number of recorded schedule steps. -/
def time (S : GreedyScheduleTrace) : ℕ :=
  S.steps.length

/-- Forget step order and retain the accounting data used by the bound. -/
def accounting (S : GreedyScheduleTrace) : GreedyScheduleAccounting where
  processors := S.processors
  totalWork := S.totalWork
  totalSpan := S.totalSpan
  completeSteps := S.steps.count .complete
  incompleteSteps := S.steps.count .incomplete
  processors_pos := S.processors_pos
  complete_work_bound := S.complete_work_bound
  incomplete_span_bound := S.incomplete_span_bound

private theorem count_complete_add_count_incomplete
    (steps : List GreedyStepKind) :
    steps.count .complete + steps.count .incomplete = steps.length := by
  induction steps with
  | nil => simp
  | cons step steps ih =>
      cases step <;> simp <;> omega

/-- The schedule-trace form of the greedy-scheduler bound:
`Tₚ ≤ T₁ / p + T∞`. -/
theorem time_le_work_div_add_span (S : GreedyScheduleTrace) :
    S.time ≤ S.totalWork / S.processors + S.totalSpan := by
  have h := S.accounting.time_le_work_div_add_span
  rw [GreedyScheduleAccounting.time] at h
  rw [time, ← count_complete_add_count_incomplete S.steps]
  exact h

end GreedyScheduleTrace

/-! ## Per-step greedy-schedule accounting -/

/-- The metric changes caused by one greedy-schedule step. -/
structure GreedyScheduleStep where
  /-- Whether the step filled every processor. -/
  kind : GreedyStepKind
  /-- Amount of remaining work consumed by the step. -/
  workConsumed : ℕ
  /-- Amount by which the remaining span decreases. -/
  spanDecrease : ℕ
deriving Repr, DecidableEq

/-! ## Concrete computation-DAG steps -/

/-- One greedy time step over an explicit residual `CompDAG` state.

`run` contains only ready nodes and has the largest cardinality allowed by the
processor count.  Thus an incomplete step necessarily executes every ready
node. -/
structure DAGScheduleStep (G : CompDAG) (processors : ℕ) where
  /-- Work remaining at every DAG node before the step. -/
  remaining : ℕ → ℕ
  /-- Ready nodes selected for one unit of execution. -/
  run : Finset ℕ
  /-- Only ready nodes may execute. -/
  run_subset_ready : run ⊆ G.ready remaining
  /-- A greedy step uses as many processors as the ready set permits. -/
  run_card_eq_min : run.card = min processors (G.ready remaining).card

namespace DAGScheduleStep

/-- Residual state after executing the selected ready nodes. -/
def after {G : CompDAG} {processors : ℕ}
    (S : DAGScheduleStep G processors) : ℕ → ℕ :=
  G.execute S.remaining S.run

/-- A step is complete exactly when it fills every processor. -/
def kind {G : CompDAG} {processors : ℕ}
    (S : DAGScheduleStep G processors) : GreedyStepKind :=
  if S.run.card = processors then .complete else .incomplete

/-- Expose a concrete DAG step at the per-step accounting boundary. -/
def metricStep {G : CompDAG} {processors : ℕ}
    (S : DAGScheduleStep G processors) : GreedyScheduleStep where
  kind := S.kind
  workConsumed := S.run.card
  spanDecrease := G.remainingSpan S.remaining - G.remainingSpan S.after

theorem kind_eq_complete_iff {G : CompDAG} {processors : ℕ}
    (S : DAGScheduleStep G processors) :
    S.kind = .complete ↔ S.run.card = processors := by
  simp [kind]

theorem kind_eq_incomplete_iff {G : CompDAG} {processors : ℕ}
    (S : DAGScheduleStep G processors) :
    S.kind = .incomplete ↔ S.run.card ≠ processors := by
  simp [kind]

/-- The concrete residual-work balance for one DAG step. -/
theorem remainingWork_after_add_card {G : CompDAG} {processors : ℕ}
    (S : DAGScheduleStep G processors) :
    G.remainingWork S.after + S.run.card = G.remainingWork S.remaining := by
  exact G.remainingWork_execute_add_card S.remaining S.run S.run_subset_ready

/-- The accounting work obligation is automatic for complete DAG steps. -/
theorem complete_progress {G : CompDAG} {processors : ℕ}
    (S : DAGScheduleStep G processors) (hcomplete : S.kind = .complete) :
    processors ≤ S.metricStep.workConsumed := by
  have hcard := (S.kind_eq_complete_iff).mp hcomplete
  simp [metricStep, hcard]

/-- If a greedy step is incomplete, it executes the entire ready set. -/
theorem incomplete_run_eq_ready {G : CompDAG} {processors : ℕ}
    (S : DAGScheduleStep G processors) (hincomplete : S.kind = .incomplete) :
    S.run = G.ready S.remaining := by
  have hcard_ne : S.run.card ≠ processors :=
    (S.kind_eq_incomplete_iff).mp hincomplete
  have hready_lt : (G.ready S.remaining).card < processors := by
    by_contra hnot
    have hprocessors_le : processors ≤ (G.ready S.remaining).card :=
      Nat.le_of_not_gt hnot
    have : S.run.card = processors := by
      rw [S.run_card_eq_min, Nat.min_eq_left hprocessors_le]
    exact hcard_ne this
  have hcards : S.run.card = (G.ready S.remaining).card := by
    rw [S.run_card_eq_min, Nat.min_eq_right (Nat.le_of_lt hready_lt)]
  exact Finset.eq_of_subset_of_card_le S.run_subset_ready hcards.ge

/-- The accounting span obligation is automatic for every active incomplete
DAG step. -/
theorem incomplete_progress {G : CompDAG} {processors : ℕ}
    (S : DAGScheduleStep G processors)
    (hactive : 0 < G.remainingWork S.remaining)
    (hincomplete : S.kind = .incomplete) :
    1 ≤ S.metricStep.spanDecrease := by
  have hrun := S.incomplete_run_eq_ready hincomplete
  have hdrop := G.remainingSpan_execute_ready_add_one_le S.remaining hactive
  simp only [metricStep, after]
  rw [hrun]
  omega

end DAGScheduleStep

/-! ## Chained computation-DAG schedules -/

/-- A type-safe sequence of active greedy DAG steps ending at zero work.

The index is the initial residual state.  In the `step` constructor the tail is
indexed by `S.after`, so consecutive states agree by construction; `done`
requires that no work remains. -/
inductive DAGSchedule (G : CompDAG) (processors : ℕ) : (ℕ → ℕ) → Type where
  | done (remaining : ℕ → ℕ) (complete : G.remainingWork remaining = 0) :
      DAGSchedule G processors remaining
  | step (S : DAGScheduleStep G processors)
      (active : 0 < G.remainingWork S.remaining)
      (tail : DAGSchedule G processors S.after) :
      DAGSchedule G processors S.remaining

namespace DAGSchedule

/-- Per-step accounting records of a chained DAG execution. -/
def metricSteps {G : CompDAG} {processors : ℕ} :
    {remaining : ℕ → ℕ} → DAGSchedule G processors remaining →
      List GreedyScheduleStep
  | _, .done _ _ => []
  | _, .step S _ tail => S.metricStep :: tail.metricSteps

/-- The residual state where the recorded execution stops. -/
def finalState {G : CompDAG} {processors : ℕ} :
    {remaining : ℕ → ℕ} → DAGSchedule G processors remaining → ℕ → ℕ
  | _, .done remaining _ => remaining
  | _, .step _ _ tail => tail.finalState

/-- Every recorded execution stops only after all DAG work is complete. -/
theorem final_work_eq_zero {G : CompDAG} {processors : ℕ}
    {remaining : ℕ → ℕ} (D : DAGSchedule G processors remaining) :
    G.remainingWork D.finalState = 0 := by
  induction D with
  | done _ complete => exact complete
  | step _ _ _ ih => exact ih

/-- Parallel time of the chained execution. -/
def time {G : CompDAG} {processors : ℕ} {remaining : ℕ → ℕ}
    (D : DAGSchedule G processors remaining) : ℕ :=
  D.metricSteps.length

/-- Work consumption telescopes over a chained execution. -/
theorem work_balance {G : CompDAG} {processors : ℕ} {remaining : ℕ → ℕ}
    (D : DAGSchedule G processors remaining) :
    (D.metricSteps.map GreedyScheduleStep.workConsumed).sum +
        G.remainingWork D.finalState =
      G.remainingWork remaining := by
  induction D with
  | done => simp [metricSteps, finalState]
  | step S _active tail ih =>
      have hstep := S.remainingWork_after_add_card
      simp only [metricSteps, List.map_cons, List.sum_cons,
        DAGScheduleStep.metricStep]
      change S.run.card +
          (tail.metricSteps.map GreedyScheduleStep.workConsumed).sum +
            G.remainingWork tail.finalState =
        G.remainingWork S.remaining
      omega

/-- Span decreases telescope over a chained execution. -/
theorem span_balance {G : CompDAG} {processors : ℕ} {remaining : ℕ → ℕ}
    (D : DAGSchedule G processors remaining) :
    (D.metricSteps.map GreedyScheduleStep.spanDecrease).sum +
        G.remainingSpan D.finalState =
      G.remainingSpan remaining := by
  induction D with
  | done => simp [metricSteps, finalState]
  | step S _active tail ih =>
      have hmono : G.remainingSpan S.after ≤ G.remainingSpan S.remaining := by
        simpa [DAGScheduleStep.after] using
          G.remainingSpan_execute_le S.remaining S.run
      simp only [metricSteps, List.map_cons, List.sum_cons,
        DAGScheduleStep.metricStep, DAGScheduleStep.after]
      change (G.remainingSpan S.remaining - G.remainingSpan S.after) +
          (tail.metricSteps.map GreedyScheduleStep.spanDecrease).sum +
            G.remainingSpan tail.finalState =
        G.remainingSpan S.remaining
      omega

private theorem all_complete_progress {G : CompDAG} {processors : ℕ}
    {remaining : ℕ → ℕ} (D : DAGSchedule G processors remaining) :
    ∀ step ∈ D.metricSteps,
      step.kind = .complete → processors ≤ step.workConsumed := by
  induction D with
  | done => simp [metricSteps]
  | step S _active tail ih =>
      intro step hmem hcomplete
      simp only [metricSteps, List.mem_cons] at hmem
      rcases hmem with rfl | htail
      · simpa [DAGScheduleStep.metricStep] using S.complete_progress hcomplete
      · exact ih step htail hcomplete

private theorem all_incomplete_progress {G : CompDAG} {processors : ℕ}
    {remaining : ℕ → ℕ} (D : DAGSchedule G processors remaining) :
    ∀ step ∈ D.metricSteps,
      step.kind = .incomplete → 1 ≤ step.spanDecrease := by
  induction D with
  | done => simp [metricSteps]
  | step S active tail ih =>
      intro step hmem hincomplete
      simp only [metricSteps, List.mem_cons] at hmem
      rcases hmem with rfl | htail
      · simpa [DAGScheduleStep.metricStep] using
          S.incomplete_progress active hincomplete
      · exact ih step htail hincomplete

end DAGSchedule

/-- A schedule run whose resource bounds and progress obligations are stated
locally, one execution step at a time.

`DAGSchedule.toRun` produces this interface from the concrete ready-set
semantics: a complete step consumes at least `processors` work, and an
incomplete step decreases the remaining span by at least one. -/
structure GreedyScheduleRun where
  /-- Number of processors used by the schedule. -/
  processors : ℕ
  /-- Initial work `T₁`. -/
  totalWork : ℕ
  /-- Initial span `T∞`. -/
  totalSpan : ℕ
  /-- Metric changes of the execution steps, in order. -/
  steps : List GreedyScheduleStep
  /-- A schedule has at least one processor. -/
  processors_pos : 0 < processors
  /-- All step work consumptions fit within the initial work. -/
  work_budget : (steps.map GreedyScheduleStep.workConsumed).sum ≤ totalWork
  /-- All span decreases fit within the initial span. -/
  span_budget : (steps.map GreedyScheduleStep.spanDecrease).sum ≤ totalSpan
  /-- Every complete step keeps all processors busy. -/
  complete_progress : ∀ step ∈ steps,
    step.kind = .complete → processors ≤ step.workConsumed
  /-- Every incomplete step advances the critical path. -/
  incomplete_progress : ∀ step ∈ steps,
    step.kind = .incomplete → 1 ≤ step.spanDecrease

namespace GreedyScheduleRun

/-- Parallel running time is the number of execution steps. -/
def time (S : GreedyScheduleRun) : ℕ :=
  S.steps.length

private theorem complete_count_mul_le_work
    (processors : ℕ) (steps : List GreedyScheduleStep)
    (hprogress : ∀ step ∈ steps,
      step.kind = .complete → processors ≤ step.workConsumed) :
    (steps.map GreedyScheduleStep.kind).count .complete * processors ≤
      (steps.map GreedyScheduleStep.workConsumed).sum := by
  induction steps with
  | nil => simp
  | cons step steps ih =>
      have htail : ∀ tailStep ∈ steps,
          tailStep.kind = .complete → processors ≤ tailStep.workConsumed := by
        intro tailStep hmem
        exact hprogress tailStep (List.mem_cons_of_mem step hmem)
      have ih' := ih htail
      cases hkind : step.kind with
      | complete =>
          have hstep : processors ≤ step.workConsumed :=
            hprogress step List.mem_cons_self hkind
          simp [hkind]
          rw [Nat.add_mul]
          omega
      | incomplete =>
          simp [hkind]
          omega

private theorem incomplete_count_le_span
    (steps : List GreedyScheduleStep)
    (hprogress : ∀ step ∈ steps,
      step.kind = .incomplete → 1 ≤ step.spanDecrease) :
    (steps.map GreedyScheduleStep.kind).count .incomplete ≤
      (steps.map GreedyScheduleStep.spanDecrease).sum := by
  induction steps with
  | nil => simp
  | cons step steps ih =>
      have htail : ∀ tailStep ∈ steps,
          tailStep.kind = .incomplete → 1 ≤ tailStep.spanDecrease := by
        intro tailStep hmem
        exact hprogress tailStep (List.mem_cons_of_mem step hmem)
      have ih' := ih htail
      cases hkind : step.kind with
      | complete =>
          simp [hkind]
          omega
      | incomplete =>
          have hstep : 1 ≤ step.spanDecrease :=
            hprogress step List.mem_cons_self hkind
          simp [hkind]
          omega

/-- Forget metric magnitudes while deriving the global trace bounds from the
per-step progress and resource-budget obligations. -/
def trace (S : GreedyScheduleRun) : GreedyScheduleTrace where
  processors := S.processors
  totalWork := S.totalWork
  totalSpan := S.totalSpan
  steps := S.steps.map GreedyScheduleStep.kind
  processors_pos := S.processors_pos
  complete_work_bound :=
    (complete_count_mul_le_work S.processors S.steps S.complete_progress).trans
      S.work_budget
  incomplete_span_bound :=
    (incomplete_count_le_span S.steps S.incomplete_progress).trans S.span_budget

/-- The aggregate accounting certificate derived from local step progress. -/
def accounting (S : GreedyScheduleRun) : GreedyScheduleAccounting :=
  S.trace.accounting

/-- The per-step execution form of the greedy-scheduler bound:
`Tₚ ≤ T₁ / p + T∞`. -/
theorem time_le_work_div_add_span (S : GreedyScheduleRun) :
    S.time ≤ S.totalWork / S.processors + S.totalSpan := by
  have h := S.trace.time_le_work_div_add_span
  simpa [time, GreedyScheduleTrace.time, trace] using h

end GreedyScheduleRun

namespace DAGSchedule

/-- Convert a type-safe DAG execution into the local per-step accounting
interface.  Both global budgets are derived by telescoping; neither is supplied
by the caller. -/
def toRun {G : CompDAG} {processors : ℕ} {remaining : ℕ → ℕ}
    (D : DAGSchedule G processors remaining) (hprocessors : 0 < processors) :
    GreedyScheduleRun where
  processors := processors
  totalWork := G.remainingWork remaining
  totalSpan := G.remainingSpan remaining
  steps := D.metricSteps
  processors_pos := hprocessors
  work_budget := by
    have hbalance := D.work_balance
    omega
  span_budget := by
    have hbalance := D.span_balance
    omega
  complete_progress := all_complete_progress D
  incomplete_progress := all_incomplete_progress D

/-- Greedy-scheduler bound for a chained execution from an arbitrary residual
state. -/
theorem time_le_remainingWork_div_add_remainingSpan
    {G : CompDAG} {processors : ℕ} {remaining : ℕ → ℕ}
    (D : DAGSchedule G processors remaining) (hprocessors : 0 < processors) :
    D.time ≤ G.remainingWork remaining / processors + G.remainingSpan remaining := by
  have hbound := (D.toRun hprocessors).time_le_work_div_add_span
  simpa [time, toRun, GreedyScheduleRun.time] using hbound

/-- CLRS Theorems 26.1/26.2 for an explicit greedy execution of a computation
DAG: `Tₚ ≤ T₁ / p + T∞`. -/
theorem time_le_work_div_add_span {G : CompDAG} {processors : ℕ}
    (D : DAGSchedule G processors G.node_work) (hprocessors : 0 < processors) :
    D.time ≤ G.work / processors + G.span := by
  have hbound := D.time_le_remainingWork_div_add_remainingSpan hprocessors
  simpa [CompDAG.remainingWork, CompDAG.work, CompDAG.remainingSpan,
    CompDAG.withWork] using hbound

end DAGSchedule

end Chapter27
end CLRS

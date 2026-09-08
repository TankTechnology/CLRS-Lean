import CLRSLean.FourthEdition.Chapter_16.Section_16_1_Amortized_Framework.Section_16_2_Stack_And_Counter

/-!
# Mixed stack execution and aggregate cost

Each command returns its removed elements in pop order (an empty list for PUSH
or an unsuccessful POP). All pushes succeed in this unbounded list-stack model.
MULTIPOP visits only the cells it actually removes, even when the requested count
is larger than the stack. The same execution returns the final stack, per-command
outputs, successful pushes, actual pops, and command count.

Charged work is one controller event per command plus one per pushed or popped
cell. List allocation and element representation costs are outside this model.
-/

namespace CLRS.Chapter17.StackExecution

inductive Command (α : Type u) where
  | push (value : α)
  | pop
  | multiPop (count : Nat)
  deriving Repr, DecidableEq

structure Removal (α : Type u) where
  stack : List α
  removed : List α
  pops : Nat
  deriving Repr

/-- A single traversal both removes and counts stack cells. -/
def remove : Nat → List α → Removal α
  | 0, s => ⟨s, [], 0⟩
  | _ + 1, [] => ⟨[], [], 0⟩
  | k + 1, x :: s =>
      let rest := remove k s
      ⟨rest.stack, x :: rest.removed, rest.pops + 1⟩

theorem remove_stack (k : Nat) (s : List α) : (remove k s).stack = s.drop k := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => cases s <;> simp [remove, ih]

theorem remove_removed (k : Nat) (s : List α) : (remove k s).removed = s.take k := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => cases s <;> simp [remove, ih]

theorem remove_pops (k : Nat) (s : List α) : (remove k s).pops = min k s.length := by
  induction k generalizing s with
  | zero => simp [remove]
  | succ k ih => cases s <;> simp [remove, ih, Nat.succ_min_succ]

theorem remove_conservation (k : Nat) (s : List α) :
    (remove k s).stack.length + (remove k s).pops = s.length := by
  rw [remove_stack, remove_pops, List.length_drop]
  omega

theorem remove_refines_multiPop (k : Nat) (s : List α) :
    (remove k s).stack = CLRS.Chapter17.multiPop s k ∧
    (remove k s).pops = multiPopCost s k :=
  ⟨remove_stack k s, remove_pops k s⟩

structure Step (α : Type u) extends Removal α where
  pushes : Nat
  deriving Repr

def step (s : List α) : Command α → Step α
  | .push x => ⟨⟨x :: s, [], 0⟩, 1⟩
  | .pop => ⟨remove 1 s, 0⟩
  | .multiPop k => ⟨remove k s, 0⟩

theorem step_conservation (s : List α) (op : Command α) :
    (step s op).stack.length + (step s op).pops = s.length + (step s op).pushes := by
  cases op with
  | push x => simp [step]
  | pop => simpa [step] using remove_conservation 1 s
  | multiPop k => simpa [step] using remove_conservation k s

theorem step_pushes_le_one (s : List α) (op : Command α) : (step s op).pushes ≤ 1 := by
  cases op <;> simp [step]

structure Run (α : Type u) where
  stack : List α
  outputs : List (List α)
  pushes : Nat
  pops : Nat
  commands : Nat
  deriving Repr

/-- Thread the actual stack through arbitrary mixed commands and collect outputs. -/
def execute (s : List α) : List (Command α) → Run α
  | [] => ⟨s, [], 0, 0, 0⟩
  | op :: ops =>
      let current := step s op
      let rest := execute current.stack ops
      ⟨rest.stack, current.removed :: rest.outputs,
        current.pushes + rest.pushes, current.pops + rest.pops, rest.commands + 1⟩

/-- Conservation is exact, including arbitrary nonempty initial stacks. -/
theorem execute_conservation (s : List α) (ops : List (Command α)) :
    (execute s ops).stack.length + (execute s ops).pops =
      s.length + (execute s ops).pushes := by
  induction ops generalizing s with
  | nil => simp [execute]
  | cons op ops ih =>
      have hc := step_conservation s op
      have ht := ih (step s op).stack
      simp only [execute]
      omega

theorem execute_commands (s : List α) (ops : List (Command α)) :
    (execute s ops).commands = ops.length := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => simp [execute, ih]

theorem execute_outputs_length (s : List α) (ops : List (Command α)) :
    (execute s ops).outputs.length = ops.length := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => simp [execute, ih]

theorem execute_pushes_le (s : List α) (ops : List (Command α)) :
    (execute s ops).pushes ≤ ops.length := by
  induction ops generalizing s with
  | nil => simp [execute]
  | cons op ops ih =>
      have hc := step_pushes_le_one s op
      have ht := ih (step s op).stack
      simp only [execute, List.length_cons]
      omega

/-- Every popped cell came from an initial resident or a successful PUSH. -/
theorem execute_pops_le_initial_add_pushes (s : List α) (ops : List (Command α)) :
    (execute s ops).pops ≤ s.length + (execute s ops).pushes := by
  have h := execute_conservation s ops
  omega

/-- From empty, arbitrary interleaved POP/MULTIPOP cannot outnumber PUSH cells. -/
theorem execute_pops_le_pushes (ops : List (Command α)) :
    (execute [] ops).pops ≤ (execute [] ops).pushes := by
  simpa using execute_pops_le_initial_add_pushes [] ops

def Run.work (run : Run α) : Nat := run.commands + run.pushes + run.pops

/-- Linear aggregate work, with credit for cells present initially. -/
theorem execute_work_le (s : List α) (ops : List (Command α)) :
    (execute s ops).work ≤ 3 * ops.length + s.length := by
  have hp := execute_pushes_le s ops
  have hr := execute_pops_le_initial_add_pushes s ops
  simp only [Run.work, execute_commands]
  omega

theorem execute_empty_work_le (ops : List (Command α)) :
    (execute [] ops).work ≤ 3 * ops.length := by
  simpa using execute_work_le [] ops

end CLRS.Chapter17.StackExecution

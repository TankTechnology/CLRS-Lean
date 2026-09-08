import CLRSLean.FourthEdition.Chapter_19.Section_19_2_Linked_List_Representation

/-!
# Weighted-union traces and aggregate pointer rewrites

The execution starts from the native head-table state and runs arbitrary FIND
and weighted UNION commands. Each union enumerates the representatives that
actually changed, then derives both its rewrite total and per-element move
counts from this list. No move events or doubling assumptions are supplied by
a caller. The initialized invariant identifies every recorded class size with
the cardinality of its actual head fiber.

The returned total is the sum of constructed per-element counts and is at most
{lit}`n * Nat.log2 n`. Adding one abstract controller event per command gives
{lit}`m + n * Nat.log2 n`. This is the head-pointer rewrite model: enumeration
of audit events, persistent function evaluation, and linked-list allocation are
outside the charged model. It is not a runtime bound for these instrumentation
lists or an implementation of explicit linked-list cells.
-/

namespace CLRS.Chapter21.LinkedList.WeightedExecution
open Finset State

variable {n : Nat}

def classOf (s : State n) (x : Fin n) : Finset (Fin n) :=
  univ.filter (fun z => s.head z = s.head x)

/-- Recorded class sizes agree with the actual represented partition. -/
def Sized (s : State n) : Prop := ∀ z, s.setSize z = (classOf s z).card

theorem singleton_sized : Sized (singleton n) := by
  intro z
  simp [setSize, State.singleton, classOf, Finset.filter_eq']

theorem class_disjoint (s : State n) {x y : Fin n} (h : s.head x ≠ s.head y) :
    Disjoint (classOf s x) (classOf s y) := by
  apply Finset.disjoint_left.mpr
  simp only [classOf, mem_filter, mem_univ, true_and]
  intro z hx hy
  exact h (hx.symm.trans hy)

theorem merge_class_left (s : State n) (x y z : Fin n)
    (hz : s.head z = s.head x) :
    classOf (s.mergeToward x y) z = classOf s x ∪ classOf s y := by
  ext w
  by_cases hw : s.head w = s.head x <;> simp [classOf, mergeToward, hz, hw]

theorem merge_class_right (s : State n) (x y z : Fin n)
    (hxy : s.head x ≠ s.head y) (hz : s.head z = s.head y) :
    classOf (s.mergeToward x y) z = classOf s x ∪ classOf s y := by
  ext w
  by_cases hw : s.head w = s.head x <;> simp [classOf, mergeToward, hz, hw, hxy]

theorem merge_class_other (s : State n) (x y z : Fin n)
    (hzx : s.head z ≠ s.head x) (hzy : s.head z ≠ s.head y) :
    classOf (s.mergeToward x y) z = classOf s z := by
  ext w
  by_cases hw : s.head w = s.head x
  · have hwz : s.head w ≠ s.head z := by rw [hw]; exact Ne.symm hzx
    simp [classOf, mergeToward, hzx, Ne.symm hzy, hw, Ne.symm hzx]
  · simp [classOf, mergeToward, hzx, hw]

theorem merge_sized (s : State n) (x y : Fin n)
    (hs : Sized s) (hxy : s.head x ≠ s.head y) : Sized (s.mergeToward x y) := by
  intro z
  by_cases hzx : s.head z = s.head x
  · rw [merge_class_left s x y z hzx, card_union_of_disjoint (class_disjoint s hxy)]
    simp [setSize, mergeToward, hzx, ← hs x, ← hs y]
  · by_cases hzy : s.head z = s.head y
    · rw [merge_class_right s x y z hxy hzy, card_union_of_disjoint (class_disjoint s hxy)]
      simp [setSize, mergeToward, hzy, ← hs x, ← hs y]
    · rw [merge_class_other s x y z hzx hzy]
      simpa [setSize, mergeToward, hzx, hzy] using hs z

theorem union_sized (s : State n) (x y : Fin n) (hs : Sized s) :
    Sized (s.weightedUnion x y).1 := by
  unfold weightedUnion
  split
  · exact hs
  · rename_i hxy
    split
    · exact merge_sized s x y hs hxy
    · exact merge_sized s y x hs (Ne.symm hxy)

theorem merge_size_mono (s : State n) (x y z : Fin n)
    (_hxy : s.head x ≠ s.head y) :
    s.setSize z ≤ (s.mergeToward x y).setSize z := by
  by_cases hzx : s.head z = s.head x
  · simp [setSize, mergeToward, hzx]
  · by_cases hzy : s.head z = s.head y
    · simp [setSize, mergeToward, hzy]
    · simp [setSize, mergeToward, hzx, hzy]

theorem union_size_mono (s : State n) (x y z : Fin n) :
    s.setSize z ≤ (s.weightedUnion x y).1.setSize z := by
  unfold weightedUnion
  split
  · exact Nat.le_refl _
  · rename_i hxy
    split
    · exact merge_size_mono s x y z hxy
    · exact merge_size_mono s y x z (Ne.symm hxy)


/-- Enumerate actual pre/post representative changes for the audit ledger. -/
def changes (s t : State n) : List (Fin n) :=
  (List.finRange n).filter (fun z => decide (t.head z ≠ s.head z))

theorem changes_count (s t : State n) (z : Fin n) :
    (changes s t).count z = if t.head z ≠ s.head z then 1 else 0 := by
  by_cases h : t.head z ≠ s.head z
  · rw [if_pos h]
    exact List.count_eq_one_of_mem ((List.nodup_finRange n).filter _) (by simp [changes, h])
  · rw [if_neg h]
    apply List.count_eq_zero.mpr
    simp [changes, h]

theorem sum_counts (xs : List (Fin n)) : ∑ z, xs.count z = xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.count_cons, Finset.sum_add_distrib, ih, beq_iff_eq]

theorem changes_length (s t : State n) :
    (changes s t).length = ∑ z, (changes s t).count z := by
  exact (sum_counts (changes s t)).symm

theorem merge_changes (s : State n) (x y : Fin n)
    (hxy : s.head x ≠ s.head y) :
    changes s (s.mergeToward x y) =
      (List.finRange n).filter (fun z => decide (s.head z = s.head x)) := by
  apply List.filter_congr
  intro z _
  by_cases hz : s.head z = s.head x
  · simp [mergeToward, hz, Ne.symm hxy]
  · simp [mergeToward, hz]

theorem merge_changes_length (s : State n) (x y : Fin n)
    (hxy : s.head x ≠ s.head y) :
    (changes s (s.mergeToward x y)).length = (classOf s x).card := by
  rw [merge_changes s x y hxy]
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)]
  congr 1
  ext z
  simp [classOf]

theorem union_changes_cost (s : State n) (x y : Fin n) (hs : Sized s) :
    (changes s (s.weightedUnion x y).1).length = (s.weightedUnion x y).2 := by
  unfold weightedUnion
  split
  · simp [changes]
  · rename_i hxy
    split
    · exact (merge_changes_length s x y hxy).trans (hs x).symm
    · exact (merge_changes_length s y x (Ne.symm hxy)).trans (hs y).symm

structure Step (n : Nat) where
  state : State n
  output : Option (Fin n)
  rewritten : List (Fin n)

def step (s : State n) : Operation (Fin n) → Step n
  | .find x => ⟨s, some (s.head x), []⟩
  | .union x y =>
      let next := s.weightedUnion x y
      ⟨next.1, none, changes s next.1⟩

theorem step_sized (s : State n) (op : Operation (Fin n)) (hs : Sized s) :
    Sized (step s op).state := by
  cases op with
  | find x => exact hs
  | union x y => exact union_sized s x y hs

theorem step_headInvariant (s : State n) (op : Operation (Fin n))
    (hs : s.HeadInvariant) : (step s op).state.HeadInvariant := by
  cases op with
  | find x => exact hs
  | union x y => exact s.weightedUnion_preserves_headInvariant x y hs

theorem step_growth (s : State n) (op : Operation (Fin n)) (z : Fin n) :
    2 ^ (step s op).rewritten.count z * s.setSize z ≤ (step s op).state.setSize z := by
  cases op with
  | find x => simp [step]
  | union x y =>
      simp only [step, changes_count]
      split
      · simpa using s.weightedUnion_changed_doubles x y z ‹_›
      · simpa using union_size_mono s x y z

structure Run (n : Nat) where
  state : State n
  outputs : List (Option (Fin n))
  moves : Fin n → Nat
  rewrites : Nat
  commands : Nat

/-- Run native transitions, returning query outputs and the derived rewrite ledger. -/
def execute (s : State n) : List (Operation (Fin n)) → Run n
  | [] => ⟨s, [], fun _ => 0, 0, 0⟩
  | op :: ops =>
      let current := step s op
      let rest := execute current.state ops
      ⟨rest.state, current.output :: rest.outputs,
        fun z => current.rewritten.count z + rest.moves z,
        current.rewritten.length + rest.rewrites, rest.commands + 1⟩

theorem execute_sized (s : State n) (ops : List (Operation (Fin n))) (hs : Sized s) :
    Sized (execute s ops).state := by
  induction ops generalizing s with
  | nil => exact hs
  | cons op ops ih => exact ih _ (step_sized s op hs)

theorem execute_headInvariant (s : State n) (ops : List (Operation (Fin n)))
    (hs : s.HeadInvariant) : (execute s ops).state.HeadInvariant := by
  induction ops generalizing s with
  | nil => exact hs
  | cons op ops ih => exact ih _ (step_headInvariant s op hs)

/-- The returned rewrite total is exactly the sum of its per-element move counts. -/
theorem execute_rewrites_eq_sum (s : State n) (ops : List (Operation (Fin n))) :
    (execute s ops).rewrites = ∑ z, (execute s ops).moves z := by
  induction ops generalizing s with
  | nil => simp [execute]
  | cons op ops ih =>
      simp only [execute, Finset.sum_add_distrib, ← ih]
      congr 1
      exact (sum_counts (step s op).rewritten).symm

theorem execute_growth (s : State n) (ops : List (Operation (Fin n))) (z : Fin n) :
    2 ^ (execute s ops).moves z * s.setSize z ≤ (execute s ops).state.setSize z := by
  induction ops generalizing s with
  | nil => simp [execute]
  | cons op ops ih =>
      have hg := step_growth s op z
      have ht := ih (step s op).state
      simp only [execute, pow_add]
      calc
        _ = 2 ^ (execute (step s op).state ops).moves z *
            (2 ^ (step s op).rewritten.count z * s.setSize z) := by ring
        _ ≤ 2 ^ (execute (step s op).state ops).moves z * (step s op).state.setSize z :=
          Nat.mul_le_mul_left _ hg
        _ ≤ _ := ht

theorem execute_singleton_moves_le (ops : List (Operation (Fin n))) (z : Fin n) :
    (execute (State.singleton n) ops).moves z ≤ Nat.log2 n := by
  have hs := execute_sized (State.singleton n) ops singleton_sized
  have hg := execute_growth (State.singleton n) ops z
  rw [singleton_size, Nat.mul_one, hs z] at hg
  apply (Nat.le_log2 (by have h := z.isLt; omega)).2
  exact hg.trans (by simpa [classOf] using Finset.card_le_card (Finset.filter_subset
    (fun w => (execute (State.singleton n) ops).state.head w =
      (execute (State.singleton n) ops).state.head z) (univ : Finset (Fin n))))

/-- Aggregate doubling bound for arbitrary operations from singleton sets. -/
theorem execute_singleton_rewrites_le (ops : List (Operation (Fin n))) :
    (execute (State.singleton n) ops).rewrites ≤ n * Nat.log2 n := by
  rw [execute_rewrites_eq_sum]
  exact total_rewrites_le_n_mul_log2 _ (execute_singleton_moves_le ops)


private theorem partition_ext {P Q : Partition (Fin n)}
    (h : ∀ x y, P.sameSet x y ↔ Q.sameSet x y) : P = Q := by
  cases P
  cases Q
  congr
  funext x y
  exact propext (h x y)

theorem step_refines_spec (s : State n) (op : Operation (Fin n)) :
    (step s op).state.partition = stepSpec s.partition op := by
  cases op with
  | find x => rfl
  | union x y =>
      apply partition_ext
      intro a b
      exact s.weightedUnion_refines_merge x y a b

theorem execute_refines_spec (s : State n) (ops : List (Operation (Fin n))) :
    (execute s ops).state.partition = runSpec s.partition ops := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
      change (execute (step s op).state ops).state.partition = runSpec (stepSpec s.partition op) ops
      rw [ih, step_refines_spec]

theorem execute_commands (s : State n) (ops : List (Operation (Fin n))) :
    (execute s ops).commands = ops.length := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => simp [execute, ih]

theorem execute_outputs_length (s : State n) (ops : List (Operation (Fin n))) :
    (execute s ops).outputs.length = ops.length := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => simp [execute, ih]

theorem execute_append_state (s : State n) (xs ys : List (Operation (Fin n))) :
    (execute s (xs ++ ys)).state = (execute (execute s xs).state ys).state := by
  induction xs generalizing s with
  | nil => rfl
  | cons op xs ih => exact ih (step s op).state

theorem execute_append_outputs (s : State n) (xs ys : List (Operation (Fin n))) :
    (execute s (xs ++ ys)).outputs =
      (execute s xs).outputs ++ (execute (execute s xs).state ys).outputs := by
  induction xs generalizing s with
  | nil => rfl
  | cons op xs ih => simp [execute, ih]

/-- A FIND returns the representative in the state reached by its preceding commands. -/
theorem execute_find_output (s : State n) (before suffix : List (Operation (Fin n)))
    (x : Fin n) :
    (execute s (before ++ .find x :: suffix)).outputs[before.length]? =
      some (some ((execute s before).state.head x)) := by
  rw [execute_append_outputs, List.getElem?_append_right (by rw [execute_outputs_length])]
  simp [execute_outputs_length, execute, step]

/-- Returned FIND representatives are resident representatives of the queried class. -/
theorem execute_find_representative (s : State n) (before : List (Operation (Fin n)))
    (hs : s.HeadInvariant) (x : Fin n) :
    (execute s before).state.sameSet x ((execute s before).state.head x) ∧
      (execute s before).state.head ((execute s before).state.head x) =
        (execute s before).state.head x := by
  have hi := execute_headInvariant s before hs x
  exact ⟨hi.symm, hi⟩

/-- One abstract command event plus actual representative-pointer changes.
This excludes scanning head tables to enumerate the audit events. -/
def Run.charged (run : Run n) : Nat := run.commands + run.rewrites

theorem execute_singleton_charged_le (ops : List (Operation (Fin n))) :
    (execute (State.singleton n) ops).charged ≤ ops.length + n * Nat.log2 n := by
  unfold Run.charged
  rw [execute_commands]
  exact Nat.add_le_add_left (execute_singleton_rewrites_le ops) _

end CLRS.Chapter21.LinkedList.WeightedExecution

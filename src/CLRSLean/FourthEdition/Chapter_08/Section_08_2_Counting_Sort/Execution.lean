import CLRSLean.FourthEdition.Chapter_08.Section_08_2_Counting_Sort

/-!
# Counting sort through one stable indexed distribution

The input is traversed once, storing each element in an indexed list bucket.
The output loop traverses these stored buckets and pushes each emitted element
once. The returned counters count the visits to these actual loops. A separate
indexed-work ledger expands each accepted distribution step into its key,
check, indexed-read, cons, and indexed-write operations.

This is an indexed stable-bucket refinement of counting sort. It does not run
the textbook cumulative-counter decrement program. Indexed array operations
are unit-cost primitives here; persistent-array copying, array/list view conversion, allocation internals, and
machine instructions are not modeled by this controller ledger.
-/

namespace CLRS.Chapter08.CountingExecution

structure Distribution (α : Type*) where
  buckets : Array (List α)
  inputs : Nat
  updates : Nat
  deriving Repr

/-- Initialize buckets with one array push per slot. -/
def initializeBuckets : Nat → Array (List α) × Nat
  | 0 => (#[], 0)
  | n + 1 => let prev := initializeBuckets n; (prev.1.push [], prev.2 + 1)

@[simp] theorem initializeBuckets_array (n : Nat) :
    (initializeBuckets (α := α) n).1 = Array.replicate n [] := by
  induction n with
  | zero => simp [initializeBuckets]
  | succ n ih => simp [initializeBuckets, ih, Array.replicate_succ]

@[simp] theorem initializeBuckets_visits (n : Nat) : (initializeBuckets (α := α) n).2 = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [initializeBuckets, ih]

/-- Scan from right to left, evaluating each input key once. Each successful
index check performs one bucket read, one cons, and one bucket write. -/
def distribute (key : α → Nat) : List α → Array (List α) → Distribution α
  | [], acc => ⟨acc, 0, 0⟩
  | x :: xs, acc =>
      let rest := distribute key xs acc
      let k := key x
      if h : k < rest.buckets.size then
        ⟨rest.buckets.set k (x :: rest.buckets[k]), rest.inputs + 1, rest.updates + 1⟩
      else ⟨rest.buckets, rest.inputs + 1, rest.updates⟩

@[simp] theorem distribute_size (key : α → Nat) (xs : List α) (acc : Array (List α)) :
    (distribute key xs acc).buckets.size = acc.size := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [distribute]; split <;> simp_all

@[simp] theorem distribute_inputs (key : α → Nat) (xs : List α) (acc : Array (List α)) :
    (distribute key xs acc).inputs = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [distribute]; split <;> simp_all

theorem distribute_updates_le (key : α → Nat) (xs : List α) (acc : Array (List α)) :
    (distribute key xs acc).updates ≤ xs.length := by
  induction xs with
  | nil => simp [distribute]
  | cons x xs ih => simp only [distribute]; split <;> simp_all; omega

theorem distribute_updates_eq (key : α → Nat) (xs : List α) (acc : Array (List α))
    (hkeys : ∀ x ∈ xs, key x < acc.size) :
    (distribute key xs acc).updates = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hx := hkeys x (by simp)
      have ht : ∀ y ∈ xs, key y < acc.size := fun y hy => hkeys y (by simp [hy])
      simp [distribute, hx, ih ht]

/-- Every bucket preserves input order, even with an arbitrary initial table. -/
theorem distribute_get (key : α → Nat) (xs : List α) (acc : Array (List α))
    (k : Nat) (hk : k < acc.size) :
    (distribute key xs acc).buckets[k]'(by simpa using hk) = bucket key xs k ++ acc[k] := by
  induction xs with
  | nil => simp [distribute, bucket]
  | cons x xs ih =>
      have hk' : k < (distribute key xs acc).buckets.size := by simpa using hk
      simp only [distribute]
      split
      next h =>
        by_cases heq : key x = k
        · subst k
          simp [bucket, ih, Bool.beq_eq_decide_eq]
        · simp [Array.getElem_set, heq, bucket, Bool.beq_eq_decide_eq] at ih ⊢
          exact ih
      next h =>
        have heq : key x ≠ k := by intro he; apply h; simpa [he] using hk'
        simpa [bucket, List.filter_cons, Bool.beq_eq_decide_eq, heq] using ih

structure Output (α : Type*) where
  value : Array α
  writes : Nat

/-- Push each supplied element once into the output. -/
def pushList : List α → Array α → Output α
  | [], out => ⟨out, 0⟩
  | x :: xs, out =>
      let rest := pushList xs (out.push x)
      ⟨rest.value, rest.writes + 1⟩

@[simp] theorem pushList_value (xs : List α) (out : Array α) :
    (pushList xs out).value.toList = out.toList ++ xs := by
  induction xs generalizing out with
  | nil => simp [pushList]
  | cons x xs ih => simp [pushList, ih, List.append_assoc]

@[simp] theorem pushList_writes (xs : List α) (out : Array α) :
    (pushList xs out).writes = xs.length := by
  induction xs generalizing out with
  | nil => rfl
  | cons x xs ih => simp [pushList, ih]

structure Emission (α : Type*) where
  output : Array α
  bucketVisits : Nat
  outputWrites : Nat

/-- Visit each stored bucket once and push its elements in order. -/
def emit : List (List α) → Array α → Emission α
  | [], out => ⟨out, 0, 0⟩
  | b :: bs, out =>
      let pushed := pushList b out
      let rest := emit bs pushed.value
      ⟨rest.output, rest.bucketVisits + 1, pushed.writes + rest.outputWrites⟩

@[simp] theorem emit_value (bs : List (List α)) (out : Array α) :
    (emit bs out).output.toList = out.toList ++ bs.flatten := by
  induction bs generalizing out with
  | nil => simp [emit]
  | cons b bs ih => simp [emit, ih, List.append_assoc]

@[simp] theorem emit_visits (bs : List (List α)) (out : Array α) :
    (emit bs out).bucketVisits = bs.length := by
  induction bs generalizing out with
  | nil => rfl
  | cons b bs ih => simp [emit, ih]

@[simp] theorem emit_writes (bs : List (List α)) (out : Array α) :
    (emit bs out).outputWrites = bs.flatten.length := by
  induction bs generalizing out with
  | nil => rfl
  | cons b bs ih => simp [emit, ih]

structure Execution (α : Type*) where
  output : Array α
  initializationWrites : Nat
  inputVisits : Nat
  bucketUpdates : Nat
  bucketVisits : Nat
  outputWrites : Nat

/-- The number of visits to the four controller loops. -/
def Execution.controllerVisits (run : Execution α) : Nat :=
  run.initializationWrites + run.inputVisits + run.bucketVisits + run.outputWrites

/-- Explicit indexed-operation ledger: initialization pushes, one key evaluation
and index check per input, a read/cons/write triple per accepted input, bucket
visits, and output pushes. This does not model persistent-array machine time. -/
def Execution.indexedWork (run : Execution α) : Nat :=
  run.initializationWrites + 2 * run.inputVisits + 3 * run.bucketUpdates +
    run.bucketVisits + run.outputWrites

/-- Stable indexed-bucket counting sort and the counters produced by its loops. -/
def execute (maxKey : Nat) (key : α → Nat) (xs : List α) : Execution α :=
  let initial := initializeBuckets (α := α) (maxKey + 1)
  let distributed := distribute key xs initial.1
  let emitted := emit distributed.buckets.toList #[]
  ⟨emitted.output, initial.2, distributed.inputs, distributed.updates,
    emitted.bucketVisits, emitted.outputWrites⟩

theorem distribute_toList (bucketCount : Nat) (key : α → Nat) (xs : List α) :
    (distribute key xs (Array.replicate bucketCount [])).buckets.toList =
      (List.range bucketCount).map (bucket key xs) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
    have he := distribute_get key xs (Array.replicate bucketCount []) i (by simpa using hj)
    simpa using he

/-- The new execution refines the stable bucket specification, including its
out-of-range-key behavior. -/
theorem execute_result (maxKey : Nat) (key : α → Nat) (xs : List α) :
    (execute maxKey key xs).output.toList = countingSortBy maxKey key xs := by
  simp [execute, distribute_toList, countingSortBy, List.flatMap]

theorem execute_counts (maxKey : Nat) (key : α → Nat) (xs : List α) :
    (execute maxKey key xs).initializationWrites = maxKey + 1 ∧
    (execute maxKey key xs).inputVisits = xs.length ∧
    (execute maxKey key xs).bucketVisits = maxKey + 1 ∧
    (execute maxKey key xs).outputWrites = (countingSortBy maxKey key xs).length := by
  simp [execute, distribute_toList, countingSortBy, List.flatMap]

theorem execute_updates (maxKey : Nat) (key : α → Nat) (xs : List α)
    (hkeys : AllKeysLe key xs maxKey) :
    (execute maxKey key xs).bucketUpdates = xs.length := by
  apply distribute_updates_eq
  simpa [AllKeysLe, Nat.lt_succ_iff] using hkeys

/-- Under bounded keys, all four loop visits total the traditional linear ledger. -/
theorem execute_controllerVisits [DecidableEq α] (maxKey : Nat) (key : α → Nat)
    (xs : List α) (hkeys : AllKeysLe key xs maxKey) :
    (execute maxKey key xs).controllerVisits = 2 * xs.length + 2 * (maxKey + 1) := by
  rcases execute_counts maxKey key xs with ⟨hi, hn, hb, ho⟩
  have hl := (countingSortBy_perm maxKey key xs hkeys).length_eq
  simp only [Execution.controllerVisits, hi, hn, hb, ho, hl]
  omega

/-- The explicitly listed key/index/list operations also have linear total work. -/
theorem execute_indexedWork [DecidableEq α] (maxKey : Nat) (key : α → Nat)
    (xs : List α) (hkeys : AllKeysLe key xs maxKey) :
    (execute maxKey key xs).indexedWork = 6 * xs.length + 2 * (maxKey + 1) := by
  rcases execute_counts maxKey key xs with ⟨hi, hn, hb, ho⟩
  have hl := (countingSortBy_perm maxKey key xs hkeys).length_eq
  rw [Execution.indexedWork, hi, hn, hb, ho, hl, execute_updates maxKey key xs hkeys]
  omega

end CLRS.Chapter08.CountingExecution

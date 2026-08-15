import CLRSLean.FourthEdition.Chapter_16.Section_16_4_Dynamic_Tables

/-!
# CLRS Section 16.4 - Mutable-array dynamic tables and sharper load-factor potential

This nested section refines the size-level dynamic-table model of
{lit}`Section_16_4_Dynamic_Tables` in two independent directions requested by
CLRS Section 16.4.

**Sub-issue A - mutable-array copying.**  We model the physical array-copy step
that a real dynamic table performs on reallocation with {lit}`growTo`, an actual
{lit}`Array` operation that allocates a larger backing store and copies every
existing element.  A concrete {lit}`ArrayTable` structure carries a backing
{lit}`Array` together with its capacity, and its insertion projects onto the
abstract {lit}`dynamicTableInsert` transition and matches the abstract
{lit}`dynamicTableInsertCost`.  The connecting theorem {lit}`insert_copy_cost`
splits the abstract cost into copied elements plus one write, and
{lit}`dynamicTableCopyCount_eq_growCopyCost` identifies the abstract copy count
with the number of elements a physical {lit}`growTo` moves.

**Sub-issue B - sharper load-factor potential.**  We define the CLRS
load-factor potential Φ, whose value depends on whether the load factor
α = num / size is at least 1/2, via a division-free doubled integer form
{lit}`sharpPotentialZ` (Ψ = 2Φ) and its rational wrapper {lit}`sharpPotential`.
A sharper contraction {lit}`sharpDelete` halves the table to exactly restore
α = 1/2.  We prove constant amortized bounds (≤ 3, the CLRS result) for both
insertion and deletion, plus the CLRS guarantee that α is exactly 1/2 (hence at
least 1/2) immediately after a contraction.

Main results:

- Definition {lit}`growTo`: allocate a larger array and copy every element.
- Theorems {lit}`growTo_size` and {lit}`growTo_toList`: the physical copy has
  the requested length and preserves every copied element in order.
- Theorems {lit}`arrayTable_toState_insert` and {lit}`arrayTable_insertCost_eq`:
  the concrete mutable-array insertion refines the abstract transition and cost.
- Theorem {lit}`insert_copy_cost`: abstract insertion cost equals copied
  elements plus one write.
- Theorem {lit}`dynamicTableCopyCount_eq_growCopyCost`: the abstract copy count
  equals the number of elements a physical {lit}`growTo` moves.
- Definitions {lit}`sharpPotentialZ`, {lit}`sharpPotential`, {lit}`loadFactor`:
  the CLRS load-factor potential and load factor.
- Theorems {lit}`sharpPotentialZ_nonneg` and {lit}`sharpPotential_nonneg`: the
  sharper potential is nonnegative.
- Theorems {lit}`sharpInsert_amortized_le_three` and
  {lit}`sharpDelete_amortized_le_three`: constant (≤ 3) amortized cost for
  insertion and deletion under the load-factor potential.
- Theorem {lit}`sharpDelete_loadFactor_eq_half_of_contract` and its corollary
  {lit}`sharpDelete_loadFactor_ge_half_of_contract`: the load factor is exactly
  1/2, hence at least 1/2, right after a contraction.
- Definition {lit}`TableOp` ({lit}`insert` / {lit}`delete`) with
  {lit}`tableStep`, {lit}`tableOpCost`, {lit}`execTrace`, and {lit}`traceCost`:
  an executable interleaved insert/delete trace model.
- Theorem {lit}`tableOp_amortized_le_three`: every single operation has
  amortized cost at most `3` under the load-factor potential.
- Theorem {lit}`trace_amortized_le`: the whole-trace amortized cost telescopes,
  so a valid trace of `n` operations costs at most `3n + Φ(s₀)`.
- Theorem {lit}`trace_totalCost_le_three_mul`: starting from the empty table, a
  trace of `n` operations has total actual cost at most `3n`.

Notation conventions used in this section:

- `s` : an abstract {lit}`DynamicTableState` (stored count `num`, capacity `size`)
- `t` : a concrete {lit}`ArrayTable`
- `α` : load factor `num / size`
- `Φ` : CLRS load-factor potential; `Ψ = 2Φ` is its division-free integer form

Current gaps:

- General allocator / RAM cost semantics remain out of scope.
-/

namespace CLRS
namespace Chapter17

/-! ## Sub-issue A: an actual array copy operation -/

/--
Physical array-copy step of a dynamic table: allocate an array of length
{lit}`newSize`, copy every element of {lit}`old`, and pad the remaining slots
with {lit}`dflt`.  This models CLRS's "copy the items into the new table"
operation on reallocation.
-/
def growTo {α : Type u} (old : Array α) (newSize : Nat) (dflt : α) : Array α :=
  old ++ (List.replicate (newSize - old.size) dflt).toArray

/--
The physical copy preserves every existing element in order: its list of
elements is exactly {lit}`old` followed by the padding.  This certifies that
{lit}`growTo` is a faithful copy rather than an arbitrary array.
-/
theorem growTo_toList {α : Type u} (old : Array α) (newSize : Nat) (dflt : α) :
    (growTo old newSize dflt).toList
      = old.toList ++ List.replicate (newSize - old.size) dflt := by
  simp [growTo]

/-- A copy into a table of size at least {lit}`old.size` has that size. -/
theorem growTo_size {α : Type u} (old : Array α) (newSize : Nat) (dflt : α)
    (h : old.size ≤ newSize) : (growTo old newSize dflt).size = newSize := by
  unfold growTo
  rw [Array.size_append]
  simp
  omega

/--
Number of elements a physical copy of {lit}`old` moves: one per existing
element.  This is the per-element copy cost that CLRS charges on reallocation.
-/
def growCopyCost {α : Type u} (old : Array α) : Nat := old.size

/--
A concrete mutable-array dynamic table: a backing {lit}`Array` whose length is
the allocated capacity, with the invariant that it is never overfilled.  The
number of stored elements is {lit}`elements.size` and the capacity is
{lit}`capacity`.
-/
structure ArrayTable (α : Type u) where
  /-- Backing store; its length is the number of stored elements. -/
  elements : Array α
  /-- Allocated capacity. -/
  capacity : Nat
  /-- The table never stores more elements than its capacity. -/
  hcap : elements.size ≤ capacity

/-- The abstract size-level state of a concrete mutable-array table. -/
def ArrayTable.toState {α : Type u} (t : ArrayTable α) : DynamicTableState :=
  { num := t.elements.size, size := t.capacity }

/--
Concrete mutable-array insertion of {lit}`x`.  If there is spare capacity, write
{lit}`x` in place; otherwise reallocate to a capacity that both fits the new
element and at least doubles the old allocation (the value padded into new slots
is {lit}`x` itself).
-/
def ArrayTable.insert {α : Type u} (t : ArrayTable α) (x : α) : ArrayTable α :=
  if h : t.elements.size + 1 ≤ t.capacity then
    { elements := t.elements.push x
      capacity := t.capacity
      hcap := by rw [Array.size_push]; exact h }
  else
    { elements := t.elements.push x
      capacity := max (t.elements.size + 1) (2 * t.capacity)
      hcap := by rw [Array.size_push]; exact le_max_left _ _ }

/-- Concrete insertion cost: one write, plus one copy per existing element on reallocation. -/
def ArrayTable.insertCost {α : Type u} (t : ArrayTable α) : Nat :=
  if t.elements.size + 1 ≤ t.capacity then 1 else t.elements.size + 1

/--
The concrete mutable-array insertion refines the abstract size-level transition:
its abstract state is exactly {lit}`dynamicTableInsert` of the abstract state.
-/
theorem arrayTable_toState_insert {α : Type u} (t : ArrayTable α) (x : α) :
    (t.insert x).toState = dynamicTableInsert t.toState := by
  by_cases h : t.elements.size + 1 ≤ t.capacity
  · simp only [ArrayTable.insert, ArrayTable.toState, dynamicTableInsert,
      dynamicTableInsertSize, dif_pos h, if_pos h, Array.size_push]
  · simp only [ArrayTable.insert, ArrayTable.toState, dynamicTableInsert,
      dynamicTableInsertSize, dif_neg h, if_neg h, Array.size_push]

/-- The concrete insertion cost matches the abstract size-level insertion cost. -/
theorem arrayTable_insertCost_eq {α : Type u} (t : ArrayTable α) :
    t.insertCost = dynamicTableInsertCost t.toState := by
  unfold ArrayTable.insertCost dynamicTableInsertCost ArrayTable.toState
  by_cases h : t.elements.size + 1 ≤ t.capacity <;> simp [h]

/--
Number of elements a real reallocation copies for one abstract insertion: none
when there is spare capacity, otherwise every stored element.
-/
def dynamicTableCopyCount (s : DynamicTableState) : Nat :=
  if s.num + 1 ≤ s.size then 0 else s.num

/--
**Insertion-cost accounting matches copy calls.**  The abstract insertion cost is
exactly the number of elements physically copied plus the single write of the
new element.  This is CLRS's decomposition of `TABLE-INSERT` cost into copy work
and the constant insert step.
-/
theorem insert_copy_cost (s : DynamicTableState) :
    dynamicTableInsertCost s = dynamicTableCopyCount s + 1 := by
  unfold dynamicTableInsertCost dynamicTableCopyCount
  by_cases h : s.num + 1 ≤ s.size <;> simp [h]

/--
At a reallocation, the abstract copy count equals the number of elements a
physical {lit}`growTo` moves out of the old backing store: one per stored
element.
-/
theorem dynamicTableCopyCount_eq_growCopyCost {α : Type u} (s : DynamicTableState)
    (t : ArrayTable α) (hcount : t.elements.size = s.num)
    (hexpand : ¬ s.num + 1 ≤ s.size) :
    dynamicTableCopyCount s = growCopyCost t.elements := by
  unfold dynamicTableCopyCount growCopyCost
  rw [if_neg hexpand, hcount]

/--
Concrete form of {lit}`insert_copy_cost` for a real {lit}`ArrayTable` at a
reallocation: the insertion cost is the number of elements the physical copy
moves plus one write.
-/
theorem arrayTable_insert_copy_cost_of_expand {α : Type u} (t : ArrayTable α)
    (hfull : ¬ t.elements.size + 1 ≤ t.capacity) :
    t.insertCost = growCopyCost t.elements + 1 := by
  unfold ArrayTable.insertCost growCopyCost
  simp [hfull]

/-! ## Sub-issue B: the sharper load-factor potential -/

/--
Load factor α = num / size of a dynamic table, as a rational number (with the
Mathlib convention that division by zero yields zero for the empty allocation).
-/
def loadFactor (s : DynamicTableState) : ℚ := (s.num : ℚ) / (s.size : ℚ)

/--
Doubled, division-free integer form Ψ = 2Φ of the CLRS load-factor potential.
When α ≥ 1/2 (equivalently `size ≤ 2 * num`) it is `4 * num - 2 * size`;
otherwise it is `size - 2 * num`.  Doubling clears the `size / 2` that appears in
the textbook potential so that the branch algebra stays over the integers.
-/
def sharpPotentialZ (s : DynamicTableState) : Int :=
  if s.size ≤ 2 * s.num then
    4 * (s.num : Int) - 2 * (s.size : Int)
  else
    (s.size : Int) - 2 * (s.num : Int)

/--
The CLRS load-factor potential Φ = Ψ / 2: it is `2 * num - size` when α ≥ 1/2 and
`size / 2 - num` when α < 1/2.
-/
def sharpPotential (s : DynamicTableState) : ℚ := (sharpPotentialZ s : ℚ) / 2

/-- The doubled load-factor potential is nonnegative. -/
theorem sharpPotentialZ_nonneg (s : DynamicTableState) : 0 ≤ sharpPotentialZ s := by
  unfold sharpPotentialZ
  split <;> omega

/-- The CLRS load-factor potential is nonnegative. -/
theorem sharpPotential_nonneg (s : DynamicTableState) : 0 ≤ sharpPotential s := by
  unfold sharpPotential
  apply div_nonneg _ (by norm_num)
  exact_mod_cast sharpPotentialZ_nonneg s

/--
Sharper contraction capacity: on contraction, halve the table to exactly twice
the post-deletion count so that the resulting load factor is exactly 1/2.
Otherwise keep the current capacity.
-/
def sharpDeleteSize (s : DynamicTableState) : Nat :=
  if 4 * (s.num - 1) ≤ s.size then 2 * (s.num - 1) else s.size

/-- Sharper deletion/contraction transition. -/
def sharpDelete (s : DynamicTableState) : DynamicTableState :=
  { num := s.num - 1, size := sharpDeleteSize s }

/-- Sharper deletion cost: one delete, plus one copy per remaining element on contraction. -/
def sharpDeleteCost (s : DynamicTableState) : Nat :=
  if s.num = 0 then 0
  else if 4 * (s.num - 1) ≤ s.size then s.num
  else 1

/-- On contraction the sharper capacity halves to twice the post-deletion count. -/
theorem sharpDeleteSize_of_contract (s : DynamicTableState)
    (hc : 4 * (s.num - 1) ≤ s.size) :
    sharpDeleteSize s = 2 * (s.num - 1) := by
  unfold sharpDeleteSize; rw [if_pos hc]

/-- Without contraction the sharper capacity is unchanged. -/
theorem sharpDeleteSize_of_no_contract (s : DynamicTableState)
    (hc : ¬ 4 * (s.num - 1) ≤ s.size) :
    sharpDeleteSize s = s.size := by
  unfold sharpDeleteSize; rw [if_neg hc]

/-- Sharper deletion decrements the stored-element count, saturating at zero. -/
theorem sharpDelete_num (s : DynamicTableState) : (sharpDelete s).num = s.num - 1 := rfl

/-- Sharper deletion sets the post-state capacity to the sharper capacity choice. -/
theorem sharpDelete_size (s : DynamicTableState) :
    (sharpDelete s).size = sharpDeleteSize s := rfl

/-- Sharper deletion/contraction preserves the table-size invariant. -/
theorem sharpDelete_valid (s : DynamicTableState)
    (hvalid : DynamicTableState.Valid s) :
    DynamicTableState.Valid (sharpDelete s) := by
  unfold DynamicTableState.Valid at hvalid ⊢
  unfold sharpDelete sharpDeleteSize
  by_cases hc : 4 * (s.num - 1) ≤ s.size
  · rw [if_pos hc]
    simpa [mul_comm] using Nat.mul_le_mul (le_refl (s.num - 1)) (by decide : 1 ≤ 2)
  · rw [if_neg hc]
    exact Nat.le_trans (Nat.sub_le s.num 1) hvalid

/--
**Doubled insertion amortized bound.**  For a valid table, twice the actual
insertion cost plus the change in the doubled load-factor potential is at most
`6`.  Dividing by two gives the CLRS amortized bound of `3`.
-/
theorem sharpInsert_doubledAmortized_le_six (s : DynamicTableState)
    (hvalid : DynamicTableState.Valid s) :
    2 * (dynamicTableInsertCost s : Int)
      + sharpPotentialZ (dynamicTableInsert s) - sharpPotentialZ s ≤ 6 := by
  unfold DynamicTableState.Valid at hvalid
  by_cases hfit : s.num + 1 ≤ s.size
  · have hc : dynamicTableInsertCost s = 1 := dynamicTableInsertCost_of_fits s hfit
    have hsz : (dynamicTableInsert s).size = s.size := dynamicTableInsert_size_of_fits s hfit
    have hn : (dynamicTableInsert s).num = s.num + 1 := dynamicTableInsert_num s
    rw [hc]
    unfold sharpPotentialZ
    rw [hsz, hn]
    split <;> split <;> omega
  · have hfull := hfit
    have hc : dynamicTableInsertCost s = s.num + 1 := dynamicTableInsertCost_of_expand s hfull
    have hn : (dynamicTableInsert s).num = s.num + 1 := dynamicTableInsert_num s
    have hnum : s.num = s.size := by omega
    rcases Nat.eq_zero_or_pos s.size with hz | hpos
    · have hsz : (dynamicTableInsert s).size = 1 := by
        rw [dynamicTableInsert_size_of_expand s hfull, hnum, hz]; decide
      rw [hc]
      unfold sharpPotentialZ
      rw [hsz, hn]
      split <;> split <;> omega
    · have hsz : (dynamicTableInsert s).size = 2 * s.size := by
        rw [dynamicTableInsert_size_of_expand s hfull, hnum, max_eq_right (by omega)]
      rw [hc]
      unfold sharpPotentialZ
      rw [hsz, hn]
      split <;> split <;> omega

/--
**Insertion is O(1) amortized under the load-factor potential.**  For a valid
table, the amortized cost of `TABLE-INSERT` - actual cost plus the change in the
CLRS load-factor potential Φ - is at most `3`.  In particular this covers the
low-load case α < 1, where the actual cost is a single write.

This is CLRS Theorem 16.4-style amortized analysis for insertion.
-/
theorem sharpInsert_amortized_le_three (s : DynamicTableState)
    (hvalid : DynamicTableState.Valid s) :
    (dynamicTableInsertCost s : ℚ)
      + sharpPotential (dynamicTableInsert s) - sharpPotential s ≤ 3 := by
  have h := sharpInsert_doubledAmortized_le_six s hvalid
  have hq : (2 * (dynamicTableInsertCost s : Int)
      + sharpPotentialZ (dynamicTableInsert s) - sharpPotentialZ s : ℚ) ≤ (6 : ℚ) := by
    exact_mod_cast h
  unfold sharpPotential
  push_cast at hq
  linarith

/--
**Doubled deletion amortized bound.**  For a valid nonempty table, twice the
actual deletion cost plus the change in the doubled load-factor potential is at
most `6`.  Dividing by two gives the CLRS amortized bound of `3`.
-/
theorem sharpDelete_doubledAmortized_le_six (s : DynamicTableState)
    (hvalid : DynamicTableState.Valid s) (hne : s.num ≠ 0) :
    2 * (sharpDeleteCost s : Int)
      + sharpPotentialZ (sharpDelete s) - sharpPotentialZ s ≤ 6 := by
  unfold DynamicTableState.Valid at hvalid
  by_cases hc : 4 * (s.num - 1) ≤ s.size
  · have hcost : sharpDeleteCost s = s.num := by
      unfold sharpDeleteCost; simp [hne, hc]
    have hsz : (sharpDelete s).size = 2 * (s.num - 1) := by
      rw [sharpDelete_size, sharpDeleteSize_of_contract s hc]
    have hn : (sharpDelete s).num = s.num - 1 := sharpDelete_num s
    rw [hcost]
    unfold sharpPotentialZ
    rw [hsz, hn]
    split <;> split <;> omega
  · have hcost : sharpDeleteCost s = 1 := by
      unfold sharpDeleteCost; simp [hne, hc]
    have hsz : (sharpDelete s).size = s.size := by
      rw [sharpDelete_size, sharpDeleteSize_of_no_contract s hc]
    have hn : (sharpDelete s).num = s.num - 1 := sharpDelete_num s
    rw [hcost]
    unfold sharpPotentialZ
    rw [hsz, hn]
    split <;> split <;> omega

/--
**Deletion is O(1) amortized under the load-factor potential.**  For a valid
nonempty table, the amortized cost of `TABLE-DELETE` - actual cost plus the
change in the CLRS load-factor potential Φ - is at most `3`.  In particular this
covers the high-load case α > 1/4, where the actual cost is a single delete.

This is CLRS Theorem 16.4-style amortized analysis for deletion.
-/
theorem sharpDelete_amortized_le_three (s : DynamicTableState)
    (hvalid : DynamicTableState.Valid s) (hne : s.num ≠ 0) :
    (sharpDeleteCost s : ℚ)
      + sharpPotential (sharpDelete s) - sharpPotential s ≤ 3 := by
  have h := sharpDelete_doubledAmortized_le_six s hvalid hne
  have hq : (2 * (sharpDeleteCost s : Int)
      + sharpPotentialZ (sharpDelete s) - sharpPotentialZ s : ℚ) ≤ (6 : ℚ) := by
    exact_mod_cast h
  unfold sharpPotential
  push_cast at hq
  linarith

/--
**Load-factor guarantee after contraction.**  When a table with at least two
elements contracts, the sharper contraction restores the load factor to exactly
1/2: the new count `num - 1` sits in a table of capacity `2 * (num - 1)`.

This is the CLRS invariant that a contraction leaves the table half full.
-/
theorem sharpDelete_loadFactor_eq_half_of_contract (s : DynamicTableState)
    (hnum : 2 ≤ s.num) (hc : 4 * (s.num - 1) ≤ s.size) :
    loadFactor (sharpDelete s) = 1 / 2 := by
  unfold loadFactor
  rw [sharpDelete_num, sharpDelete_size, sharpDeleteSize_of_contract s hc]
  push_cast
  have ha : (s.num : ℚ) - 1 ≠ 0 := by
    intro h
    have hq : (s.num : ℚ) = 1 := by linarith
    have hn : s.num = 1 := by exact_mod_cast hq
    omega
  field_simp [ha]

/--
The load factor is at least 1/2 immediately after a contraction, a direct
corollary of {lit}`sharpDelete_loadFactor_eq_half_of_contract`.
-/
theorem sharpDelete_loadFactor_ge_half_of_contract (s : DynamicTableState)
    (hnum : 2 ≤ s.num) (hc : 4 * (s.num - 1) ≤ s.size) :
    1 / 2 ≤ loadFactor (sharpDelete s) := by
  rw [sharpDelete_loadFactor_eq_half_of_contract s hnum hc]

/-! ## Interleaved insert/delete trace amortization -/

/-- A dynamic-table operation: an insertion or a deletion. -/
inductive TableOp where
  | insert
  | delete
  deriving DecidableEq

/-- Apply one operation to an abstract dynamic-table state. -/
def tableStep (op : TableOp) (s : DynamicTableState) : DynamicTableState :=
  match op with
  | .insert => dynamicTableInsert s
  | .delete => sharpDelete s

/-- Actual cost of one operation in the abstract model. -/
def tableOpCost (op : TableOp) (s : DynamicTableState) : ℚ :=
  match op with
  | .insert => (dynamicTableInsertCost s : ℚ)
  | .delete => (sharpDeleteCost s : ℚ)

/-- The final state after executing a whole trace, one operation at a time. -/
def execTrace : List TableOp → DynamicTableState → DynamicTableState
  | [], s => s
  | op :: rest, s => execTrace rest (tableStep op s)

/-- The total actual cost of a whole trace. -/
def traceCost : List TableOp → DynamicTableState → ℚ
  | [], _ => 0
  | op :: rest, s => tableOpCost op s + traceCost rest (tableStep op s)

/-- Every operation preserves the table-size invariant. -/
theorem tableStep_valid (op : TableOp) (s : DynamicTableState)
    (h : DynamicTableState.Valid s) : DynamicTableState.Valid (tableStep op s) := by
  cases op with
  | insert => simpa [tableStep] using dynamicTableInsert_valid s h
  | delete => simpa [tableStep] using sharpDelete_valid s h

/-- Deleting from an empty table is free and leaves a table of capacity zero, so
its amortized cost is trivially at most `3`. -/
theorem sharpDelete_amortized_le_three_of_empty (s : DynamicTableState) (hempty : s.num = 0) :
    (sharpDeleteCost s : ℚ) + sharpPotential (sharpDelete s) - sharpPotential s ≤ 3 := by
  have hcost : (sharpDeleteCost s : ℚ) = 0 := by
    unfold sharpDeleteCost
    simp [hempty]
  have hfinal : sharpDelete s = { num := 0, size := 0 } := by
    unfold sharpDelete sharpDeleteSize
    rw [hempty]
    simp
  have hΦ0 : sharpPotential { num := 0, size := 0 } = 0 := by
    unfold sharpPotential sharpPotentialZ
    norm_num
  have hpot : sharpPotential (sharpDelete s) = 0 := by
    rw [hfinal, hΦ0]
  have hnonneg : 0 ≤ sharpPotential s := sharpPotential_nonneg s
  linarith

/--
**Single-operation amortized bound.**  Every dynamic-table operation — an
insertion or a deletion — has amortized cost at most `3` under the CLRS
load-factor potential: actual cost plus the potential change is `≤ 3`.
-/
theorem tableOp_amortized_le_three (op : TableOp) (s : DynamicTableState)
    (hvalid : DynamicTableState.Valid s) :
    tableOpCost op s + sharpPotential (tableStep op s) - sharpPotential s ≤ 3 := by
  cases op with
  | insert => simpa [tableOpCost, tableStep] using sharpInsert_amortized_le_three s hvalid
  | delete =>
      by_cases hne : s.num = 0
      · simpa [tableOpCost, tableStep] using sharpDelete_amortized_le_three_of_empty s hne
      · simpa [tableOpCost, tableStep] using sharpDelete_amortized_le_three s hvalid hne

/--
**Whole-trace amortized bound.**  The per-operation amortized bounds telescope:
for a valid initial table, a trace of `n` insertions and deletions has total
amortized cost (actual cost plus the potential change) at most `3n`.  This is
the interleaved insert/delete amortized analysis of CLRS Section 16.4.
-/
theorem trace_amortized_le (s : DynamicTableState) (hvalid : DynamicTableState.Valid s)
    (ops : List TableOp) :
    traceCost ops s + sharpPotential (execTrace ops s) - sharpPotential s ≤ 3 * (ops.length : ℚ) := by
  induction ops generalizing s hvalid with
  | nil => simp [traceCost, execTrace]
  | cons op rest ih =>
      have hstep_valid : DynamicTableState.Valid (tableStep op s) := tableStep_valid op s hvalid
      have hstep : tableOpCost op s + sharpPotential (tableStep op s) - sharpPotential s ≤ 3 :=
        tableOp_amortized_le_three op s hvalid
      have hrest := ih (tableStep op s) hstep_valid
      calc
        traceCost (op :: rest) s + sharpPotential (execTrace (op :: rest) s) - sharpPotential s
            = tableOpCost op s + traceCost rest (tableStep op s)
                + sharpPotential (execTrace rest (tableStep op s)) - sharpPotential s := rfl
        _ = tableOpCost op s
              + (traceCost rest (tableStep op s)
                + sharpPotential (execTrace rest (tableStep op s))
                - sharpPotential (tableStep op s))
              + (sharpPotential (tableStep op s) - sharpPotential s) := by ring
        _ ≤ 3 + 3 * (rest.length : ℚ) := by linarith [hstep, hrest]
        _ = 3 * ((op :: rest).length : ℚ) := by
            simp [List.length_cons]
            ring

/-- The empty table has zero potential. -/
theorem sharpPotential_empty : sharpPotential { num := 0, size := 0 } = 0 := by
  unfold sharpPotential sharpPotentialZ
  norm_num

/-- The empty table satisfies the table-size invariant. -/
theorem emptyState_valid : DynamicTableState.Valid { num := 0, size := 0 } := by
  unfold DynamicTableState.Valid
  decide

/--
**Interleaved trace cost is linear.**  Starting from the empty table, any trace
of `n` insertions and deletions has total actual cost at most `3n`: the CLRS
`O(1)` amortized bound for a sequence of dynamic-table operations.
-/
theorem trace_totalCost_le_three_mul (ops : List TableOp) :
    traceCost ops { num := 0, size := 0 } ≤ 3 * (ops.length : ℚ) := by
  have h := trace_amortized_le { num := 0, size := 0 } emptyState_valid ops
  have hfinal : 0 ≤ sharpPotential (execTrace ops { num := 0, size := 0 }) :=
    sharpPotential_nonneg _
  have hinit : sharpPotential { num := 0, size := 0 } = 0 := sharpPotential_empty
  linarith

end Chapter17
end CLRS

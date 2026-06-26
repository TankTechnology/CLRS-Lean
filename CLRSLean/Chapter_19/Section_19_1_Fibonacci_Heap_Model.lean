import Mathlib
import CLRSLean.Chapter_17.Section_17_1_Amortized_Framework

/-!
# CLRS Section 19.1 - Fibonacci heap specification model

This first-pass section records Fibonacci-heap operations at the mathematical
key-set level.  The model keeps the CLRS names for root and mark counters and
uses the standard potential function, while deferring pointer-level circular
lists and cascading-cut traces to later refinements.

Main results:

- Theorem {lit}`FibHeap.minimum_correct`: a returned minimum is represented and
  is no larger than any represented key.
- Theorems {lit}`FibHeap.minimum_mem` and {lit}`FibHeap.minimum_le`: direct
  membership and lower-bound corollaries for a returned minimum.
- Theorem {lit}`FibHeap.minimum_none_iff`: no minimum is returned exactly when
  the represented key set is empty.
- Theorem {lit}`FibHeap.makeHeap_minimum_none`: the empty heap has no minimum.
- Theorem {lit}`FibHeap.makeHeap_correct`: the empty heap represents the empty
  key set.
- Theorem {lit}`FibHeap.potential_makeHeap`: the empty heap has zero potential.
- Theorem {lit}`FibHeap.potential_nonneg`: heap potential is nonnegative.
- Theorems {lit}`FibHeap.insert_correct`, {lit}`FibHeap.union_correct`,
  {lit}`FibHeap.extractMin_correct`, {lit}`FibHeap.decreaseKey_correct`, and
  {lit}`FibHeap.delete_correct`: operations match finite-set specifications.
- Theorems {lit}`FibHeap.makeHeap_valid`, {lit}`FibHeap.insert_valid`,
  {lit}`FibHeap.union_valid`, {lit}`FibHeap.extractMin_valid`,
  {lit}`FibHeap.decreaseKey_valid`, and {lit}`FibHeap.delete_valid`:
  operation results have valid normalized counters.
- Theorems {lit}`FibHeap.insert_mem_iff`, {lit}`FibHeap.union_mem_iff`,
  {lit}`FibHeap.extractMin_mem_iff`, {lit}`FibHeap.decreaseKey_mem_iff`, and
  {lit}`FibHeap.delete_mem_iff`:
  key membership after set-updating operations matches the finite-set update.
- Theorems {lit}`FibHeap.insert_mem_self`, {lit}`FibHeap.extractMin_not_mem`,
  {lit}`FibHeap.decreaseKey_mem_new`, and {lit}`FibHeap.delete_not_mem`:
  direct membership corollaries for the updated key after heap operations.
- Theorems {lit}`FibHeap.insert_mem_old`, {lit}`FibHeap.union_mem_left`,
  {lit}`FibHeap.union_mem_right`, {lit}`FibHeap.extractMin_mem_of_ne`,
  {lit}`FibHeap.decreaseKey_mem_old`, and {lit}`FibHeap.delete_mem_of_ne`:
  direct preservation corollaries for old keys after heap operations.
- Theorems {lit}`FibHeap.insert_not_mem_iff`,
  {lit}`FibHeap.union_not_mem_iff`,
  {lit}`FibHeap.extractMin_not_mem_iff`,
  {lit}`FibHeap.decreaseKey_not_mem_iff`, and
  {lit}`FibHeap.delete_not_mem_iff`: exact failed membership specifications
  after heap operations.
- Theorems {lit}`FibHeap.insert_minimum_correct`,
  {lit}`FibHeap.union_minimum_correct`,
  {lit}`FibHeap.extractMin_remaining_minimum_correct`,
  {lit}`FibHeap.decreaseKey_minimum_correct`, and
  {lit}`FibHeap.delete_minimum_correct`: returned minima after heap updates
  are least elements of the updated key sets.
- Theorems {lit}`FibHeap.insert_minimum_mem`,
  {lit}`FibHeap.insert_minimum_le_inserted`, and
  {lit}`FibHeap.insert_minimum_le_old`: direct membership and lower-bound
  corollaries for a returned minimum after insertion.
- Theorems {lit}`FibHeap.union_minimum_mem`,
  {lit}`FibHeap.union_minimum_le_left`, and
  {lit}`FibHeap.union_minimum_le_right`: direct membership and lower-bound
  corollaries for a returned minimum after union.
- Theorems {lit}`FibHeap.extractMin_remaining_minimum_ne`,
  {lit}`FibHeap.extractMin_remaining_minimum_mem`, and
  {lit}`FibHeap.extractMin_remaining_minimum_le_old`: direct membership and
  lower-bound corollaries for a returned minimum after extract-min.
- Theorems {lit}`FibHeap.decreaseKey_minimum_mem`,
  {lit}`FibHeap.decreaseKey_minimum_le_new`, and
  {lit}`FibHeap.decreaseKey_minimum_le_old`: direct membership and
  lower-bound corollaries for a returned minimum after decrease-key.
- Theorems {lit}`FibHeap.delete_minimum_ne`,
  {lit}`FibHeap.delete_minimum_mem`, and
  {lit}`FibHeap.delete_minimum_le_old`: direct membership and lower-bound
  corollaries for a returned minimum after deletion.
- Theorems {lit}`FibHeap.insert_minimum_none_iff`,
  {lit}`FibHeap.union_minimum_none_iff`,
  {lit}`FibHeap.extractMin_remaining_minimum_none_iff`,
  {lit}`FibHeap.decreaseKey_minimum_none_iff`, and
  {lit}`FibHeap.delete_minimum_none_iff`: empty minimum results after heap
  updates match whether the updated key set is empty.
- Theorem {lit}`FibHeap.heapPotential_telescope`: heap potential instantiates
  the Chapter 17 potential-method telescoping theorem.
- Theorem {lit}`FibHeap.fibLowerBound_step`: the Fibonacci-style lower-bound
  sequence satisfies the local growth recurrence used by the degree proof.
- Theorems {lit}`FibHeap.fibLowerBound_pos` and
  {lit}`FibHeap.fibLowerBound_le_succ`: the lower-bound sequence is positive
  and adjacent-monotone.
- Theorem {lit}`FibHeap.fibLowerBound_monotone`: the lower-bound sequence is
  monotone for arbitrary indices.
- Theorems {lit}`FibHeap.fibLowerBound_add_two_ge_double` and
  {lit}`FibHeap.fibLowerBound_even_lower_bound`: the lower-bound sequence has
  the first exponential-growth bridge needed by the future degree proof.
- Theorem {lit}`FibHeap.fibLowerBound_half_lower_bound`: the exponential-growth
  bridge is available at half of any degree index.
- Theorems {lit}`FibHeap.degreeIndex_half_le_log_card` and
  {lit}`FibHeap.degreeIndex_le_twice_log_card_add_one`: a Fibonacci-style
  subtree-size lower bound condition implies a natural binary-log degree
  budget.
- Theorem {lit}`FibHeap.degree_bound_log`: the first-pass maximum-degree
  wrapper is bounded by its conservative key-count budget.

Current gaps:

- Handles, duplicate keys, consolidation arrays, and destructive pointer
  mutation are future refinement targets.
- The full subtree-size-to-logarithmic-degree theorem remains future work.
-/

namespace CLRS
namespace Chapter19

/-- Abstract Fibonacci heap state for the first-pass specification layer. -/
structure FibHeap where
  keys : Finset Int
  roots : Nat
  marked : Nat

namespace FibHeap

/-- Heap counters are valid when they do not exceed the represented key count. -/
def Valid (h : FibHeap) : Prop :=
  h.roots <= h.keys.card ∧ h.marked <= h.keys.card

/-- A heap represents exactly a finite key set and has valid counters. -/
def Represents (h : FibHeap) (s : Finset Int) : Prop :=
  h.keys = s ∧ Valid h

/-- The empty heap. -/
def makeHeap : FibHeap :=
  { keys := ∅, roots := 0, marked := 0 }

/-- The empty heap represents the empty key set. -/
theorem makeHeap_correct :
    Represents makeHeap ∅ := by
  constructor
  · simp [makeHeap]
  · simp [Valid, makeHeap]

/-- The empty heap has valid counters. -/
theorem makeHeap_valid :
    Valid makeHeap := by
  exact makeHeap_correct.2

/-- The standard Fibonacci-heap potential {lit}`roots + 2 * marked`. -/
def potential (h : FibHeap) : Int :=
  Int.ofNat h.roots + 2 * Int.ofNat h.marked

/-- The empty heap has zero Fibonacci-heap potential. -/
theorem potential_makeHeap :
    potential makeHeap = 0 := by
  simp [potential, makeHeap]

/-- Fibonacci-heap potential is always nonnegative. -/
theorem potential_nonneg (h : FibHeap) :
    0 <= potential h := by
  unfold potential
  exact add_nonneg (Int.natCast_nonneg h.roots)
    (mul_nonneg (by norm_num) (Int.natCast_nonneg h.marked))

/-- Minimum key, if the heap is nonempty. -/
def minimum (h : FibHeap) : Option Int :=
  if hne : h.keys.Nonempty then
    some (h.keys.min' hne)
  else
    none

/-- A returned minimum is represented and is a lower bound for all keys. -/
theorem minimum_correct {h : FibHeap} {s : Finset Int} {x : Int}
    (hrep : Represents h s) (hmin : minimum h = some x) :
    x ∈ s ∧ forall y, y ∈ s -> x <= y := by
  unfold minimum at hmin
  by_cases hne : h.keys.Nonempty
  · simp [hne] at hmin
    subst x
    constructor
    · simpa [hrep.1] using Finset.min'_mem h.keys hne
    · intro y hy
      have hyh : y ∈ h.keys := by
        simpa [hrep.1] using hy
      exact Finset.min'_le h.keys y hyh
  · simp [hne] at hmin

/-- A returned minimum belongs to the represented key set. -/
theorem minimum_mem {h : FibHeap} {s : Finset Int} {x : Int}
    (hrep : Represents h s) (hmin : minimum h = some x) :
    x ∈ s := by
  exact (minimum_correct (h := h) (s := s) (x := x) hrep hmin).1

/-- A returned minimum is no larger than any represented key. -/
theorem minimum_le {h : FibHeap} {s : Finset Int} {x y : Int}
    (hrep : Represents h s) (hmin : minimum h = some x) (hy : y ∈ s) :
    x <= y := by
  exact (minimum_correct (h := h) (s := s) (x := x) hrep hmin).2 y hy

/-- No minimum is returned exactly when the represented key set is empty. -/
theorem minimum_none_iff {h : FibHeap} {s : Finset Int}
    (hrep : Represents h s) :
    minimum h = none <-> s = ∅ := by
  unfold minimum
  constructor
  · intro hnone
    by_cases hne : h.keys.Nonempty
    · simp [hne] at hnone
    · have hkeysEmpty : h.keys = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      simpa [hrep.1] using hkeysEmpty
  · intro hs
    have hkeysEmpty : h.keys = ∅ := by
      simpa [hrep.1] using hs
    have hne : ¬ h.keys.Nonempty := by
      simpa [Finset.not_nonempty_iff_eq_empty] using hkeysEmpty
    simp [hne]

/-- The empty heap has no minimum key. -/
theorem makeHeap_minimum_none :
    minimum makeHeap = none := by
  rw [minimum_none_iff (h := makeHeap) (s := ∅) makeHeap_correct]

/-- Insert a key.  Counter fields are normalized to the represented key count. -/
def insert (x : Int) (h : FibHeap) : FibHeap :=
  let ks := Insert.insert x h.keys
  { keys := ks, roots := ks.card, marked := 0 }

/-- Insertion adds the inserted key to the represented set. -/
theorem insert_correct {h : FibHeap} {s : Finset Int} {x : Int}
    (hrep : Represents h s) :
    Represents (insert x h) (Insert.insert x s) := by
  constructor
  · simp [insert, hrep.1]
  · simp [Valid, insert]

/-- Insertion normalizes counters, so the result is valid. -/
theorem insert_valid (h : FibHeap) (x : Int) :
    Valid (insert x h) := by
  simp [Valid, insert]

/-- Key membership after insertion is exactly the new key or an old key. -/
theorem insert_mem_iff (h : FibHeap) (x y : Int) :
    y ∈ (insert x h).keys <-> y = x ∨ y ∈ h.keys := by
  simp [insert]

/-- The inserted key is present after insertion. -/
theorem insert_mem_self (h : FibHeap) (x : Int) :
    x ∈ (insert x h).keys := by
  rw [insert_mem_iff]
  exact Or.inl rfl

/-- Old keys remain present after insertion. -/
theorem insert_mem_old (h : FibHeap) (x y : Int) (hy : y ∈ h.keys) :
    y ∈ (insert x h).keys := by
  rw [insert_mem_iff]
  exact Or.inr hy

/-- Insertion misses exactly noninserted keys absent from the old heap. -/
theorem insert_not_mem_iff (h : FibHeap) (x y : Int) :
    y ∉ (insert x h).keys <-> y ≠ x ∧ y ∉ h.keys := by
  rw [insert_mem_iff]
  constructor
  · intro hnot
    constructor
    · intro hyx
      exact hnot (Or.inl hyx)
    · intro hy
      exact hnot (Or.inr hy)
  · intro h hmem
    cases hmem with
    | inl hyx => exact h.1 hyx
    | inr hy => exact h.2 hy

/-- A returned minimum after insertion is least among the inserted key and old keys. -/
theorem insert_minimum_correct {h : FibHeap} {s : Finset Int} {x m : Int}
    (hrep : Represents h s) (hmin : minimum (insert x h) = some m) :
    (m = x ∨ m ∈ s) ∧ m <= x ∧ forall y, y ∈ s -> m <= y := by
  have hinsert : Represents (insert x h) (Insert.insert x s) :=
    insert_correct (h := h) (s := s) (x := x) hrep
  have hmin' := minimum_correct
    (h := insert x h) (s := Insert.insert x s) (x := m) hinsert hmin
  refine ⟨?_, ?_, ?_⟩
  · simpa [Finset.mem_insert] using hmin'.1
  · exact hmin'.2 x (by simp)
  · intro y hy
    exact hmin'.2 y (by simp [hy])

/-- A returned minimum after insertion is either the inserted key or an old key. -/
theorem insert_minimum_mem {h : FibHeap} {s : Finset Int} {x m : Int}
    (hrep : Represents h s) (hmin : minimum (insert x h) = some m) :
    m = x ∨ m ∈ s := by
  exact (insert_minimum_correct
    (h := h) (s := s) (x := x) (m := m) hrep hmin).1

/-- A returned minimum after insertion is no larger than the inserted key. -/
theorem insert_minimum_le_inserted {h : FibHeap} {s : Finset Int} {x m : Int}
    (hrep : Represents h s) (hmin : minimum (insert x h) = some m) :
    m <= x := by
  exact (insert_minimum_correct
    (h := h) (s := s) (x := x) (m := m) hrep hmin).2.1

/-- A returned minimum after insertion is no larger than any old key. -/
theorem insert_minimum_le_old {h : FibHeap} {s : Finset Int} {x m y : Int}
    (hrep : Represents h s) (hmin : minimum (insert x h) = some m)
    (hy : y ∈ s) :
    m <= y := by
  exact (insert_minimum_correct
    (h := h) (s := s) (x := x) (m := m) hrep hmin).2.2 y hy

/-- Insertion makes the updated heap nonempty, so no minimum-empty result is possible. -/
theorem insert_minimum_none_iff {h : FibHeap} {s : Finset Int} {x : Int}
    (hrep : Represents h s) :
    minimum (insert x h) = none <-> False := by
  have hinsert : Represents (insert x h) (Insert.insert x s) :=
    insert_correct (h := h) (s := s) (x := x) hrep
  rw [minimum_none_iff (h := insert x h) (s := Insert.insert x s) hinsert]
  simp

/-- Meld two heaps. -/
def union (h₁ h₂ : FibHeap) : FibHeap :=
  let ks := h₁.keys ∪ h₂.keys
  { keys := ks, roots := ks.card, marked := 0 }

/-- Union represents the union of the represented key sets. -/
theorem union_correct {h₁ h₂ : FibHeap} {s₁ s₂ : Finset Int}
    (hrep₁ : Represents h₁ s₁) (hrep₂ : Represents h₂ s₂) :
    Represents (union h₁ h₂) (s₁ ∪ s₂) := by
  constructor
  · simp [union, hrep₁.1, hrep₂.1]
  · simp [Valid, union]

/-- Union normalizes counters, so the result is valid. -/
theorem union_valid (h₁ h₂ : FibHeap) :
    Valid (union h₁ h₂) := by
  simp [Valid, union]

/-- Key membership after union is exactly membership in either input heap. -/
theorem union_mem_iff (h₁ h₂ : FibHeap) (x : Int) :
    x ∈ (union h₁ h₂).keys <-> x ∈ h₁.keys ∨ x ∈ h₂.keys := by
  simp [union]

/-- Keys from the left heap remain present after union. -/
theorem union_mem_left (h₁ h₂ : FibHeap) (x : Int) (hx : x ∈ h₁.keys) :
    x ∈ (union h₁ h₂).keys := by
  rw [union_mem_iff]
  exact Or.inl hx

/-- Keys from the right heap remain present after union. -/
theorem union_mem_right (h₁ h₂ : FibHeap) (x : Int) (hx : x ∈ h₂.keys) :
    x ∈ (union h₁ h₂).keys := by
  rw [union_mem_iff]
  exact Or.inr hx

/-- Union misses exactly keys absent from both input heaps. -/
theorem union_not_mem_iff (h₁ h₂ : FibHeap) (x : Int) :
    x ∉ (union h₁ h₂).keys <-> x ∉ h₁.keys ∧ x ∉ h₂.keys := by
  rw [union_mem_iff]
  constructor
  · intro hnot
    constructor
    · intro hx
      exact hnot (Or.inl hx)
    · intro hx
      exact hnot (Or.inr hx)
  · intro h hmem
    cases hmem with
    | inl hx => exact h.1 hx
    | inr hx => exact h.2 hx

/-- A returned minimum after union is least among both input key sets. -/
theorem union_minimum_correct {h₁ h₂ : FibHeap} {s₁ s₂ : Finset Int}
    {m : Int} (hrep₁ : Represents h₁ s₁) (hrep₂ : Represents h₂ s₂)
    (hmin : minimum (union h₁ h₂) = some m) :
    (m ∈ s₁ ∨ m ∈ s₂) ∧
      (forall y, y ∈ s₁ -> m <= y) ∧
      (forall y, y ∈ s₂ -> m <= y) := by
  have hunion : Represents (union h₁ h₂) (s₁ ∪ s₂) :=
    union_correct (h₁ := h₁) (h₂ := h₂) (s₁ := s₁) (s₂ := s₂)
      hrep₁ hrep₂
  have hmin' := minimum_correct
    (h := union h₁ h₂) (s := s₁ ∪ s₂) (x := m) hunion hmin
  refine ⟨?_, ?_, ?_⟩
  · simpa [Finset.mem_union] using hmin'.1
  · intro y hy
    exact hmin'.2 y (by simp [Finset.mem_union, hy])
  · intro y hy
    exact hmin'.2 y (by simp [Finset.mem_union, hy])

/-- A returned minimum after union belongs to one of the represented input sets. -/
theorem union_minimum_mem {h₁ h₂ : FibHeap} {s₁ s₂ : Finset Int}
    {m : Int} (hrep₁ : Represents h₁ s₁) (hrep₂ : Represents h₂ s₂)
    (hmin : minimum (union h₁ h₂) = some m) :
    m ∈ s₁ ∨ m ∈ s₂ := by
  exact (union_minimum_correct
    (h₁ := h₁) (h₂ := h₂) (s₁ := s₁) (s₂ := s₂) (m := m)
    hrep₁ hrep₂ hmin).1

/-- A returned minimum after union is no larger than any key from the left heap. -/
theorem union_minimum_le_left {h₁ h₂ : FibHeap} {s₁ s₂ : Finset Int}
    {m y : Int} (hrep₁ : Represents h₁ s₁) (hrep₂ : Represents h₂ s₂)
    (hmin : minimum (union h₁ h₂) = some m) (hy : y ∈ s₁) :
    m <= y := by
  exact (union_minimum_correct
    (h₁ := h₁) (h₂ := h₂) (s₁ := s₁) (s₂ := s₂) (m := m)
    hrep₁ hrep₂ hmin).2.1 y hy

/-- A returned minimum after union is no larger than any key from the right heap. -/
theorem union_minimum_le_right {h₁ h₂ : FibHeap} {s₁ s₂ : Finset Int}
    {m y : Int} (hrep₁ : Represents h₁ s₁) (hrep₂ : Represents h₂ s₂)
    (hmin : minimum (union h₁ h₂) = some m) (hy : y ∈ s₂) :
    m <= y := by
  exact (union_minimum_correct
    (h₁ := h₁) (h₂ := h₂) (s₁ := s₁) (s₂ := s₂) (m := m)
    hrep₁ hrep₂ hmin).2.2 y hy

/-- A union has no minimum exactly when both represented input sets are empty. -/
theorem union_minimum_none_iff {h₁ h₂ : FibHeap} {s₁ s₂ : Finset Int}
    (hrep₁ : Represents h₁ s₁) (hrep₂ : Represents h₂ s₂) :
    minimum (union h₁ h₂) = none <-> s₁ = ∅ ∧ s₂ = ∅ := by
  have hunion : Represents (union h₁ h₂) (s₁ ∪ s₂) :=
    union_correct (h₁ := h₁) (h₂ := h₂) (s₁ := s₁) (s₂ := s₂)
      hrep₁ hrep₂
  rw [minimum_none_iff (h := union h₁ h₂) (s := s₁ ∪ s₂) hunion]
  exact Finset.union_eq_empty

/-- Extract the minimum key, if present, and remove it from the heap. -/
def extractMin (h : FibHeap) : Option (Int × FibHeap) :=
  if hne : h.keys.Nonempty then
    let x := h.keys.min' hne
    let ks := h.keys.erase x
    some (x, { keys := ks, roots := ks.card, marked := 0 })
  else
    none

/--
Extract-min returns the old minimum and leaves a heap representing the remaining
keys.
-/
theorem extractMin_correct {h h' : FibHeap} {s : Finset Int} {x : Int}
    (hrep : Represents h s) (hextract : extractMin h = some (x, h')) :
    x ∈ s ∧ (forall y, y ∈ s -> x <= y) ∧ Represents h' (s.erase x) := by
  unfold extractMin at hextract
  by_cases hne : h.keys.Nonempty
  · simp [hne] at hextract
    rcases hextract with ⟨rfl, rfl⟩
    constructor
    · simpa [hrep.1] using Finset.min'_mem h.keys hne
    constructor
    · intro y hy
      have hyh : y ∈ h.keys := by
        simpa [hrep.1] using hy
      exact Finset.min'_le h.keys y hyh
    · constructor
      · simp [hrep.1]
      · simp [Valid]
  · simp [hne] at hextract

/-- A heap returned by extract-min has valid counters. -/
theorem extractMin_valid {h h' : FibHeap} {x : Int}
    (hextract : extractMin h = some (x, h')) :
    Valid h' := by
  unfold extractMin at hextract
  by_cases hne : h.keys.Nonempty
  · simp [hne] at hextract
    rcases hextract with ⟨rfl, rfl⟩
    simp [Valid]
  · simp [hne] at hextract

/-- Key membership after extract-min is exactly old membership away from the extracted key. -/
theorem extractMin_mem_iff {h h' : FibHeap} {x y : Int}
    (hextract : extractMin h = some (x, h')) :
    y ∈ h'.keys <-> y ≠ x ∧ y ∈ h.keys := by
  unfold extractMin at hextract
  by_cases hne : h.keys.Nonempty
  · simp [hne] at hextract
    rcases hextract with ⟨rfl, rfl⟩
    simp
  · simp [hne] at hextract

/-- The extracted minimum key is absent from the remaining heap. -/
theorem extractMin_not_mem {h h' : FibHeap} {x : Int}
    (hextract : extractMin h = some (x, h')) :
    x ∉ h'.keys := by
  rw [extractMin_mem_iff hextract]
  simp

/-- Old keys different from the extracted minimum remain present after extract-min. -/
theorem extractMin_mem_of_ne {h h' : FibHeap} {x y : Int}
    (hextract : extractMin h = some (x, h')) (hxy : y ≠ x)
    (hy : y ∈ h.keys) :
    y ∈ h'.keys := by
  rw [extractMin_mem_iff hextract]
  exact ⟨hxy, hy⟩

/-- Extract-min misses exactly the extracted key and old keys that were absent already. -/
theorem extractMin_not_mem_iff {h h' : FibHeap} {x y : Int}
    (hextract : extractMin h = some (x, h')) :
    y ∉ h'.keys <-> y = x ∨ y ∉ h.keys := by
  rw [extractMin_mem_iff hextract]
  constructor
  · intro hnot
    by_cases hxy : y = x
    · exact Or.inl hxy
    · right
      intro hy
      exact hnot ⟨hxy, hy⟩
  · intro h hmem
    cases h with
    | inl hyx => exact hmem.1 hyx
    | inr hyNot => exact hyNot hmem.2

/-- Extract-min returns nothing exactly when the represented key set is empty. -/
theorem extractMin_none_iff {h : FibHeap} {s : Finset Int}
    (hrep : Represents h s) :
    extractMin h = none <-> s = ∅ := by
  unfold extractMin
  constructor
  · intro hnone
    by_cases hne : h.keys.Nonempty
    · simp [hne] at hnone
    · have hkeysEmpty : h.keys = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      simpa [hrep.1] using hkeysEmpty
  · intro hs
    have hkeysEmpty : h.keys = ∅ := by
      simpa [hrep.1] using hs
    have hne : ¬ h.keys.Nonempty := by
      simpa [Finset.not_nonempty_iff_eq_empty] using hkeysEmpty
    simp [hne]

/-- A returned minimum in the heap left by extract-min is least among remaining old keys. -/
theorem extractMin_remaining_minimum_correct {h h' : FibHeap}
    {s : Finset Int} {x m : Int} (hrep : Represents h s)
    (hextract : extractMin h = some (x, h'))
    (hmin : minimum h' = some m) :
    m ≠ x ∧ m ∈ s ∧ forall y, y ∈ s -> y ≠ x -> m <= y := by
  have hextract' := extractMin_correct
    (h := h) (h' := h') (s := s) (x := x) hrep hextract
  have hmin' := minimum_correct
    (h := h') (s := s.erase x) (x := m) hextract'.2.2 hmin
  have hmem : m ≠ x ∧ m ∈ s := by
    simpa [Finset.mem_erase] using hmin'.1
  refine ⟨hmem.1, hmem.2, ?_⟩
  intro y hy hyx
  exact hmin'.2 y (by simp [Finset.mem_erase, hyx, hy])

/-- A returned remaining minimum after extract-min is not the extracted key. -/
theorem extractMin_remaining_minimum_ne {h h' : FibHeap}
    {s : Finset Int} {x m : Int} (hrep : Represents h s)
    (hextract : extractMin h = some (x, h'))
    (hmin : minimum h' = some m) :
    m ≠ x := by
  exact (extractMin_remaining_minimum_correct
    (h := h) (h' := h') (s := s) (x := x) (m := m)
    hrep hextract hmin).1

/-- A returned remaining minimum after extract-min is an old key. -/
theorem extractMin_remaining_minimum_mem {h h' : FibHeap}
    {s : Finset Int} {x m : Int} (hrep : Represents h s)
    (hextract : extractMin h = some (x, h'))
    (hmin : minimum h' = some m) :
    m ∈ s := by
  exact (extractMin_remaining_minimum_correct
    (h := h) (h' := h') (s := s) (x := x) (m := m)
    hrep hextract hmin).2.1

/-- A returned remaining minimum after extract-min is no larger than any remaining old key. -/
theorem extractMin_remaining_minimum_le_old {h h' : FibHeap}
    {s : Finset Int} {x m y : Int} (hrep : Represents h s)
    (hextract : extractMin h = some (x, h'))
    (hmin : minimum h' = some m) (hy : y ∈ s) (hyx : y ≠ x) :
    m <= y := by
  exact (extractMin_remaining_minimum_correct
    (h := h) (h' := h') (s := s) (x := x) (m := m)
    hrep hextract hmin).2.2 y hy hyx

/-- No remaining minimum after extract-min means every old key was the extracted key. -/
theorem extractMin_remaining_minimum_none_iff {h h' : FibHeap}
    {s : Finset Int} {x : Int} (hrep : Represents h s)
    (hextract : extractMin h = some (x, h')) :
    minimum h' = none <-> forall y, y ∈ s -> y = x := by
  have hextract' := extractMin_correct
    (h := h) (h' := h') (s := s) (x := x) hrep hextract
  rw [minimum_none_iff (h := h') (s := s.erase x) hextract'.2.2]
  constructor
  · intro hempty y hy
    by_contra hyx
    have hyerase : y ∈ s.erase x := by
      simp [Finset.mem_erase, hyx, hy]
    have hnot : y ∉ s.erase x := by
      simp [hempty]
    exact False.elim (hnot hyerase)
  · intro hall
    ext y
    constructor
    · intro hyerase
      rw [Finset.mem_erase] at hyerase
      exact False.elim (hyerase.1 (hall y hyerase.2))
    · intro hyempty
      simp at hyempty

/-- Decrease a key by replacing an old key with a new key. -/
def decreaseKey (oldKey newKey : Int) (h : FibHeap) : FibHeap :=
  let ks := Insert.insert newKey (h.keys.erase oldKey)
  { keys := ks, roots := ks.card, marked := 0 }

/-- Decrease-key matches finite-set erase/insert replacement. -/
theorem decreaseKey_correct {h : FibHeap} {s : Finset Int} {oldKey newKey : Int}
    (hrep : Represents h s) (hnew : newKey <= oldKey) :
    Represents (decreaseKey oldKey newKey h) (Insert.insert newKey (s.erase oldKey)) ∧
      newKey <= oldKey := by
  constructor
  · constructor
    · simp [decreaseKey, hrep.1]
    · simp [Valid, decreaseKey]
  · exact hnew

/-- Decrease-key normalizes counters, so the result is valid. -/
theorem decreaseKey_valid (h : FibHeap) (oldKey newKey : Int) :
    Valid (decreaseKey oldKey newKey h) := by
  simp [Valid, decreaseKey]

/--
Key membership after decrease-key is exactly the new key or an old key other
than the replaced key.
-/
theorem decreaseKey_mem_iff (h : FibHeap) (oldKey newKey y : Int) :
    y ∈ (decreaseKey oldKey newKey h).keys <->
      y = newKey ∨ (y ≠ oldKey ∧ y ∈ h.keys) := by
  simp [decreaseKey, eq_comm]

/-- The decreased-to key is present after decrease-key. -/
theorem decreaseKey_mem_new (h : FibHeap) (oldKey newKey : Int) :
    newKey ∈ (decreaseKey oldKey newKey h).keys := by
  rw [decreaseKey_mem_iff]
  exact Or.inl rfl

/-- Old keys different from the replaced key remain present after decrease-key. -/
theorem decreaseKey_mem_old (h : FibHeap) (oldKey newKey y : Int)
    (hyold : y ≠ oldKey) (hy : y ∈ h.keys) :
    y ∈ (decreaseKey oldKey newKey h).keys := by
  rw [decreaseKey_mem_iff]
  exact Or.inr ⟨hyold, hy⟩

/-- Decrease-key misses exactly nonreplacement keys that are the old key or were absent. -/
theorem decreaseKey_not_mem_iff (h : FibHeap) (oldKey newKey y : Int) :
    y ∉ (decreaseKey oldKey newKey h).keys <->
      y ≠ newKey ∧ (y = oldKey ∨ y ∉ h.keys) := by
  rw [decreaseKey_mem_iff]
  constructor
  · intro hnot
    constructor
    · intro hynew
      exact hnot (Or.inl hynew)
    · by_cases hyold : y = oldKey
      · exact Or.inl hyold
      · right
        intro hy
        exact hnot (Or.inr ⟨hyold, hy⟩)
  · intro h hmem
    cases hmem with
    | inl hynew => exact h.1 hynew
    | inr hold =>
        cases h.2 with
        | inl hyold => exact hold.1 hyold
        | inr hyNot => exact hyNot hold.2

/-- A returned minimum after decrease-key is least among the replacement and old remaining keys. -/
theorem decreaseKey_minimum_correct {h : FibHeap} {s : Finset Int}
    {oldKey newKey m : Int} (hrep : Represents h s)
    (hnew : newKey <= oldKey)
    (hmin : minimum (decreaseKey oldKey newKey h) = some m) :
    (m = newKey ∨ (m ≠ oldKey ∧ m ∈ s)) ∧ m <= newKey ∧
      forall y, y ∈ s -> y ≠ oldKey -> m <= y := by
  have hdecrease : Represents (decreaseKey oldKey newKey h)
      (Insert.insert newKey (s.erase oldKey)) :=
    (decreaseKey_correct (h := h) (s := s) (oldKey := oldKey)
      (newKey := newKey) hrep hnew).1
  have hmin' := minimum_correct
    (h := decreaseKey oldKey newKey h)
    (s := Insert.insert newKey (s.erase oldKey)) (x := m)
    hdecrease hmin
  refine ⟨?_, ?_, ?_⟩
  · simpa [Finset.mem_insert, Finset.mem_erase] using hmin'.1
  · exact hmin'.2 newKey (by simp)
  · intro y hy hyold
    exact hmin'.2 y (by simp [Finset.mem_insert, Finset.mem_erase, hyold, hy])

/-- A returned minimum after decrease-key is the replacement or an old remaining key. -/
theorem decreaseKey_minimum_mem {h : FibHeap} {s : Finset Int}
    {oldKey newKey m : Int} (hrep : Represents h s)
    (hnew : newKey <= oldKey)
    (hmin : minimum (decreaseKey oldKey newKey h) = some m) :
    m = newKey ∨ (m ≠ oldKey ∧ m ∈ s) := by
  exact (decreaseKey_minimum_correct
    (h := h) (s := s) (oldKey := oldKey) (newKey := newKey) (m := m)
    hrep hnew hmin).1

/-- A returned minimum after decrease-key is no larger than the replacement key. -/
theorem decreaseKey_minimum_le_new {h : FibHeap} {s : Finset Int}
    {oldKey newKey m : Int} (hrep : Represents h s)
    (hnew : newKey <= oldKey)
    (hmin : minimum (decreaseKey oldKey newKey h) = some m) :
    m <= newKey := by
  exact (decreaseKey_minimum_correct
    (h := h) (s := s) (oldKey := oldKey) (newKey := newKey) (m := m)
    hrep hnew hmin).2.1

/-- A returned minimum after decrease-key is no larger than any old remaining key. -/
theorem decreaseKey_minimum_le_old {h : FibHeap} {s : Finset Int}
    {oldKey newKey m y : Int} (hrep : Represents h s)
    (hnew : newKey <= oldKey)
    (hmin : minimum (decreaseKey oldKey newKey h) = some m)
    (hy : y ∈ s) (hyold : y ≠ oldKey) :
    m <= y := by
  exact (decreaseKey_minimum_correct
    (h := h) (s := s) (oldKey := oldKey) (newKey := newKey) (m := m)
    hrep hnew hmin).2.2 y hy hyold

/-- Decrease-key inserts the replacement key, so no minimum-empty result is possible. -/
theorem decreaseKey_minimum_none_iff {h : FibHeap} {s : Finset Int}
    {oldKey newKey : Int} (hrep : Represents h s) (hnew : newKey <= oldKey) :
    minimum (decreaseKey oldKey newKey h) = none <-> False := by
  have hdecrease : Represents (decreaseKey oldKey newKey h)
      (Insert.insert newKey (s.erase oldKey)) :=
    (decreaseKey_correct (h := h) (s := s) (oldKey := oldKey)
      (newKey := newKey) hrep hnew).1
  rw [minimum_none_iff
    (h := decreaseKey oldKey newKey h)
    (s := Insert.insert newKey (s.erase oldKey)) hdecrease]
  simp

/-- Delete a key from the heap. -/
def delete (x : Int) (h : FibHeap) : FibHeap :=
  let ks := h.keys.erase x
  { keys := ks, roots := ks.card, marked := 0 }

/-- Deletion removes the key from the represented set. -/
theorem delete_correct {h : FibHeap} {s : Finset Int} {x : Int}
    (hrep : Represents h s) :
    Represents (delete x h) (s.erase x) := by
  constructor
  · simp [delete, hrep.1]
  · simp [Valid, delete]

/-- Deletion normalizes counters, so the result is valid. -/
theorem delete_valid (h : FibHeap) (x : Int) :
    Valid (delete x h) := by
  simp [Valid, delete]

/-- Key membership after deletion is exactly old membership away from the deleted key. -/
theorem delete_mem_iff (h : FibHeap) (x y : Int) :
    y ∈ (delete x h).keys <-> y ≠ x ∧ y ∈ h.keys := by
  simp [delete]

/-- The deleted key is absent after deletion. -/
theorem delete_not_mem (h : FibHeap) (x : Int) :
    x ∉ (delete x h).keys := by
  rw [delete_mem_iff]
  simp

/-- Old keys different from the deleted key remain present after deletion. -/
theorem delete_mem_of_ne (h : FibHeap) (x y : Int) (hxy : y ≠ x)
    (hy : y ∈ h.keys) :
    y ∈ (delete x h).keys := by
  rw [delete_mem_iff]
  exact ⟨hxy, hy⟩

/-- Deletion misses exactly the deleted key and old keys that were absent already. -/
theorem delete_not_mem_iff (h : FibHeap) (x y : Int) :
    y ∉ (delete x h).keys <-> y = x ∨ y ∉ h.keys := by
  rw [delete_mem_iff]
  constructor
  · intro hnot
    by_cases hyx : y = x
    · exact Or.inl hyx
    · right
      intro hy
      exact hnot ⟨hyx, hy⟩
  · intro h hmem
    cases h with
    | inl hyx => exact hmem.1 hyx
    | inr hyNot => exact hyNot hmem.2

/-- A returned minimum after deletion is least among the remaining old keys. -/
theorem delete_minimum_correct {h : FibHeap} {s : Finset Int} {x m : Int}
    (hrep : Represents h s) (hmin : minimum (delete x h) = some m) :
    m ≠ x ∧ m ∈ s ∧ forall y, y ∈ s -> y ≠ x -> m <= y := by
  have hdelete : Represents (delete x h) (s.erase x) :=
    delete_correct (h := h) (s := s) (x := x) hrep
  have hmin' := minimum_correct
    (h := delete x h) (s := s.erase x) (x := m) hdelete hmin
  have hmem : m ≠ x ∧ m ∈ s := by
    simpa [Finset.mem_erase] using hmin'.1
  refine ⟨hmem.1, hmem.2, ?_⟩
  intro y hy hyx
  exact hmin'.2 y (by simp [Finset.mem_erase, hyx, hy])

/-- A returned minimum after deletion is not the deleted key. -/
theorem delete_minimum_ne {h : FibHeap} {s : Finset Int} {x m : Int}
    (hrep : Represents h s) (hmin : minimum (delete x h) = some m) :
    m ≠ x := by
  exact (delete_minimum_correct
    (h := h) (s := s) (x := x) (m := m) hrep hmin).1

/-- A returned minimum after deletion is an old key. -/
theorem delete_minimum_mem {h : FibHeap} {s : Finset Int} {x m : Int}
    (hrep : Represents h s) (hmin : minimum (delete x h) = some m) :
    m ∈ s := by
  exact (delete_minimum_correct
    (h := h) (s := s) (x := x) (m := m) hrep hmin).2.1

/-- A returned minimum after deletion is no larger than any old remaining key. -/
theorem delete_minimum_le_old {h : FibHeap} {s : Finset Int}
    {x m y : Int} (hrep : Represents h s)
    (hmin : minimum (delete x h) = some m) (hy : y ∈ s) (hyx : y ≠ x) :
    m <= y := by
  exact (delete_minimum_correct
    (h := h) (s := s) (x := x) (m := m) hrep hmin).2.2 y hy hyx

/-- No minimum after deletion means every old key was the deleted key. -/
theorem delete_minimum_none_iff {h : FibHeap} {s : Finset Int} {x : Int}
    (hrep : Represents h s) :
    minimum (delete x h) = none <-> forall y, y ∈ s -> y = x := by
  have hdelete : Represents (delete x h) (s.erase x) :=
    delete_correct (h := h) (s := s) (x := x) hrep
  rw [minimum_none_iff (h := delete x h) (s := s.erase x) hdelete]
  constructor
  · intro hempty y hy
    by_contra hyx
    have hyerase : y ∈ s.erase x := by
      simp [Finset.mem_erase, hyx, hy]
    have hnot : y ∉ s.erase x := by
      simp [hempty]
    exact False.elim (hnot hyerase)
  · intro hall
    ext y
    constructor
    · intro hyerase
      rw [Finset.mem_erase] at hyerase
      exact False.elim (hyerase.1 (hall y hyerase.2))
    · intro hyempty
      simp at hyempty

/-- A heap-indexed potential trace for Chapter 17's potential method. -/
def potentialTrace (heap : Nat -> FibHeap) (actual : Nat -> Int) :
    CLRS.Chapter17.PotentialTrace :=
  { actual := actual, potential := fun i => potential (heap i) }

/-- Heap potential telescopes exactly by the Chapter 17 potential theorem. -/
theorem heapPotential_telescope
    (heap : Nat -> FibHeap) (actual : Nat -> Int) (n : Nat) :
    CLRS.Chapter17.prefixCostR actual n =
      CLRS.Chapter17.prefixCostR
        (CLRS.Chapter17.amortizedCost (potentialTrace heap actual)) n -
          (potential (heap n) - potential (heap 0)) := by
  exact CLRS.Chapter17.potential_totalCost_eq_totalAmortized_sub_delta
    (potentialTrace heap actual) n

/--
Fibonacci-style lower-bound sequence for subtree sizes.  The first two entries
are positive so later degree lemmas can use it directly as a size lower bound.
-/
def fibLowerBound : Nat -> Nat
  | 0 => 1
  | 1 => 2
  | n + 2 => fibLowerBound (n + 1) + fibLowerBound n

/-- Local Fibonacci growth recurrence for the lower-bound sequence. -/
theorem fibLowerBound_step (d : Nat) :
    fibLowerBound (d + 2) = fibLowerBound (d + 1) + fibLowerBound d := by
  rfl

/-- Every Fibonacci-style lower-bound entry is positive. -/
theorem fibLowerBound_pos (d : Nat) :
    0 < fibLowerBound d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
      cases d with
      | zero =>
          simp [fibLowerBound]
      | succ d =>
          cases d with
          | zero =>
              simp [fibLowerBound]
          | succ d =>
              change 0 < fibLowerBound (d + 1) + fibLowerBound d
              have hleft : 0 < fibLowerBound (d + 1) := ih (d + 1) (by omega)
              omega

/-- Adjacent Fibonacci-style lower-bound entries are monotone. -/
theorem fibLowerBound_le_succ (d : Nat) :
    fibLowerBound d <= fibLowerBound (d + 1) := by
  cases d with
  | zero =>
      simp [fibLowerBound]
  | succ d =>
      cases d with
      | zero =>
          simp [fibLowerBound]
      | succ d =>
          have hstep : fibLowerBound (d + 3) =
              fibLowerBound (d + 2) + fibLowerBound (d + 1) := by
            simpa using fibLowerBound_step (d + 1)
          change fibLowerBound (d + 2) <= fibLowerBound (d + 3)
          rw [hstep]
          omega

/-- Fibonacci-style lower-bound entries are monotone in the degree index. -/
theorem fibLowerBound_monotone {a b : Nat} (hab : a <= b) :
    fibLowerBound a <= fibLowerBound b := by
  induction hab with
  | refl =>
      rfl
  | step hab ih =>
      exact Nat.le_trans ih (fibLowerBound_le_succ _)

/-- Fibonacci-style lower-bound entries at least double every two degree levels. -/
theorem fibLowerBound_add_two_ge_double (d : Nat) :
    2 * fibLowerBound d <= fibLowerBound (d + 2) := by
  rw [fibLowerBound_step]
  have hmono : fibLowerBound d <= fibLowerBound (d + 1) :=
    fibLowerBound_le_succ d
  omega

/-- Even-indexed Fibonacci-style lower-bound entries dominate powers of two. -/
theorem fibLowerBound_even_lower_bound (k : Nat) :
    2 ^ k <= fibLowerBound (2 * k) := by
  induction k with
  | zero =>
      simp [fibLowerBound]
  | succ k ih =>
      calc
        2 ^ (k + 1) = 2 ^ k * 2 := by
          rw [pow_succ]
        _ = 2 * 2 ^ k := by
          rw [Nat.mul_comm]
        _ <= 2 * fibLowerBound (2 * k) := Nat.mul_le_mul_left 2 ih
        _ <= fibLowerBound (2 * (k + 1)) := by
          simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
            using fibLowerBound_add_two_ge_double (2 * k)

/-- Fibonacci-style lower-bound entries dominate powers of two at half the index. -/
theorem fibLowerBound_half_lower_bound (d : Nat) :
    2 ^ (d / 2) <= fibLowerBound d := by
  have hhalf : 2 * (d / 2) <= d := Nat.mul_div_le d 2
  exact Nat.le_trans (fibLowerBound_even_lower_bound (d / 2))
    (fibLowerBound_monotone hhalf)

/--
If a degree index has the standard Fibonacci-style subtree-size lower bound
inside the current key set, then half of the degree is bounded by the binary
floor logarithm of the key count.
-/
theorem degreeIndex_half_le_log_card {h : FibHeap} {d : Nat}
    (hfit : fibLowerBound d <= h.keys.card) :
    d / 2 <= Nat.log 2 h.keys.card := by
  have hpow : 2 ^ (d / 2) <= h.keys.card :=
    Nat.le_trans (fibLowerBound_half_lower_bound d) hfit
  exact Nat.le_log_of_pow_le (by norm_num : 1 < 2) hpow

/--
Conditional first-pass logarithmic degree bridge: a Fibonacci-style
subtree-size lower bound for degree index {lit}`d` implies the familiar
{lit}`d <= 2 * log_2 n + 1` natural-number budget.
-/
theorem degreeIndex_le_twice_log_card_add_one {h : FibHeap} {d : Nat}
    (hfit : fibLowerBound d <= h.keys.card) :
    d <= 2 * Nat.log 2 h.keys.card + 1 := by
  have hhalf : d / 2 <= Nat.log 2 h.keys.card :=
    degreeIndex_half_le_log_card hfit
  have hdecomp : d <= 2 * (d / 2) + 1 := by
    have hmod : d % 2 < 2 := Nat.mod_lt d (by norm_num)
    omega
  omega

/-- Conservative first-pass maximum-degree proxy. -/
def maxDegree (h : FibHeap) : Nat :=
  h.keys.card

/-- Conservative first-pass logarithmic-degree budget placeholder. -/
def logDegreeBudget (h : FibHeap) : Nat :=
  h.keys.card

/-- The first-pass maximum-degree proxy is bounded by its key-count budget. -/
theorem degree_bound_log (h : FibHeap) :
    maxDegree h <= logDegreeBudget h := by
  rfl

end FibHeap
end Chapter19
end CLRS

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
- Theorem {lit}`FibHeap.minimum_none_iff`: no minimum is returned exactly when
  the represented key set is empty.
- Theorem {lit}`FibHeap.makeHeap_correct`: the empty heap represents the empty
  key set.
- Theorem {lit}`FibHeap.potential_makeHeap`: the empty heap has zero potential.
- Theorem {lit}`FibHeap.potential_nonneg`: heap potential is nonnegative.
- Theorems {lit}`FibHeap.insert_correct`, {lit}`FibHeap.union_correct`,
  {lit}`FibHeap.extractMin_correct`, {lit}`FibHeap.decreaseKey_correct`, and
  {lit}`FibHeap.delete_correct`: operations match finite-set specifications.
- Theorems {lit}`FibHeap.insert_mem_iff`, {lit}`FibHeap.union_mem_iff`,
  {lit}`FibHeap.extractMin_mem_iff`, {lit}`FibHeap.decreaseKey_mem_iff`, and
  {lit}`FibHeap.delete_mem_iff`:
  key membership after set-updating operations matches the finite-set update.
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

/-- Key membership after insertion is exactly the new key or an old key. -/
theorem insert_mem_iff (h : FibHeap) (x y : Int) :
    y ∈ (insert x h).keys <-> y = x ∨ y ∈ h.keys := by
  simp [insert]

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

/-- Key membership after union is exactly membership in either input heap. -/
theorem union_mem_iff (h₁ h₂ : FibHeap) (x : Int) :
    x ∈ (union h₁ h₂).keys <-> x ∈ h₁.keys ∨ x ∈ h₂.keys := by
  simp [union]

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

/--
Key membership after decrease-key is exactly the new key or an old key other
than the replaced key.
-/
theorem decreaseKey_mem_iff (h : FibHeap) (oldKey newKey y : Int) :
    y ∈ (decreaseKey oldKey newKey h).keys <->
      y = newKey ∨ (y ≠ oldKey ∧ y ∈ h.keys) := by
  simp [decreaseKey, eq_comm]

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

/-- Key membership after deletion is exactly old membership away from the deleted key. -/
theorem delete_mem_iff (h : FibHeap) (x y : Int) :
    y ∈ (delete x h).keys <-> y ≠ x ∧ y ∈ h.keys := by
  simp [delete]

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

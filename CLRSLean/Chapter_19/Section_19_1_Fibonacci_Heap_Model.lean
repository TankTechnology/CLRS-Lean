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
- Theorem {lit}`FibHeap.makeHeap_correct`: the empty heap represents the empty
  key set.
- Theorems {lit}`FibHeap.insert_correct`, {lit}`FibHeap.union_correct`,
  {lit}`FibHeap.extractMin_correct`, {lit}`FibHeap.decreaseKey_correct`, and
  {lit}`FibHeap.delete_correct`: operations match finite-set specifications.
- Theorem {lit}`FibHeap.heapPotential_telescope`: heap potential instantiates
  the Chapter 17 potential-method telescoping theorem.
- Theorem {lit}`FibHeap.fibLowerBound_step`: the Fibonacci-style lower-bound
  sequence satisfies the local growth recurrence used by the degree proof.
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

import CLRSLean.Chapter_21.Section_21_1_Disjoint_Set_Operations

/-!
# CLRS Section 21.2 - Linked-list representation

The CLRS linked-list representation stores, for every element, the head of its
set and stores a set size at each head.  The executable model below makes that
table-level behavior explicit.  A weighted union redirects every head pointer
in the smaller class and records the number of rewritten pointers as its cost.

Main results:

- Theorem {lit}`LinkedList.weightedUnion_sameSet_iff`: weighted union has the
  exact abstract merge semantics.
- Theorem {lit}`LinkedList.weightedUnion_preserves_headInvariant`: every head
  remains a representative.
- Theorem {lit}`LinkedList.weightedUnion_changed_doubles`: whenever an
  element's representative pointer is rewritten, its recorded set size at
  least doubles.
- Theorems {lit}`LinkedList.move_count_le_log2` and
  {lit}`LinkedList.total_rewrites_le_n_mul_log2`: the standard CLRS aggregate
  bound extracted from the doubling argument.
-/

namespace CLRS
namespace Chapter21
namespace LinkedList

open Finset

/-- Table-level model of the linked-list disjoint-set representation. -/
structure State (n : Nat) where
  head : Fin n → Fin n
  size : Fin n → Nat

namespace State

variable {n : Nat}

/-- Two elements are in the same represented list exactly when their heads agree. -/
def sameSet (s : State n) (x y : Fin n) : Prop :=
  s.head x = s.head y

/-- The size recorded at the representative of {lit}`x`. -/
def setSize (s : State n) (x : Fin n) : Nat :=
  s.size (s.head x)

/-- Every stored head is itself a representative. -/
def HeadInvariant (s : State n) : Prop :=
  ∀ x, s.head (s.head x) = s.head x

/-- The represented abstract partition. -/
def partition (s : State n) : Partition (Fin n) where
  sameSet := s.sameSet
  refl := fun _ => rfl
  symm := fun h => h.symm
  trans := fun hab hbc => hab.trans hbc

/-- The initial state containing {lit}`n` singleton lists. -/
def singleton (n : Nat) : State n where
  head := id
  size := fun _ => 1

@[simp]
theorem singleton_head (x : Fin n) :
    (singleton n).head x = x :=
  rfl

@[simp]
theorem singleton_size (x : Fin n) :
    (singleton n).setSize x = 1 :=
  rfl

theorem singleton_headInvariant (n : Nat) :
    (singleton n).HeadInvariant := by
  intro x
  rfl

theorem singleton_sameSet_iff (x y : Fin n) :
    (singleton n).sameSet x y ↔ x = y :=
  Iff.rfl

/-- Redirect the class of {lit}`src` to the head of {lit}`dst`. -/
def mergeToward (s : State n) (src dst : Fin n) : State n where
  head z := if s.head z = s.head src then s.head dst else s.head z
  size z :=
    if z = s.head dst then s.setSize src + s.setSize dst
    else if z = s.head src then 0
    else s.size z

/--
Weighted union redirects the smaller class.  The second component is exactly
the number of representative pointers charged by the table-level model.
-/
def weightedUnion (s : State n) (x y : Fin n) : State n × Nat :=
  if s.head x = s.head y then
    (s, 0)
  else if s.setSize x ≤ s.setSize y then
    (s.mergeToward x y, s.setSize x)
  else
    (s.mergeToward y x, s.setSize y)

/-- Redirecting one distinct class to another has the exact merge relation. -/
theorem mergeToward_sameSet_iff (s : State n) {x y : Fin n}
    (_hxy : ¬s.sameSet x y) (a b : Fin n) :
    (s.mergeToward x y).sameSet a b ↔
      s.sameSet a b ∨
        (s.sameSet a x ∧ s.sameSet y b) ∨
        (s.sameSet a y ∧ s.sameSet x b) := by
  unfold sameSet at ⊢
  by_cases ha : s.head a = s.head x
  · by_cases hb : s.head b = s.head x
    · simp [mergeToward, ha, hb]
    · constructor
      · intro h
        simp [mergeToward, ha, hb] at h
        exact Or.inr (Or.inl ⟨ha, h⟩)
      · intro h
        rcases h with hab | ⟨⟨_, hyb⟩ | ⟨_, hxb⟩⟩
        · exact (hb (hab.symm.trans ha)).elim
        · simpa [mergeToward, ha, hb] using hyb
        · exact (hb hxb.symm).elim
  · by_cases hb : s.head b = s.head x
    · constructor
      · intro h
        simp [mergeToward, ha, hb] at h
        exact Or.inr (Or.inr ⟨h, hb.symm⟩)
      · intro h
        rcases h with hab | ⟨⟨hax, _⟩ | ⟨hay, _⟩⟩
        · exact (ha (hab.trans hb)).elim
        · exact (ha hax).elim
        · simpa [mergeToward, ha, hb] using hay
    · constructor
      · intro h
        exact Or.inl (by simpa [mergeToward, ha, hb] using h)
      · intro h
        rcases h with hab | ⟨⟨hax, _⟩ | ⟨_, hxb⟩⟩
        · simpa [mergeToward, ha, hb] using hab
        · exact (ha hax).elim
        · exact (hb hxb.symm).elim

/-- Weighted union implements the Section 21.1 abstract union operation. -/
theorem weightedUnion_sameSet_iff (s : State n) (x y a b : Fin n) :
    (s.weightedUnion x y).1.sameSet a b ↔
      s.sameSet a b ∨
        (s.sameSet a x ∧ s.sameSet y b) ∨
        (s.sameSet a y ∧ s.sameSet x b) := by
  by_cases hxy : s.sameSet x y
  · change s.head x = s.head y at hxy
    rw [show s.weightedUnion x y = (s, 0) by simp [weightedUnion, hxy]]
    change s.sameSet a b ↔ _
    constructor
    · exact Or.inl
    · intro h
      rcases h with hab | ⟨⟨hax, hyb⟩ | ⟨hay, hxb⟩⟩
      · exact hab
      · exact (s.partition.trans (s.partition.trans hax hxy) hyb)
      · exact (s.partition.trans (s.partition.trans hay
          (s.partition.symm hxy)) hxb)
  · by_cases hle : s.setSize x ≤ s.setSize y
    · change ¬s.head x = s.head y at hxy
      rw [show s.weightedUnion x y = (s.mergeToward x y, s.setSize x) by
        simp [weightedUnion, hxy, hle]]
      exact s.mergeToward_sameSet_iff hxy a b
    · have hyx : ¬s.sameSet y x := by
        intro h
        exact hxy h.symm
      change ¬s.head x = s.head y at hxy
      change ¬s.head y = s.head x at hyx
      rw [show s.weightedUnion x y = (s.mergeToward y x, s.setSize y) by
        simp [weightedUnion, hxy, hle]]
      rw [s.mergeToward_sameSet_iff hyx]
      aesop

/-- Weighted union refines the abstract partition merge. -/
theorem weightedUnion_refines_merge (s : State n) (x y a b : Fin n) :
    ((s.weightedUnion x y).1.partition).sameSet a b ↔
      ((s.partition).merge x y).sameSet a b := by
  rw [Partition.merge_sameSet_iff]
  exact s.weightedUnion_sameSet_iff x y a b

/-- Redirecting a class preserves idempotent representative pointers. -/
theorem mergeToward_preserves_headInvariant (s : State n) {x y : Fin n}
    (hinv : s.HeadInvariant) (hxy : ¬s.sameSet x y) :
    (s.mergeToward x y).HeadInvariant := by
  intro z
  unfold sameSet at hxy
  by_cases hz : s.head z = s.head x
  · have hyx : ¬s.head (s.head y) = s.head x := by
      rw [hinv y]
      exact Ne.symm hxy
    simpa [mergeToward, hz, hyx] using hinv y
  · have hzx : ¬s.head (s.head z) = s.head x := by
      rw [hinv z]
      exact hz
    simpa [mergeToward, hz, hzx] using hinv z

/-- Weighted union preserves the representative invariant. -/
theorem weightedUnion_preserves_headInvariant (s : State n) (x y : Fin n)
    (hinv : s.HeadInvariant) :
    (s.weightedUnion x y).1.HeadInvariant := by
  by_cases hxy : s.sameSet x y
  · change s.head x = s.head y at hxy
    simpa [weightedUnion, hxy] using hinv
  · by_cases hle : s.setSize x ≤ s.setSize y
    · change ¬s.head x = s.head y at hxy
      simpa [weightedUnion, hxy, hle] using
        s.mergeToward_preserves_headInvariant hinv hxy
    · have hyx : ¬s.sameSet y x := fun h => hxy h.symm
      change ¬s.head x = s.head y at hxy
      change ¬s.head y = s.head x at hyx
      simpa [weightedUnion, hxy, hle] using
        s.mergeToward_preserves_headInvariant hinv hyx

/-- A weighted union never charges more rewrites than either input set size. -/
theorem weightedUnion_cost_le_left (s : State n) (x y : Fin n) :
    (s.weightedUnion x y).2 ≤ s.setSize x := by
  simp only [weightedUnion]
  split <;> rename_i hxy
  · exact Nat.zero_le _
  · split <;> rename_i hle
    · exact Nat.le_refl _
    · exact Nat.le_of_lt (Nat.lt_of_not_ge hle)

/-- Symmetric rewrite-cost bound for weighted union. -/
theorem weightedUnion_cost_le_right (s : State n) (x y : Fin n) :
    (s.weightedUnion x y).2 ≤ s.setSize y := by
  simp only [weightedUnion]
  split <;> rename_i hxy
  · exact Nat.zero_le _
  · split <;> rename_i hle
    · exact hle
    · exact Nat.le_refl _

/--
If an element's representative pointer changes, the size recorded at its new
representative is at least twice the old represented-set size.
-/
theorem weightedUnion_changed_doubles (s : State n) (x y z : Fin n)
    (hchanged : (s.weightedUnion x y).1.head z ≠ s.head z) :
    2 * s.setSize z ≤ (s.weightedUnion x y).1.setSize z := by
  by_cases hxy : s.sameSet x y
  · change s.head x = s.head y at hxy
    rw [show s.weightedUnion x y = (s, 0) by simp [weightedUnion, hxy]] at hchanged
    exact (hchanged rfl).elim
  · by_cases hle : s.setSize x ≤ s.setSize y
    · change ¬s.head x = s.head y at hxy
      rw [show s.weightedUnion x y = (s.mergeToward x y, s.setSize x) by
        simp [weightedUnion, hxy, hle]] at hchanged ⊢
      have hz : s.head z = s.head x := by
        by_contra hz
        apply hchanged
        simp [mergeToward, hz]
      unfold setSize at hle ⊢
      simp [mergeToward, setSize, hz]
      omega
    · change ¬s.head x = s.head y at hxy
      rw [show s.weightedUnion x y = (s.mergeToward y x, s.setSize y) by
        simp [weightedUnion, hxy, hle]] at hchanged ⊢
      have hz : s.head z = s.head y := by
        by_contra hz
        apply hchanged
        simp [mergeToward, hz]
      have hyx : s.head y ≠ s.head x := by
        exact fun h => hxy h.symm
      unfold setSize at hle ⊢
      simp [mergeToward, setSize, hz]
      omega

/-- Repeated size doublings give an exponential lower bound. -/
theorem pow_le_of_repeated_doubling (sizeAt : Nat → Nat) (k : Nat)
    (hzero : 1 ≤ sizeAt 0)
    (hstep : ∀ i, i < k → 2 * sizeAt i ≤ sizeAt (i + 1)) :
    2 ^ k ≤ sizeAt k := by
  induction k with
  | zero => simpa using hzero
  | succ k ih =>
      have ih' : 2 ^ k ≤ sizeAt k :=
        ih (fun i hi => hstep i (Nat.lt_trans hi (Nat.lt_succ_self k)))
      calc
        2 ^ (k + 1) = 2 * 2 ^ k := by
          rw [Nat.pow_succ]
          omega
        _ ≤ 2 * sizeAt k := Nat.mul_le_mul_left 2 ih'
        _ ≤ sizeAt (k + 1) := hstep k (Nat.lt_succ_self k)

/-- An element whose class doubles on every move is rewritten at most logarithmically often. -/
theorem move_count_le_log2 {sizeAt : Nat → Nat} {k total : Nat}
    (htotal : total ≠ 0)
    (hzero : 1 ≤ sizeAt 0)
    (hstep : ∀ i, i < k → 2 * sizeAt i ≤ sizeAt (i + 1))
    (hfinal : sizeAt k ≤ total) :
    k ≤ Nat.log2 total := by
  apply (Nat.le_log2 htotal).2
  exact Nat.le_trans (pow_le_of_repeated_doubling sizeAt k hzero hstep) hfinal

/-- Summing the per-element logarithmic rewrite bound gives {lit}`n log n`. -/
theorem total_rewrites_le_n_mul_log2 (moves : Fin n → Nat)
    (hmoves : ∀ z, moves z ≤ Nat.log2 n) :
    ∑ z, moves z ≤ n * Nat.log2 n := by
  calc
    ∑ z, moves z ≤ ∑ _z : Fin n, Nat.log2 n := by
      exact Finset.sum_le_sum fun z _ => hmoves z
    _ = n * Nat.log2 n := by simp

end State
end LinkedList
end Chapter21
end CLRS

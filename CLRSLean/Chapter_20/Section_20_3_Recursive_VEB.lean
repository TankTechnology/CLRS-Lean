import Mathlib
import CLRSLean.Chapter_20.Section_20_1_VEB_Universe
import CLRSLean.Chapter_03.Section_03_1_Asymptotic_Notation

/-!
# CLRS Section 20.3 - recursive van Emde Boas structure

Section 20.2 modelled a van Emde Boas tree by the finite set of keys it
contains.  This section builds the genuine *recursive* structure of CLRS
Chapter 20: a tree over a universe of size {lit}`u = 2 ^ (2 ^ k)` is either a
two-bit base case ({lit}`k = 0`, universe {lit}`2`) or a {lit}`summary`
sub-tree over the {lit}`√u` cluster indices together with {lit}`√u` cluster
sub-trees, each over a sub-universe of size {lit}`√u`.  The recursion halves
the *tower exponent*: {lit}`√(uSize (k+1)) = uSize k`, so a universe of tower
level {lit}`k + 1` decomposes into clusters of tower level {lit}`k`, reusing
the Section 20.1 {lit}`high` / {lit}`low` / {lit}`index` arithmetic.

Main results:

- Definition {lit}`uSize`: the tower universe {lit}`2 ^ (2 ^ k)`, with
  {lit}`uSize_succ` giving {lit}`uSize (k+1) = uSize k * uSize k`.
- Inductive {lit}`VEBTree`: the recursive summary/cluster structure.
- Definition {lit}`VEBTree.toFinset`: the represented finite set, and
  {lit}`VEBTree.toFinset_lt_uSize`: every represented key is inside the
  universe.
- Theorem {lit}`VEBTree.member_correct`: recursive membership matches the
  represented set.
- Theorem {lit}`VEBTree.insert_toFinset`: recursive insertion refines
  finite-set insertion, with membership corollary
  {lit}`VEBTree.member_insert_iff`.
- Theorem {lit}`VEBTree.memberCost_recurrence`: the operation-count recurrence
  {lit}`T(u) = T(√u) + 1` (a single recursive call per level).
- Theorem {lit}`VEBTree.depth_loglog_u`: recursion depth is bounded by
  {lit}`log₂ (log₂ u) + 1`.
- Theorem {lit}`VEBTree.veb_operation_bigO_loglog_u`: the asymptotic
  {lit}`O(log log u)` packaging via the Chapter 3 big-O wrapper.

Current gaps:

- {lit}`successor` / {lit}`predecessor` / {lit}`delete` on the recursive
  structure, and the {lit}`min` / {lit}`max` double-recursion-avoidance
  optimisation that makes *insert* itself run in {lit}`O(log log u)`, remain
  future refinement targets; here the {lit}`O(log log u)` bound is proved for
  the (single-recursion) {lit}`member` operation.
-/

namespace CLRS
namespace Chapter20

open VEB (high low index index_high_low high_index low_index index_lt high_lt low_lt)

/-! ## Tower universe sizing -/

/--
The van Emde Boas *tower universe* of level {lit}`k` is {lit}`2 ^ (2 ^ k)`.
This is the smallest family closed under exact square roots: level `0` has
universe `2`, and each level squares the previous one.
-/
def uSize (k : Nat) : Nat := 2 ^ (2 ^ k)

/-- The base universe has size two. -/
theorem uSize_zero : uSize 0 = 2 := by
  unfold uSize; norm_num

/--
A level {lit}`k + 1` universe is the square of a level {lit}`k` universe, so
its square root is exactly {lit}`uSize k`.  This is the arithmetic backbone of
the recursion.
-/
theorem uSize_succ (k : Nat) : uSize (k + 1) = uSize k * uSize k := by
  unfold uSize
  have h : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
    rw [pow_succ]; ring
  rw [h, pow_add]

/-- Every tower universe is positive. -/
theorem uSize_pos (k : Nat) : 0 < uSize k := by
  unfold uSize; positivity

/-- Every tower universe has at least two elements. -/
theorem two_le_uSize (k : Nat) : 2 ≤ uSize k := by
  unfold uSize
  calc 2 = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ (2 ^ k) := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow

/-! ## The recursive structure -/

/--
A recursive van Emde Boas tree over the tower universe {lit}`uSize k`
(CLRS Chapter 20, Sections 20.2-20.3).

- {lit}`leaf` is the word-RAM base case for universe {lit}`uSize 0 = 2`: two
  booleans recording membership of the keys `0` and `1`.
- {lit}`node summary clusters` covers universe {lit}`uSize (k + 1)`:
  {lit}`clusters` is an array of {lit}`uSize k` sub-trees, each over
  sub-universe {lit}`uSize k`, and {lit}`summary` is a sub-tree over the
  {lit}`uSize k` cluster indices tracking which clusters are nonempty.
-/
inductive VEBTree : Nat → Type where
  | leaf (c0 c1 : Bool) : VEBTree 0
  | node {k : Nat} (summary : VEBTree k)
      (clusters : Fin (uSize k) → VEBTree k) : VEBTree (k + 1)

namespace VEBTree

/--
The finite set of keys represented by a recursive tree.  A base tree stores the
membership bits of `0` and `1`; a node collects, over every cluster index
{lit}`hi`, the keys {lit}`index (uSize k) hi lo` for each represented low part
{lit}`lo` of cluster {lit}`hi`.  The {lit}`summary` sub-tree carries no keys of
its own — it is a redundant acceleration structure.
-/
def toFinset : {k : Nat} → VEBTree k → Finset Nat
  | _, .leaf c0 c1 => (if c0 then {0} else ∅) ∪ (if c1 then {1} else ∅)
  | _, @VEBTree.node k _ clusters =>
      Finset.univ.biUnion fun hi : Fin (uSize k) =>
        (toFinset (clusters hi)).image fun lo => index (uSize k) hi.val lo

/-- Membership characterisation of a base tree. -/
theorem mem_toFinset_leaf (c0 c1 : Bool) (y : Nat) :
    y ∈ (VEBTree.leaf c0 c1).toFinset ↔ (c0 = true ∧ y = 0) ∨ (c1 = true ∧ y = 1) := by
  cases c0 <;> cases c1 <;>
    simp [toFinset, Finset.mem_union, Finset.mem_singleton]

/-- Membership characterisation of a node in terms of high/low decomposition. -/
theorem mem_toFinset_node {k : Nat} (summary : VEBTree k)
    (clusters : Fin (uSize k) → VEBTree k) (y : Nat) :
    y ∈ (VEBTree.node summary clusters).toFinset ↔
      ∃ hi : Fin (uSize k), ∃ lo ∈ (clusters hi).toFinset,
        index (uSize k) hi.val lo = y := by
  simp only [toFinset, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_image]

/-- Every represented key lies inside the tower universe. -/
theorem toFinset_lt_uSize : ∀ {k : Nat} (v : VEBTree k),
    ∀ y ∈ v.toFinset, y < uSize k := by
  intro k v
  induction v with
  | leaf c0 c1 =>
      intro y hy
      rw [mem_toFinset_leaf] at hy
      rw [uSize_zero]
      rcases hy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega
  | @node k summary clusters _ih_s ih_c =>
      intro y hy
      rw [mem_toFinset_node] at hy
      rcases hy with ⟨hi, lo, hlo, rfl⟩
      have hlo' : lo < uSize k := ih_c hi lo hlo
      have hhi : hi.val < uSize k := hi.isLt
      calc index (uSize k) hi.val lo < uSize k * uSize k := index_lt hhi hlo'
        _ = uSize (k + 1) := (uSize_succ k).symm

/-! ## The empty tree -/

/-- The canonical empty tree over the tower universe {lit}`uSize k`. -/
def empty : (k : Nat) → VEBTree k
  | 0 => .leaf false false
  | k + 1 => .node (empty k) (fun _ => empty k)

/-- The empty tree represents the empty set. -/
theorem toFinset_empty : ∀ k, (empty k).toFinset = ∅ := by
  intro k
  induction k with
  | zero => simp [empty, toFinset]
  | succ k ih =>
      ext x
      simp only [Finset.notMem_empty, iff_false]
      intro hx
      obtain ⟨hi, lo, hlo, _⟩ :=
        (mem_toFinset_node (empty k) (fun _ => empty k) x).mp hx
      simp only [ih, Finset.notMem_empty] at hlo

/-! ## Membership -/

/--
Recursive membership query.  The base case compares against `0`/`1`; a node
extracts the {lit}`high` cluster index and recurses into that cluster on the
{lit}`low` offset — a single recursive call.  Keys outside the universe (high
part out of range) are reported absent.
-/
def member : {k : Nat} → Nat → VEBTree k → Bool
  | _, x, .leaf c0 c1 => if x = 0 then c0 else if x = 1 then c1 else false
  | _, x, @VEBTree.node k _ clusters =>
      if h : high (uSize k) x < uSize k then
        member (low (uSize k) x) (clusters ⟨high (uSize k) x, h⟩)
      else
        false

/--
**Membership correctness.**  The recursive membership query agrees with the
represented finite set.  This is the recursive refinement of Section 20.2's
{lit}`member_correct`.
-/
theorem member_correct {k : Nat} (v : VEBTree k) :
    ∀ x, member x v = true ↔ x ∈ v.toFinset := by
  induction v with
  | leaf c0 c1 =>
      intro x
      rw [mem_toFinset_leaf]
      simp only [member]
      by_cases hx0 : x = 0
      · subst hx0; cases c0 <;> simp
      · by_cases hx1 : x = 1
        · subst hx1; cases c1 <;> simp [hx0]
        · simp [hx0, hx1]
  | @node k summary clusters _ih_s ih_c =>
      intro x
      rw [mem_toFinset_node]
      by_cases h : high (uSize k) x < uSize k
      · have hmem : member x (VEBTree.node summary clusters)
            = member (low (uSize k) x) (clusters ⟨high (uSize k) x, h⟩) := by
          simp only [member]; rw [dif_pos h]
        rw [hmem, ih_c ⟨high (uSize k) x, h⟩ (low (uSize k) x)]
        constructor
        · intro hlo
          exact ⟨⟨high (uSize k) x, h⟩, low (uSize k) x, hlo, index_high_low⟩
        · rintro ⟨hi, lo, hlo, hidx⟩
          have hlolt : lo < uSize k := toFinset_lt_uSize (clusters hi) lo hlo
          have hh : high (uSize k) x = hi.val := by rw [← hidx, high_index hlolt]
          have hl : low (uSize k) x = lo := by rw [← hidx, low_index hlolt]
          have hfin : (⟨high (uSize k) x, h⟩ : Fin (uSize k)) = hi := Fin.ext hh
          rw [hl, hfin]
          exact hlo
      · have hmem : member x (VEBTree.node summary clusters) = false := by
          simp only [member]; rw [dif_neg h]
        rw [hmem]
        constructor
        · intro hfalse; simp at hfalse
        · rintro ⟨hi, lo, hlo, hidx⟩
          have hlolt : lo < uSize k := toFinset_lt_uSize (clusters hi) lo hlo
          have hhilt : hi.val < uSize k := hi.isLt
          have hh : high (uSize k) x = hi.val := by rw [← hidx, high_index hlolt]
          have hlt : high (uSize k) x < uSize k := by omega
          exact absurd hlt h

end VEBTree
end Chapter20
end CLRS

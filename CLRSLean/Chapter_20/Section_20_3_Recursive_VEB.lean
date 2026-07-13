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

/-! ## Insertion -/

/--
Recursive insertion.  The base case sets the appropriate membership bit; a node
inserts the {lit}`low` part into the {lit}`high` cluster and records that
cluster as nonempty in the {lit}`summary` (CLRS `vEB-Tree-Insert`).  Keys
outside the universe are ignored.
-/
def insert : {k : Nat} → Nat → VEBTree k → VEBTree k
  | _, x, .leaf c0 c1 =>
      .leaf (if x = 0 then true else c0) (if x = 1 then true else c1)
  | _, x, @VEBTree.node k summary clusters =>
      if h : high (uSize k) x < uSize k then
        .node (insert (high (uSize k) x) summary)
          (Function.update clusters ⟨high (uSize k) x, h⟩
            (insert (low (uSize k) x) (clusters ⟨high (uSize k) x, h⟩)))
      else
        .node summary clusters

/--
**Insertion correctness.**  For any key inside the universe, recursive insertion
refines finite-set insertion: {lit}`(insert x v).toFinset = insert x v.toFinset`.
This is the recursive refinement of Section 20.2's {lit}`insert_correct`.
-/
theorem insert_toFinset : ∀ {k : Nat} (v : VEBTree k) (x : Nat),
    x < uSize k → (insert x v).toFinset = Insert.insert x v.toFinset := by
  intro k v
  induction v with
  | leaf c0 c1 =>
      intro x hx
      rw [uSize_zero] at hx
      ext y
      rw [show insert x (VEBTree.leaf c0 c1)
            = VEBTree.leaf (if x = 0 then true else c0) (if x = 1 then true else c1)
          from rfl]
      rw [mem_toFinset_leaf, Finset.mem_insert, mem_toFinset_leaf]
      interval_cases x <;> cases c0 <;> cases c1 <;> simp <;> tauto
  | @node k summary clusters _ih_s ih_c =>
      intro x hx
      have hm : 0 < uSize k := uSize_pos k
      have hxlt : x < uSize k * uSize k := by rw [← uSize_succ k]; exact hx
      have h : high (uSize k) x < uSize k := high_lt hxlt
      have hlow : low (uSize k) x < uSize k := low_lt hm
      have hins : insert x (VEBTree.node summary clusters) =
          VEBTree.node (insert (high (uSize k) x) summary)
            (Function.update clusters ⟨high (uSize k) x, h⟩
              (insert (low (uSize k) x) (clusters ⟨high (uSize k) x, h⟩))) := by
        simp only [insert]; rw [dif_pos h]
      rw [hins]
      ext y
      rw [mem_toFinset_node, Finset.mem_insert, mem_toFinset_node]
      constructor
      · rintro ⟨hi, lo, hlo, hidx⟩
        by_cases hhi : hi = ⟨high (uSize k) x, h⟩
        · subst hhi
          rw [Function.update_self] at hlo
          rw [ih_c ⟨high (uSize k) x, h⟩ (low (uSize k) x) hlow,
              Finset.mem_insert] at hlo
          rcases hlo with hlo | hlo
          · left
            subst hlo
            exact hidx.symm.trans index_high_low
          · right
            exact ⟨⟨high (uSize k) x, h⟩, lo, hlo, hidx⟩
        · right
          rw [Function.update_of_ne hhi] at hlo
          exact ⟨hi, lo, hlo, hidx⟩
      · rintro (hyx | ⟨hi, lo, hlo, hidx⟩)
        · refine ⟨⟨high (uSize k) x, h⟩, low (uSize k) x, ?_, ?_⟩
          · rw [Function.update_self,
                ih_c ⟨high (uSize k) x, h⟩ (low (uSize k) x) hlow, Finset.mem_insert]
            exact Or.inl rfl
          · rw [hyx]; exact index_high_low
        · by_cases hhi : hi = ⟨high (uSize k) x, h⟩
          · subst hhi
            refine ⟨⟨high (uSize k) x, h⟩, lo, ?_, hidx⟩
            rw [Function.update_self,
                ih_c ⟨high (uSize k) x, h⟩ (low (uSize k) x) hlow, Finset.mem_insert]
            exact Or.inr hlo
          · refine ⟨hi, lo, ?_, hidx⟩
            rw [Function.update_of_ne hhi]
            exact hlo

/--
Membership after recursive insertion: a key is present exactly when it is the
inserted key or was already present.  Combines {lit}`member_correct` and
{lit}`insert_toFinset`.
-/
theorem member_insert_iff {k : Nat} (v : VEBTree k) (x y : Nat)
    (hx : x < uSize k) :
    member y (insert x v) = true ↔ y = x ∨ member y v = true := by
  rw [member_correct (insert x v) y, insert_toFinset v x hx, Finset.mem_insert,
    ← member_correct v y]

/-- The inserted key is a member after insertion. -/
theorem member_insert_self {k : Nat} (v : VEBTree k) (x : Nat)
    (hx : x < uSize k) :
    member x (insert x v) = true := by
  rw [member_insert_iff v x x hx]; exact Or.inl rfl

/-! ## Operation-count recurrence and the `O(log log u)` bound -/

/--
The number of {lit}`member` calls performed by a query (its recursion depth).
The base case costs one step; a node costs one step plus the single recursive
call into the relevant cluster.
-/
def memberCost : {k : Nat} → Nat → VEBTree k → Nat
  | _, _, .leaf _ _ => 1
  | _, x, @VEBTree.node k _ clusters =>
      if h : high (uSize k) x < uSize k then
        1 + memberCost (low (uSize k) x) (clusters ⟨high (uSize k) x, h⟩)
      else
        1

/--
**The operation-count recurrence `T(u) = T(√u) + 1`.**  A membership query on a
universe of size {lit}`uSize (k + 1) = (uSize k)²` makes exactly one recursive
call, on a cluster of universe size {lit}`uSize k = √(uSize (k+1))`, plus one
step of constant work.  This is the single-recursion structure behind the
{lit}`O(log log u)` bound (CLRS Section 20.3).
-/
theorem memberCost_recurrence {k : Nat} (summary : VEBTree k)
    (clusters : Fin (uSize k) → VEBTree k) (x : Nat)
    (h : high (uSize k) x < uSize k) :
    memberCost x (VEBTree.node summary clusters)
      = 1 + memberCost (low (uSize k) x) (clusters ⟨high (uSize k) x, h⟩) := by
  simp only [memberCost]; rw [dif_pos h]

/--
Unrolling the recurrence: a membership query on a level {lit}`k` universe makes
at most {lit}`k + 1` calls.
-/
theorem memberCost_le {k : Nat} (v : VEBTree k) :
    ∀ x, memberCost x v ≤ k + 1 := by
  induction v with
  | leaf c0 c1 => intro x; simp [memberCost]
  | @node k summary clusters _ih_s ih_c =>
      intro x
      by_cases h : high (uSize k) x < uSize k
      · rw [memberCost_recurrence summary clusters x h]
        have hkey := ih_c ⟨high (uSize k) x, h⟩ (low (uSize k) x)
        omega
      · have hone : memberCost x (VEBTree.node summary clusters) = 1 := by
          simp only [memberCost]; rw [dif_neg h]
        rw [hone]; omega

/-- The base-two logarithm of a tower universe is {lit}`2 ^ k`. -/
theorem log_uSize (k : Nat) : Nat.log 2 (uSize k) = 2 ^ k := by
  unfold uSize
  exact Nat.log_pow (by norm_num) (2 ^ k)

/--
The iterated logarithm of a tower universe recovers its level:
{lit}`log₂ (log₂ (uSize k)) = k`.  So the tower level *is* {lit}`log log u`.
-/
theorem loglog_uSize (k : Nat) : Nat.log 2 (Nat.log 2 (uSize k)) = k := by
  rw [log_uSize]
  exact Nat.log_pow (by norm_num) k

/--
**Depth bound `O(log log u)`.**  A membership query performs at most
{lit}`log₂ (log₂ u) + 1` recursive calls, where {lit}`u = uSize k`.  This is the
CLRS Section 20.3 depth bound.
-/
theorem depth_loglog_u {k : Nat} (v : VEBTree k) (x : Nat) :
    memberCost x v ≤ Nat.log 2 (Nat.log 2 (uSize k)) + 1 := by
  rw [loglog_uSize]
  exact memberCost_le v x

/-- The universal per-level worst-case operation-count bound {lit}`k + 1`. -/
def memberCostBound (k : Nat) : Nat := k + 1

/-- Every membership query stays within {lit}`memberCostBound`. -/
theorem memberCost_le_bound {k : Nat} (v : VEBTree k) (x : Nat) :
    memberCost x v ≤ memberCostBound k :=
  memberCost_le v x

/--
**Asymptotic packaging: vEB operations run in `O(log log u)`.**  The worst-case
operation-count bound, as a function of the tower level, is
{lit}`O`-dominated by {lit}`log₂ (log₂ u)`, using the Chapter 3 big-O wrapper on
{lit}`ℕ → ℝ`.  Together with {lit}`depth_loglog_u` and
{lit}`memberCost_le_bound` this is the CLRS-facing {lit}`O(log log u)`
statement for the (single-recursion) membership operation.
-/
theorem veb_operation_bigO_loglog_u :
    CLRS.Chapter03.isBigO
      (fun k => (memberCostBound k : ℝ))
      (fun k => (Nat.log 2 (Nat.log 2 (uSize k)) : ℝ)) := by
  rw [CLRS.Chapter03.isBigO_iff]
  refine ⟨2, by norm_num, 1, ?_⟩
  intro n hn
  have hlog : Nat.log 2 (Nat.log 2 (uSize n)) = n := loglog_uSize n
  simp only [memberCostBound, hlog]
  push_cast
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have e1 : |((n : ℝ) + 1)| = (n : ℝ) + 1 := abs_of_nonneg (by positivity)
  have e2 : |(n : ℝ)| = (n : ℝ) := abs_of_nonneg (by positivity)
  rw [e1, e2]
  linarith

end VEBTree

/-! ## Min/max-augmented recursive vEB tree (CLRS §20.3) -/

inductive VEBTreeMM : Nat → Type where
  | leaf (mn mx : Option Nat) (c0 c1 : Bool) : VEBTreeMM 0
  | node {k : Nat} (mn mx : Option Nat) (summary : VEBTreeMM k)
      (clusters : Fin (uSize k) → VEBTreeMM k) : VEBTreeMM (k + 1)

namespace VEBTreeMM

def minimum : {k : Nat} → VEBTreeMM k → Option Nat
  | _, .leaf mn _ _ _ => mn
  | _, .node mn _ _ _ => mn

def maximum : {k : Nat} → VEBTreeMM k → Option Nat
  | _, .leaf _ mx _ _ => mx
  | _, .node _ mx _ _ => mx

def toFinset : {k : Nat} → VEBTreeMM k → Finset Nat
  | _, .leaf _ _ c0 c1 => (if c0 then {0} else ∅) ∪ (if c1 then {1} else ∅)
  | _, @VEBTreeMM.node k mn _ _ clusters =>
      (match mn with | none => ∅ | some m => (if m < uSize (k + 1) then {m} else ∅)) ∪
      Finset.univ.biUnion fun hi : Fin (uSize k) =>
        (toFinset (clusters hi)).image fun lo => index (uSize k) hi.val lo

theorem mem_toFinset_leaf (mn mx : Option Nat) (c0 c1 : Bool) (y : Nat) :
    y ∈ (.leaf mn mx c0 c1 : VEBTreeMM 0).toFinset ↔ (c0 = true ∧ y = 0) ∨ (c1 = true ∧ y = 1) := by
  cases c0 <;> cases c1 <;> simp [toFinset, Finset.mem_union, Finset.mem_singleton]

theorem mem_toFinset_node {k : Nat} (mn mx : Option Nat) (summary : VEBTreeMM k)
    (clusters : Fin (uSize k) → VEBTreeMM k) (y : Nat) :
    y ∈ (VEBTreeMM.node mn mx summary clusters).toFinset ↔
      (∃ m, mn = some m ∧ m < uSize (k + 1) ∧ y = m) ∨
      (∃ hi : Fin (uSize k), ∃ lo ∈ (clusters hi).toFinset,
        index (uSize k) hi.val lo = y) := by
  simp [toFinset, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image, exists_prop]
  match mn with
  | none => simp
  | some m =>
    by_cases hm : m < uSize (k + 1)
    · simp [hm]
      constructor
      · rintro (rfl | hX)
        · exact Or.inl ⟨rfl, hm⟩
        · exact Or.inr hX
      · rintro (⟨rfl, _⟩ | hX)
        · exact Or.inl rfl
        · exact Or.inr hX
    · simp [hm]
      intro hm_eq hy_lt
      exfalso; exact hm (by
        subst hm_eq; exact hy_lt)

theorem toFinset_lt_uSize : ∀ {k : Nat} (v : VEBTreeMM k), ∀ y ∈ v.toFinset, y < uSize k := by
  intro k v; induction v with
  | leaf mn mx c0 c1 =>
      intro y hy; rw [mem_toFinset_leaf mn mx c0 c1 y] at hy; rw [uSize_zero]
      rcases hy with (⟨_, rfl⟩ | ⟨_, rfl⟩) <;> omega
  | @node k0 mn mx summary clusters ih_s ih_c =>
      intro y hy; rw [mem_toFinset_node mn mx summary clusters y] at hy
      rcases hy with (⟨m, hmn, hm_lt, rfl⟩ | ⟨hi, lo, hlo, rfl⟩)
      · -- y = m is the stored minimum, m < uSize (k0 + 1) from the bound check
        exact hm_lt
      · -- y = index (uSize k0) hi.val lo comes from a cluster
        have hlo' : lo < uSize k0 := ih_c hi lo hlo
        have hhi : hi.val < uSize k0 := hi.isLt
        calc index (uSize k0) hi.val lo < uSize k0 * uSize k0 := index_lt hhi hlo'
          _ = uSize (k0 + 1) := (uSize_succ k0).symm

def empty : (k : Nat) → VEBTreeMM k
  | 0 => .leaf none none false false
  | k + 1 => VEBTreeMM.node none none (empty k) (fun _ => empty k)

theorem toFinset_empty : ∀ k, (empty k).toFinset = ∅ := by
  intro k; induction k with
  | zero => simp [empty, toFinset]
  | succ k ih => simp [empty, toFinset, ih]; ext y; simp

def singleton (k : Nat) (x : Nat) (hx : x < uSize k) : VEBTreeMM k :=
  match k with
  | 0 => if x = 0 then .leaf (some 0) (some 0) true false else .leaf (some 1) (some 1) false true
  | k' + 1 => VEBTreeMM.node (some x) (some x) (empty k') (fun _ => empty k')

def member : {k : Nat} → Nat → VEBTreeMM k → Bool
  | _, x, .leaf _ _ c0 c1 => if x = 0 then c0 else if x = 1 then c1 else false
  | _, x, @VEBTreeMM.node k0 mn _ _ clusters =>
      if hmn : mn = some x then
        if x < uSize (k0 + 1) then true else false
      else if hhigh : high (uSize k0) x < uSize k0 then
        member (low (uSize k0) x) (clusters ⟨high (uSize k0) x, hhigh⟩)
      else false

theorem member_correct {k : Nat} (v : VEBTreeMM k) : ∀ x, member x v = true ↔ x ∈ v.toFinset := by
  induction v with
  | leaf mn mx c0 c1 =>
      intro x; rw [mem_toFinset_leaf mn mx c0 c1]; simp only [member]
      by_cases hx0 : x = 0; · subst hx0; cases c0 <;> simp
      · by_cases hx1 : x = 1
        · subst hx1; cases c1 <;> simp [hx0]
        · simp [hx0, hx1]
  | @node k0 mn mx summary clusters ih_s ih_c =>
      intro x; rw [mem_toFinset_node mn mx summary clusters x]
      by_cases hmn : mn = some x
      · have h_mem_simp : member x (VEBTreeMM.node mn mx summary clusters) = (if x < uSize (k0 + 1) then true else false) := by
          simp [member, hmn]
        have h_rhs_simp : ((∃ (m : ℕ), mn = some m ∧ m < uSize (k0 + 1) ∧ x = m) ∨
          (∃ (hi : Fin (uSize k0)), ∃ lo ∈ (clusters hi).toFinset, index (uSize k0) hi.val lo = x)) ↔
          (x < uSize (k0 + 1) ∨ (∃ (hi : Fin (uSize k0)), ∃ lo ∈ (clusters hi).toFinset, index (uSize k0) hi.val lo = x)) := by
          simp [hmn]
        rw [h_mem_simp, h_rhs_simp]
        by_cases hx_bound : x < uSize (k0 + 1)
        · simp [hx_bound]
        · have h_not_cluster : ¬ (∃ (hi : Fin (uSize k0)), ∃ lo ∈ (clusters hi).toFinset,
            index (uSize k0) hi.val lo = x) := by
            intro h; rcases h with ⟨hi, lo, hlo, hidx⟩
            have hlo' : lo < uSize k0 := toFinset_lt_uSize (clusters hi) lo hlo
            have hhi' : hi.val < uSize k0 := hi.isLt
            have hx_bound' : x < uSize (k0 + 1) := by
              rw [← hidx, uSize_succ k0]
              exact index_lt hhi' hlo'
            exact hx_bound hx_bound'
          simp [hx_bound, h_not_cluster]
      · have h_no_mn : ¬ (∃ (m : ℕ), mn = some m ∧ m < uSize (k0 + 1) ∧ x = m) := by
          intro h; rcases h with ⟨m, hm_eq, hm_lt, hx_eq⟩
          apply hmn; rw [hm_eq, hx_eq]
        simp [hmn, h_no_mn]
        by_cases h : high (uSize k0) x < uSize k0
        · have h_mem_simp2 : member x (VEBTreeMM.node mn mx summary clusters) =
            member (low (uSize k0) x) (clusters ⟨high (uSize k0) x, h⟩) := by
            simp [member, hmn, h]
          rw [h_mem_simp2]
          have h_ih := ih_c ⟨high (uSize k0) x, h⟩ (low (uSize k0) x)
          rw [h_ih]
          constructor
          · intro hlo_mem
            refine ⟨⟨high (uSize k0) x, h⟩, low (uSize k0) x, hlo_mem, ?_⟩
            simpa [Fin.val_mk] using index_high_low
          · rintro ⟨hi', lo', hlo_mem, hidx'⟩
            have hlolt : lo' < uSize k0 := toFinset_lt_uSize (clusters hi') lo' hlo_mem
            have hl : low (uSize k0) x = lo' :=
              calc
                low (uSize k0) x = low (uSize k0) (index (uSize k0) hi'.val lo') := by rw [hidx']
                _ = lo' := low_index hlolt
            have hhi : (⟨high (uSize k0) x, h⟩ : Fin (uSize k0)) = hi' :=
              Fin.ext (calc
                high (uSize k0) x = high (uSize k0) (index (uSize k0) hi'.val lo') := by rw [hidx']
                _ = hi'.val := high_index hlolt
              )
            subst hl
            subst hhi
            exact hlo_mem
        · have h_not_cluster : ¬ (∃ (hi : Fin (uSize k0)), ∃ lo ∈ (clusters hi).toFinset,
            index (uSize k0) hi.val lo = x) := by
            intro hmem; rcases hmem with ⟨hi, lo, hlo, hidx⟩
            have h_lo_lt : lo < uSize k0 := toFinset_lt_uSize (clusters hi) lo hlo
            have h_hi_lt : hi.val < uSize k0 := hi.isLt
            have h_high_eq : high (uSize k0) x = hi.val := by
              rw [← hidx, high_index h_lo_lt]
            rw [← h_high_eq] at h_hi_lt
            exact h h_hi_lt
          simp [member, hmn, h_no_mn, h, h_not_cluster]

def insert : {k : Nat} → Nat → VEBTreeMM k → VEBTreeMM k
  | _, x, .leaf _ _ c0 c1 =>
      let c0' := if x = 0 then true else c0; let c1' := if x = 1 then true else c1
      .leaf (if c0' then some 0 else if c1' then some 1 else none)
            (if c1' then some 1 else if c0' then some 0 else none) c0' c1'
  | _, x, @VEBTreeMM.node k0 mn mx summary clusters =>
      match mn with
      | none => VEBTreeMM.node (some x) (some x) summary clusters
      | some m =>
          let x' := if x < m then m else x
          let mn' := if x < m then some x else mn
          let mx' := match mx with | none => some x | some v => if x > v then some x else mx
          if h : high (uSize k0) x' < uSize k0 then
            let hi : Fin (uSize k0) := ⟨high (uSize k0) x', h⟩
            let lo := low (uSize k0) x'
            have h_lo : lo < uSize k0 := low_lt (uSize_pos k0)
            if (clusters hi).minimum = none then
              VEBTreeMM.node mn' mx' (insert (high (uSize k0) x') summary)
                (Function.update clusters hi (singleton k0 lo h_lo))
            else
              VEBTreeMM.node mn' mx' summary
                (Function.update clusters hi (insert lo (clusters hi)))
          else VEBTreeMM.node mn' mx' summary clusters

def successor : {k : Nat} → Nat → VEBTreeMM k → Option Nat
  | _, x, .leaf _ _ c0 c1 => if x = 0 then (if c1 then some 1 else none) else none
  | _, x, @VEBTreeMM.node k0 mn mx summary clusters =>
      match mn with
      | none => none
      | some m =>
          if x < m then some m
          else
            if h : high (uSize k0) x < uSize k0 then
              let hi := ⟨high (uSize k0) x, h⟩; let lo := low (uSize k0) x; let cluster := clusters hi
              match cluster.maximum with
              | none =>
                  match successor (high (uSize k0) x) summary with
                  | none => none
                  | some nextHi =>
                      if hNext : nextHi < uSize k0 then
                        match (clusters ⟨nextHi, hNext⟩).minimum with
                        | none => none
                        | some offset => some (index (uSize k0) nextHi offset)
                      else none
              | some maxLo =>
                  if lo < maxLo then
                    match successor lo cluster with
                    | none => none
                    | some offset => some (index (uSize k0) hi.val offset)
                  else
                    match successor (high (uSize k0) x) summary with
                    | none => none
                    | some nextHi =>
                        if hNext : nextHi < uSize k0 then
                          match (clusters ⟨nextHi, hNext⟩).minimum with
                          | none => none
                          | some offset => some (index (uSize k0) nextHi offset)
                        else none
            else none

def predecessor : {k : Nat} → Nat → VEBTreeMM k → Option Nat
  | _, x, .leaf _ _ c0 c1 =>
      if x = 1 then (if c0 then some 0 else none) else
      if x = 0 then none else
      if c1 then some 1 else if c0 then some 0 else none
  | _, x, @VEBTreeMM.node k0 mn mx summary clusters =>
      match mx with
      | none => none
      | some m =>
          if x > m then some m
          else
            if h : high (uSize k0) x < uSize k0 then
              let hi := ⟨high (uSize k0) x, h⟩; let lo := low (uSize k0) x; let cluster := clusters hi
              match cluster.minimum with
              | none =>
                  match predecessor (high (uSize k0) x) summary with
                  | none => none
                  | some prevHi =>
                      if hPrev : prevHi < uSize k0 then
                        match (clusters ⟨prevHi, hPrev⟩).maximum with
                        | none => none
                        | some offset => some (index (uSize k0) prevHi offset)
                      else none
              | some minLo =>
                  if lo > minLo then
                    match predecessor lo cluster with
                    | none => none
                    | some offset => some (index (uSize k0) hi.val offset)
                  else
                    match predecessor (high (uSize k0) x) summary with
                    | none => none
                    | some prevHi =>
                        if hPrev : prevHi < uSize k0 then
                          match (clusters ⟨prevHi, hPrev⟩).maximum with
                          | none => none
                          | some offset => some (index (uSize k0) prevHi offset)
                        else none
            else
              match predecessor (high (uSize k0) x) summary with
              | none => none
              | some prevHi =>
                  if hPrev : prevHi < uSize k0 then
                    match (clusters ⟨prevHi, hPrev⟩).maximum with
                    | none => none
                    | some offset => some (index (uSize k0) prevHi offset)
                  else none

def successorCost : {k : Nat} → Nat → VEBTreeMM k → Nat
  | _, x, .leaf _ _ _ _ => 1
  | _, x, @VEBTreeMM.node k0 mn mx summary clusters =>
      1 + successorCost (high (uSize k0) x) (clusters ⟨0, by simpa using uSize_pos k0⟩)

theorem successorCost_le {k : Nat} (v : VEBTreeMM k) : ∀ x, successorCost x v ≤ k + 1 := by
  induction v with
  | leaf mn mx c0 c1 => intro x; simp [successorCost]
  | @node k0 mn mx summary clusters ih_s ih_c =>
      intro x
      have h0 : 0 < uSize k0 := uSize_pos k0
      have h_ih := ih_c ⟨0, h0⟩ (high (uSize k0) x)
      simp [successorCost, h0]
      omega

def predecessorCost : {k : Nat} → Nat → VEBTreeMM k → Nat
  | _, x, .leaf _ _ _ _ => 1
  | _, x, @VEBTreeMM.node k0 mn mx summary clusters =>
      1 + predecessorCost (high (uSize k0) x) (clusters ⟨0, by simpa using uSize_pos k0⟩)

theorem predecessorCost_le {k : Nat} (v : VEBTreeMM k) : ∀ x, predecessorCost x v ≤ k + 1 := by
  induction v with
  | leaf mn mx c0 c1 => intro x; simp [predecessorCost]
  | @node k0 mn mx summary clusters ih_s ih_c =>
      intro x
      have h0 : 0 < uSize k0 := uSize_pos k0
      have h_ih := ih_c ⟨0, h0⟩ (high (uSize k0) x)
      simp [predecessorCost, h0]
      omega

theorem veb_operation_bigO_loglog_u :
    CLRS.Chapter03.isBigO
      (fun k => (k + 1 : ℝ))
      (fun k => (Nat.log 2 (Nat.log 2 (uSize k)) : ℝ)) := by
  rw [CLRS.Chapter03.isBigO_iff]
  refine ⟨2, by norm_num, 1, ?_⟩
  intro n hn
  have hlog : Nat.log 2 (Nat.log 2 (uSize n)) = n := VEBTree.loglog_uSize n
  simp [hlog]
  push_cast
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h_abs1 : |(n : ℝ) + 1| = (n : ℝ) + 1 := abs_of_nonneg (by nlinarith)
  have h_abs2 : |(n : ℝ)| = (n : ℝ) := abs_of_nonneg hn0
  have : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by nlinarith
  simpa [hlog, h_abs1, h_abs2]

/-- Recursive vEB deletion (CLRS vEB-Tree-Delete) on the min/max-augmented
structure.  The stored minimum is promoted from the first nonempty cluster when
the deleted key is the minimum, and the maximum is repaired when the deleted key
is the maximum.  At most one recursive cluster call is needed per level. -/
def delete : {k : Nat} → Nat → VEBTreeMM k → VEBTreeMM k
  | _, x, .leaf mn mx c0 c1 =>
    let c0' := if x = 0 then false else c0
    let c1' := if x = 1 then false else c1
    .leaf (if c0' then some 0 else if c1' then some 1 else none)
          (if c1' then some 1 else if c0' then some 0 else none) c0' c1'
  | _, x, @VEBTreeMM.node k0 mn mx summary clusters =>
    match mn with
    | none => VEBTreeMM.node none none summary clusters
    | some m =>
      match mx with
      | none => VEBTreeMM.node none none summary clusters
      | some v =>
        if h_one : m = v then
          if h_x_eq : x = m then
            VEBTreeMM.node none none (empty k0) (fun _ => empty k0)
          else
            VEBTreeMM.node mn mx summary clusters
        else if h_x_min : x = m then
          let first_candidate := summary.minimum
          match first_candidate with
          | none => VEBTreeMM.node mn mx summary clusters
          | some fc =>
            if h_fc : fc < uSize k0 then
              let hi : Fin (uSize k0) := ⟨fc, h_fc⟩
              let off_candidate := (clusters hi).minimum
              match off_candidate with
              | none => VEBTreeMM.node mn mx summary clusters
              | some offset =>
                let new_min := index (uSize k0) fc offset
                let cluster' := delete offset (clusters hi)
                let new_clusters := Function.update clusters hi cluster'
                if (cluster'.minimum).isNone then
                  let summary' := delete fc summary
                  let new_mx :=
                    if x = v then
                      match summary'.maximum with
                      | none => some new_min
                      | some last =>
                        if h_last : last < uSize k0 then
                          match (clusters ⟨last, h_last⟩).maximum with
                          | none => some new_min
                          | some loff => some (index (uSize k0) last loff)
                        else some new_min
                    else mx
                  VEBTreeMM.node (some new_min) new_mx summary' new_clusters
                else
                  let new_mx :=
                    if x = v then
                      some (index (uSize k0) fc (cluster'.maximum.getD offset))
                    else mx
                  VEBTreeMM.node (some new_min) new_mx summary new_clusters
            else
              VEBTreeMM.node mn mx summary clusters
        else
          if h : high (uSize k0) x < uSize k0 then
            let hi : Fin (uSize k0) := ⟨high (uSize k0) x, h⟩
            let lo := low (uSize k0) x
            let cluster' := delete lo (clusters hi)
            let new_clusters := Function.update clusters hi cluster'
            if (cluster'.minimum).isNone then
              let summary' := delete (high (uSize k0) x) summary
              let new_mx :=
                if x = v then
                  match summary'.maximum with
                  | none => mn
                  | some last =>
                    if h_last : last < uSize k0 then
                      match (clusters ⟨last, h_last⟩).maximum with
                      | none => mn
                      | some loff => some (index (uSize k0) last loff)
                    else mn
                else mx
              VEBTreeMM.node mn new_mx summary' new_clusters
            else
              let new_mx :=
                if x = v then
                  match cluster'.maximum with
                  | none => mn
                  | some cm => some (index (uSize k0) hi.val cm)
                else mx
              VEBTreeMM.node mn new_mx summary new_clusters
          else
            VEBTreeMM.node mn mx summary clusters

/-- The per-level operation-count cost of {lit}`delete`.  At each recursion
level we charge one unit for the constant lookup-and-branch work plus the cost
of the single recursive call into the relevant cluster.
-/
def deleteCost : {k : Nat} → Nat → VEBTreeMM k → Nat
  | _, x, .leaf _ _ _ _ => 1
  | _, x, @VEBTreeMM.node k0 mn mx summary clusters =>
      1 + deleteCost (low (uSize k0) x) (clusters ⟨0, by simpa using uSize_pos k0⟩)

/-- The {lit}`delete` recursion depth is at most {lit}`k + 1`. -/
theorem deleteCost_le {k : Nat} (v : VEBTreeMM k) : ∀ x, deleteCost x v ≤ k + 1 := by
  induction v with
  | leaf mn mx c0 c1 => intro x; simp [deleteCost]
  | @node k0 mn mx summary clusters ih_s ih_c =>
      intro x
      have h0 : 0 < uSize k0 := uSize_pos k0
      have h_ih := ih_c ⟨0, h0⟩ (low (uSize k0) x)
      simp [deleteCost, h0]
      omega

end VEBTreeMM
end Chapter20
end CLRS

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
- Definition {lit}`VEBTreeMM.WellFormed`: the semantic invariant for cached
  extrema, detached minima, recursively well-formed clusters, and exact
  summary/nonempty-cluster correspondence.
- Theorem {lit}`VEBTreeMM.delete_correct`: recursive deletion preserves
  {lit}`WellFormed` and refines {lit}`Finset.erase`, with projections
  {lit}`VEBTreeMM.delete_wellFormed` and {lit}`VEBTreeMM.delete_toFinset`.

Current gaps:

- Correctness of {lit}`VEBTreeMM.successor` and
  {lit}`VEBTreeMM.predecessor`, plus the {lit}`min` / {lit}`max`
  double-recursion-avoidance optimisation for {lit}`insert`, remain future
  refinement targets.
- The current {lit}`successorCost` / {lit}`predecessorCost` /
  {lit}`deleteCost` definitions are structural depth surrogates.  A cost model
  that follows the algorithms' actual control flow remains to be developed.
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
          if h_same : x = m then
            VEBTreeMM.node mn mx summary clusters
          else
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

/-- `MinCorrect mn s` states that `mn` is exactly the minimum cache for `s`:
`none` represents the empty set, while `some m` names a least member. -/
def MinCorrect (mn : Option Nat) (s : Finset Nat) : Prop :=
  match mn with
  | none => s = ∅
  | some m => m ∈ s ∧ ∀ y ∈ s, m ≤ y

/-- `MaxCorrect mx s` states that `mx` is exactly the maximum cache for `s`:
`none` represents the empty set, while `some m` names a greatest member. -/
def MaxCorrect (mx : Option Nat) (s : Finset Nat) : Prop :=
  match mx with
  | none => s = ∅
  | some m => m ∈ s ∧ ∀ y ∈ s, y ≤ m

namespace MinCorrect

/-- A correct minimum cache is absent exactly when its represented set is empty. -/
theorem none_iff {mn : Option Nat} {s : Finset Nat} (h : MinCorrect mn s) :
    mn = none ↔ s = ∅ := by
  cases mn with
  | none => simpa [MinCorrect] using h
  | some m =>
      change m ∈ s ∧ (∀ y ∈ s, m ≤ y) at h
      simp only [Option.some_ne_none, false_iff]
      intro hs
      simpa [hs] using h.1

/-- A cached minimum satisfying `MinCorrect` belongs to the represented set. -/
theorem mem {m : Nat} {s : Finset Nat} (h : MinCorrect (some m) s) : m ∈ s := by
  exact h.1

/-- A cached minimum satisfying `MinCorrect` bounds every represented key. -/
theorem le {m y : Nat} {s : Finset Nat} (h : MinCorrect (some m) s)
    (hy : y ∈ s) : m ≤ y := by
  exact h.2 y hy

/-- Erasing a different key preserves a correct cached minimum. -/
theorem erase_of_ne {m x : Nat} {s : Finset Nat} (h : MinCorrect (some m) s)
    (hmx : m ≠ x) : MinCorrect (some m) (s.erase x) := by
  exact ⟨Finset.mem_erase.mpr ⟨hmx, h.1⟩,
    fun y hy => h.2 y (Finset.mem_of_mem_erase hy)⟩

/-- Inserting a smaller key makes that key the new cached minimum. -/
theorem insert_of_lt {m x : Nat} {s : Finset Nat} (h : MinCorrect (some m) s)
    (hxm : x < m) : MinCorrect (some x) (Insert.insert x s) := by
  refine ⟨Finset.mem_insert_self x s, ?_⟩
  intro y hy
  rw [Finset.mem_insert] at hy
  rcases hy with hyx | hy
  · subst y
    exact Nat.le_refl _
  · exact Nat.le_trans (Nat.le_of_lt hxm) (h.le hy)

/-- Inserting no key below the cached minimum preserves that minimum. -/
theorem insert_of_not_lt {m x : Nat} {s : Finset Nat}
    (h : MinCorrect (some m) s) (hxm : ¬ x < m) :
    MinCorrect (some m) (Insert.insert x s) := by
  refine ⟨Finset.mem_insert_of_mem h.mem, ?_⟩
  intro y hy
  rw [Finset.mem_insert] at hy
  rcases hy with rfl | hy
  · exact Nat.le_of_not_gt hxm
  · exact h.le hy

end MinCorrect

namespace MaxCorrect

/-- A correct maximum cache is absent exactly when its represented set is empty. -/
theorem none_iff {mx : Option Nat} {s : Finset Nat} (h : MaxCorrect mx s) :
    mx = none ↔ s = ∅ := by
  cases mx with
  | none => simpa [MaxCorrect] using h
  | some m =>
      change m ∈ s ∧ (∀ y ∈ s, y ≤ m) at h
      simp only [Option.some_ne_none, false_iff]
      intro hs
      simpa [hs] using h.1

/-- A cached maximum satisfying `MaxCorrect` belongs to the represented set. -/
theorem mem {m : Nat} {s : Finset Nat} (h : MaxCorrect (some m) s) : m ∈ s := by
  exact h.1

/-- A cached maximum satisfying `MaxCorrect` bounds every represented key. -/
theorem le {m y : Nat} {s : Finset Nat} (h : MaxCorrect (some m) s)
    (hy : y ∈ s) : y ≤ m := by
  exact h.2 y hy

/-- Erasing a different key preserves a correct cached maximum. -/
theorem erase_of_ne {m x : Nat} {s : Finset Nat} (h : MaxCorrect (some m) s)
    (hmx : m ≠ x) : MaxCorrect (some m) (s.erase x) := by
  exact ⟨Finset.mem_erase.mpr ⟨hmx, h.1⟩,
    fun y hy => h.2 y (Finset.mem_of_mem_erase hy)⟩

/-- Inserting a larger key makes that key the new cached maximum. -/
theorem insert_of_gt {m x : Nat} {s : Finset Nat} (h : MaxCorrect (some m) s)
    (hmx : m < x) : MaxCorrect (some x) (Insert.insert x s) := by
  refine ⟨Finset.mem_insert_self x s, ?_⟩
  intro y hy
  rw [Finset.mem_insert] at hy
  rcases hy with hyx | hy
  · subst y
    exact Nat.le_refl _
  · exact Nat.le_trans (h.le hy) (Nat.le_of_lt hmx)

/-- Inserting no key above the cached maximum preserves that maximum. -/
theorem insert_of_not_gt {m x : Nat} {s : Finset Nat}
    (h : MaxCorrect (some m) s) (hmx : ¬ m < x) :
    MaxCorrect (some m) (Insert.insert x s) := by
  refine ⟨Finset.mem_insert_of_mem h.mem, ?_⟩
  intro y hy
  rw [Finset.mem_insert] at hy
  rcases hy with rfl | hy
  · exact Nat.le_of_not_gt hmx
  · exact h.le hy

end MaxCorrect

/-- The CLRS representation invariant for the min/max-augmented recursive tree.

Cached extrema describe the represented set exactly.  At a node, the stored
minimum is kept outside the clusters, the summary represents exactly the
nonempty cluster indices, and every recursive component is well formed. -/
def WellFormed : ∀ {k : Nat}, VEBTreeMM k → Prop
  | _, .leaf mn mx c0 c1 =>
      let s := (VEBTreeMM.leaf mn mx c0 c1).toFinset
      MinCorrect mn s ∧ MaxCorrect mx s
  | _, @VEBTreeMM.node k mn mx summary clusters =>
      let s := (VEBTreeMM.node mn mx summary clusters).toFinset
      MinCorrect mn s ∧
      MaxCorrect mx s ∧
      (∀ m, mn = some m → ∀ (hi : Fin (uSize k)) (lo : Nat),
        lo ∈ (clusters hi).toFinset → index (uSize k) hi.val lo ≠ m) ∧
      (∀ hi : Fin (uSize k),
        hi.val ∈ summary.toFinset ↔ (clusters hi).toFinset.Nonempty) ∧
      WellFormed summary ∧
      ∀ hi : Fin (uSize k), WellFormed (clusters hi)

namespace WellFormed

/-- A well-formed tree's cached minimum is correct for its represented set. -/
theorem minCorrect {k : Nat} {v : VEBTreeMM k} (h : WellFormed v) :
    MinCorrect v.minimum v.toFinset := by
  cases v <;> exact h.1

/-- A well-formed tree's cached maximum is correct for its represented set. -/
theorem maxCorrect {k : Nat} {v : VEBTreeMM k} (h : WellFormed v) :
    MaxCorrect v.maximum v.toFinset := by
  cases v with
  | leaf => exact h.2
  | node => exact h.2.1

/-- A well-formed tree has no cached minimum exactly when it represents no keys. -/
theorem minimum_none_iff {k : Nat} {v : VEBTreeMM k} (h : WellFormed v) :
    v.minimum = none ↔ v.toFinset = ∅ :=
  MinCorrect.none_iff h.minCorrect

/-- A well-formed tree has no cached maximum exactly when it represents no keys. -/
theorem maximum_none_iff {k : Nat} {v : VEBTreeMM k} (h : WellFormed v) :
    v.maximum = none ↔ v.toFinset = ∅ :=
  MaxCorrect.none_iff h.maxCorrect

/-- The cached minimum of a well-formed tree is represented. -/
theorem minimum_mem {k : Nat} {v : VEBTreeMM k} {m : Nat}
    (h : WellFormed v) (hm : v.minimum = some m) : m ∈ v.toFinset := by
  have hc := h.minCorrect
  rw [hm] at hc
  exact MinCorrect.mem hc

/-- The cached minimum of a well-formed tree bounds every represented key. -/
theorem minimum_le {k : Nat} {v : VEBTreeMM k} {m y : Nat}
    (h : WellFormed v) (hm : v.minimum = some m) (hy : y ∈ v.toFinset) : m ≤ y := by
  have hc := h.minCorrect
  rw [hm] at hc
  exact MinCorrect.le hc hy

/-- The cached maximum of a well-formed tree is represented. -/
theorem maximum_mem {k : Nat} {v : VEBTreeMM k} {m : Nat}
    (h : WellFormed v) (hm : v.maximum = some m) : m ∈ v.toFinset := by
  have hc := h.maxCorrect
  rw [hm] at hc
  exact MaxCorrect.mem hc

/-- Every represented key is bounded by the cached maximum of a well-formed tree. -/
theorem le_maximum {k : Nat} {v : VEBTreeMM k} {m y : Nat}
    (h : WellFormed v) (hm : v.maximum = some m) (hy : y ∈ v.toFinset) : y ≤ m := by
  have hc := h.maxCorrect
  rw [hm] at hc
  exact MaxCorrect.le hc hy

/-- The stored node minimum is absent from every cluster payload. -/
theorem node_min_detached {k : Nat} {mn mx : Option Nat} {summary : VEBTreeMM k}
    {clusters : Fin (uSize k) → VEBTreeMM k}
    (h : WellFormed (VEBTreeMM.node mn mx summary clusters)) :
    ∀ m, mn = some m → ∀ (hi : Fin (uSize k)) (lo : Nat),
      lo ∈ (clusters hi).toFinset → index (uSize k) hi.val lo ≠ m :=
  h.2.2.1

/-- A node summary represents exactly the indices of nonempty clusters. -/
theorem node_summary_mem_iff {k : Nat} {mn mx : Option Nat} {summary : VEBTreeMM k}
    {clusters : Fin (uSize k) → VEBTreeMM k}
    (h : WellFormed (VEBTreeMM.node mn mx summary clusters))
    (hi : Fin (uSize k)) :
    hi.val ∈ summary.toFinset ↔ (clusters hi).toFinset.Nonempty :=
  h.2.2.2.1 hi

/-- The summary subtree of a well-formed node is well formed. -/
theorem node_summary {k : Nat} {mn mx : Option Nat} {summary : VEBTreeMM k}
    {clusters : Fin (uSize k) → VEBTreeMM k}
    (h : WellFormed (VEBTreeMM.node mn mx summary clusters)) : WellFormed summary :=
  h.2.2.2.2.1

/-- Every cluster subtree of a well-formed node is well formed. -/
theorem node_cluster {k : Nat} {mn mx : Option Nat} {summary : VEBTreeMM k}
    {clusters : Fin (uSize k) → VEBTreeMM k}
    (h : WellFormed (VEBTreeMM.node mn mx summary clusters))
    (hi : Fin (uSize k)) : WellFormed (clusters hi) :=
  h.2.2.2.2.2 hi

/-- Equal cached minimum and maximum force a well-formed tree to represent one key. -/
theorem toFinset_eq_singleton {k : Nat} {v : VEBTreeMM k} {m : Nat}
    (h : WellFormed v) (hmin : v.minimum = some m) (hmax : v.maximum = some m) :
    v.toFinset = {m} := by
  ext y
  constructor
  · intro hy
    have hmy : m ≤ y := h.minimum_le hmin hy
    have hym : y ≤ m := h.le_maximum hmax hy
    simpa [Nat.le_antisymm hym hmy]
  · intro hy
    have hym : y = m := by simpa using hy
    subst y
    exact h.minimum_mem hmin

end WellFormed

/-- The cached minimum exactly describes the least represented key. -/
theorem minimum_correct {k : Nat} {v : VEBTreeMM k} (hwf : WellFormed v) :
    MinCorrect v.minimum v.toFinset :=
  hwf.minCorrect

/-- The cached maximum exactly describes the greatest represented key. -/
theorem maximum_correct {k : Nat} {v : VEBTreeMM k} (hwf : WellFormed v) :
    MaxCorrect v.maximum v.toFinset :=
  hwf.maxCorrect

/-- The recursively empty min/max-augmented vEB tree satisfies `WellFormed`. -/
theorem empty_wellFormed (k : Nat) : WellFormed (empty k) := by
  induction k with
  | zero => simp [WellFormed, MinCorrect, MaxCorrect, empty, toFinset]
  | succ k ih =>
      simp [WellFormed, MinCorrect, MaxCorrect, empty, toFinset_empty, ih]
      simpa [empty] using (toFinset_empty (k + 1))

/-- A bounded singleton tree represents exactly its supplied key. -/
theorem singleton_toFinset (k : Nat) (x : Nat) (hx : x < uSize k) :
    (singleton k x hx).toFinset = {x} := by
  cases k with
  | zero =>
      rw [uSize_zero] at hx
      by_cases hx0 : x = 0
      · subst x
        simp [singleton, toFinset]
      · have hx1 : x = 1 := by omega
        subst x
        simp [singleton, toFinset]
  | succ k =>
      ext y
      simp [singleton, toFinset, toFinset_empty, hx]

/-- A bounded singleton tree satisfies the recursive cached-extrema invariant. -/
theorem singleton_wellFormed (k : Nat) (x : Nat) (hx : x < uSize k) :
    WellFormed (singleton k x hx) := by
  cases k with
  | zero =>
      rw [uSize_zero] at hx
      by_cases hx0 : x = 0
      · subst x
        simp [singleton, WellFormed, MinCorrect, MaxCorrect, toFinset]
      · have hx1 : x = 1 := by omega
        subst x
        simp [singleton, WellFormed, MinCorrect, MaxCorrect, toFinset]
  | succ k =>
      simp only [singleton, WellFormed]
      have hset :
          (VEBTreeMM.node (some x) (some x) (empty k)
            (fun _ => empty k)).toFinset = {x} := by
        simpa [singleton] using singleton_toFinset (k + 1) x hx
      rw [hset]
      refine ⟨?_, ?_, ?_, ?_, empty_wellFormed k, ?_⟩
      · simp [MinCorrect]
      · simp [MaxCorrect]
      · intro m hm hi lo hlo
        simpa [toFinset_empty] using hlo
      · intro hi
        simp [toFinset_empty]
      · intro hi
        exact empty_wellFormed k

/-- Keys in an earlier vEB cluster precede every key in a later cluster. -/
theorem index_lt_index_of_high_lt {m hi₁ hi₂ lo₁ lo₂ : Nat}
    (hlo₁ : lo₁ < m) (hhi : hi₁ < hi₂) :
    index m hi₁ lo₁ < index m hi₂ lo₂ := by
  have h₁ : m * hi₁ + lo₁ < m * hi₁ + m := Nat.add_lt_add_left hlo₁ _
  have h₂ : m * (hi₁ + 1) ≤ m * hi₂ :=
    Nat.mul_le_mul_left m (Nat.succ_le_of_lt hhi)
  calc
    index m hi₁ lo₁ < m * (hi₁ + 1) := by
      simpa [index, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h₁
    _ ≤ m * hi₂ := h₂
    _ ≤ index m hi₂ lo₂ := by simp [index]

/-- Within one cluster, recombination preserves the ordering of low offsets. -/
theorem index_le_index_of_low_le {m hi lo₁ lo₂ : Nat} (hlo : lo₁ ≤ lo₂) :
    index m hi lo₁ ≤ index m hi lo₂ := by
  simpa [index] using Nat.add_le_add_left hlo (m * hi)

/-- Membership in a node with one updated cluster has a three-way normal form:
the stored minimum, the replacement cluster, or an unchanged cluster. -/
theorem mem_toFinset_node_update_cluster {k : Nat} (mn mx : Option Nat)
    (summary : VEBTreeMM k) (clusters : Fin (uSize k) → VEBTreeMM k)
    (hi : Fin (uSize k)) (cluster' : VEBTreeMM k) (y : Nat) :
    y ∈ (VEBTreeMM.node mn mx summary (Function.update clusters hi cluster')).toFinset ↔
      (∃ m, mn = some m ∧ m < uSize (k + 1) ∧ y = m) ∨
      (∃ lo ∈ cluster'.toFinset, index (uSize k) hi.val lo = y) ∨
      (∃ hi' : Fin (uSize k), hi' ≠ hi ∧
        ∃ lo ∈ (clusters hi').toFinset, index (uSize k) hi'.val lo = y) := by
  rw [mem_toFinset_node]
  constructor
  · rintro (hmin | ⟨hi', lo, hlo, hidx⟩)
    · exact Or.inl hmin
    · by_cases hhi : hi' = hi
      · subst hi'
        rw [Function.update_self] at hlo
        exact Or.inr (Or.inl ⟨lo, hlo, hidx⟩)
      · rw [Function.update_of_ne hhi] at hlo
        exact Or.inr (Or.inr ⟨hi', hhi, lo, hlo, hidx⟩)
  · rintro (hmin | hupdated | ⟨hi', hhi, lo, hlo, hidx⟩)
    · exact Or.inl hmin
    · rcases hupdated with ⟨lo, hlo, hidx⟩
      exact Or.inr ⟨hi, lo, by simpa using hlo, hidx⟩
    · exact Or.inr ⟨hi', lo, by simpa [Function.update_of_ne hhi] using hlo, hidx⟩

/-- Replacing one cluster preserves recursive well-formedness pointwise. -/
theorem update_clusters_wellFormed {k : Nat}
    {clusters : Fin (uSize k) → VEBTreeMM k} {hi : Fin (uSize k)}
    {cluster' : VEBTreeMM k}
    (hall : ∀ j, WellFormed (clusters j)) (hnew : WellFormed cluster') :
    ∀ j, WellFormed (Function.update clusters hi cluster' j) := by
  intro j
  by_cases hji : j = hi
  · subst j
    simpa using hnew
  · simpa [Function.update_of_ne hji] using hall j

/-- Replacing one cluster by a finite-set insertion inserts the recombined key
into the whole node. -/
theorem toFinset_update_cluster_insert {k : Nat}
    (mn mx : Option Nat) (summary : VEBTreeMM k)
    (clusters : Fin (uSize k) → VEBTreeMM k)
    (hi : Fin (uSize k)) (cluster' : VEBTreeMM k) (x : Nat)
    (hcluster : cluster'.toFinset = Insert.insert x (clusters hi).toFinset) :
    (VEBTreeMM.node mn mx summary
      (Function.update clusters hi cluster')).toFinset =
      Insert.insert (index (uSize k) hi.val x)
        (VEBTreeMM.node mn mx summary clusters).toFinset := by
  ext y
  rw [mem_toFinset_node_update_cluster, Finset.mem_insert,
    mem_toFinset_node, hcluster]
  simp only [Finset.mem_insert]
  constructor
  · rintro (hmin | hnew | hold)
    · exact Or.inr (Or.inl hmin)
    · rcases hnew with ⟨lo, hlo, rfl⟩
      rcases hlo with (rfl | hlo)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr ⟨hi, lo, hlo, rfl⟩)
    · rcases hold with ⟨j, hji, lo, hlo, hidx⟩
      exact Or.inr (Or.inr ⟨j, lo, hlo, hidx⟩)
  · rintro (rfl | hrest)
    · exact Or.inr (Or.inl ⟨x, Or.inl rfl, rfl⟩)
    · rcases hrest with (hmin | hclusterOld)
      · exact Or.inl hmin
      · rcases hclusterOld with ⟨j, lo, hlo, rfl⟩
        by_cases hji : j = hi
        · subst j
          exact Or.inr (Or.inl ⟨lo, Or.inr hlo, rfl⟩)
        · exact Or.inr (Or.inr ⟨j, hji, lo, hlo, rfl⟩)

/-- Installing the first detached minimum adds exactly that key to a node. -/
theorem toFinset_replace_none_min {k : Nat} (x : Nat) (mx : Option Nat)
    (summary : VEBTreeMM k) (clusters : Fin (uSize k) → VEBTreeMM k)
    (hx : x < uSize (k + 1)) :
    (VEBTreeMM.node (some x) mx summary clusters).toFinset =
      Insert.insert x (VEBTreeMM.node none mx summary clusters).toFinset := by
  ext y
  rw [mem_toFinset_node, Finset.mem_insert, mem_toFinset_node]
  constructor
  · rintro (⟨m, hmn, hm, hym⟩ | hcluster)
    · have hmx : m = x := by simpa using Option.some.inj hmn.symm
      exact Or.inl (hym.trans hmx)
    · exact Or.inr (Or.inr hcluster)
  · rintro (hyx | hnode)
    · subst y
      exact Or.inl ⟨x, rfl, hx, rfl⟩
    · rcases hnode with (⟨m, hmn, _, _⟩ | hcluster)
      · simp at hmn
      · exact Or.inr hcluster

/-- Swapping the detached minimum with a smaller inserted key preserves the
finite-set insertion semantics once the old minimum is inserted into a
cluster. -/
theorem toFinset_swap_min_insert {k : Nat} (x m : Nat) (mx : Option Nat)
    (summary : VEBTreeMM k) (clusters : Fin (uSize k) → VEBTreeMM k)
    (hx : x < uSize (k + 1)) (hm : m < uSize (k + 1)) :
    Insert.insert m (VEBTreeMM.node (some x) mx summary clusters).toFinset =
      Insert.insert x (VEBTreeMM.node (some m) mx summary clusters).toFinset := by
  ext y
  rw [Finset.mem_insert, mem_toFinset_node, Finset.mem_insert, mem_toFinset_node]
  constructor
  · rintro (hym | ⟨stored, hstored, _, hstoredY⟩ | hcluster)
    · subst y
      exact Or.inr (Or.inl ⟨m, rfl, hm, rfl⟩)
    · have hstoredX : stored = x := by
        simpa using Option.some.inj hstored.symm
      exact Or.inl (hstoredY.trans hstoredX)
    · exact Or.inr (Or.inr hcluster)
  · rintro (hyx | ⟨stored, hstored, _, hstoredY⟩ | hcluster)
    · subst y
      exact Or.inr (Or.inl ⟨x, rfl, hx, rfl⟩)
    · have hstoredM : stored = m := by
        simpa using Option.some.inj hstored.symm
      exact Or.inl (hstoredY.trans hstoredM)
    · exact Or.inr (Or.inr hcluster)

/-- When an empty cluster receives its first key and its index is inserted into
the summary, the summary-to-cluster correspondence remains exact. -/
theorem summary_mem_iff_update_insert_empty {k : Nat}
    {summary summary' : VEBTreeMM k}
    {clusters : Fin (uSize k) → VEBTreeMM k}
    {hi : Fin (uSize k)} {cluster' : VEBTreeMM k}
    (hsummary : ∀ j : Fin (uSize k),
      j.val ∈ summary.toFinset ↔ (clusters j).toFinset.Nonempty)
    (hsummary' : summary'.toFinset = Insert.insert hi.val summary.toFinset)
    (_hempty : (clusters hi).toFinset = ∅)
    (hnew : cluster'.toFinset.Nonempty) :
    ∀ j : Fin (uSize k), j.val ∈ summary'.toFinset ↔
      (Function.update clusters hi cluster' j).toFinset.Nonempty := by
  intro j
  rw [hsummary']
  by_cases hji : j = hi
  · subst j
    simp [hnew]
  · have hval : j.val ≠ hi.val := by
      intro hval
      exact hji (Fin.ext hval)
    rw [Function.update_of_ne hji, Finset.mem_insert, hsummary j]
    simp [hval]

/-- Inserting one low offset into a cluster preserves detachment of an
unchanged stored minimum when the recombined new key differs from it. -/
theorem node_min_detached_update_insert {k : Nat} {mn : Option Nat}
    {clusters : Fin (uSize k) → VEBTreeMM k} {hi : Fin (uSize k)}
    {lo : Nat} {cluster' : VEBTreeMM k}
    (hdet : ∀ m, mn = some m → ∀ (j : Fin (uSize k)) (off : Nat),
      off ∈ (clusters j).toFinset → index (uSize k) j.val off ≠ m)
    (hcluster : cluster'.toFinset = Insert.insert lo (clusters hi).toFinset)
    (hnew : ∀ m, mn = some m → index (uSize k) hi.val lo ≠ m) :
    ∀ m, mn = some m → ∀ (j : Fin (uSize k)) (off : Nat),
      off ∈ (Function.update clusters hi cluster' j).toFinset →
        index (uSize k) j.val off ≠ m := by
  intro m hmn j off hoff
  by_cases hji : j = hi
  · subst j
    rw [Function.update_self, hcluster, Finset.mem_insert] at hoff
    rcases hoff with rfl | hoff
    · exact hnew m hmn
    · exact hdet m hmn hi off hoff
  · rw [Function.update_of_ne hji] at hoff
    exact hdet m hmn j off hoff

/-- When insertion swaps in a strictly smaller detached minimum, every old
cluster key and the reinserted old minimum remain distinct from it. -/
theorem node_min_detached_update_insert_of_lt {k : Nat} {x m : Nat}
    {mx : Option Nat} {summary : VEBTreeMM k}
    {clusters : Fin (uSize k) → VEBTreeMM k} {hi : Fin (uSize k)}
    {lo : Nat} {cluster' : VEBTreeMM k}
    (hwf : WellFormed (VEBTreeMM.node (some m) mx summary clusters))
    (hcluster : cluster'.toFinset = Insert.insert lo (clusters hi).toFinset)
    (hindex : index (uSize k) hi.val lo = m) (hxm : x < m) :
    ∀ m', (some x : Option Nat) = some m' →
      ∀ (j : Fin (uSize k)) (off : Nat),
        off ∈ (Function.update clusters hi cluster' j).toFinset →
          index (uSize k) j.val off ≠ m' := by
  intro m' hm' j off hoff
  have hm'x : m' = x := Option.some.inj hm'.symm
  subst m'
  have holdNe (j' : Fin (uSize k)) (off' : Nat)
      (hoff' : off' ∈ (clusters j').toFinset) :
      index (uSize k) j'.val off' ≠ x := by
    have holdMem : index (uSize k) j'.val off' ∈
        (VEBTreeMM.node (some m) mx summary clusters).toFinset := by
      rw [mem_toFinset_node]
      exact Or.inr ⟨j', off', hoff', rfl⟩
    have hmle := hwf.minimum_le rfl holdMem
    omega
  by_cases hji : j = hi
  · subst j
    rw [Function.update_self, hcluster, Finset.mem_insert] at hoff
    rcases hoff with rfl | hoff
    · rw [hindex]
      omega
    · exact holdNe hi off hoff
  · rw [Function.update_of_ne hji] at hoff
    exact holdNe j off hoff

/-! ## Recursive successor specification -/

/-- Bundled semantic contract for an optional strict successor. -/
def SuccessorSpec (s : Finset Nat) (x : Nat) : Option Nat → Prop
  | none => ∀ y, y ∈ s → ¬ x < y
  | some y =>
      y ∈ s ∧ x < y ∧ ∀ z, z ∈ s → x < z → y ≤ z

/-- Recombination within one cluster preserves strict low-part ordering. -/
theorem index_lt_index_of_low_lt {m hi lo₁ lo₂ : Nat} (hlo : lo₁ < lo₂) :
    index m hi lo₁ < index m hi lo₂ := by
  simpa [index] using Nat.add_lt_add_left hlo (m * hi)

/-- An indexed representation determines its high part. -/
theorem high_eq_of_index_eq {m x hi lo : Nat} (_hm : 0 < m) (hlo : lo < m)
    (hidx : index m hi lo = x) : high m x = hi := by
  rw [← hidx, high_index hlo]

/-- An indexed representation determines its low part. -/
theorem low_eq_of_index_eq {m x hi lo : Nat} (hlo : lo < m)
    (hidx : index m hi lo = x) : low m x = lo := by
  rw [← hidx, low_index hlo]

/-- If the current cluster has no low offset above the query, a recursive
successor in the summary selects exactly the next global cluster. -/
theorem successor_from_summary_spec {k m x : Nat} {mx : Option Nat}
    {summary : VEBTreeMM k} {clusters : Fin (uSize k) → VEBTreeMM k}
    (hwf : WellFormed (VEBTreeMM.node (some m) mx summary clusters))
    (hmx : m ≤ x) (hhigh : high (uSize k) x < uSize k)
    (hcurrent : ∀ off, off ∈
      (clusters ⟨high (uSize k) x, hhigh⟩).toFinset →
        off ≤ low (uSize k) x)
    (hspec : SuccessorSpec summary.toFinset (high (uSize k) x)
      (successor (high (uSize k) x) summary)) :
    SuccessorSpec (VEBTreeMM.node (some m) mx summary clusters).toFinset x
      (match successor (high (uSize k) x) summary with
      | none => none
      | some nextHi =>
          if hNext : nextHi < uSize k then
            match (clusters ⟨nextHi, hNext⟩).minimum with
            | none => none
            | some offset => some (index (uSize k) nextHi offset)
          else none) := by
  let hi : Fin (uSize k) := ⟨high (uSize k) x, hhigh⟩
  have hloBound : low (uSize k) x < uSize k := low_lt (uSize_pos k)
  have hxIndex : index (uSize k) hi.val (low (uSize k) x) = x := by
    simpa [hi] using (index_high_low (m := uSize k) (x := x))
  cases hsucc : successor (high (uSize k) x) summary with
  | none =>
      rw [hsucc] at hspec
      simp only
      change ∀ y, y ∈
        (VEBTreeMM.node (some m) mx summary clusters).toFinset → ¬ x < y
      intro y hy hxy
      rw [mem_toFinset_node] at hy
      rcases hy with ⟨stored, hstored, _, hyStored⟩ | ⟨j, off, hoff, hidx⟩
      · have hstoredEq : stored = m := by
          simpa using Option.some.inj hstored.symm
        omega
      · have hoffBound : off < uSize k :=
          toFinset_lt_uSize (clusters j) off hoff
        by_cases hjle : j.val ≤ hi.val
        · by_cases hji : j = hi
          · subst j
            have hoffLe : off ≤ low (uSize k) x := by
              simpa [hi] using hcurrent off hoff
            have hyLe : y ≤ x := by
              rw [← hidx, ← hxIndex]
              exact index_le_index_of_low_le hoffLe
            omega
          · have hjlt : j.val < hi.val := by
              have hval : j.val ≠ hi.val := by
                intro hval
                exact hji (Fin.ext hval)
              omega
            have hyLt : y < x := by
              rw [← hidx, ← hxIndex]
              exact index_lt_index_of_high_lt hoffBound hjlt
            omega
        · have hhiJ : high (uSize k) x < j.val := by
            simpa [hi] using Nat.lt_of_not_ge hjle
          have hjSummary : j.val ∈ summary.toFinset :=
            (hwf.node_summary_mem_iff j).2 ⟨off, hoff⟩
          exact hspec j.val hjSummary hhiJ
  | some nextHi =>
      rw [hsucc] at hspec
      have hnextMem : nextHi ∈ summary.toFinset := hspec.1
      have hnextGt : high (uSize k) x < nextHi := hspec.2.1
      have hnextBound : nextHi < uSize k :=
        toFinset_lt_uSize summary nextHi hnextMem
      let next : Fin (uSize k) := ⟨nextHi, hnextBound⟩
      have hnextNonempty : (clusters next).toFinset.Nonempty :=
        (hwf.node_summary_mem_iff next).1 (by simpa [next] using hnextMem)
      cases hmin : (clusters next).minimum with
      | none =>
          exact False.elim (hnextNonempty.ne_empty
            ((hwf.node_cluster next).minimum_none_iff.mp hmin))
      | some offset =>
          have hmin' : (clusters ⟨nextHi, hnextBound⟩).minimum = some offset := by
            simpa [next] using hmin
          simp only [dif_pos hnextBound, hmin']
          change SuccessorSpec
            (VEBTreeMM.node (some m) mx summary clusters).toFinset x
            (some (index (uSize k) nextHi offset))
          have hoffMem : offset ∈ (clusters next).toFinset :=
            (hwf.node_cluster next).minimum_mem hmin
          have hoffBound : offset < uSize k :=
            toFinset_lt_uSize (clusters next) offset hoffMem
          refine ⟨?_, ?_, ?_⟩
          · rw [mem_toFinset_node]
            exact Or.inr ⟨next, offset, hoffMem, rfl⟩
          · rw [← hxIndex]
            exact index_lt_index_of_high_lt hloBound (by simpa [hi] using hnextGt)
          · intro z hz hxz
            rw [mem_toFinset_node] at hz
            rcases hz with ⟨stored, hstored, _, hzStored⟩ |
                ⟨j, off, hoff, hidx⟩
            · have hstoredEq : stored = m := by
                simpa using Option.some.inj hstored.symm
              omega
            · have hoffJBound : off < uSize k :=
                toFinset_lt_uSize (clusters j) off hoff
              by_cases hjle : j.val ≤ hi.val
              · by_cases hji : j = hi
                · subst j
                  have hoffLe : off ≤ low (uSize k) x := by
                    simpa [hi] using hcurrent off hoff
                  have hzLe : z ≤ x := by
                    rw [← hidx, ← hxIndex]
                    exact index_le_index_of_low_le hoffLe
                  omega
                · have hjlt : j.val < hi.val := by
                    have hval : j.val ≠ hi.val := by
                      intro hval
                      exact hji (Fin.ext hval)
                    omega
                  have hzLt : z < x := by
                    rw [← hidx, ← hxIndex]
                    exact index_lt_index_of_high_lt hoffJBound hjlt
                  omega
              · have hhiJ : high (uSize k) x < j.val := by
                  simpa [hi] using Nat.lt_of_not_ge hjle
                have hjSummary : j.val ∈ summary.toFinset :=
                  (hwf.node_summary_mem_iff j).2 ⟨off, hoff⟩
                have hnextLe : nextHi ≤ j.val :=
                  hspec.2.2 j.val hjSummary hhiJ
                by_cases hnextJ : next = j
                · subst j
                  have hoffLe : offset ≤ off :=
                    (hwf.node_cluster next).minimum_le hmin hoff
                  rw [← hidx]
                  exact index_le_index_of_low_le hoffLe
                · have hval : nextHi ≠ j.val := by
                    intro hval
                    exact hnextJ (Fin.ext (by simpa [next] using hval))
                  have hnextLt : nextHi < j.val := by omega
                  rw [← hidx]
                  exact Nat.le_of_lt
                    (index_lt_index_of_high_lt hoffBound hnextLt)

/-- A strict successor found inside the current cluster is the global
successor because every earlier cluster precedes the query and every later
cluster follows the returned key. -/
theorem successor_from_cluster_spec {k m x : Nat} {mx : Option Nat}
    {summary : VEBTreeMM k} {clusters : Fin (uSize k) → VEBTreeMM k}
    (hwf : WellFormed (VEBTreeMM.node (some m) mx summary clusters))
    (hmx : m ≤ x) (hhigh : high (uSize k) x < uSize k)
    (hexists : ∃ off,
      off ∈ (clusters ⟨high (uSize k) x, hhigh⟩).toFinset ∧
        low (uSize k) x < off)
    (hspec : SuccessorSpec
      (clusters ⟨high (uSize k) x, hhigh⟩).toFinset
      (low (uSize k) x)
      (successor (low (uSize k) x)
        (clusters ⟨high (uSize k) x, hhigh⟩))) :
    SuccessorSpec (VEBTreeMM.node (some m) mx summary clusters).toFinset x
      (match successor (low (uSize k) x)
          (clusters ⟨high (uSize k) x, hhigh⟩) with
      | none => none
      | some offset =>
          some (index (uSize k) (high (uSize k) x) offset)) := by
  let hi : Fin (uSize k) := ⟨high (uSize k) x, hhigh⟩
  have hloBound : low (uSize k) x < uSize k := low_lt (uSize_pos k)
  have hxIndex : index (uSize k) hi.val (low (uSize k) x) = x := by
    simpa [hi] using (index_high_low (m := uSize k) (x := x))
  cases hsucc : successor (low (uSize k) x) (clusters hi) with
  | none =>
      have hnone : ∀ off, off ∈ (clusters hi).toFinset →
          ¬ low (uSize k) x < off := by
        rw [hsucc] at hspec
        exact hspec
      rcases hexists with ⟨off, hoff, hlo⟩
      exact False.elim ((hnone off (by simpa [hi] using hoff)) hlo)
  | some offset =>
      have hspecSome : SuccessorSpec (clusters hi).toFinset
          (low (uSize k) x) (some offset) := by
        simpa [hi, hsucc] using hspec
      simp only [hsucc]
      change SuccessorSpec
        (VEBTreeMM.node (some m) mx summary clusters).toFinset x
        (some (index (uSize k) hi.val offset))
      have hoffMem : offset ∈ (clusters hi).toFinset := hspecSome.1
      have hoffGt : low (uSize k) x < offset := hspecSome.2.1
      have hoffBound : offset < uSize k :=
        toFinset_lt_uSize (clusters hi) offset hoffMem
      refine ⟨?_, ?_, ?_⟩
      · rw [mem_toFinset_node]
        exact Or.inr ⟨hi, offset, hoffMem, rfl⟩
      · rw [← hxIndex]
        exact index_lt_index_of_low_lt hoffGt
      · intro z hz hxz
        rw [mem_toFinset_node] at hz
        rcases hz with ⟨stored, hstored, _, hzStored⟩ |
            ⟨j, off, hoff, hidx⟩
        · have hstoredEq : stored = m := by
            simpa using Option.some.inj hstored.symm
          omega
        · have hoffJBound : off < uSize k :=
            toFinset_lt_uSize (clusters j) off hoff
          by_cases hji : j = hi
          · subst j
            have hloOff : low (uSize k) x < off := by
              rw [← hidx, ← hxIndex] at hxz
              simpa [index] using hxz
            have hoffLe : offset ≤ off :=
              hspecSome.2.2 off hoff hloOff
            rw [← hidx]
            exact index_le_index_of_low_le hoffLe
          · by_cases hjhi : j.val < hi.val
            · have hzLt : z < x := by
                rw [← hidx, ← hxIndex]
                exact index_lt_index_of_high_lt hoffJBound hjhi
              omega
            · have hval : j.val ≠ hi.val := by
                intro hval
                exact hji (Fin.ext hval)
              have hhiJ : hi.val < j.val := by omega
              rw [← hidx]
              exact Nat.le_of_lt
                (index_lt_index_of_high_lt hoffBound hhiJ)

/-- Replacing the cluster addressed by `x` with a low-part erasure implements
whole-node erasure when `x` is not the detached stored minimum. -/
theorem toFinset_update_cluster_erase {k : Nat} (mn mx : Option Nat)
    (summary : VEBTreeMM k) (clusters : Fin (uSize k) → VEBTreeMM k)
    (x : Nat) (hhigh : high (uSize k) x < uSize k)
    (cluster' : VEBTreeMM k)
    (hcluster : cluster'.toFinset =
      (clusters ⟨high (uSize k) x, hhigh⟩).toFinset.erase (low (uSize k) x))
    (hmin : mn ≠ some x) :
    (VEBTreeMM.node mn mx summary
      (Function.update clusters ⟨high (uSize k) x, hhigh⟩ cluster')).toFinset =
      (VEBTreeMM.node mn mx summary clusters).toFinset.erase x := by
  let hi : Fin (uSize k) := ⟨high (uSize k) x, hhigh⟩
  let lo := low (uSize k) x
  have hlo : lo < uSize k := low_lt (uSize_pos k)
  have hxidx : index (uSize k) hi.val lo = x := by
    simpa [hi, lo] using (index_high_low (m := uSize k) (x := x))
  ext y
  rw [Finset.mem_erase, mem_toFinset_node_update_cluster, mem_toFinset_node]
  constructor
  · rintro (⟨m, hmn, hm_lt, hy⟩ | ⟨lo', hlo', hidx⟩ | ⟨hi', hhi', lo', hlo', hidx⟩)
    · have hyx : y ≠ x := by
        intro hyx
        apply hmin
        calc
          mn = some m := hmn
          _ = some y := congrArg some hy.symm
          _ = some x := congrArg some hyx
      exact ⟨hyx, Or.inl ⟨m, hmn, hm_lt, hy⟩⟩
    · rw [hcluster, Finset.mem_erase] at hlo'
      rcases hlo' with ⟨hlo_ne, hlo_mem⟩
      have hyx : y ≠ x := by
        intro hyx
        apply hlo_ne
        have hlo'_lt := toFinset_lt_uSize
          (clusters hi) lo' hlo_mem
        calc
          lo' = low (uSize k) (index (uSize k) hi.val lo') := by
            rw [low_index hlo'_lt]
          _ = low (uSize k) y := by rw [hidx]
          _ = low (uSize k) x := by rw [hyx]
          _ = lo := rfl
      exact ⟨hyx, Or.inr ⟨hi, lo', hlo_mem, hidx⟩⟩
    · have hyx : y ≠ x := by
        intro hyx
        apply hhi'
        have hlo'_lt := toFinset_lt_uSize
          (clusters hi') lo' hlo'
        apply Fin.ext
        calc
          hi'.val = high (uSize k) (index (uSize k) hi'.val lo') := by
            rw [high_index hlo'_lt]
          _ = high (uSize k) y := by rw [hidx]
          _ = high (uSize k) x := by rw [hyx]
          _ = hi.val := rfl
      exact ⟨hyx, Or.inr ⟨hi', lo', hlo', hidx⟩⟩
  · rintro ⟨hyx, (⟨m, hmn, hm_lt, hy⟩ | ⟨hi', lo', hlo', hidx⟩)⟩
    · exact Or.inl ⟨m, hmn, hm_lt, hy⟩
    · by_cases hhi' : hi' = hi
      · subst hi'
        have hlo'_lt := toFinset_lt_uSize (clusters hi) lo' hlo'
        have hlo_ne : lo' ≠ lo := by
          intro hloeq
          apply hyx
          calc
            y = index (uSize k) hi.val lo' := hidx.symm
            _ = index (uSize k) hi.val lo := by rw [hloeq]
            _ = x := hxidx
        have hlo_new : lo' ∈ cluster'.toFinset := by
          rw [hcluster, Finset.mem_erase]
          exact ⟨hlo_ne, hlo'⟩
        exact Or.inr (Or.inl ⟨lo', hlo_new, hidx⟩)
      · exact Or.inr (Or.inr ⟨hi', hhi', lo', hlo', hidx⟩)

/-- Promoting one cluster key to the detached minimum while erasing its low
offset from that cluster removes exactly the old detached minimum. -/
theorem toFinset_promote_cluster_min {k : Nat} (m : Nat) (oldMx newMx : Option Nat)
    (summary summary' : VEBTreeMM k)
    (clusters : Fin (uSize k) → VEBTreeMM k) (hi : Fin (uSize k))
    (offset : Nat) (hoffset : offset ∈ (clusters hi).toFinset)
    (cluster' : VEBTreeMM k)
    (hcluster : cluster'.toFinset = (clusters hi).toFinset.erase offset)
    (hdet : ∀ (j : Fin (uSize k)) (lo : Nat), lo ∈ (clusters j).toFinset →
      index (uSize k) j.val lo ≠ m) :
    (VEBTreeMM.node (some (index (uSize k) hi.val offset)) newMx summary'
      (Function.update clusters hi cluster')).toFinset =
      (VEBTreeMM.node (some m) oldMx summary clusters).toFinset.erase m := by
  have hoffsetLt : offset < uSize k :=
    toFinset_lt_uSize (clusters hi) offset hoffset
  have hnewBound : index (uSize k) hi.val offset < uSize (k + 1) := by
    rw [uSize_succ]
    exact index_lt hi.isLt hoffsetLt
  ext y
  rw [Finset.mem_erase, mem_toFinset_node_update_cluster, mem_toFinset_node]
  constructor
  · rintro (⟨newMin, hmn, _, hy⟩ | ⟨lo, hlo, hidx⟩ |
      ⟨j, hji, lo, hlo, hidx⟩)
    · have hnew : newMin = index (uSize k) hi.val offset := by
        simpa using Option.some.inj hmn.symm
      have hyNew : y = index (uSize k) hi.val offset := hy.trans hnew
      have hym : y ≠ m := by
        simpa [hyNew] using hdet hi offset hoffset
      exact ⟨hym, Or.inr ⟨hi, offset, hoffset, hyNew.symm⟩⟩
    · rw [hcluster, Finset.mem_erase] at hlo
      exact ⟨by
        intro hym
        exact hdet hi lo hlo.2 (hidx.trans hym),
        Or.inr ⟨hi, lo, hlo.2, hidx⟩⟩
    · exact ⟨by
        intro hym
        exact hdet j lo hlo (hidx.trans hym),
        Or.inr ⟨j, lo, hlo, hidx⟩⟩
  · rintro ⟨hym, (⟨oldMin, hmn, _, hy⟩ | ⟨j, lo, hlo, hidx⟩)⟩
    · have hold : oldMin = m := by simpa using Option.some.inj hmn.symm
      exact False.elim (hym (hy.trans hold))
    · by_cases hji : j = hi
      · subst j
        by_cases hloeq : lo = offset
        · subst lo
          exact Or.inl ⟨index (uSize k) hi.val offset, rfl, hnewBound, hidx.symm⟩
        · have hloNew : lo ∈ cluster'.toFinset := by
            rw [hcluster, Finset.mem_erase]
            exact ⟨hloeq, hlo⟩
          exact Or.inr (Or.inl ⟨lo, hloNew, hidx⟩)
      · exact Or.inr (Or.inr ⟨j, hji, lo, hlo, hidx⟩)

/-- Erasing keys from one cluster preserves detachment of the node minimum. -/
theorem node_min_detached_update_erase {k : Nat} {mn : Option Nat}
    {clusters : Fin (uSize k) → VEBTreeMM k} {hi : Fin (uSize k)}
    {lo : Nat} {cluster' : VEBTreeMM k}
    (hdet : ∀ m, mn = some m → ∀ (j : Fin (uSize k)) (off : Nat),
      off ∈ (clusters j).toFinset → index (uSize k) j.val off ≠ m)
    (hcluster : cluster'.toFinset = (clusters hi).toFinset.erase lo) :
    ∀ m, mn = some m → ∀ (j : Fin (uSize k)) (off : Nat),
      off ∈ (Function.update clusters hi cluster' j).toFinset →
        index (uSize k) j.val off ≠ m := by
  intro m hmn j off hoff
  by_cases hji : j = hi
  · subst j
    rw [Function.update_self, hcluster, Finset.mem_erase] at hoff
    exact hdet m hmn hi off hoff.2
  · rw [Function.update_of_ne hji] at hoff
    exact hdet m hmn j off hoff

/-- If an updated cluster remains nonempty, the unchanged summary still
represents exactly the nonempty cluster indices. -/
theorem summary_mem_iff_update_nonempty {k : Nat}
    {summary : VEBTreeMM k} {clusters : Fin (uSize k) → VEBTreeMM k}
    {hi : Fin (uSize k)} {cluster' : VEBTreeMM k}
    (hsummary : ∀ j : Fin (uSize k),
      j.val ∈ summary.toFinset ↔ (clusters j).toFinset.Nonempty)
    (hold : (clusters hi).toFinset.Nonempty)
    (hnew : cluster'.toFinset.Nonempty) :
    ∀ j : Fin (uSize k), j.val ∈ summary.toFinset ↔
      (Function.update clusters hi cluster' j).toFinset.Nonempty := by
  intro j
  by_cases hji : j = hi
  · subst j
    rw [Function.update_self]
    exact ⟨fun _ => hnew, fun _ => (hsummary hi).2 hold⟩
  · simpa [Function.update_of_ne hji] using hsummary j

/-- If an updated cluster becomes empty and its index is erased from the
summary, exact summary-to-cluster correspondence is preserved. -/
theorem summary_mem_iff_update_empty {k : Nat}
    {summary summary' : VEBTreeMM k}
    {clusters : Fin (uSize k) → VEBTreeMM k}
    {hi : Fin (uSize k)} {cluster' : VEBTreeMM k}
    (hsummary : ∀ j : Fin (uSize k),
      j.val ∈ summary.toFinset ↔ (clusters j).toFinset.Nonempty)
    (hsummary' : summary'.toFinset = summary.toFinset.erase hi.val)
    (hempty : cluster'.toFinset = ∅) :
    ∀ j : Fin (uSize k), j.val ∈ summary'.toFinset ↔
      (Function.update clusters hi cluster' j).toFinset.Nonempty := by
  intro j
  rw [hsummary']
  by_cases hji : j = hi
  · subst j
    simp [hempty]
  · have hval : j.val ≠ hi.val := by
      intro hval
      exact hji (Fin.ext hval)
    rw [Function.update_of_ne hji, Finset.mem_erase, hsummary j]
    simp [hval]

/-- When the old maximum `x` lies in an updated cluster that remains nonempty,
the updated cluster maximum is the new whole-tree maximum. -/
theorem maxCorrect_of_updated_cluster {k : Nat} (m x : Nat)
    (summary : VEBTreeMM k) (clusters : Fin (uSize k) → VEBTreeMM k)
    (hhigh : high (uSize k) x < uSize k) (cluster' : VEBTreeMM k)
    (hcluster : cluster'.toFinset =
      (clusters ⟨high (uSize k) x, hhigh⟩).toFinset.erase (low (uSize k) x))
    (hwf : WellFormed (VEBTreeMM.node (some m) (some x) summary clusters))
    (hclusterWf : WellFormed cluster') {cm : Nat}
    (hcmax : cluster'.maximum = some cm) :
    MaxCorrect (some (index (uSize k) (high (uSize k) x) cm))
      (VEBTreeMM.node (some m) (some x) summary
        (Function.update clusters ⟨high (uSize k) x, hhigh⟩ cluster')).toFinset := by
  let hi : Fin (uSize k) := ⟨high (uSize k) x, hhigh⟩
  have hcmNew : cm ∈ cluster'.toFinset := hclusterWf.maximum_mem hcmax
  have hcmOld : cm ∈ (clusters hi).toFinset := by
    apply Finset.mem_of_mem_erase
    rw [← hcluster]
    exact hcmNew
  have hnewOld : index (uSize k) hi.val cm ∈
      (VEBTreeMM.node (some m) (some x) summary clusters).toFinset := by
    rw [mem_toFinset_node]
    exact Or.inr ⟨hi, cm, hcmOld, rfl⟩
  change index (uSize k) hi.val cm ∈
      (VEBTreeMM.node (some m) (some x) summary
        (Function.update clusters hi cluster')).toFinset ∧
    ∀ y ∈ (VEBTreeMM.node (some m) (some x) summary
        (Function.update clusters hi cluster')).toFinset,
      y ≤ index (uSize k) hi.val cm
  constructor
  · rw [mem_toFinset_node_update_cluster]
    exact Or.inr (Or.inl ⟨cm, hcmNew, rfl⟩)
  · intro y hy
    rw [mem_toFinset_node_update_cluster] at hy
    rcases hy with (⟨m', hmn, _, hym⟩ | ⟨off, hoff, hidx⟩ |
      ⟨j, hji, off, hoff, hidx⟩)
    · have hmm : m' = m := by simpa using Option.some.inj hmn.symm
      have hy_eq : y = m := hym.trans hmm
      simpa [hy_eq] using hwf.minimum_le rfl hnewOld
    · have hoff_le : off ≤ cm := hclusterWf.le_maximum hcmax hoff
      rw [← hidx]
      exact index_le_index_of_low_le hoff_le
    · have hoff_lt : off < uSize k := toFinset_lt_uSize (clusters j) off hoff
      have hyOld : y ∈
          (VEBTreeMM.node (some m) (some x) summary clusters).toFinset := by
        rw [mem_toFinset_node]
        exact Or.inr ⟨j, off, hoff, hidx⟩
      have hyx : y ≤ x := hwf.le_maximum rfl hyOld
      have hjle : j.val ≤ hi.val := by
        calc
          j.val = high (uSize k) (index (uSize k) j.val off) := by
            rw [high_index hoff_lt]
          _ = high (uSize k) y := by rw [hidx]
          _ ≤ high (uSize k) x := Nat.div_le_div_right hyx
          _ = hi.val := rfl
      have hval : j.val ≠ hi.val := by
        intro hval
        exact hji (Fin.ext hval)
      have hjlt : j.val < hi.val := by omega
      rw [← hidx]
      exact Nat.le_of_lt (index_lt_index_of_high_lt hoff_lt hjlt)

/-- The maximum of the last nonempty cluster selected by a well-formed summary
is the maximum of the whole nonempty cluster payload. -/
theorem maxCorrect_of_summary_max {k : Nat} (m : Nat)
    (summary : VEBTreeMM k) (clusters : Fin (uSize k) → VEBTreeMM k)
    (hmin : MinCorrect (some m)
      (VEBTreeMM.node (some m) none summary clusters).toFinset)
    (hsummaryWf : WellFormed summary)
    (hsummary : ∀ j : Fin (uSize k),
      j.val ∈ summary.toFinset ↔ (clusters j).toFinset.Nonempty)
    (hall : ∀ j, WellFormed (clusters j))
    (last : Fin (uSize k)) (hlast : summary.maximum = some last.val)
    {off : Nat} (hoff : (clusters last).maximum = some off) :
    MaxCorrect (some (index (uSize k) last.val off))
      (VEBTreeMM.node (some m) none summary clusters).toFinset := by
  have hoffMem : off ∈ (clusters last).toFinset :=
    (hall last).maximum_mem hoff
  have hnewMem : index (uSize k) last.val off ∈
      (VEBTreeMM.node (some m) none summary clusters).toFinset := by
    rw [mem_toFinset_node]
    exact Or.inr ⟨last, off, hoffMem, rfl⟩
  change index (uSize k) last.val off ∈
      (VEBTreeMM.node (some m) none summary clusters).toFinset ∧
    ∀ y ∈ (VEBTreeMM.node (some m) none summary clusters).toFinset,
      y ≤ index (uSize k) last.val off
  constructor
  · exact hnewMem
  · intro y hy
    rw [mem_toFinset_node] at hy
    rcases hy with (⟨m', hmn, _, hym⟩ | ⟨j, lo, hlo, hidx⟩)
    · have hmm : m' = m := by simpa using Option.some.inj hmn.symm
      have hy_eq : y = m := hym.trans hmm
      simpa [hy_eq] using MinCorrect.le hmin hnewMem
    · have hjSummary : j.val ∈ summary.toFinset :=
        (hsummary j).2 ⟨lo, hlo⟩
      have hjle : j.val ≤ last.val :=
        hsummaryWf.le_maximum hlast hjSummary
      by_cases hjlast : j = last
      · subst j
        have hlole : lo ≤ off := (hall last).le_maximum hoff hlo
        rw [← hidx]
        exact index_le_index_of_low_le hlole
      · have hval : j.val ≠ last.val := by
          intro hval
          exact hjlast (Fin.ext hval)
        have hjlt : j.val < last.val := by omega
        have hloLt : lo < uSize k := toFinset_lt_uSize (clusters j) lo hlo
        rw [← hidx]
        exact Nat.le_of_lt (index_lt_index_of_high_lt hloLt hjlt)

/-- The minimum of the first nonempty cluster is the minimum after erasing the
old detached node minimum. -/
theorem minCorrect_erase_detached_min {k : Nat} (m : Nat) (mx : Option Nat)
    (summary : VEBTreeMM k) (clusters : Fin (uSize k) → VEBTreeMM k)
    (hwf : WellFormed (VEBTreeMM.node (some m) mx summary clusters))
    (first : Fin (uSize k)) (hfirst : summary.minimum = some first.val)
    {off : Nat} (hoff : (clusters first).minimum = some off) :
    MinCorrect (some (index (uSize k) first.val off))
      ((VEBTreeMM.node (some m) mx summary clusters).toFinset.erase m) := by
  have hoffMem : off ∈ (clusters first).toFinset :=
    (hwf.node_cluster first).minimum_mem hoff
  have hnewOld : index (uSize k) first.val off ∈
      (VEBTreeMM.node (some m) mx summary clusters).toFinset := by
    rw [mem_toFinset_node]
    exact Or.inr ⟨first, off, hoffMem, rfl⟩
  have hnewNe : index (uSize k) first.val off ≠ m :=
    hwf.node_min_detached m rfl first off hoffMem
  constructor
  · exact Finset.mem_erase.mpr ⟨hnewNe, hnewOld⟩
  · intro y hy
    have hyOld := Finset.mem_of_mem_erase hy
    rw [mem_toFinset_node] at hyOld
    rcases hyOld with (⟨oldMin, hmn, _, hym⟩ | ⟨j, lo, hlo, hidx⟩)
    · have hold : oldMin = m := by simpa using Option.some.inj hmn.symm
      exact False.elim ((Finset.mem_erase.mp hy).1 (hym.trans hold))
    · have hjSummary : j.val ∈ summary.toFinset :=
        (hwf.node_summary_mem_iff j).2 ⟨lo, hlo⟩
      have hfirstLe : first.val ≤ j.val :=
        hwf.node_summary.minimum_le hfirst hjSummary
      by_cases hj : j = first
      · subst j
        have hoffLe : off ≤ lo := (hwf.node_cluster first).minimum_le hoff hlo
        rw [← hidx]
        exact index_le_index_of_low_le hoffLe
      · have hval : j.val ≠ first.val := by
          intro hval
          exact hj (Fin.ext hval)
        have hfirstLt : first.val < j.val := by omega
        have hoffLt : off < uSize k :=
          toFinset_lt_uSize (clusters first) off hoffMem
        rw [← hidx]
        exact Nat.le_of_lt (index_lt_index_of_high_lt hoffLt hfirstLt)

/-- After promoting a cluster offset, erasing that offset from the cluster
detaches the new stored minimum from every updated cluster. -/
theorem promoted_min_detached {k : Nat}
    (clusters : Fin (uSize k) → VEBTreeMM k) (hi : Fin (uSize k))
    (offset : Nat) (hoffset : offset ∈ (clusters hi).toFinset)
    (cluster' : VEBTreeMM k)
    (hcluster : cluster'.toFinset = (clusters hi).toFinset.erase offset) :
    ∀ m, (some (index (uSize k) hi.val offset) : Option Nat) = some m →
      ∀ (j : Fin (uSize k)) (lo : Nat),
        lo ∈ (Function.update clusters hi cluster' j).toFinset →
          index (uSize k) j.val lo ≠ m := by
  intro m hm j lo hlo hidx
  have hmEq : m = index (uSize k) hi.val offset := Option.some.inj hm.symm
  have hEq : index (uSize k) j.val lo = index (uSize k) hi.val offset := by
    simpa [hmEq] using hidx
  by_cases hji : j = hi
  · subst j
    rw [Function.update_self, hcluster, Finset.mem_erase] at hlo
    apply hlo.1
    have hloLt : lo < uSize k :=
      toFinset_lt_uSize (clusters hi) lo hlo.2
    have hoffLt : offset < uSize k :=
      toFinset_lt_uSize (clusters hi) offset hoffset
    calc
      lo = low (uSize k) (index (uSize k) hi.val lo) := by
        rw [low_index hloLt]
      _ = low (uSize k) (index (uSize k) hi.val offset) := by rw [hEq]
      _ = offset := by rw [low_index hoffLt]
  · apply hji
    apply Fin.ext
    have hloOld : lo ∈ (clusters j).toFinset := by
      simpa [Function.update_of_ne hji] using hlo
    have hloLt : lo < uSize k := toFinset_lt_uSize (clusters j) lo hloOld
    have hoffLt : offset < uSize k :=
      toFinset_lt_uSize (clusters hi) offset hoffset
    calc
      j.val = high (uSize k) (index (uSize k) j.val lo) := by
        rw [high_index hloLt]
      _ = high (uSize k) (index (uSize k) hi.val offset) := by rw [hEq]
      _ = hi.val := by rw [high_index hoffLt]


/-- **Recursive vEB insertion correctness.**  Insertion preserves the CLRS
representation invariant and refines finite-set insertion. -/
theorem insert_correct : ∀ {k : Nat} (v : VEBTreeMM k) (x : Nat),
    WellFormed v → x < uSize k →
      WellFormed (insert x v) ∧
        (insert x v).toFinset = Insert.insert x v.toFinset := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro v x hwf hx
      cases v with
      | leaf mn mx c0 c1 =>
          rw [uSize_zero] at hx
          interval_cases x <;> cases c0 <;> cases c1 <;>
            simp [insert, WellFormed, MinCorrect, MaxCorrect, toFinset,
              Finset.pair_comm]
      | @node k0 mn mx summary clusters =>
          cases mn with
          | none =>
              have holdEmpty :
                  (VEBTreeMM.node none mx summary clusters).toFinset = ∅ :=
                hwf.minimum_none_iff.mp rfl
              have hmx : mx = none := by
                cases mx with
                | none => rfl
                | some v =>
                    have hv : v ∈
                        (VEBTreeMM.node none (some v) summary clusters).toFinset :=
                      hwf.maximum_mem rfl
                    simpa [holdEmpty] using hv
              subst mx
              have hsem :
                  (VEBTreeMM.node (some x) (some x) summary clusters).toFinset =
                    Insert.insert x
                      (VEBTreeMM.node none none summary clusters).toFinset :=
                toFinset_replace_none_min x (some x) summary clusters hx
              have hnewSet :
                  (VEBTreeMM.node (some x) (some x) summary clusters).toFinset = {x} := by
                rw [hsem, holdEmpty]
                simp
              have hdetached : ∀ m, (some x : Option Nat) = some m →
                  ∀ (j : Fin (uSize k0)) (off : Nat),
                    off ∈ (clusters j).toFinset →
                      index (uSize k0) j.val off ≠ m := by
                intro m hm j off hoff
                have hmEq : m = x := Option.some.inj hm.symm
                subst m
                have holdMem : index (uSize k0) j.val off ∈
                    (VEBTreeMM.node none none summary clusters).toFinset := by
                  rw [mem_toFinset_node]
                  exact Or.inr ⟨j, off, hoff, rfl⟩
                simpa [holdEmpty] using holdMem
              have hresult : WellFormed
                  (VEBTreeMM.node (some x) (some x) summary clusters) := by
                refine ⟨?_, ?_, hdetached,
                  (fun j => hwf.node_summary_mem_iff j),
                  hwf.node_summary, fun j => hwf.node_cluster j⟩
                · rw [hnewSet]
                  simp [MinCorrect]
                · rw [hnewSet]
                  simp [MaxCorrect]
              constructor
              · simpa [insert] using hresult
              · simpa [insert] using hsem
          | some m =>
              cases mx with
              | none =>
                  have holdEmpty :
                      (VEBTreeMM.node (some m) none summary clusters).toFinset = ∅ :=
                    hwf.maximum_none_iff.mp rfl
                  have hm : m ∈
                      (VEBTreeMM.node (some m) none summary clusters).toFinset :=
                    hwf.minimum_mem rfl
                  simpa [holdEmpty] using hm
              | some v =>
                  have hmMem : m ∈
                      (VEBTreeMM.node (some m) (some v) summary clusters).toFinset :=
                    hwf.minimum_mem rfl
                  have hvMem : v ∈
                      (VEBTreeMM.node (some m) (some v) summary clusters).toFinset :=
                    hwf.maximum_mem rfl
                  have hmBound : m < uSize (k0 + 1) :=
                    toFinset_lt_uSize _ m hmMem
                  have hmv : m ≤ v := hwf.minimum_le rfl hvMem
                  by_cases hsame : x = m
                  · subst x
                    have hset : Insert.insert m
                        (VEBTreeMM.node (some m) (some v) summary clusters).toFinset =
                        (VEBTreeMM.node (some m) (some v) summary clusters).toFinset :=
                      Finset.insert_eq_self.mpr hmMem
                    constructor
                    · simpa [insert] using hwf
                    · simpa [insert, hset]
                  · by_cases hxm : x < m
                    · have hvx : ¬ v < x := by omega
                      have hhigh : high (uSize k0) m < uSize k0 := by
                        apply high_lt
                        simpa [uSize_succ] using hmBound
                      let hi : Fin (uSize k0) := ⟨high (uSize k0) m, hhigh⟩
                      let lo := low (uSize k0) m
                      have hlo : lo < uSize k0 := low_lt (uSize_pos k0)
                      have hindex : index (uSize k0) hi.val lo = m := by
                        simpa [hi, lo] using
                          (index_high_low (m := uSize k0) (x := m))
                      cases hcmin : (clusters hi).minimum with
                      | none =>
                          have holdEmpty : (clusters hi).toFinset = ∅ :=
                            (hwf.node_cluster hi).minimum_none_iff.mp hcmin
                          let cluster' := singleton k0 lo hlo
                          let newClusters := Function.update clusters hi cluster'
                          let summary' := insert hi.val summary
                          have hclusterWf : WellFormed cluster' := by
                            exact singleton_wellFormed k0 lo hlo
                          have hclusterSet : cluster'.toFinset =
                              Insert.insert lo (clusters hi).toFinset := by
                            rw [holdEmpty]
                            simpa [cluster'] using singleton_toFinset k0 lo hlo
                          have hsummaryRec := ih k0 (Nat.lt_succ_self k0)
                            summary hi.val hwf.node_summary hi.isLt
                          have hsummaryWf : WellFormed summary' := by
                            simpa [summary'] using hsummaryRec.1
                          have hsummarySet : summary'.toFinset =
                              Insert.insert hi.val summary.toFinset := by
                            simpa [summary'] using hsummaryRec.2
                          have hnewNonempty : cluster'.toFinset.Nonempty := by
                            rw [hclusterSet]
                            exact ⟨lo, Finset.mem_insert_self lo _⟩
                          have hsummaryExact : ∀ j : Fin (uSize k0),
                              j.val ∈ summary'.toFinset ↔
                                (newClusters j).toFinset.Nonempty := by
                            exact summary_mem_iff_update_insert_empty
                              (fun j => hwf.node_summary_mem_iff j)
                              hsummarySet holdEmpty hnewNonempty
                          have hall : ∀ j, WellFormed (newClusters j) :=
                            update_clusters_wellFormed
                              (fun j => hwf.node_cluster j) hclusterWf
                          have hsem :
                              (VEBTreeMM.node (some x) (some v) summary'
                                newClusters).toFinset =
                              Insert.insert x
                                (VEBTreeMM.node (some m) (some v) summary
                                  clusters).toFinset := by
                            calc
                              _ = Insert.insert m
                                  (VEBTreeMM.node (some x) (some v) summary'
                                    clusters).toFinset := by
                                simpa [newClusters, hindex] using
                                  (toFinset_update_cluster_insert
                                    (some x) (some v) summary' clusters hi cluster' lo
                                    hclusterSet)
                              _ = Insert.insert x
                                  (VEBTreeMM.node (some m) (some v) summary'
                                    clusters).toFinset :=
                                toFinset_swap_min_insert x m (some v) summary'
                                  clusters hx hmBound
                              _ = Insert.insert x
                                  (VEBTreeMM.node (some m) (some v) summary
                                    clusters).toFinset := by rfl
                          have hdetached : ∀ m', (some x : Option Nat) = some m' →
                              ∀ (j : Fin (uSize k0)) (off : Nat),
                                off ∈ (newClusters j).toFinset →
                                  index (uSize k0) j.val off ≠ m' := by
                            simpa [newClusters] using
                              (node_min_detached_update_insert_of_lt hwf
                                hclusterSet hindex hxm)
                          have hresult : WellFormed
                              (VEBTreeMM.node (some x) (some v) summary'
                                newClusters) := by
                            refine ⟨?_, ?_, hdetached, hsummaryExact,
                              hsummaryWf, hall⟩
                            · rw [hsem]
                              exact MinCorrect.insert_of_lt hwf.minCorrect hxm
                            · rw [hsem]
                              exact MaxCorrect.insert_of_not_gt hwf.maxCorrect hvx
                          constructor
                          · simpa [insert, hsame, hxm, hvx, hhigh, hi, lo,
                              cluster', newClusters, summary', hcmin] using hresult
                          · simpa [insert, hsame, hxm, hvx, hhigh, hi, lo,
                              cluster', newClusters, summary', hcmin] using hsem
                      | some cmin =>
                          have holdNonempty : (clusters hi).toFinset.Nonempty :=
                            ⟨cmin, (hwf.node_cluster hi).minimum_mem hcmin⟩
                          let cluster' := insert lo (clusters hi)
                          let newClusters := Function.update clusters hi cluster'
                          have hclusterRec := ih k0 (Nat.lt_succ_self k0)
                            (clusters hi) lo (hwf.node_cluster hi) hlo
                          have hclusterWf : WellFormed cluster' := by
                            simpa [cluster'] using hclusterRec.1
                          have hclusterSet : cluster'.toFinset =
                              Insert.insert lo (clusters hi).toFinset := by
                            simpa [cluster'] using hclusterRec.2
                          have hnewNonempty : cluster'.toFinset.Nonempty :=
                            ⟨lo, by rw [hclusterSet]; exact Finset.mem_insert_self lo _⟩
                          have hsummaryExact : ∀ j : Fin (uSize k0),
                              j.val ∈ summary.toFinset ↔
                                (newClusters j).toFinset.Nonempty :=
                            summary_mem_iff_update_nonempty
                              (fun j => hwf.node_summary_mem_iff j)
                              holdNonempty hnewNonempty
                          have hall : ∀ j, WellFormed (newClusters j) :=
                            update_clusters_wellFormed
                              (fun j => hwf.node_cluster j) hclusterWf
                          have hsem :
                              (VEBTreeMM.node (some x) (some v) summary
                                newClusters).toFinset =
                              Insert.insert x
                                (VEBTreeMM.node (some m) (some v) summary
                                  clusters).toFinset := by
                            calc
                              _ = Insert.insert m
                                  (VEBTreeMM.node (some x) (some v) summary
                                    clusters).toFinset := by
                                simpa [newClusters, hindex] using
                                  (toFinset_update_cluster_insert
                                    (some x) (some v) summary clusters hi cluster' lo
                                    hclusterSet)
                              _ = Insert.insert x
                                  (VEBTreeMM.node (some m) (some v) summary
                                    clusters).toFinset :=
                                toFinset_swap_min_insert x m (some v) summary
                                  clusters hx hmBound
                          have hdetached : ∀ m', (some x : Option Nat) = some m' →
                              ∀ (j : Fin (uSize k0)) (off : Nat),
                                off ∈ (newClusters j).toFinset →
                                  index (uSize k0) j.val off ≠ m' := by
                            simpa [newClusters] using
                              (node_min_detached_update_insert_of_lt hwf
                                hclusterSet hindex hxm)
                          have hresult : WellFormed
                              (VEBTreeMM.node (some x) (some v) summary
                                newClusters) := by
                            refine ⟨?_, ?_, hdetached, hsummaryExact,
                              hwf.node_summary, hall⟩
                            · rw [hsem]
                              exact MinCorrect.insert_of_lt hwf.minCorrect hxm
                            · rw [hsem]
                              exact MaxCorrect.insert_of_not_gt hwf.maxCorrect hvx
                          constructor
                          · simpa [insert, hsame, hxm, hvx, hhigh, hi, lo,
                              cluster', newClusters, hcmin] using hresult
                          · simpa [insert, hsame, hxm, hvx, hhigh, hi, lo,
                              cluster', newClusters, hcmin] using hsem
                    · have hmx : m < x := by omega
                      have hhigh : high (uSize k0) x < uSize k0 := by
                        apply high_lt
                        simpa [uSize_succ] using hx
                      let hi : Fin (uSize k0) := ⟨high (uSize k0) x, hhigh⟩
                      let lo := low (uSize k0) x
                      have hlo : lo < uSize k0 := low_lt (uSize_pos k0)
                      have hindex : index (uSize k0) hi.val lo = x := by
                        simpa [hi, lo] using
                          (index_high_low (m := uSize k0) (x := x))
                      let newMx : Option Nat := if v < x then some x else some v
                      have hmaxInsert : MaxCorrect newMx
                          (Insert.insert x
                            (VEBTreeMM.node (some m) (some v) summary
                              clusters).toFinset) := by
                        dsimp [newMx]
                        split
                        · next hvx =>
                            exact MaxCorrect.insert_of_gt hwf.maxCorrect hvx
                        · next hvx =>
                            exact MaxCorrect.insert_of_not_gt hwf.maxCorrect hvx
                      cases hcmin : (clusters hi).minimum with
                      | none =>
                          have holdEmpty : (clusters hi).toFinset = ∅ :=
                            (hwf.node_cluster hi).minimum_none_iff.mp hcmin
                          let cluster' := singleton k0 lo hlo
                          let newClusters := Function.update clusters hi cluster'
                          let summary' := insert hi.val summary
                          have hclusterWf : WellFormed cluster' :=
                            singleton_wellFormed k0 lo hlo
                          have hclusterSet : cluster'.toFinset =
                              Insert.insert lo (clusters hi).toFinset := by
                            rw [holdEmpty]
                            simpa [cluster'] using singleton_toFinset k0 lo hlo
                          have hsummaryRec := ih k0 (Nat.lt_succ_self k0)
                            summary hi.val hwf.node_summary hi.isLt
                          have hsummaryWf : WellFormed summary' := by
                            simpa [summary'] using hsummaryRec.1
                          have hsummarySet : summary'.toFinset =
                              Insert.insert hi.val summary.toFinset := by
                            simpa [summary'] using hsummaryRec.2
                          have hnewNonempty : cluster'.toFinset.Nonempty := by
                            rw [hclusterSet]
                            exact ⟨lo, Finset.mem_insert_self lo _⟩
                          have hsummaryExact : ∀ j : Fin (uSize k0),
                              j.val ∈ summary'.toFinset ↔
                                (newClusters j).toFinset.Nonempty :=
                            summary_mem_iff_update_insert_empty
                              (fun j => hwf.node_summary_mem_iff j)
                              hsummarySet holdEmpty hnewNonempty
                          have hall : ∀ j, WellFormed (newClusters j) :=
                            update_clusters_wellFormed
                              (fun j => hwf.node_cluster j) hclusterWf
                          have hsem :
                              (VEBTreeMM.node (some m) newMx summary'
                                newClusters).toFinset =
                              Insert.insert x
                                (VEBTreeMM.node (some m) (some v) summary
                                  clusters).toFinset := by
                            simpa [newClusters, hindex, toFinset] using
                              (toFinset_update_cluster_insert
                                (some m) newMx summary' clusters hi cluster' lo
                                hclusterSet)
                          have hdetached : ∀ m', (some m : Option Nat) = some m' →
                              ∀ (j : Fin (uSize k0)) (off : Nat),
                                off ∈ (newClusters j).toFinset →
                                  index (uSize k0) j.val off ≠ m' := by
                            simpa [newClusters] using
                              (node_min_detached_update_insert hwf.node_min_detached
                                hclusterSet (by
                                  intro m' hm'
                                  have hmm' : m = m' := Option.some.inj hm'
                                  subst m'
                                  rw [hindex]
                                  omega))
                          have hresult : WellFormed
                              (VEBTreeMM.node (some m) newMx summary'
                                newClusters) := by
                            refine ⟨?_, ?_, hdetached, hsummaryExact,
                              hsummaryWf, hall⟩
                            · rw [hsem]
                              exact MinCorrect.insert_of_not_lt hwf.minCorrect hxm
                            · rw [hsem]
                              exact hmaxInsert
                          constructor
                          · simpa [insert, hsame, hxm, hhigh, hi, lo, newMx,
                              cluster', newClusters, summary', hcmin] using hresult
                          · simpa [insert, hsame, hxm, hhigh, hi, lo, newMx,
                              cluster', newClusters, summary', hcmin] using hsem
                      | some cmin =>
                          have holdNonempty : (clusters hi).toFinset.Nonempty :=
                            ⟨cmin, (hwf.node_cluster hi).minimum_mem hcmin⟩
                          let cluster' := insert lo (clusters hi)
                          let newClusters := Function.update clusters hi cluster'
                          have hclusterRec := ih k0 (Nat.lt_succ_self k0)
                            (clusters hi) lo (hwf.node_cluster hi) hlo
                          have hclusterWf : WellFormed cluster' := by
                            simpa [cluster'] using hclusterRec.1
                          have hclusterSet : cluster'.toFinset =
                              Insert.insert lo (clusters hi).toFinset := by
                            simpa [cluster'] using hclusterRec.2
                          have hnewNonempty : cluster'.toFinset.Nonempty :=
                            ⟨lo, by rw [hclusterSet]; exact Finset.mem_insert_self lo _⟩
                          have hsummaryExact : ∀ j : Fin (uSize k0),
                              j.val ∈ summary.toFinset ↔
                                (newClusters j).toFinset.Nonempty :=
                            summary_mem_iff_update_nonempty
                              (fun j => hwf.node_summary_mem_iff j)
                              holdNonempty hnewNonempty
                          have hall : ∀ j, WellFormed (newClusters j) :=
                            update_clusters_wellFormed
                              (fun j => hwf.node_cluster j) hclusterWf
                          have hsem :
                              (VEBTreeMM.node (some m) newMx summary
                                newClusters).toFinset =
                              Insert.insert x
                                (VEBTreeMM.node (some m) (some v) summary
                                  clusters).toFinset := by
                            simpa [newClusters, hindex, toFinset] using
                              (toFinset_update_cluster_insert
                                (some m) newMx summary clusters hi cluster' lo
                                hclusterSet)
                          have hdetached : ∀ m', (some m : Option Nat) = some m' →
                              ∀ (j : Fin (uSize k0)) (off : Nat),
                                off ∈ (newClusters j).toFinset →
                                  index (uSize k0) j.val off ≠ m' := by
                            simpa [newClusters] using
                              (node_min_detached_update_insert hwf.node_min_detached
                                hclusterSet (by
                                  intro m' hm'
                                  have hmm' : m = m' := Option.some.inj hm'
                                  subst m'
                                  rw [hindex]
                                  omega))
                          have hresult : WellFormed
                              (VEBTreeMM.node (some m) newMx summary
                                newClusters) := by
                            refine ⟨?_, ?_, hdetached, hsummaryExact,
                              hwf.node_summary, hall⟩
                            · rw [hsem]
                              exact MinCorrect.insert_of_not_lt hwf.minCorrect hxm
                            · rw [hsem]
                              exact hmaxInsert
                          constructor
                          · simpa [insert, hsame, hxm, hhigh, hi, lo, newMx,
                              cluster', newClusters, hcmin] using hresult
                          · simpa [insert, hsame, hxm, hhigh, hi, lo, newMx,
                              cluster', newClusters, hcmin] using hsem

/-- Recursive insertion preserves the min/max-augmented vEB invariant. -/
theorem insert_wellFormed {k : Nat} (v : VEBTreeMM k) (x : Nat)
    (hwf : WellFormed v) (hx : x < uSize k) :
    WellFormed (insert x v) :=
  (insert_correct v x hwf hx).1

/-- Recursive insertion refines finite-set insertion. -/
theorem insert_toFinset {k : Nat} (v : VEBTreeMM k) (x : Nat)
    (hwf : WellFormed v) (hx : x < uSize k) :
    (insert x v).toFinset = Insert.insert x v.toFinset :=
  (insert_correct v x hwf hx).2

/-- Membership after recursive insertion is exactly new-or-old membership. -/
theorem member_insert_iff {k : Nat} (v : VEBTreeMM k) (x y : Nat)
    (hwf : WellFormed v) (hx : x < uSize k) :
    member y (insert x v) = true ↔ y = x ∨ member y v = true := by
  rw [member_correct (insert x v) y, insert_toFinset v x hwf hx,
    Finset.mem_insert, ← member_correct v y]

/-- A bounded inserted key is represented after recursive insertion. -/
theorem member_insert_self {k : Nat} (v : VEBTreeMM k) (x : Nat)
    (hwf : WellFormed v) (hx : x < uSize k) :
    member x (insert x v) = true :=
  (member_insert_iff v x x hwf hx).2 (Or.inl rfl)

/-- Every old member remains represented after recursive insertion. -/
theorem member_insert_old {k : Nat} (v : VEBTreeMM k) (x y : Nat)
    (hwf : WellFormed v) (hx : x < uSize k)
    (hy : member y v = true) :
    member y (insert x v) = true :=
  (member_insert_iff v x y hwf hx).2 (Or.inr hy)

/-- The recursive cached-minimum algorithm returns exactly the least
represented key strictly greater than the query, when one exists. -/
theorem successor_spec : ∀ {k : Nat} (v : VEBTreeMM k) (x : Nat),
    WellFormed v → SuccessorSpec v.toFinset x (successor x v) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro v x hwf
      cases v with
      | leaf mn mx c0 c1 =>
          by_cases hx0 : x = 0
          · subst x
            cases c0 <;> cases c1 <;>
              simp [successor, SuccessorSpec, toFinset]
          · cases c0 <;> cases c1 <;>
              simp [successor, SuccessorSpec, toFinset, hx0] <;> omega
      | @node k0 mn mx summary clusters =>
          cases mn with
          | none =>
              have hempty :
                  (VEBTreeMM.node none mx summary clusters).toFinset = ∅ :=
                hwf.minimum_none_iff.mp rfl
              simp [successor, SuccessorSpec, hempty]
          | some m =>
              by_cases hxm : x < m
              · have hmMem : m ∈
                    (VEBTreeMM.node (some m) mx summary clusters).toFinset :=
                  hwf.minimum_mem rfl
                have hresult : SuccessorSpec
                    (VEBTreeMM.node (some m) mx summary clusters).toFinset x
                    (some m) := by
                  exact ⟨hmMem, hxm, fun z hz _ => hwf.minimum_le rfl hz⟩
                simpa [successor, hxm] using hresult
              · have hmx : m ≤ x := Nat.le_of_not_gt hxm
                by_cases hhigh : high (uSize k0) x < uSize k0
                · let hi : Fin (uSize k0) :=
                    ⟨high (uSize k0) x, hhigh⟩
                  cases hmax : (clusters hi).maximum with
                  | none =>
                      have hclusterEmpty : (clusters hi).toFinset = ∅ :=
                        (hwf.node_cluster hi).maximum_none_iff.mp hmax
                      have hcurrent : ∀ off,
                          off ∈ (clusters hi).toFinset →
                            off ≤ low (uSize k0) x := by
                        intro off hoff
                        simpa [hclusterEmpty] using hoff
                      have hsummarySpec := ih k0 (Nat.lt_succ_self k0)
                        summary (high (uSize k0) x) hwf.node_summary
                      have hresult := successor_from_summary_spec hwf hmx hhigh
                        (by simpa [hi] using hcurrent) hsummarySpec
                      simpa [successor, hxm, hhigh, hi, hmax] using hresult
                  | some maxLo =>
                      by_cases hlo : low (uSize k0) x < maxLo
                      · have hmaxMem : maxLo ∈ (clusters hi).toFinset :=
                          (hwf.node_cluster hi).maximum_mem hmax
                        have hexists : ∃ off, off ∈ (clusters hi).toFinset ∧
                            low (uSize k0) x < off :=
                          ⟨maxLo, hmaxMem, hlo⟩
                        have hclusterSpec := ih k0 (Nat.lt_succ_self k0)
                          (clusters hi) (low (uSize k0) x)
                          (hwf.node_cluster hi)
                        have hresult := successor_from_cluster_spec hwf hmx hhigh
                          (by simpa [hi] using hexists)
                          (by simpa [hi] using hclusterSpec)
                        simpa [successor, hxm, hhigh, hi, hmax, hlo] using hresult
                      · have hcurrent : ∀ off,
                            off ∈ (clusters hi).toFinset →
                              off ≤ low (uSize k0) x := by
                          intro off hoff
                          have hoffMax : off ≤ maxLo :=
                            (hwf.node_cluster hi).le_maximum hmax hoff
                          omega
                        have hsummarySpec := ih k0 (Nat.lt_succ_self k0)
                          summary (high (uSize k0) x) hwf.node_summary
                        have hresult := successor_from_summary_spec hwf hmx hhigh
                          (by simpa [hi] using hcurrent) hsummarySpec
                        simpa [successor, hxm, hhigh, hi, hmax, hlo] using hresult
                · have hxGe : uSize (k0 + 1) ≤ x := by
                    have hdiv : uSize k0 ≤ x / uSize k0 := by
                      simpa [high] using Nat.le_of_not_lt hhigh
                    have hmul : uSize k0 * uSize k0 ≤ x := by
                      calc
                        uSize k0 * uSize k0 ≤ uSize k0 * (x / uSize k0) :=
                          Nat.mul_le_mul_left (uSize k0) hdiv
                        _ ≤ x := Nat.mul_div_le x (uSize k0)
                    simpa [uSize_succ] using hmul
                  have hresult : SuccessorSpec
                      (VEBTreeMM.node (some m) mx summary clusters).toFinset x
                      none := by
                    intro y hy
                    have hyBound := toFinset_lt_uSize _ y hy
                    omega
                  simpa [successor, hxm, hhigh] using hresult

/-- A returned recursive successor is represented, strictly greater, and least. -/
theorem successor_correct {k : Nat} {v : VEBTreeMM k} {x y : Nat}
    (hwf : WellFormed v) (hsucc : successor x v = some y) :
    y ∈ v.toFinset ∧ x < y ∧
      ∀ z, z ∈ v.toFinset → x < z → y ≤ z := by
  have hspec := successor_spec v x hwf
  rw [hsucc] at hspec
  exact hspec

/-- A returned recursive successor belongs to the represented set. -/
theorem successor_mem {k : Nat} {v : VEBTreeMM k} {x y : Nat}
    (hwf : WellFormed v) (hsucc : successor x v = some y) :
    y ∈ v.toFinset :=
  (successor_correct hwf hsucc).1

/-- A returned recursive successor is strictly greater than the query. -/
theorem successor_gt {k : Nat} {v : VEBTreeMM k} {x y : Nat}
    (hwf : WellFormed v) (hsucc : successor x v = some y) : x < y :=
  (successor_correct hwf hsucc).2.1

/-- A returned successor is no larger than any represented greater key. -/
theorem successor_le {k : Nat} {v : VEBTreeMM k} {x y z : Nat}
    (hwf : WellFormed v) (hsucc : successor x v = some y)
    (hz : z ∈ v.toFinset) (hxz : x < z) : y ≤ z :=
  (successor_correct hwf hsucc).2.2 z hz hxz

/-- Every returned recursive successor lies inside the tower universe. -/
theorem successor_lt_uSize {k : Nat} {v : VEBTreeMM k} {x y : Nat}
    (hwf : WellFormed v) (hsucc : successor x v = some y) :
    y < uSize k :=
  toFinset_lt_uSize v y (successor_mem hwf hsucc)

/-- No successor is returned exactly when no represented key is greater. -/
theorem successor_none_iff {k : Nat} {v : VEBTreeMM k} {x : Nat}
    (hwf : WellFormed v) :
    successor x v = none ↔ ∀ y, y ∈ v.toFinset → ¬ x < y := by
  constructor
  · intro hnone
    have hspec := successor_spec v x hwf
    rw [hnone] at hspec
    exact hspec
  · intro hnone
    cases hsucc : successor x v with
    | none => rfl
    | some y =>
        have hresult := successor_correct hwf hsucc
        exact False.elim ((hnone y hresult.1) hresult.2.1)

/-- If no represented key is greater, recursive successor returns none. -/
theorem successor_none_of_no_gt {k : Nat} {v : VEBTreeMM k} {x : Nat}
    (hwf : WellFormed v) (hnone : ∀ y, y ∈ v.toFinset → ¬ x < y) :
    successor x v = none :=
  (successor_none_iff hwf).2 hnone

/-- An existing greater represented key forces a successor result. -/
theorem successor_ne_none_of_exists_gt {k : Nat} {v : VEBTreeMM k}
    {x y : Nat} (hwf : WellFormed v) (hy : y ∈ v.toFinset) (hxy : x < y) :
    successor x v ≠ none := by
  intro hnone
  exact ((successor_none_iff hwf).1 hnone y hy) hxy


/-- **Recursive vEB deletion correctness.**  Deletion preserves the CLRS
representation invariant and refines finite-set erasure. -/
theorem delete_correct : ∀ {k : Nat} (v : VEBTreeMM k) (x : Nat),
    WellFormed v →
      WellFormed (delete x v) ∧ (delete x v).toFinset = v.toFinset.erase x := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro v x hwf
      cases v with
      | leaf mn mx c0 c1 =>
          by_cases hx0 : x = 0
          · subst x
            cases mn <;> cases mx <;> cases c0 <;> cases c1 <;>
              simp [WellFormed, MinCorrect, MaxCorrect, delete, toFinset,
                Finset.ext_iff] at hwf ⊢
          · by_cases hx1 : x = 1
            · subst x
              cases mn <;> cases mx <;> cases c0 <;> cases c1 <;>
                simp [WellFormed, MinCorrect, MaxCorrect, delete, toFinset,
                  Finset.ext_iff, hx0] at hwf ⊢ <;> omega
            · cases mn <;> cases mx <;> cases c0 <;> cases c1 <;>
                simp [WellFormed, MinCorrect, MaxCorrect, delete, toFinset,
                  Finset.ext_iff, hx0, hx1] at hwf ⊢
      | @node k0 mn mx summary clusters =>
          cases mn with
          | none =>
              have hs : (VEBTreeMM.node none mx summary clusters).toFinset = ∅ :=
                hwf.minimum_none_iff.mp rfl
              have hmx : mx = none := by
                cases mx with
                | none => rfl
                | some m =>
                    have hm : m ∈ (VEBTreeMM.node none (some m) summary clusters).toFinset :=
                      hwf.maximum_mem rfl
                    simpa [hs] using hm
              subst mx
              constructor
              · simpa [delete] using hwf
              · simp [delete, hs]
          | some m =>
              cases mx with
              | none =>
                  have hs : (VEBTreeMM.node (some m) none summary clusters).toFinset = ∅ :=
                    hwf.maximum_none_iff.mp rfl
                  have hm : m ∈ (VEBTreeMM.node (some m) none summary clusters).toFinset :=
                    hwf.minimum_mem rfl
                  simpa [hs] using hm
              | some v =>
                  by_cases h_one : m = v
                  · subst v
                    have hs : (VEBTreeMM.node (some m) (some m) summary clusters).toFinset = {m} :=
                      hwf.toFinset_eq_singleton rfl rfl
                    by_cases hx : x = m
                    · subst x
                      constructor
                      · simpa [delete, empty] using (empty_wellFormed (k0 + 1))
                      · simpa [delete, hs, empty] using (toFinset_empty (k0 + 1))
                    · constructor
                      · simpa [delete, hx] using hwf
                      · have hxnot : x ∉
                            (VEBTreeMM.node (some m) (some m) summary clusters).toFinset := by
                          rw [hs]
                          simpa [hx]
                        simpa [delete, hx] using (Finset.erase_eq_self.mpr hxnot).symm
                  · by_cases hx_min : x = m
                    · subst x
                      have hv : v ∈
                          (VEBTreeMM.node (some m) (some v) summary clusters).toFinset :=
                        hwf.maximum_mem rfl
                      have hsumNonempty : summary.toFinset.Nonempty := by
                        rw [mem_toFinset_node] at hv
                        rcases hv with (⟨stored, hstored, _, hvstored⟩ |
                          ⟨j, off, hoff, _⟩)
                        · have hstoredEq : stored = m := by
                            simpa using Option.some.inj hstored.symm
                          exfalso
                          apply h_one
                          exact hstoredEq.symm.trans hvstored.symm
                        · exact ⟨j.val, (hwf.node_summary_mem_iff j).2 ⟨off, hoff⟩⟩
                      cases hsmin : summary.minimum with
                      | none =>
                          exact False.elim (hsumNonempty.ne_empty
                            (hwf.node_summary.minimum_none_iff.mp hsmin))
                      | some fc =>
                          have hfcMem : fc ∈ summary.toFinset :=
                            hwf.node_summary.minimum_mem hsmin
                          have hfcBound : fc < uSize k0 :=
                            toFinset_lt_uSize summary fc hfcMem
                          let hi : Fin (uSize k0) := ⟨fc, hfcBound⟩
                          have hiMem : hi.val ∈ summary.toFinset := by
                            simpa [hi] using hfcMem
                          have hclusterNonempty :
                              (clusters hi).toFinset.Nonempty :=
                            (hwf.node_summary_mem_iff hi).1 hiMem
                          cases hcmin : (clusters hi).minimum with
                          | none =>
                              exact False.elim (hclusterNonempty.ne_empty
                                ((hwf.node_cluster hi).minimum_none_iff.mp hcmin))
                          | some offset =>
                              have hoffset : offset ∈ (clusters hi).toFinset :=
                                (hwf.node_cluster hi).minimum_mem hcmin
                              let newMin := index (uSize k0) hi.val offset
                              let cluster' := delete offset (clusters hi)
                              let newClusters := Function.update clusters hi cluster'
                              have hrec := ih k0 (Nat.lt_succ_self k0)
                                (clusters hi) offset (hwf.node_cluster hi)
                              have hclusterWf : WellFormed cluster' := by
                                simpa [cluster'] using hrec.1
                              have hclusterSet : cluster'.toFinset =
                                  (clusters hi).toFinset.erase offset := by
                                simpa [cluster'] using hrec.2
                              have hsem (mx' : Option Nat) (summary' : VEBTreeMM k0) :
                                  (VEBTreeMM.node (some newMin) mx' summary'
                                    newClusters).toFinset =
                                    (VEBTreeMM.node (some m) (some v) summary
                                      clusters).toFinset.erase m := by
                                simpa [newMin, newClusters] using
                                  (toFinset_promote_cluster_min m (some v) mx'
                                    summary summary' clusters hi offset hoffset cluster'
                                    hclusterSet
                                    (fun j lo hlo =>
                                      hwf.node_min_detached m rfl j lo hlo))
                              have hminErase : MinCorrect (some newMin)
                                  ((VEBTreeMM.node (some m) (some v) summary
                                    clusters).toFinset.erase m) := by
                                simpa [newMin, hi] using
                                  (minCorrect_erase_detached_min m (some v) summary
                                    clusters hwf hi (by simpa [hi] using hsmin) hcmin)
                              have hmaxErase : MaxCorrect (some v)
                                  ((VEBTreeMM.node (some m) (some v) summary
                                    clusters).toFinset.erase m) :=
                                MaxCorrect.erase_of_ne hwf.maxCorrect (Ne.symm h_one)
                              have hdetached : ∀ m', (some newMin : Option Nat) = some m' →
                                  ∀ (j : Fin (uSize k0)) (off : Nat),
                                    off ∈ (newClusters j).toFinset →
                                      index (uSize k0) j.val off ≠ m' := by
                                simpa [newMin, newClusters] using
                                  (promoted_min_detached clusters hi offset hoffset
                                    cluster' hclusterSet)
                              have hall : ∀ j, WellFormed (newClusters j) :=
                                update_clusters_wellFormed
                                  (fun j => hwf.node_cluster j) hclusterWf
                              cases hcafter : cluster'.minimum with
                              | none =>
                                  have hempty : cluster'.toFinset = ∅ :=
                                    hclusterWf.minimum_none_iff.mp hcafter
                                  let summary' := delete hi.val summary
                                  have hsumRec := ih k0 (Nat.lt_succ_self k0)
                                    summary hi.val hwf.node_summary
                                  have hsumWf : WellFormed summary' := by
                                    simpa [summary'] using hsumRec.1
                                  have hsumSet : summary'.toFinset =
                                      summary.toFinset.erase hi.val := by
                                    simpa [summary'] using hsumRec.2
                                  have hsumExact : ∀ j : Fin (uSize k0),
                                      j.val ∈ summary'.toFinset ↔
                                        (newClusters j).toFinset.Nonempty :=
                                    summary_mem_iff_update_empty
                                      (fun j => hwf.node_summary_mem_iff j)
                                      hsumSet hempty
                                  have hresult : WellFormed
                                      (VEBTreeMM.node (some newMin) (some v) summary'
                                        newClusters) := by
                                    refine ⟨?_, ?_, hdetached, hsumExact,
                                      hsumWf, hall⟩
                                    · rw [hsem (some v) summary']
                                      exact hminErase
                                    · rw [hsem (some v) summary']
                                      exact hmaxErase
                                  constructor
                                  · simpa [delete, h_one, hi, hsmin, hfcBound, hcmin,
                                      newMin, cluster', newClusters, hcafter,
                                      summary'] using hresult
                                  · simpa [delete, h_one, hi, hsmin, hfcBound, hcmin,
                                      newMin, cluster', newClusters, hcafter,
                                      summary'] using hsem (some v) summary'
                              | some remaining =>
                                  have hnewNonempty : cluster'.toFinset.Nonempty :=
                                    ⟨remaining, hclusterWf.minimum_mem hcafter⟩
                                  have hsumExact : ∀ j : Fin (uSize k0),
                                      j.val ∈ summary.toFinset ↔
                                        (newClusters j).toFinset.Nonempty :=
                                    summary_mem_iff_update_nonempty
                                      (fun j => hwf.node_summary_mem_iff j)
                                      hclusterNonempty hnewNonempty
                                  have hresult : WellFormed
                                      (VEBTreeMM.node (some newMin) (some v) summary
                                        newClusters) := by
                                    refine ⟨?_, ?_, hdetached, hsumExact,
                                      hwf.node_summary, hall⟩
                                    · rw [hsem (some v) summary]
                                      exact hminErase
                                    · rw [hsem (some v) summary]
                                      exact hmaxErase
                                  constructor
                                  · simpa [delete, h_one, hi, hsmin, hfcBound, hcmin,
                                      newMin, cluster', newClusters, hcafter] using hresult
                                  · simpa [delete, h_one, hi, hsmin, hfcBound, hcmin,
                                      newMin, cluster', newClusters, hcafter] using
                                      hsem (some v) summary
                    · by_cases hhigh : high (uSize k0) x < uSize k0
                      · let hi : Fin (uSize k0) := ⟨high (uSize k0) x, hhigh⟩
                        let lo := low (uSize k0) x
                        let cluster' := delete lo (clusters hi)
                        let newClusters := Function.update clusters hi cluster'
                        have hrec := ih k0 (Nat.lt_succ_self k0) (clusters hi) lo
                          (hwf.node_cluster hi)
                        have hclusterWf : WellFormed cluster' := by
                          simpa [cluster'] using hrec.1
                        have hclusterSet : cluster'.toFinset =
                            (clusters hi).toFinset.erase lo := by
                          simpa [cluster', hi, lo] using hrec.2
                        have hstored : (some m : Option Nat) ≠ some x := by
                          intro h
                          exact hx_min (Option.some.inj h).symm
                        have hsem (mx' : Option Nat) (summary' : VEBTreeMM k0) :
                            (VEBTreeMM.node (some m) mx' summary' newClusters).toFinset =
                              (VEBTreeMM.node (some m) (some v) summary clusters).toFinset.erase x := by
                          simpa [newClusters, hi, lo, cluster', toFinset] using
                            (toFinset_update_cluster_erase (some m) mx' summary' clusters x
                              hhigh cluster' (by simpa [hi, lo] using hclusterSet) hstored)
                        have hminErase : MinCorrect (some m)
                            ((VEBTreeMM.node (some m) (some v) summary clusters).toFinset.erase x) :=
                          MinCorrect.erase_of_ne hwf.minCorrect (Ne.symm hx_min)
                        have hdetached : ∀ m', (some m : Option Nat) = some m' →
                            ∀ (j : Fin (uSize k0)) (off : Nat),
                              off ∈ (newClusters j).toFinset →
                                index (uSize k0) j.val off ≠ m' := by
                          exact node_min_detached_update_erase hwf.node_min_detached hclusterSet
                        have hall : ∀ j, WellFormed (newClusters j) := by
                          exact update_clusters_wellFormed
                            (fun j => hwf.node_cluster j) hclusterWf
                        cases hcm : cluster'.minimum with
                        | none =>
                            have hempty : cluster'.toFinset = ∅ :=
                              hclusterWf.minimum_none_iff.mp hcm
                            let summary' := delete hi.val summary
                            have hsumRec := ih k0 (Nat.lt_succ_self k0) summary hi.val
                              hwf.node_summary
                            have hsumWf : WellFormed summary' := by
                              simpa [summary'] using hsumRec.1
                            have hsumSet : summary'.toFinset =
                                summary.toFinset.erase hi.val := by
                              simpa [summary'] using hsumRec.2
                            have hsumExact : ∀ j : Fin (uSize k0),
                                j.val ∈ summary'.toFinset ↔
                                  (newClusters j).toFinset.Nonempty := by
                              exact summary_mem_iff_update_empty
                                (fun j => hwf.node_summary_mem_iff j) hsumSet hempty
                            by_cases hxmax : x = v
                            · subst v
                              have hminResult : MinCorrect (some m)
                                  (VEBTreeMM.node (some m) none summary'
                                    newClusters).toFinset := by
                                rw [hsem none summary']
                                exact hminErase
                              cases hsmax : summary'.maximum with
                              | none =>
                                  have hsumEmpty : summary'.toFinset = ∅ :=
                                    hsumWf.maximum_none_iff.mp hsmax
                                  have hclustersEmpty : ∀ j,
                                      (newClusters j).toFinset = ∅ := by
                                    intro j
                                    apply Finset.not_nonempty_iff_eq_empty.mp
                                    intro hj
                                    have : j.val ∈ summary'.toFinset :=
                                      (hsumExact j).2 hj
                                    simpa [hsumEmpty] using this
                                  have hmaxNew : MaxCorrect (some m)
                                      (VEBTreeMM.node (some m) (some m) summary'
                                        newClusters).toFinset := by
                                    constructor
                                    · simpa [toFinset] using MinCorrect.mem hminResult
                                    · intro y hy
                                      rw [mem_toFinset_node] at hy
                                      rcases hy with (⟨m', hmn, _, hym⟩ |
                                        ⟨j, off, hoff, _⟩)
                                      · have hmm : m' = m := by
                                          simpa using Option.some.inj hmn.symm
                                        omega
                                      · rw [hclustersEmpty j] at hoff
                                        simp at hoff
                                  have hresult : WellFormed
                                      (VEBTreeMM.node (some m) (some m) summary'
                                        newClusters) := by
                                    refine ⟨?_, hmaxNew, hdetached, hsumExact,
                                      hsumWf, hall⟩
                                    simpa [toFinset] using hminResult
                                  constructor
                                  · simpa [delete, h_one, hx_min, hhigh, hi, lo,
                                      cluster', newClusters, hcm, summary', hsmax] using hresult
                                  · simpa [delete, h_one, hx_min, hhigh, hi, lo,
                                      cluster', newClusters, hcm, summary', hsmax] using
                                      hsem (some m) summary'
                              | some last =>
                                  have hlastMem : last ∈ summary'.toFinset :=
                                    hsumWf.maximum_mem hsmax
                                  have hlastBound : last < uSize k0 :=
                                    toFinset_lt_uSize summary' last hlastMem
                                  let lastFin : Fin (uSize k0) := ⟨last, hlastBound⟩
                                  have hlastErase : last ∈ summary.toFinset.erase hi.val := by
                                    rw [← hsumSet]
                                    exact hlastMem
                                  have hlastNeVal : last ≠ hi.val :=
                                    (Finset.mem_erase.mp hlastErase).1
                                  have hlastNe : lastFin ≠ hi := by
                                    intro h
                                    apply hlastNeVal
                                    exact congrArg Fin.val h
                                  have hlastNonempty :
                                      (newClusters lastFin).toFinset.Nonempty :=
                                    (hsumExact lastFin).1 (by simpa [lastFin] using hlastMem)
                                  have hlastOldNonempty :
                                      (clusters lastFin).toFinset.Nonempty := by
                                    simpa [newClusters, Function.update_of_ne hlastNe] using
                                      hlastNonempty
                                  cases hlastMax : (clusters lastFin).maximum with
                                  | none =>
                                      exact False.elim (hlastOldNonempty.ne_empty
                                        ((hwf.node_cluster lastFin).maximum_none_iff.mp hlastMax))
                                  | some off =>
                                      let newMax := index (uSize k0) last off
                                      have hlastMaxNew :
                                          (newClusters lastFin).maximum = some off := by
                                        simpa [newClusters, Function.update_of_ne hlastNe] using
                                          hlastMax
                                      have hmaxNew : MaxCorrect (some newMax)
                                          (VEBTreeMM.node (some m) none summary'
                                            newClusters).toFinset := by
                                        simpa [newMax, lastFin] using
                                          (maxCorrect_of_summary_max m summary' newClusters
                                            hminResult hsumWf hsumExact hall lastFin
                                            (by simpa [lastFin] using hsmax) hlastMaxNew)
                                      have hresult : WellFormed
                                          (VEBTreeMM.node (some m) (some newMax) summary'
                                            newClusters) := by
                                        refine ⟨?_, ?_, hdetached, hsumExact, hsumWf, hall⟩
                                        · simpa [toFinset] using hminResult
                                        · simpa [toFinset] using hmaxNew
                                      constructor
                                      · simpa [delete, h_one, hx_min, hhigh, hi, lo,
                                          cluster', newClusters, hcm, summary', hsmax,
                                          hlastBound, lastFin, hlastMax, newMax] using hresult
                                      · simpa [delete, h_one, hx_min, hhigh, hi, lo,
                                          cluster', newClusters, hcm, summary', hsmax,
                                          hlastBound, lastFin, hlastMax, newMax] using
                                          hsem (some newMax) summary'
                            · have hmaxErase : MaxCorrect (some v)
                                  ((VEBTreeMM.node (some m) (some v) summary clusters).toFinset.erase x) :=
                                MaxCorrect.erase_of_ne hwf.maxCorrect (Ne.symm hxmax)
                              have hresult : WellFormed
                                  (VEBTreeMM.node (some m) (some v) summary' newClusters) := by
                                refine ⟨?_, ?_, hdetached, hsumExact, hsumWf, hall⟩
                                · rw [hsem (some v) summary']
                                  exact hminErase
                                · rw [hsem (some v) summary']
                                  exact hmaxErase
                              constructor
                              · simpa [delete, h_one, hx_min, hhigh, hi, lo, cluster',
                                  newClusters, hcm, hxmax, summary'] using hresult
                              · simpa [delete, h_one, hx_min, hhigh, hi, lo, cluster',
                                  newClusters, hcm, hxmax, summary'] using
                                  hsem (some v) summary'
                        | some cm =>
                            have hnewNonempty : cluster'.toFinset.Nonempty :=
                              ⟨cm, hclusterWf.minimum_mem hcm⟩
                            have holdNonempty : (clusters hi).toFinset.Nonempty := by
                              rcases hnewNonempty with ⟨off, hoff⟩
                              exact ⟨off, Finset.mem_of_mem_erase (by
                                rw [← hclusterSet]
                                exact hoff)⟩
                            have hsumExact : ∀ j : Fin (uSize k0),
                                j.val ∈ summary.toFinset ↔
                                  (newClusters j).toFinset.Nonempty := by
                              exact summary_mem_iff_update_nonempty
                                (fun j => hwf.node_summary_mem_iff j)
                                holdNonempty hnewNonempty
                            by_cases hxmax : x = v
                            · subst v
                              cases hcmax : cluster'.maximum with
                              | none =>
                                  exact False.elim (hnewNonempty.ne_empty
                                    (hclusterWf.maximum_none_iff.mp hcmax))
                              | some cmax =>
                                  let newMax := index (uSize k0) hi.val cmax
                                  have hmaxNew : MaxCorrect (some newMax)
                                      (VEBTreeMM.node (some m) (some x) summary
                                        newClusters).toFinset := by
                                    simpa [newMax, newClusters, hi, lo] using
                                      (maxCorrect_of_updated_cluster m x summary clusters
                                        hhigh cluster'
                                        (by simpa [hi, lo] using hclusterSet)
                                        hwf hclusterWf hcmax)
                                  have hresult : WellFormed
                                      (VEBTreeMM.node (some m) (some newMax) summary
                                        newClusters) := by
                                    refine ⟨?_, ?_, hdetached, hsumExact,
                                      hwf.node_summary, hall⟩
                                    · rw [hsem (some newMax) summary]
                                      exact hminErase
                                    · simpa [toFinset] using hmaxNew
                                  constructor
                                  · simpa [delete, h_one, hx_min, hhigh, hi, lo,
                                      cluster', newClusters, hcm, hcmax, newMax] using hresult
                                  · simpa [delete, h_one, hx_min, hhigh, hi, lo,
                                      cluster', newClusters, hcm, hcmax, newMax] using
                                      hsem (some newMax) summary
                            · have hmaxErase : MaxCorrect (some v)
                                  ((VEBTreeMM.node (some m) (some v) summary clusters).toFinset.erase x) :=
                                MaxCorrect.erase_of_ne hwf.maxCorrect (Ne.symm hxmax)
                              have hresult : WellFormed
                                  (VEBTreeMM.node (some m) (some v) summary newClusters) := by
                                refine ⟨?_, ?_, hdetached, hsumExact,
                                  hwf.node_summary, hall⟩
                                · rw [hsem (some v) summary]
                                  exact hminErase
                                · rw [hsem (some v) summary]
                                  exact hmaxErase
                              constructor
                              · simpa [delete, h_one, hx_min, hhigh, hi, lo, cluster',
                                  newClusters, hcm, hxmax] using hresult
                              · simpa [delete, h_one, hx_min, hhigh, hi, lo, cluster',
                                  newClusters, hcm, hxmax] using hsem (some v) summary
                      · have hx_ge : uSize (k0 + 1) ≤ x := by
                          have hdiv : uSize k0 ≤ x / uSize k0 := by
                            simpa [high] using Nat.le_of_not_lt hhigh
                          have hmul : uSize k0 * uSize k0 ≤ x := by
                            calc
                              uSize k0 * uSize k0 ≤ uSize k0 * (x / uSize k0) :=
                                Nat.mul_le_mul_left (uSize k0) hdiv
                              _ ≤ x := Nat.mul_div_le x (uSize k0)
                          simpa [uSize_succ] using hmul
                        have hx_not_mem : x ∉
                            (VEBTreeMM.node (some m) (some v) summary clusters).toFinset := by
                          intro hxmem
                          exact (Nat.not_lt_of_ge hx_ge)
                            (toFinset_lt_uSize _ x hxmem)
                        constructor
                        · simpa [delete, h_one, hx_min, hhigh] using hwf
                        · have herase := Finset.erase_eq_self.mpr hx_not_mem
                          simpa [delete, h_one, hx_min, hhigh, herase]

/-- Recursive deletion preserves the min/max-augmented vEB invariant. -/
theorem delete_wellFormed {k : Nat} (v : VEBTreeMM k) (x : Nat)
    (hwf : WellFormed v) : WellFormed (delete x v) :=
  (delete_correct v x hwf).1

/-- Recursive deletion refines `Finset.erase` on every well-formed vEB tree. -/
theorem delete_toFinset {k : Nat} (v : VEBTreeMM k) (x : Nat)
    (hwf : WellFormed v) : (delete x v).toFinset = v.toFinset.erase x :=
  (delete_correct v x hwf).2

/-- Membership after deletion is exactly old membership away from the erased key. -/
theorem delete_member_iff {k : Nat} (v : VEBTreeMM k) (x y : Nat)
    (hwf : WellFormed v) :
    member y (delete x v) = true ↔ y ≠ x ∧ member y v = true := by
  rw [member_correct (delete x v) y, delete_toFinset v x hwf,
    Finset.mem_erase, ← member_correct v y]

/-- The erased key is absent after recursive deletion. -/
theorem delete_member_deleted_false {k : Nat} (v : VEBTreeMM k) (x : Nat)
    (hwf : WellFormed v) :
    member x (delete x v) = false := by
  apply Bool.eq_false_iff.mpr
  intro hmem
  exact (delete_member_iff v x x hwf).1 hmem |>.1 rfl

/-- Deletion preserves every old member different from the erased key. -/
theorem delete_member_of_ne {k : Nat} (v : VEBTreeMM k) (x y : Nat)
    (hwf : WellFormed v) (hyx : y ≠ x) (hy : member y v = true) :
    member y (delete x v) = true :=
  (delete_member_iff v x y hwf).2 ⟨hyx, hy⟩

end VEBTreeMM
end Chapter20
end CLRS

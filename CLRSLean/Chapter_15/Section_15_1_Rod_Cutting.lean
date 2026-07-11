import Mathlib

/-!
# CLRS Section 15.1 - Rod cutting

This section formalizes the mathematical core of the rod-cutting dynamic
program.  Instead of committing immediately to one array implementation, it
defines the Bellman first-cut recurrence as a specification for a revenue
function.  The main theorem proves that any revenue function satisfying that
recurrence upper-bounds the value of every concrete cutting plan.  Consequently,
any plan whose value attains the recurrence value is optimal among plans of the
same total length.

Main results:

* Theorem {lit}`firstCutValue_le_of_rodCutRecurrence`: every admissible first
  cut is bounded by the recurrence value.
* Theorem {lit}`rodRevenue_le_of_firstCutValue_bounds`: the recurrence value is
  the least upper bound induced by first-cut candidates.
* Theorem {lit}`bottomUpRodRevenue_rodCutRecurrence`: the executable
  recurrence-valued rod-cutting function satisfies the CLRS Bellman recurrence.
* Theorem {lit}`planValue_le_table_of_rodCutTableRecurrence`: any finite table
  filled by the bottom-up recurrence is an upper bound for every positive-piece
  cutting plan within its filled prefix.
* Theorem {lit}`planValue_le_revenue_of_rodCutRecurrence`: every positive-piece
  cutting plan is bounded by the recurrence value of its total length.
* Theorem {lit}`planValue_le_optimalPlanValue_of_same_length`: a plan attaining
  the recurrence value is optimal among plans of the same length.
* Definition {lit}`rodRevenueArray`: the CLRS {lit}`BOTTOM-UP-CUT-ROD` table built as
  a mutable {lit}`Array Nat`, whose entry {lit}`k` is filled from the earlier stored
  entries exactly as the imperative algorithm fills {lit}`r[0 .. n]`.
* Theorem {lit}`rodRevenueArray_correct`: the mutable-array bottom-up table refines
  the pure recurrence value {lit}`bottomUpRodRevenue` at every filled index.
* Theorem {lit}`rodRevenueArray_rodCutTableRecurrence`: reading the mutable-array
  table is a correct finite bottom-up table in the sense of
  {lit}`RodCutTableRecurrence`.
* Theorem {lit}`planValue_le_rodRevenueArray`: every positive-piece cutting plan is
  bounded by the value the mutable-array table stores at its total length.

Status: `proved` for the mathematical cut-optimality layer and the mutable-array
bottom-up implementation refinement.

Deferred refinements:

* A top-down memoized-cache refinement and explicit RAM cost semantics remain
  future implementation-level targets.  The sibling dynamic-programming sections
  (matrix chain, LCS, optimal BST) follow the same mutable-array bottom-up
  pattern established here.
-/

namespace CLRS
namespace Chapter15

/-! ## Rod-cutting model -/

/-- The total length of a concrete cutting plan. -/
def planLength (pieces : List Nat) : Nat :=
  pieces.sum

/-- The value of a cutting plan under the given price table. -/
def planValue (price : Nat → Nat) (pieces : List Nat) : Nat :=
  (pieces.map price).sum

/-- Every piece in the cutting plan has positive length. -/
def PositivePieces (pieces : List Nat) : Prop :=
  ∀ piece, piece ∈ pieces → 0 < piece

/-- The value obtained by making {lit}`cut` the first cut of a rod of length {lit}`n`. -/
def FirstCutValue (price revenue : Nat → Nat) (n cut : Nat) : Nat :=
  price cut + revenue (n - cut)

/--
The CLRS rod-cutting recurrence: length zero has value zero, and every positive
length is the maximum over all possible first cuts.
-/
def RodCutRecurrence (price revenue : Nat → Nat) : Prop :=
  revenue 0 = 0 ∧
    ∀ n, revenue (n + 1) =
      (Finset.Icc 1 (n + 1)).sup
        (fun cut => FirstCutValue price revenue (n + 1) cut)

/-! ## Bottom-up table and executable recurrence -/

/--
A finite bottom-up rod-cutting table is correct through {lit}`limit` when entry
zero is zero and every positive entry up to {lit}`limit` is filled by the CLRS
first-cut recurrence using earlier table entries.
-/
def RodCutTableRecurrence (price table : Nat → Nat) (limit : Nat) : Prop :=
  table 0 = 0 ∧
    ∀ n, n < limit →
      table (n + 1) =
        (Finset.Icc 1 (n + 1)).sup
          (fun cut => FirstCutValue price table (n + 1) cut)

/--
The canonical executable rod-cutting value function obtained by recursively
evaluating the CLRS first-cut recurrence.  The recurrence is written over
{lit}`Finset.attach` so Lean sees that each recursive call is made at a strictly
smaller rod length.
-/
def bottomUpRodRevenue (price : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 =>
      (Finset.Icc 1 (n + 1)).attach.sup
        (fun cut => price cut.1 + bottomUpRodRevenue price ((n + 1) - cut.1))
termination_by n => n
decreasing_by
  simp_wf
  exact (Finset.mem_Icc.mp cut.2).1

private theorem finset_attach_sup_eq (s : Finset Nat) (f : Nat → Nat) :
    s.attach.sup (fun x => f x.1) = s.sup f := by
  apply le_antisymm
  · refine Finset.sup_le ?_
    intro x _hx
    exact Finset.le_sup (f := f) x.2
  · refine Finset.sup_le ?_
    intro x hx
    exact Finset.le_sup (f := fun x : {x // x ∈ s} => f x.1)
      (Finset.mem_attach s ⟨x, hx⟩)

@[simp] theorem bottomUpRodRevenue_zero (price : Nat → Nat) :
    bottomUpRodRevenue price 0 = 0 := by
  rw [bottomUpRodRevenue]

/-- The executable recurrence unfolds to the textbook first-cut maximum. -/
theorem bottomUpRodRevenue_succ (price : Nat → Nat) (n : Nat) :
    bottomUpRodRevenue price (n + 1) =
      (Finset.Icc 1 (n + 1)).sup
        (fun cut => FirstCutValue price (bottomUpRodRevenue price) (n + 1) cut) := by
  rw [bottomUpRodRevenue]
  change (Finset.Icc 1 (n + 1)).attach.sup
        (fun cut => price cut.1 + bottomUpRodRevenue price ((n + 1) - cut.1)) =
      (Finset.Icc 1 (n + 1)).sup
        (fun cut => price cut + bottomUpRodRevenue price ((n + 1) - cut))
  simpa [FirstCutValue] using
    (finset_attach_sup_eq (Finset.Icc 1 (n + 1))
      (fun cut => price cut + bottomUpRodRevenue price ((n + 1) - cut)))

/-- The executable recurrence-valued function satisfies the CLRS recurrence. -/
theorem bottomUpRodRevenue_rodCutRecurrence (price : Nat → Nat) :
    RodCutRecurrence price (bottomUpRodRevenue price) := by
  constructor
  · exact bottomUpRodRevenue_zero price
  · intro n
    exact bottomUpRodRevenue_succ price n

/-- A global recurrence function induces a correct finite table prefix. -/
theorem rodCutTableRecurrence_of_rodCutRecurrence {price revenue : Nat → Nat}
    (hrec : RodCutRecurrence price revenue) (limit : Nat) :
    RodCutTableRecurrence price revenue limit := by
  constructor
  · exact hrec.1
  · intro n _hn
    exact hrec.2 n

/-- Every prefix of the executable recurrence-valued function is a correct table. -/
theorem bottomUpRodRevenue_rodCutTableRecurrence
    (price : Nat → Nat) (limit : Nat) :
    RodCutTableRecurrence price (bottomUpRodRevenue price) limit :=
  rodCutTableRecurrence_of_rodCutRecurrence
    (bottomUpRodRevenue_rodCutRecurrence price) limit

/-! ## First-cut recurrence facts -/

/-- Every admissible first cut is bounded by the recurrence value. -/
theorem firstCutValue_le_of_rodCutRecurrence {price revenue : Nat → Nat}
    (hrec : RodCutRecurrence price revenue) {n cut : Nat}
    (hcut : cut ∈ Finset.Icc 1 n) :
    FirstCutValue price revenue n cut ≤ revenue n := by
  cases n with
  | zero =>
      simp at hcut
  | succ n =>
      rw [hrec.2 n]
      exact Finset.le_sup hcut

/--
If a number bounds every first-cut candidate, then it bounds the recurrence
value.  This is the upper-bound half of the Bellman maximum principle.
-/
theorem rodRevenue_le_of_firstCutValue_bounds {price revenue : Nat → Nat}
    (hrec : RodCutRecurrence price revenue) {n bound : Nat}
    (hbound : ∀ cut, cut ∈ Finset.Icc 1 n →
      FirstCutValue price revenue n cut ≤ bound) :
    revenue n ≤ bound := by
  cases n with
  | zero =>
      rw [hrec.1]
      exact Nat.zero_le bound
  | succ n =>
      rw [hrec.2 n]
      exact Finset.sup_le hbound

/-- Selling the whole rod as one piece is one admissible first-cut candidate. -/
theorem price_le_revenue_of_rodCutRecurrence {price revenue : Nat → Nat}
    (hrec : RodCutRecurrence price revenue) {n : Nat} (hn : 1 ≤ n) :
    price n ≤ revenue n := by
  have hmem : n ∈ Finset.Icc 1 n := by
    rw [Finset.mem_Icc]
    exact ⟨hn, le_rfl⟩
  have hcut := firstCutValue_le_of_rodCutRecurrence
    (price := price) (revenue := revenue) hrec hmem
  have hprice : price n ≤ FirstCutValue price revenue n n := by
    unfold FirstCutValue
    omega
  exact Nat.le_trans hprice hcut

/-! ## Bottom-up table facts -/

/--
Every admissible first cut is bounded by the value stored in a correct finite
bottom-up table, provided the queried rod length lies inside the filled prefix.
-/
theorem firstCutValue_le_of_rodCutTableRecurrence {price table : Nat → Nat}
    {limit n cut : Nat}
    (htable : RodCutTableRecurrence price table limit)
    (hn : n ≤ limit)
    (hcut : cut ∈ Finset.Icc 1 n) :
    FirstCutValue price table n cut ≤ table n := by
  cases n with
  | zero =>
      simp at hcut
  | succ n =>
      rw [htable.2 n (Nat.lt_of_succ_le hn)]
      exact Finset.le_sup hcut

/--
If a number bounds every first-cut candidate inside a correct finite table
prefix, then it bounds the stored table value.
-/
theorem rodTableValue_le_of_firstCutValue_bounds {price table : Nat → Nat}
    {limit n bound : Nat}
    (htable : RodCutTableRecurrence price table limit)
    (hn : n ≤ limit)
    (hbound : ∀ cut, cut ∈ Finset.Icc 1 n →
      FirstCutValue price table n cut ≤ bound) :
    table n ≤ bound := by
  cases n with
  | zero =>
      rw [htable.1]
      exact Nat.zero_le bound
  | succ n =>
      rw [htable.2 n (Nat.lt_of_succ_le hn)]
      exact Finset.sup_le hbound

/-- Selling the whole rod is also bounded by a correct finite table prefix. -/
theorem price_le_table_of_rodCutTableRecurrence {price table : Nat → Nat}
    {limit n : Nat}
    (htable : RodCutTableRecurrence price table limit)
    (hn : 1 ≤ n) (hlimit : n ≤ limit) :
    price n ≤ table n := by
  have hmem : n ∈ Finset.Icc 1 n := by
    rw [Finset.mem_Icc]
    exact ⟨hn, le_rfl⟩
  have hcut := firstCutValue_le_of_rodCutTableRecurrence
    (price := price) (table := table) (limit := limit) htable hlimit hmem
  have hprice : price n ≤ FirstCutValue price table n n := by
    unfold FirstCutValue
    omega
  exact Nat.le_trans hprice hcut

/-! ## Plan optimality -/

/--
Every concrete cutting plan with positive pieces is bounded by the recurrence
value of its total length.
-/
theorem planValue_le_revenue_of_rodCutRecurrence {price revenue : Nat → Nat}
    (hrec : RodCutRecurrence price revenue) :
    ∀ pieces, PositivePieces pieces →
      planValue price pieces ≤ revenue (planLength pieces)
  | [], _hpos => by
      simp [planValue, planLength, hrec.1]
  | piece :: rest, hpos => by
      have hpiece_pos : 0 < piece := by
        exact hpos piece (by simp)
      have hrest_pos : PositivePieces rest := by
        intro x hx
        exact hpos x (by simp [hx])
      have ih :=
        planValue_le_revenue_of_rodCutRecurrence
          (price := price) (revenue := revenue) hrec rest hrest_pos
      have hmem : piece ∈ Finset.Icc 1 (piece + planLength rest) := by
        rw [Finset.mem_Icc]
        exact ⟨Nat.succ_le_of_lt hpiece_pos, Nat.le_add_right piece (planLength rest)⟩
      have hcut := firstCutValue_le_of_rodCutRecurrence
        (price := price) (revenue := revenue) hrec hmem
      have hcut' :
          price piece + revenue (planLength rest) ≤
            revenue (piece + planLength rest) := by
        simpa [FirstCutValue, Nat.add_sub_cancel_left] using hcut
      have hmono :
          price piece + planValue price rest ≤
          price piece + revenue (planLength rest) :=
        Nat.add_le_add_left ih (price piece)
      simpa [planValue, planLength] using Nat.le_trans hmono hcut'

/--
Every concrete cutting plan whose total length is inside a correct finite
bottom-up table prefix is bounded by the table value at that total length.
-/
theorem planValue_le_table_of_rodCutTableRecurrence {price table : Nat → Nat}
    {limit : Nat}
    (htable : RodCutTableRecurrence price table limit) :
    ∀ pieces, PositivePieces pieces → planLength pieces ≤ limit →
      planValue price pieces ≤ table (planLength pieces)
  | [], _hpos, _hlen => by
      simp [planValue, planLength, htable.1]
  | piece :: rest, hpos, hlen => by
      have hpiece_pos : 0 < piece := by
        exact hpos piece (by simp)
      have hrest_pos : PositivePieces rest := by
        intro x hx
        exact hpos x (by simp [hx])
      have htotal : piece + planLength rest ≤ limit := by
        simpa [planLength] using hlen
      have hrest_limit : planLength rest ≤ limit := by
        omega
      have ih : planValue price rest ≤ table (planLength rest) :=
        planValue_le_table_of_rodCutTableRecurrence
          (price := price) (table := table) (limit := limit)
          htable rest hrest_pos hrest_limit
      have hmem : piece ∈ Finset.Icc 1 (piece + planLength rest) := by
        rw [Finset.mem_Icc]
        exact ⟨Nat.succ_le_of_lt hpiece_pos,
          Nat.le_add_right piece (planLength rest)⟩
      have hfirst := firstCutValue_le_of_rodCutTableRecurrence
        (price := price) (table := table) (limit := limit)
        htable htotal hmem
      have hfirstBound :
          price piece + table (planLength rest) ≤
            table (piece + planLength rest) := by
        simpa [FirstCutValue, Nat.add_sub_cancel_left] using hfirst
      have hmono :
          price piece + planValue price rest ≤
            price piece + table (planLength rest) :=
        Nat.add_le_add_left ih (price piece)
      simpa [planValue, planLength] using Nat.le_trans hmono hfirstBound

/--
Every positive-piece cutting plan is bounded by the executable recurrence value
of its total length.
-/
theorem planValue_le_bottomUpRodRevenue (price : Nat → Nat) :
    ∀ pieces, PositivePieces pieces →
      planValue price pieces ≤ bottomUpRodRevenue price (planLength pieces) :=
  planValue_le_revenue_of_rodCutRecurrence
    (price := price) (revenue := bottomUpRodRevenue price)
    (bottomUpRodRevenue_rodCutRecurrence price)

/--
If a cutting plan attains the recurrence value for its length, then every other
positive-piece plan of the same total length has value at most that plan.
-/
theorem planValue_le_optimalPlanValue_of_same_length
    {price revenue : Nat → Nat} (hrec : RodCutRecurrence price revenue)
    {candidate other : List Nat}
    (hother_pos : PositivePieces other)
    (hlen : planLength other = planLength candidate)
    (hcandidate_value :
      planValue price candidate = revenue (planLength candidate)) :
    planValue price other ≤ planValue price candidate := by
  have hother_bound :=
    planValue_le_revenue_of_rodCutRecurrence
      (price := price) (revenue := revenue) hrec other hother_pos
  rw [hlen, ← hcandidate_value] at hother_bound
  exact hother_bound

/--
If a cutting plan attains the table value inside a correct finite bottom-up
prefix, then every other positive-piece plan of the same length has value at
most that plan.
-/
theorem planValue_le_tablePlanValue_of_same_length
    {price table : Nat → Nat} {limit : Nat}
    (htable : RodCutTableRecurrence price table limit)
    {candidate other : List Nat}
    (hother_pos : PositivePieces other)
    (hlen : planLength other = planLength candidate)
    (hcandidate_value :
      planValue price candidate = table (planLength candidate))
    (hcandidate_len : planLength candidate ≤ limit) :
    planValue price other ≤ planValue price candidate := by
  have hother_len : planLength other ≤ limit := by
    rw [hlen]
    exact hcandidate_len
  have hother_bound :=
    planValue_le_table_of_rodCutTableRecurrence
      (price := price) (table := table) (limit := limit)
      htable other hother_pos hother_len
  rw [hlen, ← hcandidate_value] at hother_bound
  exact hother_bound

/--
If a cutting plan attains the executable recurrence value for its length, then
every other positive-piece plan of the same length has value at most that plan.
-/
theorem planValue_le_bottomUpRodPlanValue_of_same_length
    {price : Nat → Nat} {candidate other : List Nat}
    (hother_pos : PositivePieces other)
    (hlen : planLength other = planLength candidate)
    (hcandidate_value :
      planValue price candidate =
        bottomUpRodRevenue price (planLength candidate)) :
    planValue price other ≤ planValue price candidate :=
  planValue_le_optimalPlanValue_of_same_length
    (price := price) (revenue := bottomUpRodRevenue price)
    (bottomUpRodRevenue_rodCutRecurrence price)
    hother_pos hlen hcandidate_value

/-! ## Mutable-array bottom-up implementation

This block refines the pure recurrence-valued rod-cutting function to CLRS's
{lit}`BOTTOM-UP-CUT-ROD`, which fills a physical revenue table {lit}`r[0 .. n]` from
the bottom up.  We model the table as an actual {lit}`Array Nat` grown one slot at
a time with {name}`Array.push`, reusing the mutable-{lit}`Array` pattern of Section
17.4, and prove a refinement theorem: reading the mutable table at any filled index
returns exactly the pure recurrence value {name}`bottomUpRodRevenue`.  As a
corollary the array read satisfies {name}`RodCutTableRecurrence`, so the mutable
table inherits the plan-optimality guarantees proved above.
-/

/--
Total read from a {lit}`Nat`-valued array, returning {lit}`0` for out-of-range
indices.  This models the invariant-guarded reads a bottom-up dynamic-programming
table performs: every access made by the algorithm is in range, and the default
never fires during a real fill.
-/
def arrGet (a : Array Nat) (i : Nat) : Nat := (a[i]?).getD 0

/-- Reading an in-range index is unaffected by pushing a new trailing element. -/
theorem arrGet_push_lt (a : Array Nat) (x i : Nat) (h : i < a.size) :
    arrGet (a.push x) i = arrGet a i := by
  unfold arrGet
  rw [Array.getElem?_push, if_neg (Nat.ne_of_lt h)]

/-- Reading the freshly pushed slot returns the pushed element. -/
theorem arrGet_push_size (a : Array Nat) (x : Nat) :
    arrGet (a.push x) a.size = x := by
  unfold arrGet
  rw [Array.getElem?_push, if_pos rfl]
  rfl

/--
Bottom-up mutable-array construction of the rod-cutting revenue table.  The value
{lit}`rodRevenueArrayAux price n` is an {lit}`Array Nat` of length {lit}`n + 1`
whose entry {lit}`k` is the best revenue for a rod of length {lit}`k`.  Each new
entry is computed as the CLRS first-cut maximum over {lit}`Finset.Icc 1 (j + 1)`,
reading the earlier revenues that are already stored in the array - the imperative
{lit}`BOTTOM-UP-CUT-ROD` inner loop {lit}`q = max(q, p[i] + r[j - i])`.
-/
def rodRevenueArrayAux (price : Nat → Nat) : Nat → Array Nat
  | 0 => #[0]
  | j + 1 =>
      (rodRevenueArrayAux price j).push
        ((Finset.Icc 1 (j + 1)).sup
          (fun i => price i + arrGet (rodRevenueArrayAux price j) ((j + 1) - i)))

/-- The bottom-up table for rod length {lit}`n` stores exactly {lit}`n + 1` entries. -/
theorem rodRevenueArrayAux_size (price : Nat → Nat) (n : Nat) :
    (rodRevenueArrayAux price n).size = n + 1 := by
  induction n with
  | zero => rfl
  | succ j ih => simp only [rodRevenueArrayAux, Array.size_push, ih]

/--
**Refinement of the mutable-array fill to the recurrence value.**  Every filled
entry of the bottom-up array equals the pure recurrence value
{name}`bottomUpRodRevenue` at the same index.  The proof is an induction on the
table length whose step reads back the earlier entries the fill relied upon.
-/
theorem arrGet_rodRevenueArrayAux (price : Nat → Nat) :
    ∀ n k, k ≤ n → arrGet (rodRevenueArrayAux price n) k = bottomUpRodRevenue price k := by
  intro n
  induction n with
  | zero =>
      intro k hk
      obtain rfl : k = 0 := Nat.le_zero.mp hk
      simp only [rodRevenueArrayAux, bottomUpRodRevenue_zero]
      rfl
  | succ j ih =>
      intro k hk
      have hsize : (rodRevenueArrayAux price j).size = j + 1 :=
        rodRevenueArrayAux_size price j
      simp only [rodRevenueArrayAux]
      rcases Nat.eq_or_lt_of_le hk with heq | hlt
      · -- k is the newly pushed top entry j + 1
        have hk_size : k = (rodRevenueArrayAux price j).size := by rw [hsize]; exact heq
        rw [hk_size, arrGet_push_size, ← hk_size, heq]
        have hsup :
            (Finset.Icc 1 (j + 1)).sup
                (fun i => price i + arrGet (rodRevenueArrayAux price j) ((j + 1) - i))
              = (Finset.Icc 1 (j + 1)).sup
                (fun i => price i + bottomUpRodRevenue price ((j + 1) - i)) := by
          apply Finset.sup_congr rfl
          intro i hi
          have hle : (j + 1) - i ≤ j := by
            have := (Finset.mem_Icc.mp hi).1
            omega
          rw [ih ((j + 1) - i) hle]
        rw [hsup, bottomUpRodRevenue_succ]
        simp only [FirstCutValue]
      · -- k lies inside the already-filled prefix
        have hkj : k ≤ j := Nat.lt_succ_iff.mp hlt
        have hk_lt : k < (rodRevenueArrayAux price j).size := by rw [hsize]; omega
        rw [arrGet_push_lt _ _ _ hk_lt]
        exact ih k hkj

/--
The CLRS {lit}`BOTTOM-UP-CUT-ROD` revenue table for a rod of length {lit}`n`,
materialized as a mutable {lit}`Array Nat` of length {lit}`n + 1`.
-/
def rodRevenueArray (price : Nat → Nat) (n : Nat) : Array Nat :=
  rodRevenueArrayAux price n

/-- The materialized table has one entry per rod length in {lit}`0 .. n`. -/
theorem rodRevenueArray_size (price : Nat → Nat) (n : Nat) :
    (rodRevenueArray price n).size = n + 1 :=
  rodRevenueArrayAux_size price n

/--
**Correctness of the mutable-array bottom-up rod cutting.**  For every rod length
{lit}`k` inside the filled prefix, the entry the imperative table stores equals the
pure recurrence value {name}`bottomUpRodRevenue`.  This is the refinement theorem
requested by the mutable-array dynamic-programming layer of CLRS Chapter 15.
-/
theorem rodRevenueArray_correct (price : Nat → Nat) (n k : Nat) (hk : k ≤ n) :
    arrGet (rodRevenueArray price n) k = bottomUpRodRevenue price k :=
  arrGet_rodRevenueArrayAux price n k hk

/-- The top table entry is the best revenue for the full rod of length {lit}`n`. -/
theorem rodRevenueArray_full (price : Nat → Nat) (n : Nat) :
    arrGet (rodRevenueArray price n) n = bottomUpRodRevenue price n :=
  rodRevenueArray_correct price n n (le_refl n)

/--
Reading the mutable-array table is a correct finite bottom-up table: its entry
zero is zero and every positive entry inside the filled prefix is the CLRS
first-cut maximum over earlier table entries.  This connects the imperative
computation to the abstract {name}`RodCutTableRecurrence` interface.
-/
theorem rodRevenueArray_rodCutTableRecurrence (price : Nat → Nat) (n : Nat) :
    RodCutTableRecurrence price (fun k => arrGet (rodRevenueArray price n) k) n := by
  constructor
  · show arrGet (rodRevenueArray price n) 0 = 0
    rw [rodRevenueArray_correct price n 0 (Nat.zero_le n), bottomUpRodRevenue_zero]
  · intro m hm
    show arrGet (rodRevenueArray price n) (m + 1)
        = (Finset.Icc 1 (m + 1)).sup
          (fun cut => FirstCutValue price (fun k => arrGet (rodRevenueArray price n) k) (m + 1) cut)
    rw [rodRevenueArray_correct price n (m + 1) hm, bottomUpRodRevenue_succ]
    apply Finset.sup_congr rfl
    intro cut hcut
    unfold FirstCutValue
    have hle : (m + 1) - cut ≤ n := by
      have := (Finset.mem_Icc.mp hcut).1
      omega
    show price cut + bottomUpRodRevenue price ((m + 1) - cut)
        = price cut + arrGet (rodRevenueArray price n) ((m + 1) - cut)
    rw [rodRevenueArray_correct price n ((m + 1) - cut) hle]

/--
**Plan optimality through the mutable-array table.**  Every positive-piece cutting
plan whose total length lies inside the filled prefix is bounded by the value the
mutable-array bottom-up table stores at that length.  This lifts the refinement to
the same end-to-end optimality statement proved for the pure recurrence table.
-/
theorem planValue_le_rodRevenueArray (price : Nat → Nat) (n : Nat) :
    ∀ pieces, PositivePieces pieces → planLength pieces ≤ n →
      planValue price pieces ≤ arrGet (rodRevenueArray price n) (planLength pieces) :=
  planValue_le_table_of_rodCutTableRecurrence
    (rodRevenueArray_rodCutTableRecurrence price n)

end Chapter15
end CLRS

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

Status: `proved` for the mathematical cut-optimality layer.

Deferred refinements:

* Mutable-array implementation and memoized-cache refinement are future
  implementation-level targets beyond the current mathematical-correctness scope.
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

end Chapter15
end CLRS

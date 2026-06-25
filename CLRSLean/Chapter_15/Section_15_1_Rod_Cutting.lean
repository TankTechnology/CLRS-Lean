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
* Theorem {lit}`planValue_le_revenue_of_rodCutRecurrence`: every positive-piece
  cutting plan is bounded by the recurrence value of its total length.
* Theorem {lit}`planValue_le_optimalPlanValue_of_same_length`: a plan attaining
  the recurrence value is optimal among plans of the same length.

Current gaps:

* This file does not yet prove a bottom-up array implementation correct.
* Matrix-chain multiplication, LCS, and optimal binary-search trees remain
  future dynamic-programming targets.
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

end Chapter15
end CLRS

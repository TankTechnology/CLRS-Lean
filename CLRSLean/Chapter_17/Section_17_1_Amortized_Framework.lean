import Mathlib

/-!
# CLRS Section 17.1-17.3 - Amortized analysis framework

This section packages the finite-prefix arithmetic behind the aggregate,
accounting, and potential methods.  Later Chapter 17 examples and Chapter 19
Fibonacci-heap bounds can reuse these small telescoping theorems instead of
reproving the same sum algebra.

Main results:

- Theorem {lit}`aggregate_bound_of_prefix_bound`: prefix total bounds imply the
  corresponding aggregate bound.
- Theorem {lit}`accounting_totalCost_eq_totalCharge_sub_delta`: accounting
  credits telescope exactly.
- Theorem {lit}`accounting_totalCost_le_totalCharge`: nonnegative final credit
  bounds total actual cost by total charge plus initial credit.
- Theorem {lit}`potential_totalCost_eq_totalAmortized_sub_delta`: potential
  costs telescope exactly.
- Theorem {lit}`potential_totalCost_le_totalAmortized`: nondecreasing endpoint
  potential bounds total actual cost by total amortized cost.

Status: `proved` for the aggregate, accounting, and potential-method framework.

Examples are in Sections 17.2 and 17.4.
-/

namespace CLRS
namespace Chapter17

/-! ## Prefix costs -/

/-- Prefix sum of natural-number costs for the first {lit}`n` operations. -/
def prefixCost (cost : Nat -> Nat) : Nat -> Nat
  | 0 => 0
  | n + 1 => prefixCost cost n + cost n

/-- Prefix sum of integer-valued costs for the first {lit}`n` operations. -/
def prefixCostR (cost : Nat -> Int) : Nat -> Int
  | 0 => 0
  | n + 1 => prefixCostR cost n + cost n

/--
Aggregate amortized analysis: once every prefix total is bounded by a comparison
function, the same finite-prefix bound is available as the public theorem.
-/
theorem aggregate_bound_of_prefix_bound
    {cost : Nat -> Nat} {bound : Nat -> Nat}
    (h : forall n, prefixCost cost n <= bound n) :
    forall n, prefixCost cost n <= bound n := by
  exact h

/-! ## Accounting method -/

/-- A finite-prefix accounting trace with actual costs, charged costs, and credit. -/
structure AccountingTrace where
  actual : Nat -> Nat
  charge : Nat -> Nat
  credit : Nat -> Int

/-- The next credit balance after charging operation {lit}`i` and paying its actual cost. -/
def accounting_balance (tr : AccountingTrace) (i : Nat) : Int :=
  tr.credit i + Int.ofNat (tr.charge i) - Int.ofNat (tr.actual i)

/--
Exact accounting identity: if credit evolves by adding the operation charge and
subtracting the operation's actual cost, then total actual cost equals total
charge plus initial credit minus final credit.
-/
theorem accounting_totalCost_eq_totalCharge_sub_delta
    (tr : AccountingTrace) (n initial : Nat)
    (hcredit0 : tr.credit 0 = Int.ofNat initial)
    (hstep : forall i, i < n -> tr.credit (i + 1) = accounting_balance tr i) :
    Int.ofNat (prefixCost tr.actual n) =
      Int.ofNat (prefixCost tr.charge n) + Int.ofNat initial - tr.credit n := by
  induction n with
  | zero =>
      simp [prefixCost, hcredit0]
  | succ n ih =>
      have ih' := ih (by
        intro i hi
        exact hstep i (Nat.lt_trans hi (Nat.lt_succ_self n)))
      have hlast := hstep n (Nat.lt_succ_self n)
      calc
        Int.ofNat (prefixCost tr.actual (n + 1))
            = Int.ofNat (prefixCost tr.actual n) + Int.ofNat (tr.actual n) := by
                simp [prefixCost]
        _ = (Int.ofNat (prefixCost tr.charge n) + Int.ofNat initial - tr.credit n) +
              Int.ofNat (tr.actual n) := by
                rw [ih']
        _ = Int.ofNat (prefixCost tr.charge (n + 1)) + Int.ofNat initial -
              tr.credit (n + 1) := by
                simp [prefixCost, hlast, accounting_balance]
                ring

/--
Accounting-method upper bound: if final credit is nonnegative, total actual
cost is at most total charged cost plus initial credit.
-/
theorem accounting_totalCost_le_totalCharge
    (tr : AccountingTrace) (n initial : Nat)
    (hcredit0 : tr.credit 0 = Int.ofNat initial)
    (hstep : forall i, i < n -> tr.credit (i + 1) = accounting_balance tr i)
    (hnonneg : 0 <= tr.credit n) :
    Int.ofNat (prefixCost tr.actual n) <=
      Int.ofNat (prefixCost tr.charge n) + Int.ofNat initial := by
  have h := accounting_totalCost_eq_totalCharge_sub_delta tr n initial hcredit0 hstep
  rw [h]
  omega

/-! ## Potential method -/

/-- A potential-method trace with integer actual costs and potentials. -/
structure PotentialTrace where
  actual : Nat -> Int
  potential : Nat -> Int

/-- Amortized cost of operation {lit}`i` under a potential function. -/
def amortizedCost (tr : PotentialTrace) (i : Nat) : Int :=
  tr.actual i + tr.potential (i + 1) - tr.potential i

/--
Exact potential-method identity: total actual cost equals total amortized cost
minus the net potential increase.
-/
theorem potential_totalCost_eq_totalAmortized_sub_delta
    (tr : PotentialTrace) (n : Nat) :
    prefixCostR tr.actual n =
      prefixCostR (amortizedCost tr) n - (tr.potential n - tr.potential 0) := by
  induction n with
  | zero =>
      simp [prefixCostR]
  | succ n ih =>
      simp [prefixCostR, amortizedCost, ih]
      ring

/--
Potential-method upper bound: if the endpoint potential has not decreased, total
actual cost is at most total amortized cost.
-/
theorem potential_totalCost_le_totalAmortized
    (tr : PotentialTrace) (n : Nat)
    (hpot : tr.potential 0 <= tr.potential n) :
    prefixCostR tr.actual n <= prefixCostR (amortizedCost tr) n := by
  have h := potential_totalCost_eq_totalAmortized_sub_delta tr n
  rw [h]
  omega

end Chapter17
end CLRS

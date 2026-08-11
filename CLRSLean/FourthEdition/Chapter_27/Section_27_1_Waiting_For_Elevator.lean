import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# 27.1 Waiting for an elevator

This section formalizes the **rent-or-buy (ski rental)** problem that opens
CLRS §27.1 on online algorithms.  You can rent the equipment for `r` per day or
buy it for a one-time cost `p`, without knowing how many days you will need it.
An *online* algorithm must choose rent-or-buy as the days arrive; the offline
optimum knows the total number of days in advance.  The elevator scenario of
the section — wait for the elevator (renting, one time unit at a time) and if it
does not come by time `S - E`, take the stairs (buying at cost `S`) — is the
same problem with `r = 1` and `p` scaled by the elevator ride time `E`.

Main results:

- Definition `SkiRental.rentThenBuyCost`: the cost of the deterministic strategy
  that rents for the first `a` days and buys on day `a+1` if the trip outlasts it.
- Definition `SkiRental.optCost`: the optimal offline cost, `min (T*r) p`.
- Definition `SkiRental.IsCompetitive`: a strategy is `c`-competitive when its
  cost is at most `c` times the optimal offline cost on every input.
- Theorem `SkiRental.rentThenBuy_two_competitive` (Theorem 27.1, upper bound):
  any strategy that rents `a` days with `a*r < p ≤ (a+1)*r` — rent strictly less
  than the break-even point, buy no later than the day renting overtakes buying
  — is `2`-competitive.
- Definition `Elevator.cost` and `Elevator.optCost`: the elevator instance.
- Theorem `Elevator.elevator_two_competitive`: the "wait `S - E` then take the
  stairs" strategy is `2`-competitive.
- Lemma `Elevator.elevator_worst_case_ratio`: when the elevator comes late the
  cost is exactly `(2 - E/S) * S`, the competitive ratio stated in CLRS §27.1.

The model is deliberately thin: costs are real numbers, the input is the total
number of days `T : ℕ`, and a deterministic online strategy is a "rent `a` days
then buy" threshold.  The lower bound that no deterministic strategy beats
`2 - r/p` is **not yet formalized** and is recorded as a gap; the framework
(`IsCompetitive`) is set up so that bound can be added as a direct statement.

Notation conventions used in this section:

- `r` : the daily rental cost
- `p` : the one-time purchase cost
- `a` : the number of days a strategy rents before buying
- `T` : the total number of days (the input, unknown to the online algorithm)
- `E` : the elevator ride time
- `S` : the time the stairs take
- `w` : the number of seconds a strategy waits before taking the stairs
-/

noncomputable section

namespace CLRS

namespace SkiRental

/--
The **cost** of the deterministic online strategy that rents for the first `a`
days and, if the trip lasts longer than `a` days, buys on day `a+1`, on an
input of `T` days: it pays `T * r` (renting every day) when `T ≤ a`, and
`a * r + p` (renting `a` days then buying) otherwise.  `r` is the per-day rental
cost and `p` the one-time purchase cost (CLRS §27.1).
-/
def rentThenBuyCost (r p : ℝ) (a T : ℕ) : ℝ :=
  if T ≤ a then (T : ℝ) * r else (a : ℝ) * r + p

/--
The **optimal offline cost** for a trip of `T` days: rent every day (cost
`T * r`) or buy once (cost `p`), whichever is cheaper.  The offline optimum
knows `T` in advance.
-/
def optCost (r p : ℝ) (T : ℕ) : ℝ :=
  min ((T : ℝ) * r) p

/--
A deterministic strategy `a` is **`c`-competitive** when, on every input `T`,
its cost is at most `c` times the optimal offline cost.
-/
def IsCompetitive (r p c : ℝ) (a : ℕ) : Prop :=
  ∀ T : ℕ, rentThenBuyCost r p a T ≤ c * optCost r p T

/-- On a trip short enough that renting every day is no more than buying, the
offline optimum is to rent every day. -/
lemma optCost_eq_rent (r p : ℝ) (T : ℕ) (h : (T : ℝ) * r ≤ p) :
    optCost r p T = (T : ℝ) * r := by
  rw [optCost]
  exact min_eq_left h

/-- On a trip long enough that buying costs no more than renting every day, the
offline optimum is to buy. -/
lemma optCost_eq_buy (r p : ℝ) (T : ℕ) (h : p ≤ (T : ℝ) * r) :
    optCost r p T = p := by
  rw [optCost]
  exact min_eq_right h

/-- A short trip's cost under the rent-`a`-then-buy strategy is pure renting. -/
lemma rentThenBuyCost_short (r p : ℝ) (a T : ℕ) (h : T ≤ a) :
    rentThenBuyCost r p a T = (T : ℝ) * r := by
  rw [rentThenBuyCost]
  exact if_pos h

/-- A long trip's cost under the rent-`a`-then-buy strategy is renting `a` days
and then buying. -/
lemma rentThenBuyCost_long (r p : ℝ) (a T : ℕ) (h : ¬ T ≤ a) :
    rentThenBuyCost r p a T = (a : ℝ) * r + p := by
  rw [rentThenBuyCost]
  exact if_neg h

set_option linter.unusedVariables false in
/--
**Theorem 27.1 (rent-or-buy is 2-competitive), upper bound.**  Let `r > 0` be
the daily rental cost and `p > 0` the purchase cost.  A strategy that rents for
`a` days with `a * r < p ≤ (a + 1) * r` — renting strictly less than the
break-even point, and buying no later than the day renting overtakes buying —
is `2`-competitive: whatever the number of days `T`, it pays at most twice the
optimal offline cost.  (CLRS §27.1 shows the strategy that waits `S - E` seconds
before taking the stairs is exactly this with competitive ratio `2 - E/S`.)
-/
theorem rentThenBuy_two_competitive (r p : ℝ) {a : ℕ} (hr : 0 < r) (hp : 0 < p)
    (hlt : (a : ℝ) * r < p) (hge : p ≤ ((a + 1 : ℕ) : ℝ) * r) :
    IsCompetitive r p 2 a := by
  intro T
  by_cases hT : T ≤ a
  · -- Short trip: the strategy rents every day, exactly the optimum.
    have hcost : rentThenBuyCost r p a T = (T : ℝ) * r :=
      rentThenBuyCost_short r p a T hT
    have hTle : (T : ℝ) ≤ (a : ℝ) := by exact_mod_cast hT
    have hTrp : (T : ℝ) * r ≤ p := by
      calc
        (T : ℝ) * r ≤ (a : ℝ) * r := mul_le_mul_of_nonneg_right hTle (le_of_lt hr)
        _ ≤ p := le_of_lt hlt
    have hopt : optCost r p T = (T : ℝ) * r := optCost_eq_rent r p T hTrp
    rw [hcost, hopt]
    have hnn : 0 ≤ (T : ℝ) * r := mul_nonneg (Nat.cast_nonneg T) (le_of_lt hr)
    nlinarith
  · -- Long trip: the strategy rents `a` days then buys, and the optimum buys.
    have haT : a < T := Nat.lt_of_not_ge hT
    have hcost : rentThenBuyCost r p a T = (a : ℝ) * r + p :=
      rentThenBuyCost_long r p a T hT
    have hTge : ((a + 1 : ℕ) : ℝ) ≤ (T : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt haT)
    have hTrp : p ≤ (T : ℝ) * r :=
      le_trans hge (mul_le_mul_of_nonneg_right hTge (le_of_lt hr))
    have hopt : optCost r p T = p := optCost_eq_buy r p T hTrp
    rw [hcost, hopt]
    have hle : (a : ℝ) * r ≤ p := le_of_lt hlt
    nlinarith

end SkiRental

namespace Elevator

/--
The **cost** of the online strategy that waits `w` seconds and then, if the
elevator has not arrived, takes the stairs, on the input where the elevator
arrives after `t` seconds.  If it arrives in time (`t ≤ w`) the cost is
`t + E`; otherwise the elevator is treated as having never arrived and the cost
is `w + S`.  `E` is the elevator ride time and `S` the stairs time (CLRS §27.1).
-/
def cost (E S w t : ℝ) : ℝ :=
  if t ≤ w then t + E else w + S

/--
The **optimal offline cost** when the elevator arrives after `t` seconds: take
the elevator (waiting `t` and riding `E`) or take the stairs immediately
(cost `S`), whichever is cheaper.
-/
def optCost (E S t : ℝ) : ℝ :=
  min (t + E) S

set_option linter.unusedVariables false in
/--
**Elevator corollary of Theorem 27.1.**  With elevator ride time `E ≥ 0` and
stairs time `S > 0`, the strategy that waits `S - E` seconds and then takes the
stairs is `2`-competitive: whatever the arrival time `t ≥ 0`, it pays at most
twice the optimal offline cost.
-/
theorem elevator_two_competitive (E S : ℝ) (hE : 0 ≤ E) (hS : 0 < S) :
    ∀ t : ℝ, 0 ≤ t → cost E S (S - E) t ≤ 2 * optCost E S t := by
  intro t ht0
  by_cases ht : t ≤ S - E
  · -- The elevator comes in time: the strategy is optimal.
    have hcost : cost E S (S - E) t = t + E := by
      simp [cost, ht]
    have hle : t + E ≤ S := by
      nlinarith
    have hopt : optCost E S t = t + E := by
      rw [optCost]
      exact min_eq_left hle
    rw [hcost, hopt]
    have hnn : 0 ≤ t + E := by
      nlinarith [ht0, hE]
    nlinarith
  · -- The elevator comes late (or never): the strategy takes the stairs.
    have hcost : cost E S (S - E) t = (S - E) + S := by
      simp [cost, ht]
    have hgt : S < t + E := by
      nlinarith
    have hopt : optCost E S t = S := by
      rw [optCost]
      exact min_eq_right (le_of_lt hgt)
    rw [hcost, hopt]
    nlinarith [hS, hE]

/--
**Worst-case cost ratio.**  When the elevator comes after the wait time, the
"wait `S - E` then take the stairs" strategy pays exactly `(2 - E/S) * S`, so
its competitive ratio on that input is `2 - E/S`, matching the value stated in
CLRS §27.1.  For `0 < E < S` the ratio lies strictly between 1 and 2 (the
second conjunct).
-/
lemma elevator_worst_case_ratio (E S : ℝ) (hE : 0 < E) (hS : 0 < S) :
    (S - E) + S = (2 - E / S) * S ∧ (2 - E / S) < 2 := by
  constructor
  · field_simp [ne_of_gt hS]
    ring
  · have hpos : 0 < E / S := div_pos hE hS
    linarith

end Elevator

end CLRS

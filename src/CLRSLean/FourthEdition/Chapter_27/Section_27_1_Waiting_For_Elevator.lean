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
- Definition `SkiRental.Strategy` and `SkiRental.onlineCost`: the general causal
  model of a deterministic online strategy (its first buy day, or never).
- Theorem `SkiRental.rentThenBuy_lower_bound` / `SkiRental.skiRental_lower_bound`
  (Theorem 27.1, lower bound): no deterministic strategy beats `2 - r/p`.
- Definition `Elevator.cost` and `Elevator.optCost`: the elevator instance.
- Theorem `Elevator.elevator_two_competitive`: the "wait `S - E` then take the
  stairs" strategy is `2`-competitive.
- Theorem `Elevator.elevator_lower_bound`: no deterministic wait beats `2 - E/S`.
- Lemma `Elevator.elevator_worst_case_ratio`: when the elevator comes late the
  cost is exactly `(2 - E/S) * S`, the competitive ratio stated in CLRS §27.1.

The model is deliberately thin: costs are real numbers, the input is the total
number of days `T : ℕ`, and a deterministic online strategy is its first buy day
(a "rent `a` days then buy" threshold, or `none` for "never buy"), which is the
general causal model — an online strategy decides rent-or-buy day by day without
seeing the future, and buying is irreversible.  The deterministic lower bound
`2 - r/p` (and its elevator form `2 - E/S`) is formalized as an adversarial
construction: for every strategy there is a finite input on which it pays at
least `2 - r/p` times the offline optimum.

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

/-! ## Deterministic lower bound -/

/--
A **deterministic online strategy** for ski rental is its first buy day: it
rents days `0 .. a-1` and buys on day `a` if the trip lasts that long, or
`none` if it never buys.  This is the general causal model — an online strategy
must decide rent-or-buy day by day without seeing the future, and buying is
irreversible, so the whole strategy is determined by this one threshold.
-/
abbrev Strategy := Option ℕ

/--
The **cost** of running a deterministic strategy `s` on a trip of `T` days: the
threshold strategy rents then buys, and the never-buy strategy rents every day.
-/
def onlineCost (r p : ℝ) (s : Strategy) (T : ℕ) : ℝ :=
  match s with
  | none => (T : ℝ) * r
  | some a => rentThenBuyCost r p a T

/--
**Theorem 27.1 (deterministic lower bound), threshold form.**  For `r > 0` and
`p > 0`, no rent-`a`-then-buy threshold strategy beats competitive ratio
`2 - r/p`: for every `a` there is an input `T` on which it pays at least
`(2 - r/p)` times the optimal offline cost.
-/
theorem rentThenBuy_lower_bound (r p : ℝ) (hr : 0 < r) (hp : 0 < p) (a : ℕ) :
    ∃ T : ℕ, (2 - r / p) * optCost r p T ≤ rentThenBuyCost r p a T := by
  refine ⟨a + 1, ?_⟩
  have ha0 : 0 ≤ (a : ℝ) := Nat.cast_nonneg a
  have hcost : rentThenBuyCost r p a (a + 1) = (a : ℝ) * r + p := by
    apply rentThenBuyCost_long
    intro h
    omega
  rw [hcost]
  have hcast : ((a + 1 : ℕ) : ℝ) = (a : ℝ) + 1 := by norm_num
  by_cases hle : ((a + 1 : ℕ) : ℝ) * r ≤ p
  · -- Buy early: the optimum is to rent every day; the strategy buys too soon.
    have hopt : optCost r p (a + 1) = ((a + 1 : ℕ) : ℝ) * r := optCost_eq_rent r p (a + 1 : ℕ) hle
    rw [hopt]
    rw [hcast]
    have hrp : r ≤ p := by
      have h1 : r ≤ ((a : ℝ) + 1) * r := by nlinarith [ha0]
      exact le_trans h1 (by rw [← hcast]; exact hle)
    have hprod : 0 ≤ (p - r) * (p - ((a : ℝ) + 1) * r) := by
      exact mul_nonneg (sub_nonneg.mpr hrp) (sub_nonneg.mpr (by rw [← hcast]; exact hle))
    have hid : p * ((a : ℝ) * r + p - (2 - r / p) * ((a : ℝ) + 1) * r) =
        (p - r) * (p - ((a : ℝ) + 1) * r) := by
      field_simp [ne_of_gt hp]
      ring
    have hnn : 0 ≤ p * ((a : ℝ) * r + p - (2 - r / p) * ((a : ℝ) + 1) * r) := by
      rw [hid]
      exact hprod
    nlinarith
  · -- Buy at or after break-even: the optimum is to buy; the strategy rents first.
    have hopt : optCost r p (a + 1) = p := optCost_eq_buy r p (a + 1 : ℕ) (le_of_not_ge hle)
    rw [hopt]
    have hge : p ≤ ((a : ℝ) + 1) * r := by rw [← hcast]; exact le_of_not_ge hle
    field_simp [ne_of_gt hp]
    nlinarith [hr, hp, hge, ha0]

/--
**Theorem 27.1 (deterministic lower bound).**  For `r > 0` and `p > 0`, no
deterministic online strategy beats competitive ratio `2 - r/p`: for every
strategy there is an input `T` on which it pays at least `(2 - r/p)` times the
optimal offline cost.
-/
theorem skiRental_lower_bound (r p : ℝ) (hr : 0 < r) (hp : 0 < p) (s : Strategy) :
    ∃ T : ℕ, (2 - r / p) * optCost r p T ≤ onlineCost r p s T := by
  cases s with
  | none =>
      -- The strategy never buys, so on a long trip it pays `T * r` while the
      -- optimum is `p`; pick `T` large enough that `2 * p - r ≤ T * r`.
      obtain ⟨T, hT⟩ := exists_nat_gt (2 * p / r : ℝ)
      refine ⟨T, ?_⟩
      simp [onlineCost]
      have hmul : (2 * p / r) * r < (T : ℝ) * r := mul_lt_mul_of_pos_right hT hr
      have h2p : (2 * p / r) * r = 2 * p := by field_simp [ne_of_gt hr]
      have hTr : 2 * p - r ≤ (T : ℝ) * r := by nlinarith
      have hp_opt : p ≤ (T : ℝ) * r := by nlinarith
      have hopt : optCost r p T = p := optCost_eq_buy r p T hp_opt
      rw [hopt]
      have hgoal : (2 - r / p) * p = 2 * p - r := by field_simp [ne_of_gt hp]
      rw [hgoal]
      exact hTr
  | some a =>
      simp [onlineCost]
      exact rentThenBuy_lower_bound r p hr hp a

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

/--
**Elevator lower bound (corollary of the deterministic bound).**  For
`0 < E < S`, no deterministic wait threshold `w` beats competitive ratio
`2 - E/S`: for every `w ≥ 0` there is an arrival time `t ≥ 0` on which the
strategy pays at least `(2 - E/S)` times the optimal offline cost.  Combined
with `elevator_two_competitive`, the "wait `S - E` then stairs" strategy is
exactly optimal.
-/
theorem elevator_lower_bound (E S : ℝ) (hE : 0 < E) (hS : 0 < S) (hES : E < S)
    (w : ℝ) (hw0 : 0 ≤ w) :
    ∃ t : ℝ, 0 ≤ t ∧ (2 - E / S) * optCost E S t ≤ cost E S w t := by
  have hdiv : E / S < 1 := (div_lt_one hS).mpr hES
  have hden : 0 < 2 - E / S := by nlinarith
  have hden2 : 2 - E / S ≠ 0 := ne_of_gt hden
  have hpos : 0 < S * 2 - E := by nlinarith [hES, hS]
  have hpos2 : S * 2 - E ≠ 0 := ne_of_gt hpos
  by_cases hw : w < S - E
  · -- Too eager: the elevator arrives exactly at the adversarial boundary.
    let t : ℝ := (w + S) / (2 - E / S) - E
    refine ⟨t, ?_, ?_⟩
    · dsimp [t]
      field_simp [hden2, hpos2, ne_of_gt hS]
      nlinarith [hE, hS, hw0, sq_nonneg (S - E)]
    · have hgt : w < t := by
        dsimp [t]
        field_simp [hden2, hpos2, ne_of_gt hS]
        nlinarith [hw, hES, hS]
      have hcost : cost E S w t = w + S := by
        rw [cost, if_neg (show ¬ t ≤ w by intro htle; nlinarith [hgt])]
      rw [hcost]
      have hleS : t + E ≤ S := by
        dsimp [t]
        field_simp [hden2, hpos2, ne_of_gt hS]
        nlinarith [hw, hES, hS]
      have hopt : optCost E S t = t + E := by
        rw [optCost]
        exact min_eq_left hleS
      rw [hopt]
      have hmain : (2 - E / S) * (t + E) = w + S := by
        dsimp [t]
        rw [sub_add_cancel]
        exact mul_div_cancel₀ (w + S) hden2
      rw [hmain]
  · -- Patient enough: the elevator arrives after the wait is abandoned.
    refine ⟨w + 1, ?_, ?_⟩
    · nlinarith [hw0]
    · have hle : S - E ≤ w := le_of_not_gt hw
      have hcost : cost E S w (w + 1) = w + S := by
        rw [cost, if_neg (show ¬ w + 1 ≤ w by nlinarith)]
      rw [hcost]
      have hopt : optCost E S (w + 1) = S := by
        rw [optCost]
        apply min_eq_right
        nlinarith [hle]
      rw [hopt]
      have hmain : (2 - E / S) * S = 2 * S - E := by
        field_simp [ne_of_gt hS]
      rw [hmain]
      exact (by nlinarith [hle] : 2 * S - E ≤ w + S)

end Elevator

end CLRS

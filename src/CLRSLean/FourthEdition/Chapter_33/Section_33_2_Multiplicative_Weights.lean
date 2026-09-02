import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-!
# 33.2 Multiplicative-Weights Algorithms

This section formalizes the **multiplicative weights (MW) update method** from
CLRS §33.2.  The setting has `n` experts.  Over `T` days, each expert `i`
incurs a loss `m t i ∈ [0, 1]` on day `t`, and the algorithm maintains a weight
`w i` for each expert, initially `1`.  On each day it incurs the *expected*
loss `Σᵢ (w i / Φ) · m t i` under the normalized distribution `w i / Φ`, where
`Φ = Σᵢ w i` is the **potential**; it then multiplies expert `i`'s weight by
`(1 - η)^(m t i)` for a learning rate `η ∈ (0, 1/2]`.

Main results:

- Definition `weights`: the weight of each expert after any number of days.
- Definition `potential`: the sum of the weights (`Φ`).
- Definition `expectedLoss` / `totalExpectedLoss`: the algorithm's daily and
  total expected loss.
- Definition `expertLoss`: the total loss of a single expert.
- Theorem `potential_update_le_exp`: one MW update shrinks the potential:
  `Φ' ≤ Φ · exp(-η · M)` where `M` is the day's expected loss.
- Theorem `totalExpectedLoss_le`: the total expected loss of the algorithm is
  within an additive `ln n / η` and a multiplicative `(1 + η)` factor of the
  best expert's loss — for every expert `i`,
  `Σₜ Mᵗ ≤ (1 + η) · Σₜ m t i + ln n / η`.

The proof follows CLRS §33.2: three analytic inequalities — `(1-x)^y ≤ 1 - x·y`
(convexity of the exponential), `1 - x ≤ e^(-x)`, and `-ln (1 - x) ≤ x + x²`
for `0 ≤ x ≤ 1/2` — feed the potential chain `Φ^{t+1} ≤ Φᵗ·e^(-η·Mᵗ)`, which is
sandwiched between the weight of the best expert, `(1-η)^L`, and the initial
potential `n`, and the resulting logarithmic inequality is rearranged.

Notation conventions used in this section:

- `n` : the number of experts
- `T` : the number of days
- `η` : the learning rate (`0 < η ≤ 1/2`)
- `m t i` : the loss of expert `i` on day `t` (`∈ [0, 1]`)
- `w` : a weight vector (`Fin n → ℝ`)
- `Φ` : the potential, the sum of the weights
- `Mᵗ` : the algorithm's expected loss on day `t`
-/

noncomputable section

open scoped BigOperators

namespace CLRS

namespace MultiplicativeWeights

variable {n : ℕ}

/--
The **initial weight vector**: every expert starts with weight `1` (CLRS §33.2).
-/
def initialWeights (n : ℕ) : Fin n → ℝ := fun _ => 1

/--
The **potential** `Φ(w)` of a weight vector `w`: the sum of all expert weights
(CLRS §33.2).
-/
def potential {n : ℕ} (w : Fin n → ℝ) : ℝ := ∑ i : Fin n, w i

/--
The potential of the initial weight vector is the number of experts `n`.
-/
lemma potential_initialWeights (n : ℕ) : potential (initialWeights n) = n := by
  simp [potential, initialWeights, Finset.sum_const, Finset.card_univ]

/--
One **multiplicative-weights update**: expert `i`'s weight is multiplied by
`(1 - η) ^ (l i)`, where `l i ∈ [0, 1]` is expert `i`'s loss on the current day
(CLRS §33.2).
-/
def updateWeight (η : ℝ) {n : ℕ} (w : Fin n → ℝ) (l : Fin n → ℝ) : Fin n → ℝ :=
  fun i => w i * (1 - η) ^ l i

/--
The losses of the `n` experts on day `t`, totalized to every natural index:
for days `t ≥ T` the zero loss vector is returned (a junk value that the
lemmas only ever use inside `Finset.range T`).
-/
def dayLoss {T n : ℕ} (m : Fin T → Fin n → ℝ) (t : ℕ) : Fin n → ℝ :=
  if h : t < T then m ⟨t, h⟩ else fun _ => 0

/--
The weight vector after `t` days of updates (meaningful for `t ≤ T`): the
result of applying the update rule for days `0, ..., t - 1` to
`initialWeights n`.
-/
def weights {T n : ℕ} (η : ℝ) (m : Fin T → Fin n → ℝ) : ℕ → Fin n → ℝ
  | 0 => initialWeights n
  | t + 1 => updateWeight η (weights η m t) (dayLoss m t)

/--
The **expected loss** of the algorithm on a day with current weight vector `w`
and losses `l`: `Σᵢ (w i / Φ(w)) · l i`, the average loss under the
weight-normalized distribution (CLRS §33.2).
-/
def expectedLossAt {n : ℕ} (w : Fin n → ℝ) (l : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, (w i / potential w) * l i

/--
The algorithm's expected loss on day `t` (with `t < T` the loss is
`m t i`; for `t ≥ T` the totalized loss vector is zero).
-/
def expectedLoss {T n : ℕ} (η : ℝ) (m : Fin T → Fin n → ℝ) (t : ℕ) : ℝ :=
  expectedLossAt (weights η m t) (dayLoss m t)

/--
The algorithm's **total expected loss** over days `0, ..., T - 1`.
-/
def totalExpectedLoss {T n : ℕ} (η : ℝ) (m : Fin T → Fin n → ℝ) : ℝ :=
  ∑ t ∈ Finset.range T, expectedLoss η m t

/--
The **total loss** of expert `i` over days `0, ..., T - 1`.
-/
def expertLoss {T n : ℕ} (m : Fin T → Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ t ∈ Finset.range T, dayLoss m t i

/--
The day-`t` loss of every expert lies in `[0, 1]` for every totalized index.
-/
lemma dayLoss_mem_Icc {T n : ℕ} {m : Fin T → Fin n → ℝ}
    (hm : ∀ t j, m t j ∈ Set.Icc (0 : ℝ) 1) (t : ℕ) :
    ∀ i, dayLoss m t i ∈ Set.Icc (0 : ℝ) 1 := by
  intro i
  by_cases ht : t < T
  · simpa [dayLoss, ht] using hm ⟨t, ht⟩ i
  · simp [dayLoss, ht]

/--
For `0 ≤ x < 1` and `0 ≤ y ≤ 1`, `(1 - x) ^ y ≤ 1 - x·y`.  This is the fact
that the exponential function is convex, applied between the points `0` and
`log (1 - x)` with weights `1 - y` and `y`.
-/
lemma one_sub_rpow_le_one_sub_mul {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (1 - x) ^ y ≤ 1 - x * y := by
  calc
    (1 - x) ^ y = Real.exp (Real.log (1 - x) * y) := by
      exact Real.rpow_def_of_pos (by linarith : 0 < 1 - x) y
    _ = Real.exp (y * Real.log (1 - x)) := by rw [mul_comm]
    _ ≤ (1 - y) * Real.exp 0 + y * Real.exp (Real.log (1 - x)) := by
      have hc0 : Real.exp (y * Real.log (1 - x)) ≤
          (1 - y) * Real.exp 0 + y * Real.exp (Real.log (1 - x)) := by
        simpa [smul_eq_mul, zero_mul, add_zero] using
          (convexOn_exp.2 (by simp : (0 : ℝ) ∈ Set.univ)
            (by simp : Real.log (1 - x) ∈ Set.univ)
            (show 0 ≤ 1 - y by linarith) (by exact hy0) (by ring))
      exact hc0
    _ = (1 - y) * 1 + y * (1 - x) := by
      rw [Real.exp_zero, Real.exp_log (by linarith : 0 < 1 - x)]
    _ = 1 - x * y := by ring

/--
For `0 ≤ x ≤ 1/2`, `-ln (1 - x) ≤ x + x²`.  This is the logarithmic
approximation used to pass from the factor `-ln (1 - η)/η` to the clean
`1 + η` in the regret bound.
-/
lemma neg_log_one_sub_le_add_sq {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    -Real.log (1 - x) ≤ x + x ^ 2 := by
  let f : ℝ → ℝ := fun t => t + t ^ 2 + Real.log (1 - t)
  have hd : ∀ t : ℝ, t < 1 → HasDerivAt f (1 + 2 * t - (1 - t)⁻¹) t := by
    intro t ht
    have hid : HasDerivAt (fun u : ℝ => u) 1 t := hasDerivAt_id t
    have hsq : HasDerivAt (fun u : ℝ => u ^ 2) (2 * t) t := by
      simpa using (hasDerivAt_pow 2 t)
    have hlog : HasDerivAt (fun u : ℝ => Real.log (1 - u)) (-(1 - t)⁻¹) t := by
      have hsub : HasDerivAt (fun u : ℝ => (1 : ℝ) - u) (-1) t := by
        convert ((hasDerivAt_const t (1 : ℝ)).sub hid) using 1
        · rfl
        · rfl
        · rfl
        · norm_num
      have hlog1 : HasDerivAt Real.log ((1 - t)⁻¹) (1 - t) := by
        exact Real.hasDerivAt_log (by linarith : (1 - t) ≠ 0)
      convert (hlog1.comp t hsub) using 1
      · rfl
      · rfl
      · rfl
      · ring
    have hsum : HasDerivAt (fun u : ℝ => u + u ^ 2 + Real.log (1 - u))
        (1 + 2 * t - (1 - t)⁻¹) t := by
      convert ((hid.add hsq).add hlog) using 1
      · rfl
      · rfl
      · rfl
      · ring
    simpa [f] using hsum
  have hmono : MonotoneOn f (Set.Icc 0 (1 / 2)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 / 2)) ?_ ?_ ?_
    · have hc_poly : ContinuousOn (fun t : ℝ => t + t ^ 2) (Set.Icc 0 (1 / 2)) := by
        exact continuousOn_id.add (continuousOn_id.pow 2)
      have hc_log : ContinuousOn (fun t : ℝ => Real.log (1 - t)) (Set.Icc 0 (1 / 2)) := by
        refine ContinuousOn.log ?_ ?_
        · exact continuousOn_const.sub continuousOn_id
        · intro t ht
          exact ne_of_gt (by linarith [ht.2])
      have hc_sum : ContinuousOn (fun t : ℝ => (t + t ^ 2) + Real.log (1 - t))
          (Set.Icc 0 (1 / 2)) := by
        exact (hc_poly.add hc_log)
      simpa [f] using hc_sum
    · rw [interior_Icc]
      intro t ht
      exact (hd t (by linarith [ht.2])).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      have hd_t : HasDerivAt f (1 + 2 * t - (1 - t)⁻¹) t := hd t (by linarith [ht.2])
      rw [hd_t.deriv]
      have hden : 0 < 1 - t := by linarith [ht.2]
      have hnum : 0 ≤ t * (1 - 2 * t) := by
        have ht0 : 0 < t := ht.1
        have ht1 : 0 < 1 - 2 * t := by linarith [ht.2]
        positivity
      field_simp [hden.ne']
      nlinarith [hnum]
  have hmem0 : (0 : ℝ) ∈ Set.Icc 0 (1 / 2) := by norm_num
  have hmemx : x ∈ Set.Icc 0 (1 / 2) := by exact ⟨hx0, hx⟩
  have hle : f 0 ≤ f x := hmono hmem0 hmemx hx0
  have hf0 : f 0 = 0 := by simp [f]
  have hfx : f x = x + x ^ 2 + Real.log (1 - x) := by simp [f]
  nlinarith [hle, hf0, hfx]

/--
Every weight is strictly positive: weights only ever get multiplied by powers
of `1 - η > 0`.
-/
lemma weights_pos {T n : ℕ} {η : ℝ} {m : Fin T → Fin n → ℝ} (hη1 : η < 1) :
    ∀ t i, 0 < weights η m t i := by
  intro t i
  induction t with
  | zero => simp [weights, initialWeights]
  | succ t ih =>
      have hw : 0 < weights η m t i := ih
      have hp : 0 < (1 - η) ^ dayLoss m t i :=
        Real.rpow_pos_of_pos (by linarith : 0 < 1 - η) (dayLoss m t i)
      simpa [weights, updateWeight] using mul_pos hw hp

/--
The potential at any time is positive: it is a sum of strictly positive
weights, of which there is at least one when `n > 0`.
-/
lemma potential_weights_pos {T n : ℕ} {η : ℝ} {m : Fin T → Fin n → ℝ}
    (hn : 0 < n) (hη1 : η < 1) (t : ℕ) : 0 < potential (weights η m t) := by
  have h0 : 0 < weights η m t ⟨0, hn⟩ := weights_pos hη1 t ⟨0, hn⟩
  have hs : weights η m t ⟨0, hn⟩ ≤ potential (weights η m t) :=
    Finset.single_le_sum (fun i hi => le_of_lt (weights_pos hη1 t i)) (by simp)
  exact lt_of_lt_of_le h0 hs

/--
`Σᵢ w i · l i = Φ · M`, where `M` is the expected loss at `w, l`: the unweighted
sum of weighted losses equals the potential times the expected loss.
-/
lemma sum_weight_mul_loss_eq {n : ℕ} {w : Fin n → ℝ} {l : Fin n → ℝ}
    (hpw : 0 < potential w) :
    (∑ i : Fin n, w i * l i) = potential w * expectedLossAt w l := by
  calc
    (∑ i : Fin n, w i * l i)
        = ∑ i : Fin n, potential w * ((w i / potential w) * l i) := by
            apply Finset.sum_congr rfl
            intro i hi
            field_simp [ne_of_gt hpw]
    _ = potential w * (∑ i : Fin n, (w i / potential w) * l i) := by
            rw [← Finset.mul_sum]
    _ = potential w * expectedLossAt w l := by rfl

/--
**Per-round potential bound.**  One MW update shrinks the potential by at least
the weighted loss: `Φ(w') ≤ Φ(w) - η · Σᵢ w i · l i`, using the pointwise
inequality `(1 - η)^(l i) ≤ 1 - η·(l i)`.
-/
lemma potential_update_le {n : ℕ} {η : ℝ} {w : Fin n → ℝ} {l : Fin n → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hη0 : 0 ≤ η) (hη1 : η < 1) (hl : ∀ i, l i ∈ Set.Icc (0 : ℝ) 1) :
    potential (updateWeight η w l) ≤ potential w - η * (∑ i : Fin n, w i * l i) := by
  unfold potential updateWeight
  calc
    (∑ i : Fin n, w i * (1 - η) ^ l i) ≤ ∑ i : Fin n, (w i - η * (w i * l i)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hterm : (1 - η) ^ l i ≤ 1 - η * l i := by
        exact one_sub_rpow_le_one_sub_mul hη0 hη1 (hl i).1 (hl i).2
      calc
        w i * (1 - η) ^ l i ≤ w i * (1 - η * l i) := by
          exact mul_le_mul_of_nonneg_left hterm (hw i)
        _ = w i - η * (w i * l i) := by ring
    _ = (∑ i : Fin n, w i) - η * (∑ i : Fin n, w i * l i) := by
      rw [Finset.sum_sub_distrib]
      rw [← Finset.mul_sum]
    _ = potential w - η * (∑ i : Fin n, w i * l i) := by rfl

/--
**Exponential potential bound.**  One MW update shrinks the potential
multiplicatively: `Φ(w') ≤ Φ(w) · exp (-η · M)`, where `M` is the day's
expected loss.  This chains the algebraic per-round bound with `1 - x ≤ e^(-x)`.
-/
lemma potential_update_le_exp {n : ℕ} {η : ℝ} {w : Fin n → ℝ} {l : Fin n → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hpw : 0 < potential w) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hl : ∀ i, l i ∈ Set.Icc (0 : ℝ) 1) :
    potential (updateWeight η w l) ≤ potential w * Real.exp (-η * expectedLossAt w l) := by
  calc
    potential (updateWeight η w l) ≤ potential w - η * (∑ i : Fin n, w i * l i) :=
      potential_update_le hw hη0 hη1 hl
    _ = potential w * (1 - η * expectedLossAt w l) := by
      rw [sum_weight_mul_loss_eq hpw]
      ring
    _ ≤ potential w * Real.exp (-η * expectedLossAt w l) := by
      simpa using
        (mul_le_mul_of_nonneg_left (Real.one_sub_le_exp_neg (η * expectedLossAt w l))
          (le_of_lt hpw))

/--
**Potential chain.**  After `t ≤ T` days, the potential is at most
`n · exp (-η · Σ_{s < t} Mˢ)`: the initial potential `n` decays by a factor
`e^(-η·Mˢ)` on every day.  This is the induction that iterates
`potential_update_le_exp` over the days.
-/
lemma potential_weights_le {T n : ℕ} {η : ℝ} {m : Fin T → Fin n → ℝ}
    (hn : 0 < n) (hη0 : 0 ≤ η) (hη1 : η < 1) (hm : ∀ t j, m t j ∈ Set.Icc (0 : ℝ) 1) :
    ∀ t : ℕ, t ≤ T →
      potential (weights η m t) ≤
        n * Real.exp (-η * ∑ s ∈ Finset.range t, expectedLoss η m s) := by
  intro t
  induction t with
  | zero =>
      intro _ht0
      calc
        potential (weights η m 0) = n := by
          simp [weights, potential_initialWeights]
        _ ≤ n * Real.exp (-η * (∑ s ∈ Finset.range 0, expectedLoss η m s)) := by
          simp [Finset.sum_range_zero]
  | succ t ih =>
      intro hts
      have htT : t < T := Nat.lt_of_succ_le hts
      have ht_le : t ≤ T := le_of_lt htT
      have ih_t := ih ht_le
      have hup : potential (updateWeight η (weights η m t) (dayLoss m t)) ≤
          potential (weights η m t) *
            Real.exp (-η * expectedLossAt (weights η m t) (dayLoss m t)) := by
        exact potential_update_le_exp
          (fun i => le_of_lt (weights_pos hη1 t i))
          (potential_weights_pos hn hη1 t)
          hη0 hη1
          (dayLoss_mem_Icc hm t)
      have h1 : potential (weights η m (t + 1)) ≤
          potential (weights η m t) * Real.exp (-η * expectedLoss η m t) := by
        simpa [weights, expectedLoss] using hup
      have h3 : potential (weights η m t) * Real.exp (-η * expectedLoss η m t) ≤
          n * Real.exp (-η * (∑ s ∈ Finset.range (t + 1), expectedLoss η m s)) := by
        calc
          potential (weights η m t) * Real.exp (-η * expectedLoss η m t)
              ≤ (n * Real.exp (-η * (∑ s ∈ Finset.range t, expectedLoss η m s))) *
                  Real.exp (-η * expectedLoss η m t) := by
                  exact mul_le_mul_of_nonneg_right ih_t (Real.exp_pos _).le
          _ = n * (Real.exp (-η * (∑ s ∈ Finset.range t, expectedLoss η m s)) *
              Real.exp (-η * expectedLoss η m t)) := by ring
          _ = n * Real.exp ((-η * (∑ s ∈ Finset.range t, expectedLoss η m s)) +
              (-η) * expectedLoss η m t) := by
                  rw [← Real.exp_add]
          _ = n * Real.exp (-η * (∑ s ∈ Finset.range (t + 1), expectedLoss η m s)) := by
                  congr 1
                  congr 1
                  rw [Finset.sum_range_succ]
                  ring
      exact le_trans h1 h3

/--
The weight of expert `i` after `T` days is `(1 - η) ^ (expertLoss m i)`: each
day multiplies the weight by `(1 - η)^(m t i)`, so the accumulated weight is
`(1 - η)` raised to the expert's total loss.
-/
lemma weights_eq_rpow_expertLoss {T n : ℕ} {η : ℝ} {m : Fin T → Fin n → ℝ}
    (hη1 : η < 1) (i : Fin n) :
    weights η m T i = (1 - η) ^ expertLoss m i := by
  have hbase : 0 < 1 - η := by linarith
  have aux : ∀ t : ℕ, weights η m t i = ∏ s ∈ Finset.range t, (1 - η) ^ dayLoss m s i := by
    intro t
    induction t with
    | zero => simp [weights, initialWeights]
    | succ t ih =>
        rw [weights]
        rw [updateWeight]
        rw [ih]
        rw [Finset.prod_range_succ]
  calc
    weights η m T i = ∏ s ∈ Finset.range T, (1 - η) ^ dayLoss m s i := aux T
    _ = (1 - η) ^ (∑ s ∈ Finset.range T, dayLoss m s i) := by
      rw [← Real.rpow_sum_of_pos hbase]
    _ = (1 - η) ^ expertLoss m i := by
      simp [expertLoss]

/--
The total loss of every expert is nonnegative, since every daily loss lies in
`[0, 1]`.
-/
lemma expertLoss_nonneg {T n : ℕ} {m : Fin T → Fin n → ℝ}
    (hm : ∀ t j, m t j ∈ Set.Icc (0 : ℝ) 1) (i : Fin n) : 0 ≤ expertLoss m i := by
  unfold expertLoss
  exact Finset.sum_nonneg (fun t ht => (dayLoss_mem_Icc hm t i).1)

/--
**Regret bound (Theorem 33.3).**  For every expert `i`, the total expected loss
of the multiplicative-weights algorithm is within an additive `ln n / η` and a
multiplicative `(1 + η)` factor of expert `i`'s total loss:

`Σₜ Mᵗ ≤ (1 + η) · Σₜ m t i + ln n / η`.

The proof sandwiches the final potential between the best expert's remaining
weight, `(1 - η)^L`, and the decayed initial potential, `n·e^(-η·E)`, takes
logarithms, and uses `-ln (1 - η) ≤ η + η²`.
-/
theorem totalExpectedLoss_le {T n : ℕ} {η : ℝ} {m : Fin T → Fin n → ℝ} {i : Fin n}
    (hn : 0 < n) (hη0 : 0 < η) (hη1 : η ≤ 1 / 2) (hm : ∀ t j, m t j ∈ Set.Icc (0 : ℝ) 1) :
    totalExpectedLoss η m ≤ (1 + η) * expertLoss m i + Real.log n / η := by
  let E := totalExpectedLoss η m
  let L := expertLoss m i
  have hη0' : 0 ≤ η := le_of_lt hη0
  have hη1' : η < 1 := by linarith
  have hbase : 0 < 1 - η := by linarith
  have hub : potential (weights η m T) ≤ n * Real.exp (-η * E) := by
    have hpb := potential_weights_le hn hη0' hη1' hm T (le_rfl)
    simpa [E, totalExpectedLoss] using hpb
  have hlb : (1 - η) ^ L ≤ potential (weights η m T) := by
    have hprod : (1 - η) ^ L = weights η m T i := (weights_eq_rpow_expertLoss hη1' i).symm
    have hpot_ge : weights η m T i ≤ potential (weights η m T) :=
      Finset.single_le_sum (fun j hj => le_of_lt (weights_pos hη1' T j)) (by simp)
    rw [hprod]
    exact hpot_ge
  have htot : (1 - η) ^ L ≤ n * Real.exp (-η * E) := le_trans hlb hub
  have hE : L * Real.log (1 - η) ≤ Real.log n - η * E := by
    have hle := (Real.rpow_le_iff_le_log hbase
      (by positivity : 0 < (n : ℝ) * Real.exp (-η * E))).mp htot
    rw [Real.log_mul (by exact_mod_cast hn.ne') (Real.exp_pos (-η * E)).ne',
      Real.log_exp] at hle
    simpa [sub_eq_add_neg] using hle
  have hlog2 : η * E ≤ Real.log n + L * (-Real.log (1 - η)) := by
    nlinarith [hE]
  have hdiv : E ≤ (Real.log n + L * (-Real.log (1 - η))) / η := by
    rw [le_div_iff₀ hη0]
    nlinarith [hlog2]
  have hlg : -Real.log (1 - η) ≤ η + η ^ 2 := neg_log_one_sub_le_add_sq hη0' hη1
  have hLge : 0 ≤ L := expertLoss_nonneg hm i
  have hbound : (Real.log n + L * (-Real.log (1 - η))) / η ≤
      (Real.log n + L * (η + η ^ 2)) / η := by
    gcongr
  have hsplit : (Real.log n + L * (η + η ^ 2)) / η = Real.log n / η + L * (1 + η) := by
    field_simp [ne_of_gt hη0]
  have hfinal : E ≤ Real.log n / η + L * (1 + η) := by
    calc
      E ≤ (Real.log n + L * (-Real.log (1 - η))) / η := hdiv
      _ ≤ (Real.log n + L * (η + η ^ 2)) / η := hbound
      _ = Real.log n / η + L * (1 + η) := hsplit
  have hgoal : E ≤ (1 + η) * L + Real.log n / η := by
    nlinarith [hfinal]
  simpa [E, L] using hgoal

end MultiplicativeWeights

end CLRS

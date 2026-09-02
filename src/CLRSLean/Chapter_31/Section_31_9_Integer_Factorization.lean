import Mathlib
import CLRSLean.Chapter_31.Section_31_2_Greatest_Common_Divisor
import CLRSLean.Probability.FiniteExpectation

/-!
# 31.9 Integer Factorization

CLRS §31.9: **Pollard's rho** heuristic for factoring a composite integer.
The iteration `x ↦ (x² + c) mod n` eventually produces two values congruent
modulo a prime factor `p` of `n`; then `gcd(x − y, n)` is a nontrivial
divisor of `n`.

Main results:

- {lit}`rhoStep` (CLRS Pollard's rho iteration): `x ↦ (x² + c) mod n`.
- Theorem {lit}`rho_collision_factor`: if `x ≡ y (mod p)` and `p ∣ n`, then
  `p ∣ gcd(x − y, n)` — a mod-`p` collision forces the gcd to be a nontrivial
  divisor (`> 1`; when it is also `< n`, it is a proper factor).
  {lit}`rho_collision_factor_dist` is the version using `|y − x|`
  (`Nat.dist`), matching POLLARD-RHO.
- **POLLARD-RHO**: {lit}`RhoState` is the tortoise-and-hare state;
  {lit}`pollardStep` advances one step and reports
  `gcd (|y − x|, n)`; {lit}`pollardRhoLoop` runs the loop over a step budget;
  and {lit}`pollardRho` is the full algorithm.  **Soundness**:
  {lit}`pollardRho_sound` — whenever the returned value is not `n`, it is a
  nontrivial divisor of `n`.  {lit}`pollardStep_collision_factor` shows a
  mod-`p` collision at a step makes that step's candidate a multiple of `p`.
- **Probabilistic analysis (CLRS Theorem 31.40)**: CLRS models the rho orbit,
  read mod `p`, as independent uniform draws from `Z_p`.  That heuristic is
  made into an explicit model — the sample space `Fin k → Fin p` of `k`
  independent uniform draws — and the birthday-paradox bound is proved
  rigorously inside it: {lit}`noCollision_prob_eq`
  (`P[no collision] = descFactorial p k / p^k`),
  {lit}`birthday_noCollision_le` (`≤ exp(−k(k−1)/(2p))`),
  {lit}`birthday_collision_ge`, and {lit}`birthday_collision_prob_ge_half`
  (collision with probability `≥ 1/2` once `2p ≤ k(k−1)`).
- **Expected `O(√p)` running time**: an independent-rounds model (blocks of `k`
  draws) with the geometric tail-sum argument gives
  {lit}`rho_expected_rounds_le_two` and {lit}`rho_expected_draws_le`
  (expected draws `≤ 2k` for `2p ≤ k(k−1)`, i.e. `O(√p)`).
- **Detection, bound to the real construction** (unconditional):
  {lit}`RhoState_valid` (the `x < n ∧ y < n` invariant), preserved by
  {lit}`pollardStep_valid`; {lit}`pollardStep_detects` and
  {lit}`pollardRhoLoop_terminates_on_collision` show a mod-`p` collision of a
  fresh value with the snapshot forces the loop to return a nontrivial divisor.

Notation:

- {lit}`a ≡ b [MOD p]` : `Nat.ModEq`.
- {lit}`Nat.gcd a n` : the greatest common divisor.
- `Fin k → Fin p` : the i.i.d.-uniform model of the first `k` orbit values mod
  `p` (the CLRS "rho heuristic" made precise).
-/

namespace CLRS

namespace Chapter31

/--
**Pollard's rho iteration (CLRS §31.9).**  The map `x ↦ (x² + c) mod n`
whose orbit is a pseudorandom walk; two of its values colliding modulo a
prime factor `p` expose `p`.
-/
def rhoStep (c n x : ℕ) : ℕ :=
  (x * x + c) % n

/--
**Pollard's rho collision factor.**  If `x` and `y` are two rho values that
are congruent modulo a divisor `p` of `n` (in practice a prime factor), then
`p` divides `gcd(x − y, n)`, so the gcd is a nontrivial divisor of `n`.
-/
theorem rho_collision_factor {p x y n : ℕ} (hpn : p ∣ n) (hxy : x ≡ y [MOD p]) :
    p ∣ Nat.gcd (x - y) n := by
  have hdvd_xy : p ∣ x - y := by
    by_cases hyx : y ≤ x
    · have hmod : (x - y) % p = 0 := by
        have hsub := Nat.ModEq.sub (c := y) (d := y) hyx (Nat.le_refl y) hxy (Nat.ModEq.refl y)
        have hyy : y - y = 0 := by omega
        rw [hyy] at hsub
        simpa [Nat.ModEq, Nat.zero_mod] using hsub
      exact Nat.dvd_of_mod_eq_zero hmod
    · have h0 : x - y = 0 := by omega
      rw [h0]
      exact Nat.dvd_zero p
  exact Nat.dvd_gcd hdvd_xy hpn

/--
**A nontrivial divisor is a proper factor.**  If `1 < gcd(a, n)` and
`gcd(a, n) < n`, then `gcd(a, n)` divides `n` and is neither `1` nor `n`.
-/
theorem nontrivial_factor_of_gcd {a n : ℕ} (hgt : 1 < Nat.gcd a n) (hlt : Nat.gcd a n < n) :
    Nat.gcd a n ∣ n ∧ 1 < Nat.gcd a n ∧ Nat.gcd a n < n :=
  ⟨Nat.gcd_dvd_right a n, hgt, hlt⟩

/-- The `x − y` version of `rho_collision_factor`, using the absolute distance
`Nat.dist x y` (matching the `GCD(|y − x|, n)` in POLLARD-RHO). -/
theorem rho_collision_factor_dist {p x y n : ℕ} (hpn : p ∣ n) (hxy : x ≡ y [MOD p]) :
    p ∣ Nat.gcd (Nat.dist x y) n := by
  by_cases hyx : y ≤ x
  · rw [Nat.dist_comm]
    rw [Nat.dist_eq_sub_of_le hyx]
    exact rho_collision_factor hpn hxy
  · have hxy_lt : x ≤ y := le_of_not_ge hyx
    rw [Nat.dist_eq_sub_of_le hxy_lt]
    exact rho_collision_factor hpn hxy.symm

/-- The state of the tortoise-and-hare iteration in POLLARD-RHO (CLRS §31.9):
`x` runs through the rho orbit, `y` is a snapshot taken at powers of two, and
`k` is the next power-of-two boundary. -/
structure RhoState where
  i : ℕ  -- step count
  x : ℕ  -- current rho value
  y : ℕ  -- snapshot value
  k : ℕ  -- next power-of-two boundary

/--
One POLLARD-RHO step: advance `x` by `rhoStep`, take a snapshot at the
power-of-two boundary, and report the candidate factor
`gcd (|y − x|, n)`.
-/
def pollardStep (c n : ℕ) (st : RhoState) : RhoState × ℕ :=
  let i' := st.i + 1
  let x' := rhoStep c n st.x
  let d := Nat.gcd (Nat.dist st.y x') n
  let y' := if i' = st.k then x' else st.y
  let k' := if i' = st.k then st.k * 2 else st.k
  (⟨i', x', y', k'⟩, d)

/--
The POLLARD-RHO loop over a step budget.  It returns the first nontrivial
factor found, or `n` if the budget is exhausted (the loop is total; the
heuristic birthday-paradox analysis only concerns how quickly a collision
occurs).
-/
def pollardRhoLoop (c n : ℕ) : ℕ → RhoState → ℕ
  | 0, _ => n
  | steps + 1, st =>
      if 1 < (pollardStep c n st).2 ∧ (pollardStep c n st).2 < n then
        (pollardStep c n st).2
      else
        pollardRhoLoop c n steps (pollardStep c n st).1

/--
**POLLARD-RHO (CLRS §31.9).**  The tortoise-and-hare factorization heuristic
with seed `x₀`, running for up to `steps` iterations.  `x ↦ (x² + c) mod n`
is the rho iteration; `gcd(|y − x|, n)` at each step exposes a factor when a
collision modulo a prime factor occurs.
-/
def pollardRho (c n x₀ : ℕ) (steps : ℕ) : ℕ :=
  pollardRhoLoop c n steps ⟨1, x₀ % n, x₀ % n, 2⟩

/--
**POLLARD-RHO is sound.**  Whenever the loop returns a value different from
`n`, it is a nontrivial divisor of `n`.  The only exit that produces a value
is the `1 < d < n` check on `d = gcd(|y − x|, n)`, and the gcd always divides
`n`.
-/
theorem pollardRhoLoop_sound (c n : ℕ) : ∀ (steps : ℕ) (st : RhoState),
    pollardRhoLoop c n steps st ≠ n →
      pollardRhoLoop c n steps st ∣ n ∧ 1 < pollardRhoLoop c n steps st ∧
        pollardRhoLoop c n steps st < n
  | 0, _st, h => by
      simp [pollardRhoLoop] at h
  | steps + 1, st, h => by
      cases hstep : pollardStep c n st with
      | mk st' d =>
          by_cases hc : 1 < d ∧ d < n
          · have hres : pollardRhoLoop c n (steps + 1) st = d := by
              simp [pollardRhoLoop, hstep, hc]
            rw [hres]
            constructor
            · have hd : d = Nat.gcd (Nat.dist st.y (rhoStep c n st.x)) n := by
                have hsnd := congrArg Prod.snd hstep
                symm at hsnd
                simpa [pollardStep] using hsnd
              rw [hd]
              exact Nat.gcd_dvd_right _ _
            · exact hc
          · have hres : pollardRhoLoop c n (steps + 1) st = pollardRhoLoop c n steps st' := by
              simp [pollardRhoLoop, hstep, hc]
            rw [hres]
            exact pollardRhoLoop_sound c n steps st' (by simpa [hres] using h)

/-- **POLLARD-RHO is sound**: any returned factor is a nontrivial divisor of
`n`. -/
theorem pollardRho_sound {c n x₀ : ℕ} (steps : ℕ)
    (h : pollardRho c n x₀ steps ≠ n) :
    pollardRho c n x₀ steps ∣ n ∧ 1 < pollardRho c n x₀ steps ∧
      pollardRho c n x₀ steps < n := by
  unfold pollardRho
  exact pollardRhoLoop_sound c n steps ⟨1, x₀ % n, x₀ % n, 2⟩ h

/--
**Collision detection is sound.**  If at some step the new rho value is
congruent to the snapshot modulo a prime factor `p` of `n`, then the candidate
factor reported by that step is a multiple of `p` — so the loop will return a
nontrivial divisor.  (The heuristic birthday-paradox analysis concerns only
*when* such a collision occurs.)
-/
theorem pollardStep_collision_factor {c n p : ℕ} (hpn : p ∣ n)
    (st : RhoState) (hcoll : rhoStep c n st.x ≡ st.y [MOD p]) :
    p ∣ (pollardStep c n st).2 := by
  unfold pollardStep
  exact rho_collision_factor_dist hpn hcoll.symm

/-! ## Probabilistic analysis (CLRS Theorem 31.40)

CLRS analyzes POLLARD-RHO by *modeling* the rho orbit `x ↦ (x² + c) mod n`,
read modulo a prime factor `p`, as a sequence of independent uniform draws from
`Z_p`.  That independence assumption is a heuristic (a bad `c` gives a short
cycle), so it cannot be a theorem about the deterministic {lit}`rhoStep`.  We
make it an explicit probability model — the sample space `Fin k → Fin p` of `k`
independent uniform draws — and prove the birthday-paradox bound rigorously
inside it.  The detection lemmas at the end are *unconditional*: they concern
the real {lit}`pollardStep` / {lit}`pollardRhoLoop` construction. -/

open CLRS.Probability
open scoped Classical

/-- The "no collision" event for `k` independent uniform draws from a set of
size `p`: the tuple `a : Fin k → Fin p` is injective (all `k` draws distinct). -/
abbrev noCollision {p k : ℕ} (a : Fin k → Fin p) : Prop := Function.Injective a

/-- The negation of `fintypeExpect` is linear: `E[−X] = −E[X]`. -/
theorem fintypeExpect_neg {Ω : Type} [Fintype Ω] [DecidableEq Ω] (X : Ω → ℝ) :
    fintypeExpect (fun ω => -X ω) = -fintypeExpect X := by
  simp [fintypeExpect, Finset.sum_neg_distrib, neg_div]

/-- `fintypeExpect` is linear in a constant factor: `E[c·X] = c·E[X]`. -/
theorem fintypeExpect_const_mul {Ω : Type} [Fintype Ω] [DecidableEq Ω] (c : ℝ) (X : Ω → ℝ) :
    fintypeExpect (fun ω => c * X ω) = c * fintypeExpect X := by
  simp only [fintypeExpect]
  rw [← Finset.mul_sum]
  rw [mul_div_assoc]

/-- Gauss' summation formula over ℝ: `∑ i < k, i = k(k−1)/2`. -/
theorem sum_range_id_real (k : ℕ) : (∑ i ∈ Finset.range k, (i : ℝ)) = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      push_cast
      ring

/-- The uniform expectation of an indicator is the proportion of samples that
satisfy the predicate. -/
theorem fintypeExpect_indicator_eq_card {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (P : Ω → Prop) [DecidablePred P] :
    fintypeExpect (fun ω => indicator (P ω)) =
      (Fintype.card {ω : Ω // P ω} : ℝ) / (Fintype.card Ω : ℝ) := by
  unfold fintypeExpect indicator
  rw [Finset.sum_boole P Finset.univ]
  rw [Fintype.card_subtype]

/-- The number of injective maps `Fin k → Fin p` is the falling factorial
`p (p-1) ⋯ (p-k+1)`. -/
theorem card_injective_fin_fun {p k : ℕ} :
    Fintype.card {a : Fin k → Fin p // Function.Injective a} = Nat.descFactorial p k := by
  have h := Fintype.card_embedding_eq (α := Fin k) (β := Fin p)
  simp only [Fintype.card_fin] at h
  rw [← h]
  exact Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding (Fin k) (Fin p))

/-- `descFactorial p k = 0` once `p < k` (one factor is `p - p = 0`). -/
theorem descFactorial_eq_zero_of_lt {p k : ℕ} (h : p < k) : Nat.descFactorial p k = 0 := by
  rw [Nat.descFactorial_eq_prod_range]
  refine Finset.prod_eq_zero (Finset.mem_range.mpr h) ?_
  simp

/--
**Probability of no collision.**  Among `k` independent uniform draws from a set
of size `p`, the probability that all `k` values are distinct is
`p (p-1) ⋯ (p-k+1) / p^k = descFactorial p k / p^k`.
-/
theorem noCollision_prob_eq {p k : ℕ} :
    fintypeExpect (fun a : Fin k → Fin p => indicator (noCollision a)) =
      ((Nat.descFactorial p k : ℕ) : ℝ) / (p : ℝ)^k := by
  rw [fintypeExpect_indicator_eq_card (P := noCollision)]
  rw [card_injective_fin_fun]
  simp [Fintype.card_fun, Fintype.card_fin]

/--
**Birthday-paradox bound.**  The probability that `k` independent uniform draws
from a set of size `p` are all distinct is at most
`exp(−k(k−1)/(2p))`.  Equivalently the probability of a collision is at least
`1 − exp(−k(k−1)/(2p))`.  This is the probabilistic content of CLRS
Theorem 31.40 (the expected-`O(√p)` analysis of POLLARD-RHO).
-/
theorem birthday_noCollision_le {p k : ℕ} (hp : 0 < p) :
    fintypeExpect (fun a : Fin k → Fin p => indicator (noCollision a))
      ≤ Real.exp (-((k : ℝ) * ((k : ℝ) - 1)) / (2 * (p : ℝ))) := by
  rw [noCollision_prob_eq]
  by_cases hkp : p < k
  · rw [descFactorial_eq_zero_of_lt hkp]
    norm_num
    positivity
  · have hk_le_p : k ≤ p := le_of_not_gt hkp
    have h_desc : (Nat.descFactorial p k : ℝ) =
        ∏ i ∈ Finset.range k, ((p : ℝ) - (i : ℝ)) := by
      rw [Nat.descFactorial_eq_prod_range]
      rw [Nat.cast_prod]
      refine Finset.prod_congr rfl (fun i hi => ?_)
      have hi' : i < k := Finset.mem_range.mp hi
      have hip : i ≤ p := le_trans (le_of_lt hi') hk_le_p
      rw [Nat.cast_sub hip]
    have hdiv : (∏ i ∈ Finset.range k, ((p : ℝ) - (i : ℝ))) / (p : ℝ)^k
        = ∏ i ∈ Finset.range k, (((p : ℝ) - (i : ℝ)) / (p : ℝ)) := by
      rw [show (p : ℝ)^k = ∏ i ∈ Finset.range k, (p : ℝ) by simp]
      exact (Finset.prod_div_distrib (s := Finset.range k) (f := fun i => (p : ℝ) - (i : ℝ))
        (g := fun _ => (p : ℝ))).symm
    have hden : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    have hfactor : ∀ i ∈ Finset.range k,
        ((p : ℝ) - (i : ℝ)) / (p : ℝ) ≤ Real.exp (-(i : ℝ) / (p : ℝ)) := by
      intro i hi
      have h := Real.add_one_le_exp (-(i : ℝ) / (p : ℝ))
      have hgoal : 1 - (i : ℝ) / (p : ℝ) ≤ Real.exp (-(i : ℝ) / (p : ℝ)) := by
        convert h using 1
        ring
      rw [show ((p : ℝ) - (i : ℝ)) / (p : ℝ) = 1 - (i : ℝ) / (p : ℝ) by field_simp [hden]]
      exact hgoal
    have hprod : (∏ i ∈ Finset.range k, (((p : ℝ) - (i : ℝ)) / (p : ℝ)))
        ≤ ∏ i ∈ Finset.range k, Real.exp (-(i : ℝ) / (p : ℝ)) := by
      refine Finset.prod_le_prod (fun i hi => ?_) (fun i hi => hfactor i hi)
      exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast (le_trans (le_of_lt (Finset.mem_range.mp hi)) hk_le_p))) (by positivity)
    have hsum : (∏ i ∈ Finset.range k, Real.exp (-(i : ℝ) / (p : ℝ)))
        = Real.exp (-(∑ i ∈ Finset.range k, (i : ℝ)) / (p : ℝ)) := by
      rw [← Real.exp_sum]
      congr 1
      rw [(Finset.sum_div (s := Finset.range k) (f := fun i => -(i : ℝ)) (a := (p : ℝ))).symm]
      rw [Finset.sum_neg_distrib]
    calc
      (Nat.descFactorial p k : ℝ) / (p : ℝ)^k
          = (∏ i ∈ Finset.range k, ((p : ℝ) - (i : ℝ))) / (p : ℝ)^k := by rw [h_desc]
      _ = ∏ i ∈ Finset.range k, (((p : ℝ) - (i : ℝ)) / (p : ℝ)) := hdiv
      _ ≤ ∏ i ∈ Finset.range k, Real.exp (-(i : ℝ) / (p : ℝ)) := hprod
      _ = Real.exp (-(∑ i ∈ Finset.range k, (i : ℝ)) / (p : ℝ)) := hsum
      _ = Real.exp (-((k : ℝ) * ((k : ℝ) - 1)) / (2 * (p : ℝ))) := by
        rw [sum_range_id_real]
        congr 1
        ring

/--
**Birthday lower bound on the collision probability.**  Among `k` independent
uniform draws from a set of size `p`, a collision occurs with probability at
least `1 − exp(−k(k−1)/(2p))`.
-/
theorem birthday_collision_ge {p k : ℕ} (hp : 0 < p) :
    fintypeExpect (fun a : Fin k → Fin p => indicator (¬ noCollision a))
      ≥ 1 - Real.exp (-((k : ℝ) * ((k : ℝ) - 1)) / (2 * (p : ℝ))) := by
  haveI : Nonempty (Fin k → Fin p) := ⟨fun _ => ⟨0, hp⟩⟩
  have hcard : Fintype.card (Fin k → Fin p) ≠ 0 := Fintype.card_ne_zero
  have hdecomp : (fun a : Fin k → Fin p => indicator (¬ noCollision a)) =
      (fun a : Fin k → Fin p => (1 : ℝ) - indicator (noCollision a)) := by
    funext a
    unfold indicator noCollision
    by_cases h : Function.Injective a <;> simp [h]
  rw [hdecomp]
  have hlin : fintypeExpect (fun a : Fin k → Fin p => (1 : ℝ) - indicator (noCollision a))
      = 1 - fintypeExpect (fun a : Fin k → Fin p => indicator (noCollision a)) := by
    calc
      fintypeExpect (fun a : Fin k → Fin p => (1 : ℝ) - indicator (noCollision a))
          = fintypeExpect (fun a : Fin k → Fin p => (1 : ℝ) + (-indicator (noCollision a))) := by
            refine congrArg fintypeExpect (funext fun a => ?_)
            ring
      _ = fintypeExpect (fun _ : Fin k → Fin p => (1 : ℝ)) +
            fintypeExpect (fun a : Fin k → Fin p => -indicator (noCollision a)) :=
          fintypeExpect_add _ _
      _ = 1 - fintypeExpect (fun a : Fin k → Fin p => indicator (noCollision a)) := by
        rw [fintypeExpect_const hcard, fintypeExpect_neg]
        ring
  rw [hlin]
  linarith [birthday_noCollision_le (p := p) (k := k) hp]

/--
**Collision with constant probability.**  Once the number of draws `k` satisfies
`k(k−1) ≥ 2p`, a collision occurs with probability at least `1/2`.  The minimal
such `k` is `Θ(√p)`, which is the source of the `O(√p)` expected running time
(CLRS Theorem 31.40).
-/
theorem birthday_collision_prob_ge_half {p k : ℕ} (hp : 0 < p) (hk : 2 * p ≤ k * (k - 1)) :
    fintypeExpect (fun a : Fin k → Fin p => indicator (¬ noCollision a)) ≥ 1/2 := by
  have hge := birthday_collision_ge (p := p) (k := k) hp
  -- exp(-k(k-1)/(2p)) ≤ 1/2 once k(k-1)/(2p) ≥ 1
  have hexp : Real.exp (-((k : ℝ) * ((k : ℝ) - 1)) / (2 * (p : ℝ))) ≤ 1/2 := by
    have hp' : 0 < (2 : ℝ) * (p : ℝ) := by positivity
    have hk_ge : 1 ≤ k := by
      have hp2 : 0 < 2 * p := by omega
      have hpos : 0 < k * (k - 1) := lt_of_lt_of_le hp2 hk
      have hk_pos : 0 < k := pos_of_mul_pos_left hpos (Nat.zero_le _)
      omega
    have hk' : (2 : ℝ) * (p : ℝ) ≤ (k : ℝ) * ((k : ℝ) - 1) := by
      have h2p : ((2 * p : ℕ) : ℝ) = (2 : ℝ) * (p : ℝ) := by norm_num
      have hkk : ((k * (k - 1) : ℕ) : ℝ) = (k : ℝ) * ((k : ℝ) - 1) := by
        rw [Nat.cast_mul, Nat.cast_sub hk_ge]
        norm_num
      rw [← h2p, ← hkk]
      exact_mod_cast hk
    have hx : (1 : ℝ) ≤ ((k : ℝ) * ((k : ℝ) - 1)) / (2 * (p : ℝ)) := by
      rw [le_div_iff₀ hp']
      simpa using hk'
    have hneg : -((k : ℝ) * ((k : ℝ) - 1)) / (2 * (p : ℝ)) ≤ -1 := by
      rw [div_le_iff₀ hp']
      rw [show (-1 : ℝ) * (2 * (p : ℝ)) = -(2 * (p : ℝ)) by ring]
      rw [neg_le_neg_iff]
      exact hk'
    have hexp1 : Real.exp (-1 : ℝ) ≤ (1/2 : ℝ) := by
      have h2 : (2 : ℝ) ≤ Real.exp (1 : ℝ) := by
        nlinarith [Real.add_one_le_exp (1 : ℝ)]
      have hmul := mul_le_mul_of_nonneg_left h2 (le_of_lt (Real.exp_pos (-1 : ℝ)))
      have hprod : Real.exp (1 : ℝ) * Real.exp (-1 : ℝ) = 1 := by
        rw [← Real.exp_add]; norm_num
      nlinarith
    exact le_trans (Real.exp_le_exp.mpr hneg) hexp1
  linarith

/-! ## Expected running time O(√p)

The orbit is partitioned into blocks of `k` draws (a *round*), with
`2p ≤ k(k−1)`, so by {lit}`birthday_collision_prob_ge_half` each round contains
a collision with probability at least `1/2`.  A geometric tail-sum bounds the
expected number of rounds — and hence draws — by a constant times `k = Θ(√p)`. -/

/-- The probability that a single `k`-draw block is collision-free is at most
`1/2` once `2p ≤ k(k−1)` (the complement of the constant-probability collision
bound). -/
theorem noCollision_prob_le_half {p k : ℕ} (hp : 0 < p) (hk : 2 * p ≤ k * (k - 1)) :
    fintypeExpect (fun a : Fin k → Fin p => indicator (noCollision a)) ≤ 1/2 := by
  haveI : Nonempty (Fin k → Fin p) := ⟨fun _ => ⟨0, hp⟩⟩
  have hcard : Fintype.card (Fin k → Fin p) ≠ 0 := Fintype.card_ne_zero
  have hge := birthday_collision_prob_ge_half (p := p) (k := k) hp hk
  have hdecomp : (fun a : Fin k → Fin p => indicator (noCollision a)) =
      (fun a : Fin k → Fin p => (1 : ℝ) - indicator (¬ noCollision a)) := by
    funext a
    unfold indicator
    by_cases h : noCollision a <;> simp [h]
  rw [hdecomp]
  have hlin : fintypeExpect (fun a : Fin k → Fin p => (1 : ℝ) - indicator (¬ noCollision a))
      = 1 - fintypeExpect (fun a : Fin k → Fin p => indicator (¬ noCollision a)) := by
    calc
      fintypeExpect (fun a : Fin k → Fin p => (1 : ℝ) - indicator (¬ noCollision a))
          = fintypeExpect (fun a : Fin k → Fin p => (1 : ℝ) + (-indicator (¬ noCollision a))) := by
            refine congrArg fintypeExpect (funext fun a => ?_)
            ring
      _ = fintypeExpect (fun _ : Fin k → Fin p => (1 : ℝ)) +
            fintypeExpect (fun a : Fin k → Fin p => -indicator (¬ noCollision a)) :=
          fintypeExpect_add _ _
      _ = 1 - fintypeExpect (fun a : Fin k → Fin p => indicator (¬ noCollision a)) := by
        rw [fintypeExpect_const hcard, fintypeExpect_neg]
        ring
  rw [hlin]
  linarith

/-- Split `r + 1` independent rounds into the first `r` and the last. -/
noncomputable def roundsSplitLast {Ω : Type} (r : ℕ) : (Fin (r + 1) → Ω) ≃ (Fin r → Ω) × Ω where
  toFun A := ((fun j : Fin r => A (Fin.castSucc j)), A ⟨r, Nat.lt_succ_self r⟩)
  invFun q := fun x : Fin (r + 1) =>
    if hx : x.val < r then q.1 ⟨x.val, hx⟩ else q.2
  left_inv A := by
    funext x
    by_cases hx : x.val < r
    · simp [hx]
    · simp [hx]
      have hx' : x = ⟨r, Nat.lt_succ_self r⟩ := by
        apply Fin.ext
        change x.val = r
        omega
      rw [hx']
  right_inv q := by
    obtain ⟨P, L⟩ := q
    refine Prod.ext ?_ ?_
    · funext j
      simp
    · simp

/-- Split `t` rounds into a prefix of `r` and the remaining `t - r`, for `r ≤ t`. -/
noncomputable def roundsSplitPrefix {Ω : Type} {t r : ℕ} (hrt : r ≤ t) :
    (Fin t → Ω) ≃ (Fin r → Ω) × (Fin (t - r) → Ω) where
  toFun A := ((fun j : Fin r => A (Fin.castLE hrt j)),
              (fun j : Fin (t - r) => A ⟨r + j.val, by omega⟩))
  invFun q := fun x : Fin t =>
    if hx : x.val < r then q.1 ⟨x.val, hx⟩ else q.2 ⟨x.val - r, by omega⟩
  left_inv A := by
    funext x
    by_cases hx : x.val < r
    · simp [hx]
    · simp [hx]
      apply congrArg A
      apply Fin.ext
      change r + (x.val - r) = x.val
      omega
  right_inv q := by
    obtain ⟨P, S⟩ := q
    refine Prod.ext ?_ ?_
    · funext j
      simp
    · funext j
      have hnot : ¬ r + j.val < r := by omega
      simp [hnot]

/--
**Independent-rounds failure bound.**  In `r` independent rounds, each a `k`-draw
block that is collision-free with probability at most `1/2`, the probability
that all `r` rounds are collision-free is at most `(1/2)^r`.
-/
theorem rho_prefix_noCollision_prob_le {p k r : ℕ} (hp : 0 < p) (hk : 2 * p ≤ k * (k - 1)) :
    fintypeExpect (fun A : Fin r → (Fin k → Fin p) =>
      indicator (∀ j : Fin r, noCollision (A j))) ≤ (1/2 : ℝ)^r := by
  induction r with
  | zero =>
      have htrue : ∀ A : Fin 0 → (Fin k → Fin p), (∀ j : Fin 0, noCollision (A j)) := by
        intro A j
        exact Fin.elim0 j
      haveI : Nonempty (Fin k → Fin p) := ⟨fun _ => ⟨0, hp⟩⟩
      have hcard : Fintype.card (Fin 0 → (Fin k → Fin p)) ≠ 0 := Fintype.card_ne_zero
      calc
        fintypeExpect (fun A : Fin 0 → (Fin k → Fin p) =>
            indicator (∀ j : Fin 0, noCollision (A j)))
            = fintypeExpect (fun _ : Fin 0 → (Fin k → Fin p) => (1 : ℝ)) := by
              refine congrArg fintypeExpect (funext fun A => ?_)
              have hP : (∀ j : Fin 0, noCollision (A j)) := htrue A
              unfold indicator
              rw [if_pos hP]
        _ = 1 := by simp [fintypeExpect_const hcard]
        _ ≤ (1/2 : ℝ)^0 := by simp
  | succ r ih =>
      haveI : Nonempty (Fin k → Fin p) := ⟨fun _ => ⟨0, hp⟩⟩
      have hcardΩ : Fintype.card (Fin k → Fin p) ≠ 0 := Fintype.card_ne_zero
      have hsplit : ∀ A : Fin (r + 1) → (Fin k → Fin p),
          indicator (∀ j : Fin (r + 1), noCollision (A j))
            = indicator ((∀ j : Fin r, noCollision (A (Fin.castSucc j))) ∧
                noCollision (A ⟨r, Nat.lt_succ_self r⟩)) := by
        intro A
        have hiff : (∀ j : Fin (r + 1), noCollision (A j)) ↔
            (∀ j : Fin r, noCollision (A (Fin.castSucc j))) ∧
              noCollision (A ⟨r, Nat.lt_succ_self r⟩) := by
          constructor
          · intro h
            constructor
            · intro j
              exact h (Fin.castSucc j)
            · exact h ⟨r, Nat.lt_succ_self r⟩
          · rintro ⟨hpre, hlast⟩ j
            by_cases hj : j.val < r
            · have hj' : j = Fin.castSucc ⟨j.val, hj⟩ := by ext; rfl
              rw [hj']
              exact hpre ⟨j.val, hj⟩
            · have hj' : j = ⟨r, Nat.lt_succ_self r⟩ := by
                apply Fin.ext
                change j.val = r
                omega
              rw [hj']
              exact hlast
        unfold indicator
        by_cases hP1 : ∀ j : Fin (r + 1), noCollision (A j)
        · rw [if_pos hP1, if_pos (hiff.mp hP1)]
        · rw [if_neg hP1, if_neg (fun hP2 => hP1 (hiff.mpr hP2))]
      have he := fintypeExpect_equiv (roundsSplitLast (Ω := Fin k → Fin p) r)
        (fun q : (Fin r → (Fin k → Fin p)) × (Fin k → Fin p) =>
          indicator ((∀ j : Fin r, noCollision (q.1 j)) ∧ noCollision q.2))
      have hLHS : fintypeExpect (fun A : Fin (r + 1) → (Fin k → Fin p) =>
            indicator (∀ j : Fin (r + 1), noCollision (A j)))
          = fintypeExpect (fun q : (Fin r → (Fin k → Fin p)) × (Fin k → Fin p) =>
              indicator ((∀ j : Fin r, noCollision (q.1 j)) ∧ noCollision q.2)) := by
        calc
          fintypeExpect (fun A : Fin (r + 1) → (Fin k → Fin p) =>
                indicator (∀ j : Fin (r + 1), noCollision (A j)))
              = fintypeExpect (fun A : Fin (r + 1) → (Fin k → Fin p) =>
                  indicator ((∀ j : Fin r, noCollision (A (Fin.castSucc j))) ∧
                    noCollision (A ⟨r, Nat.lt_succ_self r⟩))) := by
                refine congrArg fintypeExpect (funext fun A => hsplit A)
          _ = fintypeExpect (fun A : Fin (r + 1) → (Fin k → Fin p) =>
                  indicator ((∀ j : Fin r, noCollision ((roundsSplitLast (Ω := Fin k → Fin p) r A).1 j)) ∧
                    noCollision ((roundsSplitLast (Ω := Fin k → Fin p) r A).2))) := by
                refine congrArg fintypeExpect (funext fun A => ?_)
                rfl
          _ = fintypeExpect (fun q : (Fin r → (Fin k → Fin p)) × (Fin k → Fin p) =>
                  indicator ((∀ j : Fin r, noCollision (q.1 j)) ∧ noCollision q.2)) := he
      have hprod : fintypeExpect (fun q : (Fin r → (Fin k → Fin p)) × (Fin k → Fin p) =>
              indicator ((∀ j : Fin r, noCollision (q.1 j)) ∧ noCollision q.2))
          = fintypeExpect (fun B : Fin r → (Fin k → Fin p) =>
              indicator (∀ j : Fin r, noCollision (B j)))
            * fintypeExpect (fun a : Fin k → Fin p => indicator (noCollision a)) := by
        have hsplit2 : (fun q : (Fin r → (Fin k → Fin p)) × (Fin k → Fin p) =>
              indicator ((∀ j : Fin r, noCollision (q.1 j)) ∧ noCollision q.2))
            = (fun q : (Fin r → (Fin k → Fin p)) × (Fin k → Fin p) =>
                (fun B : Fin r → (Fin k → Fin p) => indicator (∀ j : Fin r, noCollision (B j))) q.1
                  * (fun a : Fin k → Fin p => indicator (noCollision a)) q.2) := by
          funext q
          by_cases hpre : ∀ j : Fin r, noCollision (q.1 j)
          · by_cases hlast : noCollision q.2
            · simp [indicator, hpre, hlast]
            · simp [indicator, hpre, hlast]
          · by_cases hlast : noCollision q.2
            · simp [indicator, hpre, hlast]
            · simp [indicator, hpre, hlast]
        rw [hsplit2]
        exact expect_mul_of_indep (fun B : Fin r → (Fin k → Fin p) =>
          indicator (∀ j : Fin r, noCollision (B j)))
          (fun a : Fin k → Fin p => indicator (noCollision a))
      have hfail : fintypeExpect (fun a : Fin k → Fin p => indicator (noCollision a)) ≤ 1/2 :=
        noCollision_prob_le_half hp hk
      calc
        fintypeExpect (fun A : Fin (r + 1) → (Fin k → Fin p) =>
            indicator (∀ j : Fin (r + 1), noCollision (A j)))
            = fintypeExpect (fun B : Fin r → (Fin k → Fin p) =>
                indicator (∀ j : Fin r, noCollision (B j)))
              * fintypeExpect (fun a : Fin k → Fin p => indicator (noCollision a)) := by
              rw [hLHS, hprod]
        _ ≤ (1/2 : ℝ)^r * (1/2) := by
              exact mul_le_mul ih hfail
                (fintypeExpect_nonneg (fun a : Fin k → Fin p => by
                  unfold indicator
                  split <;> norm_num))
                (by positivity)
        _ = (1/2 : ℝ)^(r + 1) := by
              simp [pow_succ]

/-- The probability that the first `r` of `t` independent rounds are all
collision-free is at most `(1/2)^r`: the remaining `t - r` rounds are
independent of the prefix and marginalise out. -/
theorem rho_trials_prefix_noCollision_prob_le {p k t r : ℕ} (hp : 0 < p) (hk : 2 * p ≤ k * (k - 1))
    (hrt : r ≤ t) :
    fintypeExpect (fun A : Fin t → (Fin k → Fin p) =>
      indicator (∀ j : Fin r, noCollision (A (Fin.castLE hrt j)))) ≤ (1/2 : ℝ)^r := by
  haveI : Nonempty (Fin k → Fin p) := ⟨fun _ => ⟨0, hp⟩⟩
  have hcard_suffix : Fintype.card (Fin (t - r) → (Fin k → Fin p)) ≠ 0 := Fintype.card_ne_zero
  have hpre : fintypeExpect (fun A : Fin t → (Fin k → Fin p) =>
        indicator (∀ j : Fin r, noCollision (A (Fin.castLE hrt j))))
      = fintypeExpect (fun B : Fin r → (Fin k → Fin p) =>
        indicator (∀ j : Fin r, noCollision (B j))) := by
    calc
      fintypeExpect (fun A : Fin t → (Fin k → Fin p) =>
            indicator (∀ j : Fin r, noCollision (A (Fin.castLE hrt j))))
          = fintypeExpect (fun A : Fin t → (Fin k → Fin p) =>
              indicator (∀ j : Fin r, noCollision ((roundsSplitPrefix (Ω := Fin k → Fin p) hrt A).1 j))) := by
            refine congrArg fintypeExpect (funext fun A => ?_)
            rfl
      _ = fintypeExpect (fun q : (Fin r → (Fin k → Fin p)) × (Fin (t - r) → (Fin k → Fin p)) =>
            indicator (∀ j : Fin r, noCollision (q.1 j))) := by
            exact fintypeExpect_equiv (roundsSplitPrefix (Ω := Fin k → Fin p) hrt)
              (fun q : (Fin r → (Fin k → Fin p)) × (Fin (t - r) → (Fin k → Fin p)) =>
                indicator (∀ j : Fin r, noCollision (q.1 j)))
      _ = fintypeExpect (fun B : Fin r → (Fin k → Fin p) =>
            indicator (∀ j : Fin r, noCollision (B j))) := by
            exact fintypeExpect_fst hcard_suffix
              (fun B : Fin r → (Fin k → Fin p) => indicator (∀ j : Fin r, noCollision (B j)))
  rw [hpre]
  exact rho_prefix_noCollision_prob_le (p := p) (k := k) (r := r) hp hk

/-- The number of collision-free rounds before the first round that contains a
collision, in a truncated sequence of `t` independent rounds. -/
noncomputable def failedRounds {p k t : ℕ} (A : Fin t → (Fin k → Fin p)) : ℕ :=
  (Finset.univ.filter (fun r : Fin t =>
    ∀ j : Fin (r.val + 1), noCollision (A (Fin.castLE (Nat.succ_le_of_lt r.isLt) j)))).card

/-- `failedRounds` is the sum over round prefixes of the indicator that the
first `r + 1` rounds are all collision-free. -/
theorem failedRounds_eq_sum {p k t : ℕ} (A : Fin t → (Fin k → Fin p)) :
    failedRounds A = ∑ r : Fin t, (if (∀ j : Fin (r.val + 1),
      noCollision (A (Fin.castLE (Nat.succ_le_of_lt r.isLt) j))) then 1 else 0) := by
  unfold failedRounds
  simpa using (Finset.sum_boole (fun r : Fin t => ∀ j : Fin (r.val + 1),
    noCollision (A (Fin.castLE (Nat.succ_le_of_lt r.isLt) j)))
    (Finset.univ : Finset (Fin t))).symm

/--
**Expected collision-free rounds.**  In the truncated model of `t` independent
rounds (each collision-free with probability at most `1/2`), the expected number
of failed rounds before the first colliding round is at most `1` — via the
tail-sum identity `E[F] = Σ_r P[first r rounds fail] ≤ Σ_r (1/2)^r = 1`.
-/
theorem rho_expected_failedRounds_le_one {p k t : ℕ} (hp : 0 < p) (hk : 2 * p ≤ k * (k - 1)) :
    fintypeExpect (fun A : Fin t → (Fin k → Fin p) => (failedRounds A : ℝ)) ≤ 1 := by
  have hdecomp : (fun A : Fin t → (Fin k → Fin p) => (failedRounds A : ℝ))
      = (fun A : Fin t → (Fin k → Fin p) => ∑ r : Fin t,
          indicator (∀ j : Fin (r.val + 1),
            noCollision (A (Fin.castLE (Nat.succ_le_of_lt r.isLt) j)))) := by
    funext A
    rw [failedRounds_eq_sum A]
    simp [indicator, Nat.cast_sum]
  have hlin : fintypeExpect (fun A : Fin t → (Fin k → Fin p) => (failedRounds A : ℝ))
      = ∑ r : Fin t, fintypeExpect (fun A : Fin t → (Fin k → Fin p) =>
          indicator (∀ j : Fin (r.val + 1),
            noCollision (A (Fin.castLE (Nat.succ_le_of_lt r.isLt) j)))) := by
    rw [hdecomp]
    exact fintypeExpect_sum Finset.univ _
  have hterm : ∀ r : Fin t, fintypeExpect (fun A : Fin t → (Fin k → Fin p) =>
        indicator (∀ j : Fin (r.val + 1),
          noCollision (A (Fin.castLE (Nat.succ_le_of_lt r.isLt) j)))) ≤ (1/2 : ℝ)^(r.val + 1) := by
    intro r
    exact rho_trials_prefix_noCollision_prob_le hp hk (Nat.succ_le_of_lt r.isLt)
  calc
    fintypeExpect (fun A : Fin t → (Fin k → Fin p) => (failedRounds A : ℝ))
        ≤ ∑ r : Fin t, (1/2 : ℝ)^(r.val + 1) := by
          rw [hlin]
          exact Finset.sum_le_sum (fun r _ => hterm r)
    _ ≤ 1 := by
          have hfactor : (∑ r : Fin t, (1/2 : ℝ)^(r.val + 1)) = (1/2) * (∑ r : Fin t, (1/2 : ℝ)^r.val) := by
            calc
              (∑ r : Fin t, (1/2 : ℝ)^(r.val + 1))
                  = (∑ r : Fin t, (1/2 : ℝ)^r.val * (1/2)) := by
                    refine Finset.sum_congr rfl (fun r _ => ?_)
                    rw [pow_succ]
              _ = (1/2) * (∑ r : Fin t, (1/2 : ℝ)^r.val) := by
                    rw [Finset.mul_sum]
                    simp [mul_comm]
          rw [hfactor]
          have hgeom : (∑ r : Fin t, (1/2 : ℝ)^r.val) ≤ 2 := by
            have hrange : (∑ r : Fin t, (1/2 : ℝ)^r.val) = ∑ i ∈ Finset.range t, (1/2 : ℝ)^i := by
              rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (1/2 : ℝ)^i) t]
            rw [hrange]
            have hgeom_mul := geom_sum_mul_of_le_one (x := (1/2 : ℝ)) (by norm_num) t
            have hmul : (∑ i ∈ Finset.range t, (1/2 : ℝ)^i) * (1/2) ≤ 1 := by
              norm_num at hgeom_mul
              rw [hgeom_mul]
              have hpow : 0 ≤ (1/2 : ℝ)^t := by positivity
              nlinarith
            nlinarith
          nlinarith

/-- The number of rounds performed up to and including the first colliding
round, in a truncated model of `t` independent rounds: the failed rounds plus
the successful round itself (or `t + 1` as an overestimate when none collide). -/
noncomputable def roundsUntilCollision {p k t : ℕ} (A : Fin t → (Fin k → Fin p)) : ℕ :=
  failedRounds A + 1

/--
**Expected rounds until a collision.**  In the truncated model of `t`
independent rounds, each collision-free with probability at most `1/2` (given
`2p ≤ k(k−1)`), the expected number of rounds up to and including the first
colliding round is at most `2`.
-/
theorem rho_expected_rounds_le_two {p k t : ℕ} (hp : 0 < p) (hk : 2 * p ≤ k * (k - 1)) :
    fintypeExpect (fun A : Fin t → (Fin k → Fin p) => (roundsUntilCollision A : ℝ)) ≤ 2 := by
  unfold roundsUntilCollision
  calc
    fintypeExpect (fun A : Fin t → (Fin k → Fin p) => ((failedRounds A + 1 : ℕ) : ℝ))
        = fintypeExpect (fun A : Fin t → (Fin k → Fin p) => (failedRounds A : ℝ) + 1) := by
          refine congrArg fintypeExpect (funext fun A => ?_)
          simp
    _ = fintypeExpect (fun A : Fin t → (Fin k → Fin p) => (failedRounds A : ℝ)) + 1 := by
          calc
            fintypeExpect (fun A : Fin t → (Fin k → Fin p) => (failedRounds A : ℝ) + 1)
                = fintypeExpect (fun A : Fin t → (Fin k → Fin p) => (failedRounds A : ℝ)) +
                    fintypeExpect (fun _ : Fin t → (Fin k → Fin p) => (1 : ℝ)) := fintypeExpect_add _ _
            _ = fintypeExpect (fun A : Fin t → (Fin k → Fin p) => (failedRounds A : ℝ)) + 1 := by
                  haveI : Nonempty (Fin k → Fin p) := ⟨fun _ => ⟨0, hp⟩⟩
                  have hcard : Fintype.card (Fin t → (Fin k → Fin p)) ≠ 0 := Fintype.card_ne_zero
                  simp [fintypeExpect_const hcard]
    _ ≤ 2 := by
          linarith [rho_expected_failedRounds_le_one (p := p) (k := k) (t := t) hp hk]

/--
**Expected draws until a collision is O(√p).**  Partitioning the orbit into
rounds of `k` draws with `2p ≤ k(k−1)`, the expected number of rounds until the
first collision is at most `2`, so the expected number of draws is at most
`2k`.  Since the minimal such `k` is `Θ(√p)`, this is the expected-`O(√p)`
running-time bound of CLRS Theorem 31.40.
-/
theorem rho_expected_draws_le {p k t : ℕ} (hp : 0 < p) (hk : 2 * p ≤ k * (k - 1)) :
    fintypeExpect (fun A : Fin t → (Fin k → Fin p) =>
      (roundsUntilCollision A : ℝ) * (k : ℝ)) ≤ 2 * (k : ℝ) := by
  have hk' : 0 ≤ (k : ℝ) := by positivity
  calc
    fintypeExpect (fun A : Fin t → (Fin k → Fin p) =>
        (roundsUntilCollision A : ℝ) * (k : ℝ))
        = (k : ℝ) * fintypeExpect (fun A : Fin t → (Fin k → Fin p) =>
            (roundsUntilCollision A : ℝ)) := by
          have hswap : (fun A : Fin t → (Fin k → Fin p) =>
              (roundsUntilCollision A : ℝ) * (k : ℝ))
              = (fun A : Fin t → (Fin k → Fin p) => (k : ℝ) * (roundsUntilCollision A : ℝ)) := by
            funext A
            ring
          rw [hswap]
          haveI : Nonempty (Fin k → Fin p) := ⟨fun _ => ⟨0, hp⟩⟩
          have hcard : Fintype.card (Fin t → (Fin k → Fin p)) ≠ 0 := Fintype.card_ne_zero
          -- linearity with a constant factor: E[(k:ℝ) * X] = (k:ℝ) * E[X]
          exact fintypeExpect_const_mul (k : ℝ) (fun A : Fin t → (Fin k → Fin p) => (roundsUntilCollision A : ℝ))
    _ ≤ (k : ℝ) * 2 := by
          exact mul_le_mul_of_nonneg_left (rho_expected_rounds_le_two (p := p) (k := k) (t := t) hp hk) hk'
    _ = 2 * (k : ℝ) := by ring

/-! ## Detection: bound to the real construction -/

/-- A `RhoState` is *valid* when both the current value `x` and the snapshot `y`
are reduced modulo `n` (both `< n`).  This invariant holds for the initial state
of {lit}`pollardRho` and is preserved by {lit}`pollardStep`. -/
def RhoState_valid (n : ℕ) (st : RhoState) : Prop := st.x < n ∧ st.y < n

/-- `pollardStep` preserves validity: if both `x` and `y` are `< n`, so are the
new value and the (possibly refreshed) snapshot. -/
theorem pollardStep_valid {c n : ℕ} (hn : 0 < n) (st : RhoState) (hst : RhoState_valid n st) :
    RhoState_valid n (pollardStep c n st).1 := by
  unfold RhoState_valid pollardStep
  simp [rhoStep]
  constructor
  · exact Nat.mod_lt _ hn
  · by_cases h : st.i + 1 = st.k <;> simp [h, hst.2, Nat.mod_lt (st.x * st.x + c) hn]

/--
**Collision detection forces a proper factor.**  If a fresh rho value
`rhoStep c n st.x` collides with the snapshot `st.y` modulo a prime factor
`p < n`, and the two values actually differ, then the candidate
`d = gcd(|st.y − rhoStep c n st.x|, n)` satisfies `1 < d < n`, so the loop's
exit check succeeds at this step.
-/
theorem pollardStep_detects {c n p : ℕ} (hp : p.Prime) (hpn : p ∣ n) (hplt : p < n)
    (hn : 0 < n) (st : RhoState) (hst : RhoState_valid n st)
    (hcoll : rhoStep c n st.x ≡ st.y [MOD p]) (hxy : rhoStep c n st.x ≠ st.y) :
    1 < (pollardStep c n st).2 ∧ (pollardStep c n st).2 < n := by
  have hpdvd : p ∣ (pollardStep c n st).2 := pollardStep_collision_factor hpn st hcoll
  have hx_lt : rhoStep c n st.x < n := Nat.mod_lt _ hn
  have hdist_lt : Nat.dist st.y (rhoStep c n st.x) < n := by
    have hm : max st.y (rhoStep c n st.x) < n := max_lt hst.2 hx_lt
    have hd : Nat.dist st.y (rhoStep c n st.x) ≤ max st.y (rhoStep c n st.x) := by
      rw [Nat.dist_eq_max_sub_min]
      exact Nat.sub_le _ _
    exact lt_of_le_of_lt hd hm
  have hdist_pos : 0 < Nat.dist st.y (rhoStep c n st.x) := Nat.dist_pos_of_ne hxy.symm
  have hd : (pollardStep c n st).2 = Nat.gcd (Nat.dist st.y (rhoStep c n st.x)) n := by
    unfold pollardStep
    rfl
  constructor
  · -- 1 < d
    have hd_pos : 0 < (pollardStep c n st).2 := by
      rw [hd]
      exact Nat.gcd_pos_of_pos_right (Nat.dist st.y (rhoStep c n st.x)) hn
    have hp_le : p ≤ (pollardStep c n st).2 := Nat.le_of_dvd hd_pos hpdvd
    exact lt_of_lt_of_le hp.one_lt hp_le
  · -- d < n
    rw [hd]
    exact lt_of_le_of_lt (Nat.le_of_dvd hdist_pos (Nat.gcd_dvd_left _ _)) hdist_lt

/--
**The loop returns a nontrivial divisor on a detected collision.**  Given a
valid state whose fresh value collides with the snapshot modulo a prime factor
`p < n`, {lit}`pollardRhoLoop` returns a value that divides `n` and is strictly
between `1` and `n` (a nontrivial factor).
-/
theorem pollardRhoLoop_terminates_on_collision {c n p : ℕ} (hp : p.Prime) (hpn : p ∣ n)
    (hplt : p < n) (hn : 0 < n) (steps : ℕ) (st : RhoState) (hst : RhoState_valid n st)
    (hcoll : rhoStep c n st.x ≡ st.y [MOD p]) (hxy : rhoStep c n st.x ≠ st.y) :
    pollardRhoLoop c n (steps + 1) st ∣ n ∧ 1 < pollardRhoLoop c n (steps + 1) st ∧
      pollardRhoLoop c n (steps + 1) st < n := by
  have hdet := pollardStep_detects hp hpn hplt hn st hst hcoll hxy
  have hres : pollardRhoLoop c n (steps + 1) st = (pollardStep c n st).2 := by
    unfold pollardRhoLoop
    simp [hdet]
  have hne : pollardRhoLoop c n (steps + 1) st ≠ n := by
    rw [hres]
    exact ne_of_lt hdet.2
  exact pollardRhoLoop_sound c n (steps + 1) st hne

end Chapter31

end CLRS

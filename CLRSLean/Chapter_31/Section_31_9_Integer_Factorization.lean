import Mathlib
import CLRSLean.Chapter_31.Section_31_2_Greatest_Common_Divisor

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

Notation:

- {lit}`a ≡ b [MOD p]` : `Nat.ModEq`.
- {lit}`Nat.gcd a n` : the greatest common divisor.

Deferred: the birthday-paradox / expected-`O(√p)` running-time analysis
(CLRS Theorem 31.40), which is a heuristic in CLRS and is left informal.
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

end Chapter31

end CLRS

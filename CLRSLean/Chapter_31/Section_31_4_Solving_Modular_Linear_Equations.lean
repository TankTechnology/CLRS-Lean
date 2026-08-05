import Mathlib
import CLRSLean.Chapter_31.Section_31_3_Modular_Arithmetic

/-!
# 31.4 Solving Modular Linear Equations

CLRS §31.4: the structure of the solutions to the linear congruence
`a·x ≡ b (mod n)`.  Once one solution `x₀` is known, every solution is
`x₀ + k·(n/d)` for `d = gcd(a, n)`, so the `d` distinct solutions modulo `n`
are `x₀`, `x₀ + n/d`, …, `x₀ + (d−1)·(n/d)`.

Main results:

- {lit}`linear_congruence_shift`: if `x` solves `a·x ≡ b (mod n)`, then
  `x + k·(n/d)` solves it too — shifting by `n/d` preserves solutions.
- {lit}`linear_congruence_all_solutions`: if `x₀` and `x` both solve
  `a·x ≡ b (mod n)`, then `x ≡ x₀ (mod n/d)` — every solution differs from
  `x₀` by a multiple of `n/d`.
- Theorem {lit}`linear_congruence_solutions` (Theorem 31.10): the solutions
  are exactly the residue class `x₀ mod (n/d)`.
- Theorem {lit}`linear_congruence_distinct` (Theorem 31.10): the `d` values
  `k·(n/d)` for `0 ≤ k < d` are pairwise incongruent, so the congruence has
  exactly `d` distinct solutions.

Notation:

- {lit}`a ≡ b [MOD n]` : `Nat.ModEq`.
- {lit}`Nat.gcd a n` : the greatest common divisor.

Deferred: an explicit executable enumerator of the `d` solutions, and the
running-time analysis (§31.4 algorithms).
-/

namespace CLRS

namespace Chapter31

/-- `a·(n/d) = (a/d)·n` for `d = gcd a n`: the cross-term used in the shift. -/
lemma mul_nat_div_eq (a n : ℕ) [NeZero n] : a * (n / Nat.gcd a n) = (a / Nat.gcd a n) * n := by
  let d := Nat.gcd a n
  have hd : 0 < d := Nat.gcd_pos_of_pos_right a (NeZero.pos n)
  apply Nat.mul_right_cancel hd
  calc
    (a * (n / d)) * d = a * ((n / d) * d) := by ring
    _ = a * n := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_right a n)]
    _ = ((a / d) * d) * n := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_left a n)]
    _ = (a / d) * (n * d) := by ring
    _ = ((a / d) * n) * d := by ring

/-- If `x` solves `a·x ≡ b (mod n)`, then `x + k·(n/d)` solves it too: adding
multiples of `n/d` preserves solutions (CLRS §31.4). -/
theorem linear_congruence_shift {a b x n k : ℕ} [NeZero n] (h : a * x ≡ b [MOD n]) :
    a * (x + n / Nat.gcd a n * k) ≡ b [MOD n] := by
  have hsplit : a * (x + n / Nat.gcd a n * k) = a * x + a * (n / Nat.gcd a n * k) := by ring
  rw [hsplit]
  have h0 : a * (n / Nat.gcd a n * k) ≡ 0 [MOD n] := by
    rw [← mul_assoc]
    rw [mul_nat_div_eq a n]
    apply Nat.modEq_zero_iff_dvd.mpr
    use (a / Nat.gcd a n) * k
    ring
  simpa using (Nat.ModEq.add h h0)

/-- If `x₀` and `x` both solve `a·x ≡ b (mod n)`, then `x ≡ x₀ (mod n/d)`: every
solution differs from any given solution by a multiple of `n/d` (CLRS §31.4).
Together with {lit}`linear_congruence_shift`, the `d = gcd(a, n)` distinct
solutions modulo `n` are `x₀`, `x₀ + n/d`, …, `x₀ + (d−1)·(n/d)`. -/
theorem linear_congruence_all_solutions {a b x x₀ n : ℕ} [NeZero n]
    (h : a * x ≡ b [MOD n]) (h₀ : a * x₀ ≡ b [MOD n]) :
    x ≡ x₀ [MOD (n / Nat.gcd a n)] := by
  let d := Nat.gcd a n
  have hd : 0 < d := Nat.gcd_pos_of_pos_right a (NeZero.pos n)
  have ha : a = d * (a / d) := by
    dsimp [d]
    simpa [Nat.mul_comm] using (Nat.div_mul_cancel (Nat.gcd_dvd_left a n)).symm
  have hn : n = d * (n / d) := by
    dsimp [d]
    simpa [Nat.mul_comm] using (Nat.div_mul_cancel (Nat.gcd_dvd_right a n)).symm
  have hax : a * x ≡ a * x₀ [MOD n] := h.trans h₀.symm
  have hax2 : (a / d) * x ≡ (a / d) * x₀ [MOD (n / d)] := by
    rw [Nat.ModEq] at hax ⊢
    have hsplit : ∀ z : ℕ, (a * z) % n = d * (((a / d) * z) % (n / d)) := by
      intro z
      calc
        (a * z) % n = (d * ((a / d) * z)) % (d * (n / d)) := by
          have hz : a * z = d * ((a / d) * z) := by
            conv_lhs => rw [ha]
            rw [← mul_assoc]
          rw [hz]
          conv_lhs => rw [hn]
        _ = d * (((a / d) * z) % (n / d)) := by rw [Nat.mul_mod_mul_left]
    have hres : d * (((a / d) * x) % (n / d)) = d * (((a / d) * x₀) % (n / d)) := by
      rw [← hsplit x, ← hsplit x₀]
      exact hax
    exact Nat.eq_of_mul_eq_mul_left hd hres
  have hcop' : Nat.Coprime (a / d) (n / d) := by
    dsimp [d]
    exact Nat.coprime_div_gcd_div_gcd hd
  exact Nat.ModEq.cancel_left_of_coprime (by simpa [Nat.gcd_comm] using hcop'.gcd_eq_one) hax2

/-- **The solutions of a linear congruence (CLRS Theorem 31.10).**  If `x₀`
solves `a·x ≡ b (mod n)`, then a value `x` solves the congruence exactly when
`x ≡ x₀ (mod n/d)` for `d = gcd(a, n)`: the solutions form one residue class
modulo `n/d`. -/
theorem linear_congruence_solutions {a b x₀ n : ℕ} [NeZero n] (h : a * x₀ ≡ b [MOD n]) :
    ∀ x : ℕ, (a * x ≡ b [MOD n]) ↔ x ≡ x₀ [MOD (n / Nat.gcd a n)] := by
  intro x
  constructor
  · intro hx
    exact linear_congruence_all_solutions hx h
  · intro hx
    have h1 : a * x ≡ a * x₀ [MOD a * (n / Nat.gcd a n)] := by
      rw [Nat.ModEq] at hx ⊢
      rw [Nat.mul_mod_mul_left, Nat.mul_mod_mul_left]
      rw [hx]
    have h2 : a * x ≡ a * x₀ [MOD n] := by
      rw [mul_nat_div_eq a n] at h1
      exact Nat.ModEq.of_dvd (dvd_mul_left n (a / Nat.gcd a n)) h1
    exact h2.trans h

/-- **The `d = gcd(a, n)` solutions are distinct modulo `n` (CLRS Theorem
31.10).**  The values `k·(n/d)` for `0 ≤ k < d` are pairwise incongruent
modulo `n`, so together with {lit}`linear_congruence_shift` they give exactly
`d` distinct solutions. -/
theorem linear_congruence_distinct {a n : ℕ} [NeZero n] (k₁ k₂ : ℕ)
    (hk₁ : k₁ < Nat.gcd a n) (hk₂ : k₂ < Nat.gcd a n) (hk : k₁ < k₂) :
    ¬ k₁ * (n / Nat.gcd a n) ≡ k₂ * (n / Nat.gcd a n) [MOD n] := by
  intro hc
  have hd : n ∣ (k₂ - k₁) * (n / Nat.gcd a n) := by
    have hle : k₁ * (n / Nat.gcd a n) ≤ k₂ * (n / Nat.gcd a n) := by
      exact Nat.mul_le_mul_right _ (Nat.le_of_lt hk)
    have hmod : (k₂ * (n / Nat.gcd a n) - k₁ * (n / Nat.gcd a n)) % n = 0 := by
      have hsub := Nat.ModEq.sub (Nat.le_refl (k₁ * (n / Nat.gcd a n))) hle hc (Nat.ModEq.refl (k₁ * (n / Nat.gcd a n)))
      have h0 : k₁ * (n / Nat.gcd a n) - k₁ * (n / Nat.gcd a n) = 0 := by omega
      rw [h0] at hsub
      simpa [Nat.ModEq, Nat.zero_mod] using hsub.symm
    have hsub' : (k₂ - k₁) * (n / Nat.gcd a n) = k₂ * (n / Nat.gcd a n) - k₁ * (n / Nat.gcd a n) := by
      rw [Nat.sub_mul]
    rw [hsub']
    exact Nat.dvd_of_mod_eq_zero hmod
  have hn0 : 0 < n / Nat.gcd a n := by
    exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_neZero (n := n)) (Nat.gcd_dvd_right a n)) (Nat.gcd_pos_of_pos_right a (Nat.pos_of_neZero (n := n)))
  have hpos : 0 < (k₂ - k₁) * (n / Nat.gcd a n) := by
    have hk0 : 0 < k₂ - k₁ := by omega
    exact Nat.mul_pos hk0 hn0
  have hlt : (k₂ - k₁) * (n / Nat.gcd a n) < n := by
    have hk2 : k₂ - k₁ < Nat.gcd a n := by omega
    have hdn : (Nat.gcd a n) * (n / Nat.gcd a n) = n := Nat.mul_div_cancel' (Nat.gcd_dvd_right a n)
    calc
      (k₂ - k₁) * (n / Nat.gcd a n) < Nat.gcd a n * (n / Nat.gcd a n) := Nat.mul_lt_mul_of_pos_right hk2 hn0
      _ = n := hdn
  have hm0 : (k₂ - k₁) * (n / Nat.gcd a n) = 0 := by
    have hmod : (k₂ - k₁) * (n / Nat.gcd a n) % n = 0 := Nat.mod_eq_zero_of_dvd hd
    have hmod' : (k₂ - k₁) * (n / Nat.gcd a n) % n = (k₂ - k₁) * (n / Nat.gcd a n) := Nat.mod_eq_of_lt hlt
    omega
  omega

end Chapter31

end CLRS

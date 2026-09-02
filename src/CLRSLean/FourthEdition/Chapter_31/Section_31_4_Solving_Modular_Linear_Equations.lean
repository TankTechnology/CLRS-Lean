import Mathlib
import CLRSLean.FourthEdition.Chapter_31.Section_31_3_Modular_Arithmetic

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

Deferred: none (the executable enumerator {lit}`modularLinearEquationSolver`
and its `d`-solution length bound are proved).
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

/-- The canonical solution `x₀` of `a·x ≡ b (mod n)`: compute
`(b/d)·(a/d)⁻¹ mod (n/d)` with `d = gcd(a, n)` in `ZMod (n/d)` and take the
representative. -/
def modularLinearEquationSolution (a b n : ℕ) : ℕ :=
  ((b / Nat.gcd a n : ZMod (n / Nat.gcd a n)) *
    ((a / Nat.gcd a n : ZMod (n / Nat.gcd a n))⁻¹)).val

/-- In `ZMod m`, if `a'` is coprime to `m` then `a'·((b'·a'⁻¹).val) = b'`: the
inverse exists and the reduced representative witnesses the product. -/
private lemma zmod_solution_of_coprime {m a' b' : ℕ} [NeZero m] (hcop : Nat.Coprime a' m) :
    (a' : ZMod m) * (((b' : ZMod m) * ((a' : ZMod m)⁻¹)).val : ZMod m) = (b' : ZMod m) := by
  have hu : IsUnit (a' : ZMod m) := (ZMod.isUnit_iff_coprime a' m).2 hcop
  calc
    (a' : ZMod m) * (((b' : ZMod m) * ((a' : ZMod m)⁻¹)).val : ZMod m)
        = (a' : ZMod m) * ((b' : ZMod m) * ((a' : ZMod m)⁻¹)) := by
          rw [ZMod.natCast_zmod_val]
    _ = (b' : ZMod m) * ((a' : ZMod m) * ((a' : ZMod m)⁻¹)) := by ring
    _ = (b' : ZMod m) * 1 := by rw [ZMod.mul_inv_of_unit (a' : ZMod m) hu]
    _ = (b' : ZMod m) := by simp

/--
**The canonical solution is a solution.**  For `n > 0` and `gcd(a, n) ∣ b`,
{lit}`modularLinearEquationSolution a b n` satisfies `a·x₀ ≡ b (mod n)`.
-/
theorem modularLinearEquationSolution_spec (a b n : ℕ) (hn : 0 < n) (hdvd : Nat.gcd a n ∣ b) :
    a * modularLinearEquationSolution a b n ≡ b [MOD n] := by
  let d := Nat.gcd a n
  let m := n / d
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_right a hn
  have hmpos : 0 < m := Nat.div_pos (Nat.le_of_dvd hn (Nat.gcd_dvd_right a n)) hdpos
  haveI : NeZero m := ⟨Nat.ne_of_gt hmpos⟩
  have hcop : Nat.Coprime (a / d) m := by
    dsimp [m, d]
    exact Nat.coprime_div_gcd_div_gcd hdpos
  have hz : (a / d : ZMod m) * (((b / d : ZMod m) * ((a / d : ZMod m)⁻¹)).val : ZMod m) = (b / d : ZMod m) :=
    zmod_solution_of_coprime hcop
  have hz' : (a / d : ZMod m) * (modularLinearEquationSolution a b n : ZMod m) = (b / d : ZMod m) := by
    simpa [modularLinearEquationSolution, d, m] using hz
  have hmod : a / d * modularLinearEquationSolution a b n ≡ b / d [MOD m] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    rw [Nat.cast_mul]
    exact hz'
  rw [Nat.ModEq] at hmod
  have ha' : a = d * (a / d) := by
    dsimp [d]
    exact (Nat.mul_div_cancel' (Nat.gcd_dvd_left a n)).symm
  have hb' : b = d * (b / d) := by
    dsimp [d]
    exact (Nat.mul_div_cancel' hdvd).symm
  have hn' : n = d * m := by
    dsimp [m, d]
    exact (Nat.mul_div_cancel' (Nat.gcd_dvd_right a n)).symm
  have hscaled : d * (a / d * modularLinearEquationSolution a b n) % (d * m) = d * (b / d) % (d * m) := by
    rw [Nat.mul_mod_mul_left, Nat.mul_mod_mul_left]
    rw [hmod]
  have hax : a * modularLinearEquationSolution a b n = d * (a / d * modularLinearEquationSolution a b n) := by
    calc
      a * modularLinearEquationSolution a b n = (d * (a / d)) * modularLinearEquationSolution a b n :=
        congrArg (fun z => z * modularLinearEquationSolution a b n) ha'
      _ = d * (a / d * modularLinearEquationSolution a b n) := by ring
  have h1 : a * modularLinearEquationSolution a b n % n = d * (a / d * modularLinearEquationSolution a b n) % (d * m) :=
    congrArg₂ Nat.mod hax hn'
  have h2 : d * (b / d) % (d * m) = b % n :=
    congrArg₂ Nat.mod hb'.symm hn'.symm
  calc
    a * modularLinearEquationSolution a b n % n = d * (a / d * modularLinearEquationSolution a b n) % (d * m) := h1
    _ = d * (b / d) % (d * m) := hscaled
    _ = b % n := h2

/-- For `n > 0`, `n / gcd(a, n)` is positive (the reduced modulus of §31.4). -/
private lemma gcd_div_pos (a n : ℕ) [NeZero n] : 0 < n / Nat.gcd a n := by
  have hn : 0 < n := NeZero.pos n
  have hdn : Nat.gcd a n ∣ n := Nat.gcd_dvd_right a n
  have hdpos : 0 < Nat.gcd a n := Nat.gcd_pos_of_pos_right a hn
  exact Nat.div_pos (Nat.le_of_dvd hn hdn) hdpos

/--
**MODULAR-LINEAR-EQUATION-SOLVER (CLRS §31.4).**  Enumerate the `d = gcd(a, n)`
distinct solutions of `a·x ≡ b (mod n)` as `x₀`, `x₀ + n/d`, …,
`x₀ + (d−1)·(n/d)`; return the empty list when no solution exists
(`gcd(a, n) ∤ b`).
-/
def modularLinearEquationSolver (a b n : ℕ) : List ℕ :=
  if h : Nat.gcd a n ∣ b then
    if hm : 0 < n / Nat.gcd a n then
      (List.range (Nat.gcd a n)).map
        (fun k => modularLinearEquationSolution a b n + k * (n / Nat.gcd a n))
    else []
  else []

/-- **The solver returns exactly `d` solutions when solvable, none otherwise**
(CLRS §31.4). -/
theorem modularLinearEquationSolver_length (a b n : ℕ) [NeZero n] :
    (modularLinearEquationSolver a b n).length = if Nat.gcd a n ∣ b then Nat.gcd a n else 0 := by
  by_cases h : Nat.gcd a n ∣ b
  · have hm : 0 < n / Nat.gcd a n := gcd_div_pos a n
    simp [modularLinearEquationSolver, h, hm]
  · simp [modularLinearEquationSolver, h]

/-- **Every enumerated value is a solution and lies below `n`** (CLRS §31.4). -/
theorem modularLinearEquationSolver_sound (a b n : ℕ) [NeZero n] :
    ∀ x ∈ modularLinearEquationSolver a b n, x < n ∧ a * x ≡ b [MOD n] := by
  have hn : 0 < n := NeZero.pos n
  intro x hx
  by_cases hdvd : Nat.gcd a n ∣ b
  · have hm : 0 < n / Nat.gcd a n := gcd_div_pos a n
    simp [modularLinearEquationSolver, hdvd, hm] at hx
    rcases hx with ⟨k, hk, hxeq⟩
    rw [← hxeq]
    haveI : NeZero (n / Nat.gcd a n) := NeZero.of_pos hm
    have hx₀lt : modularLinearEquationSolution a b n < n / Nat.gcd a n := by
      dsimp [modularLinearEquationSolution]
      exact ZMod.val_lt (((b / Nat.gcd a n : ZMod (n / Nat.gcd a n)) *
        ((a / Nat.gcd a n : ZMod (n / Nat.gcd a n))⁻¹)))
    have hklt : k < Nat.gcd a n := hk
    constructor
    · have hn' : n = Nat.gcd a n * (n / Nat.gcd a n) := by
        exact (Nat.mul_div_cancel' (Nat.gcd_dvd_right a n)).symm
      calc
        modularLinearEquationSolution a b n + k * (n / Nat.gcd a n)
            < n / Nat.gcd a n + k * (n / Nat.gcd a n) :=
              Nat.add_lt_add_right hx₀lt (k * (n / Nat.gcd a n))
        _ = (k + 1) * (n / Nat.gcd a n) := by ring
        _ ≤ Nat.gcd a n * (n / Nat.gcd a n) := Nat.mul_le_mul_right (n / Nat.gcd a n) (by omega)
        _ = n := hn'.symm
    · have hsol := modularLinearEquationSolution_spec a b n hn hdvd
      have hshift := linear_congruence_shift (n := n) (a := a) (b := b)
        (x := modularLinearEquationSolution a b n) (k := k) hsol
      simpa [Nat.mul_comm] using hshift
  · simp [modularLinearEquationSolver, hdvd] at hx

/-- **Every solution `x < n` is enumerated** (CLRS §31.4). -/
theorem modularLinearEquationSolver_complete (a b n : ℕ) [NeZero n] {x : ℕ}
    (hx : a * x ≡ b [MOD n]) (hlt : x < n) : x ∈ modularLinearEquationSolver a b n := by
  have hn : 0 < n := NeZero.pos n
  have hmpos : 0 < n / Nat.gcd a n := gcd_div_pos a n
  have hdvd : Nat.gcd a n ∣ b := by
    have hda : Nat.gcd a n ∣ a := Nat.gcd_dvd_left a n
    have hdn : Nat.gcd a n ∣ n := Nat.gcd_dvd_right a n
    have hx_d : a * x ≡ b [MOD Nat.gcd a n] := Nat.ModEq.of_dvd hdn hx
    have ha_d : a ≡ 0 [MOD Nat.gcd a n] := (Nat.modEq_zero_iff_dvd).2 hda
    have hb0 : b ≡ 0 [MOD Nat.gcd a n] := by
      have h0 : a * x ≡ 0 * x [MOD Nat.gcd a n] := Nat.ModEq.mul ha_d (Nat.ModEq.refl x)
      simpa using (hx_d.symm.trans h0)
    exact (Nat.modEq_zero_iff_dvd).1 hb0
  have hx₀sol : a * modularLinearEquationSolution a b n ≡ b [MOD n] :=
    modularLinearEquationSolution_spec a b n hn hdvd
  have hcong : x ≡ modularLinearEquationSolution a b n [MOD n / Nat.gcd a n] := by
    have h := (linear_congruence_solutions (a := a) (b := b)
      (x₀ := modularLinearEquationSolution a b n) (n := n) hx₀sol) x
    exact h.1 hx
  haveI : NeZero (n / Nat.gcd a n) := NeZero.of_pos hmpos
  have hx₀lt : modularLinearEquationSolution a b n < n / Nat.gcd a n := by
    dsimp [modularLinearEquationSolution]
    exact ZMod.val_lt (((b / Nat.gcd a n : ZMod (n / Nat.gcd a n)) *
      ((a / Nat.gcd a n : ZMod (n / Nat.gcd a n))⁻¹)))
  have hmod : x % (n / Nat.gcd a n) = modularLinearEquationSolution a b n := by
    rw [Nat.ModEq] at hcong
    rw [hcong]
    rw [Nat.mod_eq_of_lt hx₀lt]
  have hxeq : x = modularLinearEquationSolution a b n + (x / (n / Nat.gcd a n)) * (n / Nat.gcd a n) := by
    have hdiv := Nat.div_add_mod x (n / Nat.gcd a n)
    nth_rewrite 1 [← hdiv]
    rw [hmod]
    ring
  have hklt : x / (n / Nat.gcd a n) < Nat.gcd a n := by
    have hxlt : x < (n / Nat.gcd a n) * Nat.gcd a n := by
      have hn' : n = (n / Nat.gcd a n) * Nat.gcd a n := by
        simpa [Nat.mul_comm] using (Nat.mul_div_cancel' (Nat.gcd_dvd_right a n)).symm
      rw [hn'] at hlt
      exact hlt
    exact Nat.div_lt_of_lt_mul hxlt
  rw [modularLinearEquationSolver]
  rw [dif_pos hdvd]
  rw [dif_pos hmpos]
  rw [List.mem_map]
  refine ⟨x / (n / Nat.gcd a n), ⟨(List.mem_range).2 hklt, hxeq.symm⟩⟩

/-- **The solver produces pairwise-distinct solutions** (CLRS §31.4). -/
theorem modularLinearEquationSolver_nodup (a b n : ℕ) [NeZero n] :
    (modularLinearEquationSolver a b n).Nodup := by
  by_cases hdvd : Nat.gcd a n ∣ b
  · have hm : 0 < n / Nat.gcd a n := gcd_div_pos a n
    simp [modularLinearEquationSolver, hdvd, hm]
    refine List.Nodup.map ?hf List.nodup_range
    intro k₁ k₂ hk
    have hkm : k₁ * (n / Nat.gcd a n) = k₂ * (n / Nat.gcd a n) := Nat.add_left_cancel hk
    exact Nat.mul_right_cancel hm hkm
  · simp [modularLinearEquationSolver, hdvd]

end Chapter31

end CLRS

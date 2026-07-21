import Mathlib

/-!
# Chapter 30 — DFT and FFT

CLRS Sections 30.1-30.2: complex roots of unity, DFT, inverse DFT.

Status: core definitions complete; FFT recursion and proofs deferred.
-/

namespace CLRS
namespace Chapter30

open Complex

noncomputable def ω (n : ℕ) : ℂ := exp (2 * Real.pi * I / (n : ℂ))

noncomputable def evalPoly (a : ℕ → ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  ∑ j ∈ Finset.range n, a j * x ^ j

noncomputable def pointValues (a : ℕ → ℂ) (n : ℕ) (xs : ℕ → ℂ) : ℕ → ℂ :=
  fun k => evalPoly a n (xs k)

noncomputable def dft (n : ℕ) (a : Fin n → ℂ) (k : Fin n) : ℂ :=
  ∑ j : Fin n, a j * (ω n) ^ ((j : ℕ) * (k : ℕ))

noncomputable def idft (n : ℕ) (y : Fin n → ℂ) (j : Fin n) : ℂ :=
  (∑ k : Fin n, y k * (ω n) ^ (-(((j : ℕ) * (k : ℕ)) : ℤ))) / (n : ℂ)

theorem ω_pow_n_eq_one (n : ℕ) (hn : n ≠ 0) : (ω n) ^ n = 1 := by
  have hnz : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  calc
    (ω n) ^ n = (exp (2 * Real.pi * I / (n : ℂ))) ^ n := rfl
    _ = exp ((n : ℂ) * (2 * Real.pi * I / (n : ℂ))) := by
      rw [← Complex.exp_nat_mul]
    _ = exp (2 * Real.pi * I) := by
      congr 1
      field_simp [hnz]
    _ = 1 := Complex.exp_two_pi_mul_I

theorem ω_half_eq_neg_one (n : ℕ) (hn : n % 2 = 0) (hnpos : n ≠ 0) : (ω n) ^ (n / 2) = -1 := by
  have hnz : (n : ℂ) ≠ 0 := by exact_mod_cast hnpos
  have h2_dvd_n : 2 ∣ n := Nat.dvd_of_mod_eq_zero hn
  -- (n / 2) * 2 = n in ℕ, and therefore in ℂ
  have h_half_mul_two : ((n / 2 : ℕ) : ℂ) * 2 = (n : ℂ) := by
    have h_nat : (n / 2 : ℕ) * 2 = n := by
      rw [mul_comm, Nat.mul_div_cancel' h2_dvd_n]
    exact_mod_cast h_nat
  calc
    (ω n) ^ (n / 2) = (exp (2 * Real.pi * I / (n : ℂ))) ^ (n / 2) := rfl
    _ = exp (((n / 2 : ℕ) : ℂ) * (2 * Real.pi * I / (n : ℂ))) := by
      rw [← Complex.exp_nat_mul]
    _ = exp (Real.pi * I) := by
      congr 1
      calc
        ((n / 2 : ℕ) : ℂ) * (2 * Real.pi * I / (n : ℂ))
            = (((n / 2 : ℕ) : ℂ) * (2 * Real.pi * I)) / (n : ℂ) := by ring
        _ = ((((n / 2 : ℕ) : ℂ) * 2) * Real.pi * I) / (n : ℂ) := by ring
        _ = ((n : ℂ) * Real.pi * I) / (n : ℂ) := by rw [h_half_mul_two]
        _ = Real.pi * I := by field_simp [hnz]
    _ = -1 := Complex.exp_pi_mul_I

theorem dft_eq_evalPoly (n : ℕ) (a : Fin n → ℂ) (k : Fin n) (hn : n ≠ 0) :
    dft n a k = evalPoly (fun j => if h : j < n then a ⟨j, h⟩ else 0) n ((ω n) ^ (k : ℕ)) := by
  dsimp [dft, evalPoly]
  -- Helper: ((ω n)^(k : ℕ))^j = (ω n)^((j : ℕ)*(k : ℕ))
  have h_pow_comm (j : ℕ) : ((ω n) ^ (k : ℕ)) ^ j = (ω n) ^ (j * (k : ℕ)) := by
    calc
      ((ω n) ^ (k : ℕ)) ^ j = (ω n) ^ ((k : ℕ) * j) := (pow_mul (ω n) (k : ℕ) j).symm
      _ = (ω n) ^ (j * (k : ℕ)) := by rw [mul_comm]
  -- Define f : ℕ → ℂ to bridge Fin n sums and range n sums
  let f (j : ℕ) : ℂ := (if h : j < n then a ⟨j, h⟩ else 0) * ((ω n) ^ (k : ℕ)) ^ j
  calc
    ∑ j : Fin n, a j * (ω n) ^ ((j : ℕ) * (k : ℕ))
        = ∑ j : Fin n, a j * ((ω n) ^ (k : ℕ)) ^ (j : ℕ) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [h_pow_comm (j : ℕ)]
    _ = ∑ j : Fin n, f (j : ℕ) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      dsimp [f]
      have hj : (j : ℕ) < n := j.2
      simp [hj]
    _ = ∑ j ∈ Finset.range n, f j := by rw [Fin.sum_univ_eq_sum_range]
    _ = ∑ j ∈ Finset.range n, (fun j => if h : j < n then a ⟨j, h⟩ else 0) j * ((ω n) ^ (k : ℕ)) ^ j := rfl

/-!
## Roots of Unity Lemmas
-/

/-- Cancellation lemma: `ω_{dn}^{dk} = ω_n^k`.

This is essential for the FFT decomposition, where taking `d = 2` gives
`ω_{2n}^{2k} = ω_n^k`. -/
theorem ω_cancellation (d n k : ℕ) (hd : d ≠ 0) : (ω (d * n)) ^ (d * k) = (ω n) ^ k := by
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  dsimp [ω]
  rw [← Complex.exp_nat_mul (2 * Real.pi * I / ((d * n : ℕ) : ℂ)) (d * k)]
  rw [← Complex.exp_nat_mul (2 * Real.pi * I / (n : ℂ)) k]
  congr 1
  push_cast
  field_simp [hd']

/-- Helper: `(ω n)^k = 1` iff `n ∣ k`. -/
theorem ω_pow_eq_one_iff (n k : ℕ) (hn : n ≠ 0) : (ω n) ^ k = 1 ↔ n ∣ k := by
  dsimp [ω]
  rw [← Complex.exp_nat_mul (2 * Real.pi * I / (n : ℂ)) k]
  -- Goal: exp ((k : ℂ) * (2 * Real.pi * I / (n : ℂ))) = 1 ↔ n ∣ k
  have h_form : (k : ℂ) * (2 * Real.pi * I / (n : ℂ)) = 2 * Real.pi * I * (k : ℂ) / (n : ℂ) := by
    ring
  rw [h_form]
  -- exp (2π·I·k / n) = 1 ↔ n ∣ k  (Mathlib lemma)
  simpa using exp_two_pi_mul_I_mul_div_eq_one_iff hn

/-- Sum of geometric series of roots of unity.

`∑_{j=0}^{n-1} (ω_n)^{j·k} = n` if `n ∣ k`, else `0`.

This is the key orthogonality relation for the inverse DFT. -/
theorem ω_sum_eq_zero (n k : ℕ) (hn : n ≠ 0) :
    ∑ j ∈ Finset.range n, (ω n) ^ (j * k) = if n ∣ k then (n : ℂ) else 0 := by
  by_cases h_dvd : n ∣ k
  · -- Case n ∣ k: each term is 1, so sum = n
    rw [if_pos h_dvd]
    have h_one : ∀ j, (ω n) ^ (j * k) = 1 := by
      intro j
      rcases h_dvd with ⟨m, hm⟩
      calc
        (ω n) ^ (j * k) = (ω n) ^ (j * (n * m)) := by rw [hm]
        _ = (ω n) ^ ((j * n) * m) := by ring
        _ = ((ω n) ^ (j * n)) ^ m := by rw [pow_mul]
        _ = (((ω n) ^ n) ^ j) ^ m := by rw [mul_comm j n, pow_mul (ω n) n j]
        _ = (1 ^ j) ^ m := by rw [ω_pow_n_eq_one n hn]
        _ = 1 := by simp
    simp [h_one]
  · -- Case n ∤ k: use geometric series formula
    rw [if_neg h_dvd]
    have h_ne_one : (ω n) ^ k ≠ 1 :=
      mt ((ω_pow_eq_one_iff n k hn).mp) h_dvd
    -- Rewrite Σ (ω n)^(j*k) as Σ ((ω n)^k)^j
    have h_sum_rewrite : ∑ j ∈ Finset.range n, (ω n) ^ (j * k) =
                          ∑ j ∈ Finset.range n, ((ω n) ^ k) ^ j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_comm j k, pow_mul]
    rw [h_sum_rewrite]
    -- Apply geometric series formula: Σ_{j=0}^{n-1} r^j = (r^n - 1)/(r - 1) when r ≠ 1
    have h_geom := geom_sum_eq h_ne_one n
    rw [h_geom]
    -- Numerator: ((ω n)^k)^n - 1 = (ω n)^(k*n) - 1 = ((ω n)^n)^k - 1 = 1^k - 1 = 0
    have h_num : ((ω n) ^ k) ^ n = 1 := by
      calc
        ((ω n) ^ k) ^ n = (ω n) ^ (k * n) := by rw [pow_mul]
        _ = ((ω n) ^ n) ^ k := by rw [mul_comm k n, pow_mul]
        _ = 1 ^ k := by rw [ω_pow_n_eq_one n hn]
        _ = 1 := by simp
    rw [h_num, sub_self, zero_div]

/-!
## Inverse DFT Correctness

Proved using orthogonality of roots of unity.  The key trick is to
convert the ℤ‑power `(ω n)⁻¹` to the ℕ‑power `(ω n) ^ (n-1)`, which
lets us reuse `ω_sum_eq_zero`.
-/

/-- `(ω n)⁻¹ = (ω n) ^ (n - 1)`.  Follows from `(ω n) * (ω n)^(n-1) = (ω n)^n = 1`. -/
theorem ω_inv_eq_pow (n : ℕ) (hn : n ≠ 0) : (ω n)⁻¹ = (ω n) ^ (n - 1) := by
  have hpos : 1 ≤ n := Nat.one_le_of_lt (Nat.pos_of_ne_zero hn)
  apply inv_eq_of_mul_eq_one_right
  calc
    (ω n) * (ω n) ^ (n - 1) = (ω n) ^ (n - 1) * (ω n) := mul_comm _ _
    _ = (ω n) ^ n := by
      rw [← pow_succ, Nat.sub_add_cancel hpos]
    _ = 1 := ω_pow_n_eq_one n hn

/-- Convert the negative ℤ‑power in the IDFT to an ℕ‑power:
`(ω n) ^ (-(j*k : ℤ)) = (ω n) ^ ((n-1) * j * k)`.
This uses `(ω n)⁻¹ = (ω n)^(n-1)`. -/
theorem ω_zpow_neg_mul_eq_npow (n j k : ℕ) (hn : n ≠ 0) :
    (ω n) ^ (-(((j * k : ℕ) : ℤ))) = (ω n) ^ ((n - 1) * j * k) := by
  calc
    (ω n) ^ (-(((j * k : ℕ) : ℤ))) = ((ω n) ^ (((j * k : ℕ) : ℤ)))⁻¹ := by rw [zpow_neg]
    _ = ((ω n) ^ (j * k : ℕ))⁻¹ := by rw [zpow_natCast]
    _ = ((ω n)⁻¹) ^ (j * k : ℕ) := by rw [inv_pow]
    _ = ((ω n) ^ (n - 1)) ^ (j * k : ℕ) := by rw [ω_inv_eq_pow n hn]
    _ = (ω n) ^ ((n - 1) * (j * k)) := by rw [← pow_mul]
    _ = (ω n) ^ ((n - 1) * j * k) := by ring

/-- Orthogonality lemma tailored for the inverse DFT:
`∑_{k:Fin n} (ω n) ^ (ℓ*k) * (ω n) ^ ((n-1)*j*k) = n` if `ℓ = j`, else `0`. -/
theorem orthogonality_idft (n ℓ j : ℕ) (hℓ : ℓ < n) (hj : j < n) (hn : n ≠ 0) :
    ∑ k : Fin n,
      (ω n) ^ (ℓ * (k : ℕ)) * (ω n) ^ ((n - 1) * j * (k : ℕ)) =
    if ℓ = j then (n : ℂ) else 0 := by
  -- Combine exponents: (ℓ + (n-1)*j) * k
  have h_combine (k : Fin n) :
      (ω n) ^ (ℓ * (k : ℕ)) * (ω n) ^ ((n - 1) * j * (k : ℕ)) =
      (ω n) ^ ((ℓ + (n - 1) * j) * (k : ℕ)) := by
    calc
      (ω n) ^ (ℓ * (k : ℕ)) * (ω n) ^ ((n - 1) * j * (k : ℕ)) =
          (ω n) ^ (ℓ * (k : ℕ) + (n - 1) * j * (k : ℕ)) := by rw [pow_add]
      _ = (ω n) ^ ((ℓ + (n - 1) * j) * (k : ℕ)) := by ring
  -- Rewrite the sum using this identity
  have h_sum_eq : (∑ k : Fin n, (ω n) ^ (ℓ * (k : ℕ)) * (ω n) ^ ((n - 1) * j * (k : ℕ))) =
                 (∑ k : Fin n, (ω n) ^ ((ℓ + (n - 1) * j) * (k : ℕ))) :=
    Finset.sum_congr rfl (fun k _ => h_combine k)
  rw [h_sum_eq]
  -- Now we have Σ_k (ω n) ^ ((ℓ + (n-1)*j) * (k : ℕ))
  -- First commute the multiplication, then use Fin.sum_univ_eq_sum_range
  have h_convert : (∑ k : Fin n, (ω n) ^ ((ℓ + (n - 1) * j) * (k : ℕ))) =
                  (∑ k ∈ Finset.range n, (ω n) ^ (k * (ℓ + (n - 1) * j))) := by
    have h_comm : (∑ k : Fin n, (ω n) ^ ((ℓ + (n - 1) * j) * (k : ℕ))) =
                 (∑ k : Fin n, (ω n) ^ ((k : ℕ) * (ℓ + (n - 1) * j))) := by
      refine Finset.sum_congr rfl (λ k _ => ?_)
      rw [mul_comm]
    rw [h_comm]
    rw [Fin.sum_univ_eq_sum_range (λ x : ℕ => (ω n) ^ (x * (ℓ + (n - 1) * j)))]
  rw [h_convert]
  -- Apply ω_sum_eq_zero: sum = n if n∣(ℓ+(n-1)*j), else 0
  rw [ω_sum_eq_zero n (ℓ + (n - 1) * j) hn]
  -- Need to decide: n ∣ (ℓ + (n-1)*j) ↔ ℓ = j
  by_cases h_eq : ℓ = j
  · rw [h_eq]
    have hn_div : n ∣ (j + (n - 1) * j) := by
      use j
      calc
        j + (n - 1) * j = (1 + (n - 1)) * j := by ring
        _ = n * j := by
          have : 1 + (n - 1) = n := by omega
          rw [this]
    rw [if_pos hn_div]
    simp
  · have hn_not_div : ¬ n ∣ (ℓ + (n - 1) * j) := by
      intro hdiv
      -- hdiv: n ∣ (ℓ + (n-1)*j) in ℕ → convert to ℤ: n ∣ (ℓ - j)
      have h_int_div : (n : ℤ) ∣ ((ℓ : ℤ) - (j : ℤ)) := by
        rcases hdiv with ⟨q, hq⟩
        -- hq: ℓ + (n-1)*j = n*q in ℕ
        have hn1 : 1 ≤ n := Nat.one_le_of_lt (Nat.pos_of_ne_zero hn)
        have hq_int : (ℓ : ℤ) + ((n : ℤ) - 1) * (j : ℤ) = (n : ℤ) * (q : ℤ) := by
          push_cast
          simpa [Nat.cast_sub hn1] using congrArg (fun x : ℕ => (x : ℤ)) hq
        use ((q : ℤ) - (j : ℤ))
        nlinarith
      -- |ℓ-j| < n and n ∣ (ℓ-j) → ℓ - j = 0 → ℓ = j
      have h_diff_zero : (ℓ : ℤ) - (j : ℤ) = 0 := by
        rcases h_int_div with ⟨q, hq⟩
        by_cases hqz : q = 0
        · rw [hqz, mul_zero] at hq; omega
        · have hq_cases : q ≥ 1 ∨ q ≤ -1 := by omega
          rcases hq_cases with (hqge1 | hqle_neg1)
          · have hℓ_lt : (ℓ : ℤ) < (n : ℤ) := by exact_mod_cast hℓ
            have hj_ge : (j : ℤ) ≥ 0 := by exact_mod_cast (Nat.zero_le j)
            nlinarith
          · have hℓ_ge : (ℓ : ℤ) ≥ 0 := by exact_mod_cast (Nat.zero_le ℓ)
            have hj_lt : (j : ℤ) < (n : ℤ) := by exact_mod_cast hj
            nlinarith
      have : (ℓ : ℤ) = (j : ℤ) := by omega
      exact h_eq (by omega)
    rw [if_neg hn_not_div]
    simp [h_eq]

/-- IDFT inverts DFT: idft n (dft n a) = a. -/
theorem idft_dft (n : ℕ) (a : Fin n → ℂ) (hn : n ≠ 0) : idft n (dft n a) = a := by
  have hnz : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  ext j
  dsimp [idft, dft]
  calc
    (∑ k : Fin n,
      (∑ ℓ : Fin n, a ℓ * (ω n) ^ (ℓ.val * k.val)) * (ω n) ^ (-(((j.val * k.val : ℕ) : ℤ)))) / (n : ℂ)
        = (∑ k : Fin n,
            ∑ ℓ : Fin n,
              (a ℓ * (ω n) ^ (ℓ.val * k.val)) * (ω n) ^ (-(((j.val * k.val : ℕ) : ℤ)))) / (n : ℂ) := by
      refine congrArg (· / (n : ℂ)) (Finset.sum_congr rfl (fun k _ => ?_))
      rw [Finset.sum_mul]
    _ = (∑ ℓ : Fin n,
          ∑ k : Fin n,
            a ℓ * (ω n) ^ (ℓ.val * k.val) * (ω n) ^ (-(((j.val * k.val : ℕ) : ℤ)))) / (n : ℂ) := by
      rw [Finset.sum_comm]
    _ = (∑ ℓ : Fin n,
          a ℓ * (∑ k : Fin n,
            (ω n) ^ (ℓ.val * k.val) * (ω n) ^ (-(((j.val * k.val : ℕ) : ℤ))))) / (n : ℂ) := by
      refine congrArg (· / (n : ℂ)) (Finset.sum_congr rfl (fun ℓ _ => ?_))
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring
    _ = (∑ ℓ : Fin n,
          a ℓ * (∑ k : Fin n,
            (ω n) ^ (ℓ.val * k.val) * (ω n) ^ ((n - 1) * j.val * k.val))) / (n : ℂ) := by
      refine congrArg (· / (n : ℂ)) (Finset.sum_congr rfl (fun ℓ _ => ?_))
      refine congrArg (a ℓ * ·) (Finset.sum_congr rfl (fun k _ => ?_))
      rw [ω_zpow_neg_mul_eq_npow n j.val k.val hn]
    _ = (∑ ℓ : Fin n,
          a ℓ * (if ℓ.val = j.val then (n : ℂ) else 0)) / (n : ℂ) := by
      refine congrArg (· / (n : ℂ)) (Finset.sum_congr rfl (fun ℓ _ => ?_))
      rw [orthogonality_idft n ℓ.val j.val (ℓ.is_lt) (j.is_lt) hn]
    _ = (a j * (n : ℂ)) / (n : ℂ) := by
      have hsum : (∑ ℓ : Fin n, a ℓ * (if ℓ.val = j.val then (n : ℂ) else 0)) =
                 a j * (n : ℂ) := by
        calc
          (∑ ℓ : Fin n, a ℓ * (if ℓ.val = j.val then (n : ℂ) else 0))
              = (∑ ℓ : Fin n, if ℓ = j then a ℓ * (n : ℂ) else 0) := by
            refine Finset.sum_congr rfl (λ ℓ hℓ => ?_)
            by_cases hℓj : ℓ = j
            · subst hℓj; simp
            · have hval_ne : ℓ.val ≠ j.val := by
                intro h; apply hℓj; exact Fin.ext h
              simp [hval_ne, hℓj]
          _ = a j * (n : ℂ) := by simp
      rw [hsum]
    _ = a j := by field_simp [hnz]

/-!
## FFT Decomposition (Cooley-Tukey)

The core recursive step: split a DFT of even length into two half-size DFTs.
-/

/-- Cooley-Tukey FFT decomposition (decimation-in-time).

Splits DFT of size `2m` into two DFTs of size `m` on even-indexed
and odd-indexed elements.

For `a : Fin (2m) → ℂ` and `k : Fin m` (representing the first half of frequencies):

`DFT(2m)(a)[k] = DFT(m)(a_even)[k] + ω_{2m}^k · DFT(m)(a_odd)[k]`

where `a_even[j] = a[2j]` and `a_odd[j] = a[2j+1]` for `j : Fin m`.

The second half (`k + m`) follows from the first using `ω_{2m}^m = -1`:
`DFT(2m)(a)[k+m] = DFT(m)(a_even)[k] - ω_{2m}^k · DFT(m)(a_odd)[k]`.

═══ PROOF SKETCH ═══

Expand `DFT(2m)(a)[k] = Σ_{j:Fin(2m)} a_j · ω_{2m}^{j·k}`.

Split the sum into even `j = 2r` and odd `j = 2r+1` for `r : Fin m`:

  `Σ_r a[2r] · ω_{2m}^{2r·k}  +  Σ_r a[2r+1] · ω_{2m}^{(2r+1)·k}`

Use `ω_cancellation` with `d=2`:  `ω_{2m}^{2r·k} = ω_m^{r·k}`
(since `ω_{2m}^2 = ω_m`).

Odd terms: `ω_{2m}^{(2r+1)·k} = ω_{2m}^{2r·k} · ω_{2m}^k = ω_m^{r·k} · ω_{2m}^k`.

Factor `ω_{2m}^k` from the odd sum, recognizing:
  • `Σ_r a[2r] · ω_m^{r·k} = DFT_m(a_even)[k]`
  • `Σ_r a[2r+1] · ω_m^{r·k} = DFT_m(a_odd)[k]`

For the second half, note that `ω_{2m}^{m} = -1` (by `ω_half_eq_neg_one`),
so `ω_{2m}^{k+m} = ω_{2m}^k · ω_{2m}^m = -ω_{2m}^k`, giving the minus sign.

Remaining work for a complete formalization:
  1. Fin index arithmetic: embed `Fin m` into `Fin (2m)` via doubling
  2. Rewrite the sum over `Fin (2m)` as sum over even + odd `Fin m` indices
     (using `Finset.sum_finset_product` or manual splitting)
  3. Apply `ω_cancellation` and algebraic simplifications
-/
theorem dft_split_even_odd (m : ℕ) (a : Fin (2*m) → ℂ) (k : Fin m) (hm : m ≠ 0) :
    -- Even-indexed subsequence: a_even[j] = a[2j]
    let a_even : Fin m → ℂ := fun j => a ⟨2 * j.val, by
      have hj := j.is_lt
      omega⟩
    -- Odd-indexed subsequence: a_odd[j] = a[2j+1]
    let a_odd : Fin m → ℂ := fun j => a ⟨2 * j.val + 1, by
      have hj := j.is_lt
      omega⟩
    -- First half: DFT_{2m}(a)[k] = DFT_m(a_even)[k] + ω_{2m}^k · DFT_m(a_odd)[k]
    dft (2*m) a ⟨k.val, by
      have hk := k.is_lt
      omega⟩ = dft m a_even k + (ω (2*m))^(k.val) * dft m a_odd k := by
  intro a_even a_odd
  -- Build the bijection ψ : Fin m ⊕ Fin m → Fin (2*m)
  let ψ : Fin m ⊕ Fin m → Fin (2*m) := λ x => match x with
    | Sum.inl r => ⟨2 * r.val, by
        have h := r.is_lt
        omega⟩
    | Sum.inr r => ⟨2 * r.val + 1, by
        have h := r.is_lt
        omega⟩
  -- ψ is a bijection: construct the two-sided inverse φ
  have hψ_bijective : Function.Bijective ψ := by
    let φ : Fin (2*m) → Fin m ⊕ Fin m := λ j =>
      have h_div_lt : j.val / 2 < m := by
        apply (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)).mpr
        simpa [mul_comm] using j.is_lt
      if h : j.val % 2 = 0 then
        Sum.inl ⟨j.val / 2, h_div_lt⟩
      else
        Sum.inr ⟨j.val / 2, h_div_lt⟩
    have h_left_inv : Function.LeftInverse φ ψ := by
      intro x
      cases x with
      | inl r =>
        have hmod : (2 * r.val) % 2 = 0 := by simp
        have hdiv : (2 * r.val) / 2 = r.val := by omega
        dsimp [ψ, φ]
        simp [hmod, hdiv]
      | inr r =>
        have hmod : (2 * r.val + 1) % 2 = 1 := by simp
        have hdiv : (2 * r.val + 1) / 2 = r.val := by omega
        dsimp [ψ, φ]
        simp [hmod, hdiv]
    have h_right_inv : Function.RightInverse φ ψ := by
      intro j
      dsimp [φ]
      by_cases h : j.val % 2 = 0
      · simp [ψ, h]
        apply Fin.ext
        have hdvd : 2 ∣ j.val := Nat.dvd_of_mod_eq_zero h
        simpa using Nat.mul_div_cancel' hdvd
      · have h_mod_one : j.val % 2 = 1 := by
          have h_mod := Nat.mod_two_eq_zero_or_one j.val
          rcases h_mod with (hz | ho)
          · exact absurd hz h
          · exact ho
        have hval_eq : j.val = 2 * (j.val / 2) + 1 := by omega
        simp [ψ, h_mod_one]
        apply Fin.ext
        simpa using hval_eq.symm
    exact ⟨h_left_inv.injective, h_right_inv.surjective⟩
  -- From the bijection ψ : Fin m ⊕ Fin m → Fin (2*m), get an Equiv
  let e : Fin m ⊕ Fin m ≃ Fin (2*m) :=
    Equiv.ofBijective ψ hψ_bijective
  dsimp [dft, a_even, a_odd]
  -- Fintype.sum_equiv reindexes: Σ_x f(x) = Σ_y g(y) where f(x) = g(e(x))
  have h_reindex : (∑ j : Fin (2*m), a j * (ω (2*m)) ^ ((j.val : ℕ) * (k.val : ℕ))) =
      (∑ x : Fin m ⊕ Fin m, a (e x) * (ω (2*m)) ^ (((e x).val : ℕ) * (k.val : ℕ))) := by
    rw [← Fintype.sum_equiv e
      (λ x => a (e x) * (ω (2*m)) ^ (((e x).val : ℕ) * (k.val : ℕ)))
      (λ j => a j * (ω (2*m)) ^ ((j.val : ℕ) * (k.val : ℕ)))
      (λ _ => rfl)]
  -- Step 1: replace e(x) with ψ(x) (they are equal)
  have h_simplify : (∑ x : Fin m ⊕ Fin m, a (e x) * (ω (2*m)) ^ (((e x).val : ℕ) * (k.val : ℕ))) =
      (∑ x : Fin m ⊕ Fin m, a (ψ x) * (ω (2*m)) ^ (((ψ x).val : ℕ) * (k.val : ℕ))) := by
    simp [e, ψ]
  -- Step 2: expand ψ for inl/inr cases
  have h_expand : (∑ x : Fin m ⊕ Fin m, a (ψ x) * (ω (2*m)) ^ (((ψ x).val : ℕ) * (k.val : ℕ))) =
      (∑ r : Fin m,
        a ⟨2 * r.val, by have h := r.is_lt; omega⟩ * (ω (2*m)) ^ (((2 * r.val) : ℕ) * (k.val : ℕ))) +
      (∑ r : Fin m,
        a ⟨2 * r.val + 1, by have h := r.is_lt; omega⟩ * (ω (2*m)) ^ (((2 * r.val + 1) : ℕ) * (k.val : ℕ))) := by
    calc
      (∑ x : Fin m ⊕ Fin m, a (ψ x) * (ω (2*m)) ^ (((ψ x).val : ℕ) * (k.val : ℕ))) =
        (∑ x : Fin m ⊕ Fin m,
          (match x with
           | Sum.inl r => a ⟨2 * r.val, by
               have h := r.is_lt; omega⟩ * (ω (2*m)) ^ (((2 * r.val) : ℕ) * (k.val : ℕ))
           | Sum.inr r => a ⟨2 * r.val + 1, by
               have h := r.is_lt; omega⟩ * (ω (2*m)) ^ (((2 * r.val + 1) : ℕ) * (k.val : ℕ)))) := by
        refine Finset.sum_congr rfl (λ x _ => ?_)
        cases x with
        | inl r => simp [ψ]
        | inr r => simp [ψ]
      _ = (∑ r : Fin m,
            a ⟨2 * r.val, by have h := r.is_lt; omega⟩ * (ω (2*m)) ^ (((2 * r.val) : ℕ) * (k.val : ℕ))) +
          (∑ r : Fin m,
            a ⟨2 * r.val + 1, by have h := r.is_lt; omega⟩ * (ω (2*m)) ^ (((2 * r.val + 1) : ℕ) * (k.val : ℕ))) := by
        simp
  -- Step 3: Apply ω_cancellation and factor out ω_{2m}^k
  have h_omega_cancel (r : Fin m) : (ω (2*m)) ^ (((2 * r.val) : ℕ) * (k.val : ℕ)) = (ω m) ^ ((r.val : ℕ) * (k.val : ℕ)) := by
    calc
      (ω (2*m)) ^ (((2 * r.val) : ℕ) * (k.val : ℕ)) = (ω (2*m)) ^ ((2 : ℕ) * (r.val * k.val)) := by ring
      _ = (ω m) ^ ((r.val : ℕ) * (k.val : ℕ)) := by
        rw [ω_cancellation 2 m (r.val * k.val) (by norm_num : (2 : ℕ) ≠ 0)]
  have h_odd_term (r : Fin m) : (ω (2*m)) ^ (((2 * r.val + 1) : ℕ) * (k.val : ℕ)) =
      (ω (2*m)) ^ (k.val) * (ω m) ^ ((r.val : ℕ) * (k.val : ℕ)) := by
    calc
      (ω (2*m)) ^ (((2 * r.val + 1) : ℕ) * (k.val : ℕ))
          = (ω (2*m)) ^ ((2 * r.val * k.val) + k.val) := by ring
      _ = (ω (2*m)) ^ (2 * r.val * k.val) * (ω (2*m)) ^ (k.val) := by rw [pow_add]
      _ = (ω (2*m)) ^ (k.val) * (ω (2*m)) ^ (2 * r.val * k.val) := by ring
      _ = (ω (2*m)) ^ (k.val) * (ω (2*m)) ^ ((2 * r.val) * k.val) := by ring
      _ = (ω (2*m)) ^ (k.val) * (ω (2*m)) ^ (((2 * r.val) : ℕ) * (k.val : ℕ)) := by simp
      _ = (ω (2*m)) ^ (k.val) * (ω m) ^ ((r.val : ℕ) * (k.val : ℕ)) := by rw [h_omega_cancel r]
  have h_even_sum : (∑ r : Fin m,
      a ⟨2 * r.val, by have h := r.is_lt; omega⟩ * (ω (2*m)) ^ (((2 * r.val) : ℕ) * (k.val : ℕ))) =
    (∑ r : Fin m,
      a ⟨2 * r.val, by have h := r.is_lt; omega⟩ * (ω m) ^ ((r.val : ℕ) * (k.val : ℕ))) := by
    refine Finset.sum_congr rfl (λ r _ => ?_)
    rw [h_omega_cancel r]
  have h_odd_sum : (∑ r : Fin m,
      a ⟨2 * r.val + 1, by have h := r.is_lt; omega⟩ * (ω (2*m)) ^ (((2 * r.val + 1) : ℕ) * (k.val : ℕ))) =
    (ω (2*m)) ^ (k.val) *
    (∑ r : Fin m,
      a ⟨2 * r.val + 1, by have h := r.is_lt; omega⟩ * (ω m) ^ ((r.val : ℕ) * (k.val : ℕ))) := by
    calc
      (∑ r : Fin m,
        a ⟨2 * r.val + 1, by have h := r.is_lt; omega⟩ * (ω (2*m)) ^ (((2 * r.val + 1) : ℕ) * (k.val : ℕ))) =
      (∑ r : Fin m,
        a ⟨2 * r.val + 1, by have h := r.is_lt; omega⟩ *
        ((ω (2*m)) ^ (k.val) * (ω m) ^ ((r.val : ℕ) * (k.val : ℕ)))) := by
        refine Finset.sum_congr rfl (λ r _ => ?_)
        rw [h_odd_term r]
      _ = (∑ r : Fin m,
        ((ω (2*m)) ^ (k.val)) * (a ⟨2 * r.val + 1, by have h := r.is_lt; omega⟩ *
        (ω m) ^ ((r.val : ℕ) * (k.val : ℕ)))) := by
        refine Finset.sum_congr rfl (λ r _ => ?_)
        ring
      _ = (ω (2*m)) ^ (k.val) *
        (∑ r : Fin m,
          a ⟨2 * r.val + 1, by have h := r.is_lt; omega⟩ * (ω m) ^ ((r.val : ℕ) * (k.val : ℕ))) := by
        rw [Finset.mul_sum]
  -- Combine all steps
  calc
    dft (2*m) a ⟨k.val, by have hk := k.is_lt; omega⟩
        = ∑ j : Fin (2*m), a j * (ω (2*m)) ^ ((j.val : ℕ) * (k.val : ℕ)) := rfl
    _ = (∑ r : Fin m,
          a ⟨2 * r.val, by have h := r.is_lt; omega⟩ * (ω m) ^ ((r.val : ℕ) * (k.val : ℕ))) +
        (ω (2*m)) ^ (k.val) *
        (∑ r : Fin m,
          a ⟨2 * r.val + 1, by have h := r.is_lt; omega⟩ * (ω m) ^ ((r.val : ℕ) * (k.val : ℕ))) := by
      rw [h_reindex, h_simplify, h_expand, h_even_sum, h_odd_sum]
    _ = dft m a_even k + (ω (2*m))^(k.val) * dft m a_odd k := rfl

/-!
## FFT Correctness

For power-of-two sizes, the recursive FFT (using `dft_split_even_odd`) computes the DFT.
-/

/- The recursive FFT algorithm (power-of-two sizes only).

Base case n=1: identity.
Recursive case n=2m: apply dft_split_even_odd, recursing on half-size DFT.

This definition uses strong recursion on n. A complete implementation would use
Nat.strongRec or WellFounded.fix with the hypothesis that n is a power of two. -/
noncomputable def fftPow2 (n : ℕ) (hpow : ∃ k, n = 2^k) (a : Fin n → ℂ) : Fin n → ℂ :=
  -- Deferred: implementation requires dependent pattern matching on the power-of-2 proof
  -- and recursive calls on n/2.
  a  -- placeholder

/- Correctness: FFT computes the DFT for power-of-two sizes.

PROOF SKETCH:

By strong induction on n (equivalently, on k where n = 2^k).

Base case n = 1 (k = 0): size-1 DFT is the identity; fftPow2 is the identity. Trivial.

Inductive step n = 2m where m = 2^{k-1} > 0:
  fftPow2 n a
    = combine(fftPow2 m a_even, fftPow2 m a_odd)   (by definition of fftPow2)
    = combine(DFT_m a_even, DFT_m a_odd)            (by induction hypothesis)
    = DFT_{2m} a                                    (by dft_split_even_odd)

where combine implements the Cooley-Tukey butterfly:
  combine(A, B)(j) = A(j) + w^j * B(j)          for j < m
  combine(A, B)(j+m) = A(j) - w^j * B(j)        for j < m
  where w = omega_{2m}.

Remaining work:
  1. Complete the definition of fftPow2 using Nat.strongRec
  2. Prove dft_split_even_odd (the core decomposition lemma)
  3. Induction on k (or strong induction on n) using the power-of-2 hypothesis
-/
theorem fftPow2_eq_dft (n : ℕ) (a : Fin n → ℂ) (hpow : ∃ k, n = 2^k) (hn : n ≠ 0) :
    fftPow2 n hpow a = dft n a := by
  -- NOTE: This theorem cannot currently be proved because `fftPow2` is a
  -- placeholder defined as the identity function (`a`), which differs from
  -- the true DFT in general. The proof depends on two items that must be
  -- completed first:
  --
  -- 1. `fftPow2` must be properly defined using `Nat.strongRec` (or
  --    `WellFounded.fix`) to implement the recursive Cooley-Tukey algorithm:
  --    * Base case n = 1: return a unchanged (size-1 DFT is identity).
  --    * Recursive case n = 2m (m = 2^{k-1} > 0):
  --        let a_even[j] = a[2j], a_odd[j] = a[2j+1] for j < m
  --        let A = fftPow2 m a_even
  --        let B = fftPow2 m a_odd
  --        for j < m:
  --          result[j]     = A[j] + ω_{2m}^j * B[j]
  --          result[j + m] = A[j] - ω_{2m}^j * B[j]
  --
  -- 2. `dft_split_even_odd` must be proved (the core decomposition lemma).
  --    This lemma states that DFT_{2m}(a) can be computed from DFT_m(a_even)
  --    and DFT_m(a_odd) using the butterfly operation described above.
  --
  -- PROOF SKETCH (once dependencies are met):
  --
  -- By strong induction on n (equivalently, on k where n = 2^k).
  --
  -- Base case n = 1 (k = 0): A size-1 DFT is the identity since
  --   dft 1 a 0 = a 0 * (ω 1)^{0*0} = a 0 * 1 = a 0.
  --   And fftPow2 1 ... a = a (by the base case of the recursive definition).
  --
  -- Inductive step n = 2m where m = 2^{k-1} > 0:
  --   By definition of fftPow2 (once properly implemented):
  --     fftPow2 n a
  --       = combine(fftPow2 m a_even, fftPow2 m a_odd)
  --   By induction hypothesis (n/2 < n since n > 1):
  --     fftPow2 m a_even = DFT_m a_even
  --     fftPow2 m a_odd  = DFT_m a_odd
  --   By `dft_split_even_odd`:
  --     combine(DFT_m a_even, DFT_m a_odd) = DFT_{2m} a
  --   Therefore fftPow2 n a = DFT_n a.
  --
  -- The combine operation must also be proven to satisfy the butterfly
  -- formula used in the second half of dft_split_even_odd (which uses
  -- ω_{2m}^m = -1 for the minus sign).
  sorry

end Chapter30
end CLRS

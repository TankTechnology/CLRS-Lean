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

Provides a detailed proof sketch using orthogonality of roots of unity.
A complete formalization requires additional lemmas for integer exponents and sum swapping.
-/

theorem idft_dft (n : ℕ) (a : Fin n → ℂ) (hn : n ≠ 0) : idft n (dft n a) = a := by
  have hnz : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  ext j
  dsimp [idft, dft]
  -- Goal:
  --   (∑ k : Fin n, (∑ ℓ : Fin n, a ℓ * (ω n)^(ℓ.val * k.val)) * (ω n)^(-(((j.val*k.val) : ℤ)))) / (n : ℂ)
  --   = a j
  --
  -- ═══ PROOF SKETCH (orthogonality of roots of unity) ═══
  --
  -- Step 1 — Swap the double sum (Fubini):
  --   Σ_k (Σ_ℓ a_ℓ · ω^{ℓ·k}) · ω^{-j·k}
  --     = Σ_ℓ a_ℓ · (Σ_k ω^{ℓ·k} · ω^{-j·k})
  --     = Σ_ℓ a_ℓ · (Σ_k ω^{(ℓ-j)·k})
  --   (Uses Finset.sum_comm and zpow_add for integer exponents.)
  --
  -- Step 2 — Apply orthogonality (ω_sum_eq_zero generalized to ℤ differences):
  --   Lemma orthogonality_int (m : ℤ) :
  --     Σ k : Fin n, (ω n)^(m * (k : ℤ)).toNat = if (n : ℤ) ∣ m then (n : ℂ) else 0
  --   Here m = ℓ - j.
  --   • If ℓ = j (as Fin n), then m = 0, so n ∣ 0, sum = n.
  --   • If ℓ ≠ j, then 0 < |ℓ - j| < n, so n ∤ (ℓ - j), sum = 0.
  --
  -- Step 3 — Conclusion:
  --   The double sum simplifies to a_j · n, and dividing by (n : ℂ) gives a_j.
  --
  -- Remaining work for a complete formalization:
  --   1. Lemma `zpow_ω_mul` : (ω n)^(a:ℤ) * (ω n)^(b:ℤ) = (ω n)^(a+b:ℤ)
  --      (follows from `zpow_add` for groups)
  --   2. Lemma `orthogonality_int` — the ℤ version of `ω_sum_eq_zero`
  --   3. `Finset.sum_comm` to swap the double sum
  --   4. Case analysis: `if h : ℓ = j then ... else ...` with Fin equality
  --   5. Division by `(n : ℂ)` after extracting the factor
  sorry

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
  -- Proof sketch above. A full formalization needs the steps outlined in the comments.
  sorry

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
  -- Proof sketch above. Depends on completing dft_split_even_odd and fftPow2.
  sorry

end Chapter30
end CLRS

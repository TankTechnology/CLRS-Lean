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

theorem idft_dft (n : ℕ) (a : Fin n → ℂ) (hn : n ≠ 0) : idft n (dft n a) = a := by
  have hnz : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  ext j
  dsimp [idft, dft]
  -- Goal:
  --   (∑ k : Fin n, (∑ ℓ : Fin n, a ℓ * (ω n) ^ (ℓ.val * k.val)) * (ω n) ^ (-(((j : ℕ) * (k : ℕ)) : ℤ))) / (n : ℂ)
  --   = a j
  --
  -- Proof sketch using orthogonality of roots of unity:
  -- Let ζ := ω n.  We have ζ^n = 1 by ω_pow_n_eq_one.
  --
  -- Define ζpow (t : ℤ) : ℂ := ζ ^ t  (where negative exponents give ζ⁻¹ ^ (-t)).
  -- The key orthogonality lemma:
  --
  --   lemma orthogonality (m : ℤ) :
  --     ∑ k : Fin n, (ω n) ^ ((m * (k : ℤ)) % (n : ℤ)).toNat =
  --       if m % (n : ℤ) = 0 then (n : ℂ) else 0 := ...
  --
  -- Once we have orthogonality, the computation unfolds as:
  --
  --   ∑_k ∑_ℓ a_ℓ * ζ^(ℓ*k) * ζ^(-(j*k : ℤ))
  --     = ∑_ℓ a_ℓ * (∑_k ζ^((ℓ - j)*k))
  --     = a_j * (n : ℂ)   (since inner sum is n when ℓ=j and 0 otherwise)
  --
  -- Dividing by (n : ℂ) gives a_j.
  --
  -- Remaining work:
  --   1. Lemma ω_pow_int : (ω n) ^ (m : ℤ) is defined coherently with ℕ exponents
  --   2. Lemma orthogonality: ∑_{k:Fin n} (ω n)^(m*k) = n if m ≡ 0 mod n, else 0
  --   3. Fubini-style sum swap: interchanging the double sum
  --   4. Case split ℓ = j vs ℓ ≠ j
  sorry

end Chapter30
end CLRS

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
  sorry

theorem ω_half_eq_neg_one (n : ℕ) (hn : n % 2 = 0) (hnpos : n ≠ 0) : (ω n) ^ (n / 2) = -1 := by
  sorry

theorem dft_eq_evalPoly (n : ℕ) (a : Fin n → ℂ) (k : Fin n) (hn : n ≠ 0) :
    dft n a k = evalPoly (fun j => if h : j < n then a ⟨j, h⟩ else 0) n ((ω n) ^ (k : ℕ)) := by
  sorry

theorem idft_dft (n : ℕ) (a : Fin n → ℂ) (hn : n ≠ 0) : idft n (dft n a) = a := by
  sorry

end Chapter30
end CLRS

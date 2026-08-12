import CLRSLean.Chapter_31

namespace CLRS
namespace Chapter31

-- Section 31.1: elementary number-theoretic notions
#check IsGCD
#check nat_gcd_isGCD
#check IsGCD.eq_gcd
#check divides_refl
#check divides_zero
#check divides_trans
#check divides_mul_right
#check divides_add
#check divides_sub
#check divides_linear_combination
#check division_unique
#check division_theorem
#check coprime_iff_gcd_eq_one
#check coprime_iff_no_common_divisor
#check prime_def_gt_one
#check prime_two
#check exists_prime_ge

-- Section 31.2: greatest common divisor
#check euclid_recursion
#check gcd_zero_left
#check gcd_zero_right
#check euclid
#check euclid_eq_gcd
#check euclid_terminates
#check gcd_is_linear_combination
#check gcd_dvd_linear_combination
#check gcd_le_positive_linear_combination
#check gcd_is_smallest_positive_linear_combination
#check gcd_eq_one_iff_coprime
#check coprime_iff_one_linear_combination
#check gcd_div_gcd_coprime
#check extendedEuclid
#check extendedEuclid_spec

-- Sections 31.3-31.9: modular arithmetic through factorization
#check mod_add
#check mod_mul
#check modEq_add
#check modEq_mul
#check modEq_pow
#check exists_mul_inverse_mod
#check mul_left_cancel_mod
#check modular_linear_solvable
#check linear_congruence_shift
#check linear_congruence_all_solutions
#check chinese_remainder_two
#check chinese_remainder_unique
#check chinese_remainder
#check modularExponentiation
#check modularExponentiation_spec
#check fermat_little_theorem
#check euler_theorem
#check totient_mul_prime
#check rsa_correct
#check fermat_test
#check fermatPseudoprime
#check pseudoprime
#check pseudoprime_correct
#check rhoStep
#check rho_collision_factor
#check nontrivial_factor_of_gcd

-- Sanity checks: EUCLID computes a concrete gcd, and the division theorem
-- picks out the expected quotient and remainder.
example : euclid 48 18 = 6 := by native_decide

example : Nat.gcd 48 18 = 6 := by native_decide

example (a : ℕ) : a ∣ a * 2 := divides_mul_right (divides_refl a)

example {a b : ℕ} (h : Nat.Coprime a b) : ∃ x y : ℤ, 1 = x * (a : ℤ) + y * (b : ℤ) :=
  coprime_iff_one_linear_combination.mp h

end Chapter31
end CLRS

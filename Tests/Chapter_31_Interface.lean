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

-- Sanity checks: EUCLID computes a concrete gcd, and the division theorem
-- picks out the expected quotient and remainder.
example : euclid 48 18 = 6 := by native_decide

example : Nat.gcd 48 18 = 6 := by native_decide

example (a : ℕ) : a ∣ a * 2 := divides_mul_right (divides_refl a)

example {a b : ℕ} (h : Nat.Coprime a b) : ∃ x y : ℤ, 1 = x * (a : ℤ) + y * (b : ℤ) :=
  coprime_iff_one_linear_combination.mp h

end Chapter31
end CLRS

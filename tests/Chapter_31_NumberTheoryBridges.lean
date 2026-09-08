import CLRSLean.FourthEdition.Chapter_31.Section_31_2_Greatest_Common_Divisor.Execution
import CLRSLean.FourthEdition.Chapter_31.Section_31_7_RSA.KeyRoundTrip
import CLRSLean.Audit.Axioms
open CLRS.Chapter31

#check euclidWithCount_spec
#check rsaKeyGen_roundTrip
#guard euclidWithCount 8 3 == (1, 4)
#guard euclidWithCount 3 8 == (1, 3)
#guard euclidWithCount 0 8 == (8, 0)
#guard euclidWithCount 8 0 == (8, 1)

example (a b : Nat) : (euclidWithCount a b).2 = euclidDivisions b a := euclidWithCount_count a b
example (a b : Nat) : (euclidWithCount a b).1 = Nat.gcd a b := by
  rw [euclidWithCount_value, euclid_eq_gcd]

-- A message sharing a factor with the generated modulus is still recovered.
example : rsaDecrypt (rsaKeyGen 3 5 3).2.2 (rsaKeyGen 3 5 3).1
    (rsaEncrypt (rsaKeyGen 3 5 3).2.1 (rsaKeyGen 3 5 3).1 6) = 6 :=
  rsaKeyGen_roundTrip 3 5 3 6 (by decide) (by decide) (by decide) (by decide) (by decide)
example : rsaDecrypt (rsaKeyGen 2 3 1).2.2 (rsaKeyGen 2 3 1).1
    (rsaEncrypt (rsaKeyGen 2 3 1).2.1 (rsaKeyGen 2 3 1).1 0) = 0 :=
  rsaKeyGen_roundTrip 2 3 1 0 (by decide) (by decide) (by decide) (by decide) (by decide)
example (m : Nat) : rsaDecrypt (rsaKeyGen 3 5 3).2.2 (rsaKeyGen 3 5 3).1
    (rsaEncrypt (rsaKeyGen 3 5 3).2.1 (rsaKeyGen 3 5 3).1 m) = m % 15 :=
  rsaKeyGen_roundTrip_mod 3 5 3 m (by decide) (by decide) (by decide) (by decide)

#assert_axioms euclidWithCount_spec
#assert_axioms rsaKeyGen_roundTrip_mod
#assert_axioms rsaKeyGen_roundTrip

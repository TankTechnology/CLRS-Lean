import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactPolynomialClock

namespace CLRS.Chapter34.Turing.PolyBuilder

#check sentinelInput
#check sentinelInput_computableInPolyTime
#check TuplePower
#check tuplePower
#check tuplePower_length
#check tuplePower_computableInPolyTime
#check tuplePrefixMatches
#check exactMonomialClock
#check exactMonomialClock_length
#check exactMonomialClock_computableInPolyTime
#check exactPolynomialClock
#check exactPolynomialClock_length
#check exactPolynomialClock_computableInPolyTime

example : (exactMonomialClock 3 [true, false]).length = 8 := by
  native_decide

example : (exactMonomialClock 0 ([] : List Bool)).length = 1 := by
  native_decide

example :
    (exactPolynomialClock
      ((3 : Polynomial Nat) * Polynomial.X ^ 2 + 2 * Polynomial.X + 5)
      [true, false]).length = 21 := by
  rw [exactPolynomialClock_length]
  norm_num [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X]

example :
    (exactPolynomialClock (7 : Polynomial Nat) ([] : List Bool)).length = 7 := by
  rw [exactPolynomialClock_length]
  norm_num

end CLRS.Chapter34.Turing.PolyBuilder

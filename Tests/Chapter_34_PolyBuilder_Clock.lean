import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Clock

namespace CLRS.Chapter34.Turing.PolyBuilder

#check unitClockBody
#check unitClock
#check unitClock_length
#check unitClock_computableInPolyTime
#check squareUnitClockBody
#check squareUnitClock
#check squareUnitClock_length
#check squareUnitClock_computableInPolyTime
#check iteratedSquareClock
#check iteratedSquareClock_length
#check iteratedSquareClock_computableInPolyTime
#check scaleUnitClock
#check scaleUnitClock_length
#check scaleUnitClock_computableInPolyTime
#check polynomialClockCoefficient
#check polynomialClock
#check polynomialClock_length
#check polynomial_eval_le_polynomialClock_length
#check polynomialClock_computableInPolyTime

example : unitClock ([true, false, true] : List Bool) = [(), (), ()] := by
  native_decide

example : (iteratedSquareClock 2 ([true, false] : List Bool)).length = 16 := by
  native_decide

end CLRS.Chapter34.Turing.PolyBuilder

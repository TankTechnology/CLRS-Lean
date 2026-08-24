import CLRSLean.Chapter_34.BinaryNat

open CLRS.Chapter34
open CLRS.Chapter34.Turing.BinaryNat

#check Adder.binaryNatValue_addWords
#check Adder.binaryNatValue_add_encoded
#check Adder.computableInPolyTime

example :
    binaryNatValue
        (Adder.addWords (encodeBinaryNat 5) (encodeBinaryNat 7)) = 12 := by
  simpa using Adder.binaryNatValue_add_encoded 5 7

#print axioms Adder.binaryNatValue_add_encoded
#print axioms Adder.computableInPolyTime

import CLRSLean.Chapter_34.BinaryNat

/-!
# Frozen interface: compact natural-number fields for strict Chapter 34 languages

The semantic decoder returns a `Nat`, but the fixed machine validates the
compact representation without expanding it to unary.  Expanding an `m`-bit
number to a unary output can require `2 ^ m` cells and therefore cannot be a
polynomial-time codec operation.
-/

#check CLRS.Chapter34.decodeBinaryNat_encode
#check CLRS.Chapter34.encodeBinaryNat_length_le
#check CLRS.Chapter34.Turing.BinaryNat.encoderComputableInPolyTime
#check CLRS.Chapter34.Turing.BinaryNat.validatorComputableInPolyTime

#print axioms CLRS.Chapter34.decodeBinaryNat_encode
#print axioms CLRS.Chapter34.Turing.BinaryNat.encoderComputableInPolyTime
#print axioms CLRS.Chapter34.Turing.BinaryNat.validatorComputableInPolyTime

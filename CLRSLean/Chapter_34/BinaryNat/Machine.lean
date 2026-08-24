import CLRSLean.Chapter_34.BinaryNat.Machine.Encoder.Runtime
import CLRSLean.Chapter_34.BinaryNat.Machine.Validator
import CLRSLean.Chapter_34.BinaryNat.Machine.Adder

/-!
# Fixed-machine interface for compact natural-number fields
-/

noncomputable section

namespace CLRS.Chapter34.Turing.BinaryNat

/-- Encode the length of a Boolean word as a canonical compact natural.
The Boolean values are ignored, so callers can first map any finite unary
clock alphabet to `Bool`. -/
noncomputable def encoderComputableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List Bool =>
        CLRS.Chapter34.encodeBinaryNat input.length) :=
  Encoder.computableInPolyTime

end CLRS.Chapter34.Turing.BinaryNat

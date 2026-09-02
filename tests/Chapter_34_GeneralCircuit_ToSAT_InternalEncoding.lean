import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.InternalEncoding

namespace CLRS.Chapter34

#check NormalizedCircuitSym
#check encodeNormalizedNat
#check decodeNormalizedNat
#check encodeNormalizedCircuit
#check decodeNormalizedCircuit
#check decode_encodeNormalizedCircuit
#check normalizeGeneralCircuit
#check normalizeGeneralCircuit_eq_invalid_iff
#check normalizeGeneralCircuit_eq_valid_iff
#check encodeNormalizedCircuit_length_le
#check normalizeGeneralCircuit_length_le

private def constantCircuit : Circuit :=
  { inputCount := 0, gates := [.const true], output := 0 }

example :
    decodeNormalizedCircuit (encodeNormalizedCircuit constantCircuit) =
      some constantCircuit :=
  decode_encodeNormalizedCircuit _

example : decodeNormalizedCircuit [.invalidMark] = none := by
  rfl

example :
    decodeNormalizedCircuit
        (encodeNormalizedCircuit constantCircuit ++ [.tick]) = none := by
  native_decide

end CLRS.Chapter34

import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Encoding

namespace CLRS.Chapter34

private def triangle : CliqueInstance where
  vertexCount := 3
  targetSize := 3
  edges := [(0, 1), (0, 2), (1, 2)]

#check encodeCliqueInstance_length
#check decodeCliqueInstance_fields_le_length

example : decodeCliqueInstance (encodeCliqueInstance triangle) = some triangle := by
  exact decode_encodeCliqueInstance triangle

example : decodeCliqueCertificate (encodeCliqueCertificate [0, 1, 2]) =
    some [0, 1, 2] := by
  exact decode_encodeCliqueCertificate [0, 1, 2]

example : (encodeCliqueInstance triangle).length = 24 := by native_decide

example : triangle.vertexCount + triangle.targetSize + 3 ≤
    (encodeCliqueInstance triangle).length := by
  exact decodeCliqueInstance_fields_le_length
    (decode_encodeCliqueInstance triangle)

example : decodeCliqueInstance [] = none := by native_decide

example : decodeCliqueInstance [.certificateMark] = none := by native_decide

example : decodeCliqueInstance [.instanceMark, .fieldSep] = none := by native_decide

example : decodeCliqueInstance
    [.instanceMark, .fieldSep, .fieldSep, .edgeMark, .tick] = none := by
  native_decide

example : decodeCliqueInstance
    [.instanceMark, .fieldSep, .fieldSep, .vertexMark, .recordEnd] = none := by
  native_decide

example : decodeCliqueCertificate [.certificateMark, .vertexMark, .tick] = none := by
  native_decide

example : decodeCliqueCertificate
    [.certificateMark, .vertexMark, .recordEnd, .fieldSep] = none := by
  native_decide

end CLRS.Chapter34

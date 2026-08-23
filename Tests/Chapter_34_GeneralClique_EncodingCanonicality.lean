import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Encoding.Canonicality

open CLRS Chapter34

#check prepend_consumeCliqueTicks
#check eq_flatMap_encodeCliqueEdge_of_decodeCliqueEdges_eq_some
#check eq_flatMap_encodeCliqueVertex_of_decodeCliqueVertices_eq_some
#check encodeCliqueInstance_eq_of_decode_eq_some
#check encodeCliqueCertificate_eq_of_decode_eq_some

example (I : CliqueInstance) :
    encodeCliqueInstance I = encodeCliqueInstance I :=
  encodeCliqueInstance_eq_of_decode_eq_some
    (encodeCliqueInstance I) I (decode_encodeCliqueInstance I)

example (vertices : List Nat) :
    encodeCliqueCertificate vertices = encodeCliqueCertificate vertices :=
  encodeCliqueCertificate_eq_of_decode_eq_some
    (encodeCliqueCertificate vertices) vertices
    (decode_encodeCliqueCertificate vertices)

example :
    [.edgeMark, .tick, .pairSep, .tick, .tick, .recordEnd] =
      [(1, 2)].flatMap encodeCliqueEdge := by
  apply eq_flatMap_encodeCliqueEdge_of_decodeCliqueEdges_eq_some
  decide

import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.Encoding.RoundTrip
import Mathlib.Tactic

/-!
# Canonicality of successful decision-TSP decodes

The parser rejects every noncanonical compact natural and every malformed
delimiter layout.  Consequently, a successful parse reconstructs the exact
word produced by the corresponding encoder.
-/

namespace CLRS.Chapter34

private def TSPFieldCanonical (reversed : List Bool)
    (input : List TSPSym) : Prop :=
  ∀ values, decodeTSPField reversed input = some values →
    ∃ value rest,
      values = value :: rest ∧
      reversed.reverse.map TSPSym.bit ++ input =
        (encodeBinaryNat value).map TSPSym.bit ++
          .fieldEnd :: (encodeTSPFields rest ++ [.recordEnd])

/-- A successful field-list parse consumes exactly the canonical serialization
of the returned natural numbers. -/
theorem eq_encodeTSPFields_append_recordEnd_of_decode_eq_some
    (input : List TSPSym) (values : List Nat)
    (hdecode : decodeTSPFields input = some values) :
    input = encodeTSPFields values ++ [.recordEnd] := by
  let fieldsMotive := fun input : List TSPSym =>
    ∀ values, decodeTSPFields input = some values →
      input = encodeTSPFields values ++ [.recordEnd]
  let fieldMotive := fun reversed input =>
    TSPFieldCanonical reversed input
  have hall : fieldsMotive input := by
    refine decodeTSPFields.induct fieldsMotive fieldMotive
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ input
    · dsimp [fieldsMotive]
      intro result h
      simp [decodeTSPFields] at h
      subst result
      rfl
    · intro fieldInput hfield
      dsimp [fieldsMotive, fieldMotive, TSPFieldCanonical] at hfield ⊢
      intro result h
      simp only [decodeTSPFields] at h
      rcases hfield result h with ⟨value, rest, rfl, hencoded⟩
      simpa [encodeTSPFields, encodeTSPField, List.append_assoc] using
        congrArg (List.cons .numberMark) hencoded
    · intro current hrecord hnumber
      dsimp [fieldsMotive]
      intro result h
      cases current with
      | nil => simp [decodeTSPFields] at h
      | cons symbol rest =>
          cases symbol with
          | recordEnd =>
              cases rest with
              | nil => exact (hrecord rfl).elim
              | cons next tail => simp [decodeTSPFields] at h
          | numberMark => exact (hnumber rest rfl).elim
          | instanceMark | certificateMark | bit | fieldEnd =>
              simp [decodeTSPFields] at h
    · intro reversed bit rest hfield
      dsimp [fieldMotive, TSPFieldCanonical] at hfield ⊢
      intro result h
      simp only [decodeTSPField] at h
      rcases hfield result h with ⟨value, values, rfl, hencoded⟩
      refine ⟨value, values, rfl, ?_⟩
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        hencoded
    · intro reversed rest value values hvalues hvalue hfields
      dsimp [fieldMotive, TSPFieldCanonical]
      intro result h
      simp [decodeTSPField, hvalue, hvalues] at h
      subst result
      refine ⟨value, values, rfl, ?_⟩
      have hvalueEncoded := encodeBinaryNat_of_decode_eq_some hvalue
      have hrestEncoded := hfields values hvalues
      rw [hvalueEncoded, hrestEncoded]
    · intro reversed rest hmissing hfields
      dsimp [fieldMotive, TSPFieldCanonical]
      intro result h
      simp only [decodeTSPField] at h
      generalize hvalue : decodeBinaryNat reversed.reverse = valueResult at h
      generalize hvalues : decodeTSPFields rest = valuesResult at h
      cases valueResult <;> cases valuesResult <;> simp_all
    · intro current reversed hbit hfieldEnd
      dsimp [fieldMotive, TSPFieldCanonical]
      intro result h
      cases current with
      | nil => simp [decodeTSPField] at h
      | cons symbol rest =>
          cases symbol with
          | bit value => exact (hbit value rest rfl).elim
          | fieldEnd => exact (hfieldEnd rest rfl).elim
          | instanceMark | certificateMark | numberMark | recordEnd =>
              simp [decodeTSPField] at h
  exact hall values hdecode

/-- Every successfully decoded raw instance is already its canonical
complete-matrix encoding. -/
theorem encodeTSPData_eq_of_decode_eq_some
    (input : List TSPSym) (data : TSPData)
    (hdecode : decodeTSPData input = some data) :
    encodeTSPData data = input := by
  cases input with
  | nil => simp [decodeTSPData] at hdecode
  | cons symbol payload =>
      cases symbol <;> try simp [decodeTSPData] at hdecode
      case instanceMark =>
        generalize hfields : decodeTSPFields payload = result at hdecode
        cases result with
        | none => simp [decodeTSPData, hfields] at hdecode
        | some fields =>
            cases fields with
            | nil => simp [decodeTSPData, hfields] at hdecode
            | cons vertexCount rest =>
                cases rest with
                | nil => simp [decodeTSPData, hfields] at hdecode
                | cons budget weights =>
                    simp only [decodeTSPData, hfields, Option.some.injEq] at hdecode
                    subst data
                    have hcanonical :=
                      eq_encodeTSPFields_append_recordEnd_of_decode_eq_some
                        payload (vertexCount :: budget :: weights) hfields
                    simp [encodeTSPData, hcanonical]

/-- Every successfully decoded raw certificate is already its canonical
ordered-tour encoding. -/
theorem encodeTSPCertificate_eq_of_decode_eq_some
    (input : List TSPSym) (vertices : List Nat)
    (hdecode : decodeTSPCertificate input = some vertices) :
    encodeTSPCertificate vertices = input := by
  cases input with
  | nil => simp [decodeTSPCertificate] at hdecode
  | cons symbol payload =>
      cases symbol <;> try simp [decodeTSPCertificate] at hdecode
      case certificateMark =>
        have hpayload :=
          eq_encodeTSPFields_append_recordEnd_of_decode_eq_some
            payload vertices hdecode
        simp [encodeTSPCertificate, hpayload]

end CLRS.Chapter34

import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.VerifierMachine.Syntax
import Mathlib.Tactic

/-! # Exact semantics of the SUBSET-SUM syntax automata -/

namespace CLRS.Chapter34.Turing.SubsetSumVerifier.Syntax

@[simp] theorem finalMode_nil (mode : Mode) : finalMode mode [] = mode := rfl

@[simp] theorem finalMode_cons (mode : Mode) (symbol : SubsetSumSym)
    (rest : List SubsetSumSym) :
    finalMode mode (symbol :: rest) = finalMode (nextMode mode symbol) rest :=
  rfl

@[simp] theorem finalMode_invalid (input : List SubsetSumSym) :
    finalMode .invalid input = .invalid := by
  induction input with
  | nil => rfl
  | cons symbol rest ih =>
      rw [finalMode_cons]
      simpa [nextMode] using ih

private theorem finalMode_append (mode : Mode)
    (left right : List SubsetSumSym) :
    finalMode mode (left ++ right) =
      finalMode (finalMode mode left) right := by
  simp [finalMode, List.foldl_append]

private theorem ended_eq_ended_iff (input : List SubsetSumSym) :
    finalMode .ended input = .ended ↔ input = [] := by
  cases input with
  | nil => simp
  | cons symbol rest => simp [nextMode, finalMode_invalid]

private theorem accepts_iff_ended (mode : Mode) :
    modeAccepts mode = true ↔ mode = .ended := by
  cases mode <;> simp [modeAccepts]

private theorem positive_ended (input : List SubsetSumSym)
    (h : finalMode .fieldPositive input = .ended) :
    ∃ bits : List Bool, ∃ rest : List SubsetSumSym,
      input = bits.map TSPSym.bit ++ .fieldEnd :: rest ∧
      finalMode .instanceBetween rest = .ended := by
  induction input with
  | nil => simp at h
  | cons symbol tail ih =>
      cases symbol with
      | bit value =>
          have htail : finalMode .fieldPositive tail = .ended := by
            simpa [nextMode] using h
          rcases ih htail with ⟨bits, rest, hshape, hend⟩
          exact ⟨value :: bits, rest, by simp [hshape], hend⟩
      | fieldEnd =>
          exact ⟨[], tail, rfl, by simpa [nextMode] using h⟩
      | instanceMark | certificateMark | numberMark | recordEnd =>
          simp [nextMode, finalMode_invalid] at h

private theorem singleZero_ended (input : List SubsetSumSym)
    (h : finalMode .fieldSingleZero input = .ended) :
    ∃ rest, input = .fieldEnd :: rest ∧
      finalMode .instanceBetween rest = .ended := by
  cases input with
  | nil => simp at h
  | cons symbol rest =>
      cases symbol with
      | fieldEnd => exact ⟨rest, rfl, by simpa [nextMode] using h⟩
      | instanceMark | certificateMark | numberMark | bit | recordEnd =>
          simp [nextMode, finalMode_invalid] at h

private theorem fieldEmpty_ended (input : List SubsetSumSym)
    (h : finalMode .fieldEmpty input = .ended) :
    ∃ value rest,
      input = (encodeBinaryNat value).map TSPSym.bit ++
        .fieldEnd :: rest ∧
      finalMode .instanceBetween rest = .ended := by
  cases input with
  | nil => simp at h
  | cons symbol tail =>
      cases symbol with
      | bit value =>
          cases value with
          | false =>
              rcases singleZero_ended tail (by simpa [nextMode] using h) with
                ⟨rest, hshape, hend⟩
              exact ⟨0, rest, by simp [encodeBinaryNat, hshape], hend⟩
          | true =>
              rcases positive_ended tail (by simpa [nextMode] using h) with
                ⟨bits, rest, hshape, hend⟩
              let payload := true :: bits
              have hcanonical : isCanonicalBinaryNat payload = true := rfl
              let number := binaryNatValue payload
              have hdecode : decodeBinaryNat payload = some number := by
                simp [decodeBinaryNat, hcanonical, number]
              have hencode : encodeBinaryNat number = payload :=
                encodeBinaryNat_of_decode_eq_some hdecode
              refine ⟨number, rest, ?_, hend⟩
              rw [hencode]
              simp [payload, hshape]
      | instanceMark | certificateMark | numberMark | fieldEnd | recordEnd =>
          simp [nextMode, finalMode_invalid] at h

private theorem instanceBetween_ended (input : List SubsetSumSym)
    (h : finalMode .instanceBetween input = .ended) :
    ∃ values, input = encodeTSPFields values ++ [.recordEnd] := by
  cases input with
  | nil => simp at h
  | cons symbol tail =>
      cases symbol with
      | recordEnd =>
          have htail := (ended_eq_ended_iff tail).1 (by
            simpa [nextMode] using h)
          subst tail
          exact ⟨[], rfl⟩
      | numberMark =>
          rcases fieldEmpty_ended tail (by simpa [nextMode] using h) with
            ⟨value, rest, hshape, hend⟩
          rcases instanceBetween_ended rest hend with ⟨values, hvalues⟩
          exact ⟨value :: values, by
            simp [encodeTSPFields, encodeTSPField, hshape, hvalues,
              List.append_assoc]⟩
      | instanceMark | certificateMark | bit | fieldEnd =>
          simp [nextMode, finalMode_invalid] at h
termination_by input.length
decreasing_by
  simp_all [List.length_append]
  omega

private theorem instanceNeedField_ended (input : List SubsetSumSym)
    (h : finalMode .instanceNeedField input = .ended) :
    ∃ target values,
      input = encodeTSPFields (target :: values) ++ [.recordEnd] := by
  cases input with
  | nil => simp at h
  | cons symbol tail =>
      cases symbol with
      | numberMark =>
          rcases fieldEmpty_ended tail (by simpa [nextMode] using h) with
            ⟨target, rest, hshape, hend⟩
          rcases instanceBetween_ended rest hend with ⟨values, hvalues⟩
          exact ⟨target, values, by
            simp [encodeTSPFields, encodeTSPField, hshape, hvalues,
              List.append_assoc]⟩
      | instanceMark | certificateMark | bit | fieldEnd | recordEnd =>
          simp [nextMode, finalMode_invalid] at h

private theorem finalMode_positive_bits (bits : List Bool) :
    finalMode .fieldPositive (bits.map TSPSym.bit) = .fieldPositive := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simpa [nextMode] using ih

private theorem finalMode_field (value : Nat) :
    finalMode .fieldEmpty
        ((encodeBinaryNat value).map TSPSym.bit ++ [.fieldEnd]) =
      .instanceBetween := by
  have hcanonical := isCanonicalBinaryNat_encode value
  generalize hbits : encodeBinaryNat value = bits at hcanonical ⊢
  cases bits with
  | nil => simp [isCanonicalBinaryNat] at hcanonical
  | cons first rest =>
      cases first with
      | false =>
          cases rest with
          | nil => simp [nextMode]
          | cons next tail => simp [isCanonicalBinaryNat] at hcanonical
      | true =>
          rw [List.map_cons, List.cons_append]
          simp only [finalMode, List.foldl_cons, nextMode,
            List.foldl_append]
          rw [show List.foldl nextMode .fieldPositive
              (rest.map TSPSym.bit) = .fieldPositive by
            simpa [finalMode] using finalMode_positive_bits rest]
          rfl

private theorem finalMode_field_instanceBetween (value : Nat) :
    finalMode .instanceBetween (encodeTSPField value) =
      .instanceBetween := by
  unfold encodeTSPField
  change finalMode .fieldEmpty
    ((encodeBinaryNat value).map TSPSym.bit ++ [.fieldEnd]) =
      .instanceBetween
  exact finalMode_field value

private theorem finalMode_field_instanceNeed (value : Nat) :
    finalMode .instanceNeedField (encodeTSPField value) =
      .instanceBetween := by
  unfold encodeTSPField
  change finalMode .fieldEmpty
    ((encodeBinaryNat value).map TSPSym.bit ++ [.fieldEnd]) =
      .instanceBetween
  exact finalMode_field value

private theorem finalMode_fields (values : List Nat) :
    finalMode .instanceBetween (encodeTSPFields values) =
      .instanceBetween := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      rw [encodeTSPFields, List.flatMap_cons, finalMode_append]
      rw [finalMode_field_instanceBetween]
      exact ih

theorem instanceSyntax_encode (data : SubsetSumData) :
    instanceSyntax (encodeSubsetSumData data) = true := by
  rw [instanceSyntax_eq, encodeSubsetSumData]
  simp only [finalMode_cons, nextMode]
  rw [show encodeTSPFields (data.target :: data.values) =
      encodeTSPField data.target ++ encodeTSPFields data.values by rfl,
    finalMode_append]
  rw [finalMode_append, finalMode_field_instanceNeed, finalMode_fields]
  rfl

theorem instanceSyntax_eq_true_iff_exists_decode
    (input : List SubsetSumSym) :
    instanceSyntax input = true ↔
      ∃ data, decodeSubsetSumData input = some data := by
  constructor
  · intro hsyntax
    have hfinal : finalMode .instanceStart input = .ended :=
      (accepts_iff_ended _).1 (by simpa [instanceSyntax_eq] using hsyntax)
    cases input with
    | nil => simp at hfinal
    | cons symbol tail =>
        cases symbol with
        | instanceMark =>
            rcases instanceNeedField_ended tail
                (by simpa [nextMode] using hfinal) with
              ⟨target, values, htail⟩
            refine ⟨{ target, values }, ?_⟩
            rw [htail]
            simp [decodeSubsetSumData, decodeTSPFields_encode]
        | certificateMark | numberMark | bit | fieldEnd | recordEnd =>
            simp [nextMode, finalMode_invalid] at hfinal
  · rintro ⟨data, hdecode⟩
    rw [← encodeSubsetSumData_eq_of_decode_eq_some input data hdecode]
    exact instanceSyntax_encode data

private theorem maskBody_ended (input : List SubsetSumSym)
    (h : finalMode .maskBody input = .ended) :
    ∃ mask : List Bool, input = mask.map TSPSym.bit ++ [.recordEnd] := by
  induction input with
  | nil => simp at h
  | cons symbol tail ih =>
      cases symbol with
      | bit value =>
          rcases ih (by simpa [nextMode] using h) with ⟨mask, hmask⟩
          exact ⟨value :: mask, by simp [hmask]⟩
      | recordEnd =>
          have htail := (ended_eq_ended_iff tail).1 (by
            simpa [nextMode] using h)
          subst tail
          exact ⟨[], rfl⟩
      | instanceMark | certificateMark | numberMark | fieldEnd =>
          simp [nextMode, finalMode_invalid] at h

private theorem finalMode_maskBits (mask : List Bool) :
    finalMode .maskBody (mask.map TSPSym.bit) = .maskBody := by
  induction mask with
  | nil => rfl
  | cons bit mask ih => simpa [nextMode] using ih

theorem maskSyntax_encode (mask : List Bool) :
    maskSyntax (encodeSubsetSumMask mask) = true := by
  unfold encodeSubsetSumMask
  rw [maskSyntax_eq]
  change modeAccepts
    (finalMode .maskBody (mask.map TSPSym.bit ++ [.recordEnd])) = true
  rw [finalMode_append, finalMode_maskBits]
  rfl

theorem maskSyntax_eq_true_iff_exists_encode
    (input : List SubsetSumSym) :
    maskSyntax input = true ↔ ∃ mask, input = encodeSubsetSumMask mask := by
  constructor
  · intro hsyntax
    have hfinal : finalMode .maskStart input = .ended :=
      (accepts_iff_ended _).1 (by simpa [maskSyntax_eq] using hsyntax)
    cases input with
    | nil => simp at hfinal
    | cons symbol tail =>
        cases symbol with
        | certificateMark =>
            rcases maskBody_ended tail (by simpa [nextMode] using hfinal) with
              ⟨mask, htail⟩
            exact ⟨mask, by simp [encodeSubsetSumMask, htail]⟩
        | instanceMark | numberMark | bit | fieldEnd | recordEnd =>
            simp [nextMode, finalMode_invalid] at hfinal
  · rintro ⟨mask, rfl⟩
    exact maskSyntax_encode mask

end CLRS.Chapter34.Turing.SubsetSumVerifier.Syntax

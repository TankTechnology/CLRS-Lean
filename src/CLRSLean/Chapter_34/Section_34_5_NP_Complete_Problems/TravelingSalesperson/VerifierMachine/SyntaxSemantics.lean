import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.VerifierMachine.Syntax

/-!
# Exact semantics of the decision-TSP syntax automata

Acceptance is characterized on arbitrary raw words, not only on encoder
outputs.  This closes the malformed-input boundary needed by the final
verifier composition.
-/

namespace CLRS.Chapter34.Turing.TSPVerifier.Syntax

@[simp] theorem finalMode_nil (mode : Mode) : finalMode mode [] = mode := rfl

@[simp] theorem finalMode_cons (mode : Mode) (symbol : TSPSym)
    (rest : List TSPSym) :
    finalMode mode (symbol :: rest) = finalMode (nextMode mode symbol) rest :=
  rfl

@[simp] theorem finalMode_invalid (input : List TSPSym) :
    finalMode .invalid input = .invalid := by
  induction input with
  | nil => rfl
  | cons symbol rest ih =>
      rw [finalMode_cons]
      simpa [nextMode] using ih

theorem finalMode_ended_eq_ended_iff (input : List TSPSym) :
    finalMode .ended input = .ended ↔ input = [] := by
  cases input with
  | nil => simp
  | cons symbol rest =>
      simp [finalMode_cons, nextMode, finalMode_invalid]

private theorem modeAccepts_eq_true_iff (mode : Mode) :
    modeAccepts mode = true ↔ mode = .ended := by
  cases mode <;> simp [modeAccepts]

private theorem positive_ended (returnTo : FieldReturn)
    (input : List TSPSym)
    (h : finalMode (.fieldPositive returnTo) input = .ended) :
    ∃ (bits : List Bool) (rest : List TSPSym),
      input = bits.map TSPSym.bit ++ .fieldEnd :: rest ∧
      finalMode (returned returnTo) rest = .ended := by
  induction input with
  | nil => simp at h
  | cons symbol tail ih =>
      cases symbol with
      | bit value =>
          have htail : finalMode (.fieldPositive returnTo) tail = .ended := by
            simpa [nextMode] using h
          rcases ih htail with ⟨bits, rest, hshape, hend⟩
          exact ⟨value :: bits, rest, by simp [hshape], hend⟩
      | fieldEnd =>
          exact ⟨[], tail, rfl, by simpa [nextMode] using h⟩
      | instanceMark | certificateMark | numberMark | recordEnd =>
          simp [nextMode, finalMode_invalid] at h

private theorem singleZero_ended (returnTo : FieldReturn)
    (input : List TSPSym)
    (h : finalMode (.fieldSingleZero returnTo) input = .ended) :
    ∃ rest, input = .fieldEnd :: rest ∧
      finalMode (returned returnTo) rest = .ended := by
  cases input with
  | nil => simp at h
  | cons symbol rest =>
      cases symbol with
      | fieldEnd => exact ⟨rest, rfl, by simpa [nextMode] using h⟩
      | instanceMark | certificateMark | numberMark | bit | recordEnd =>
          simp [nextMode, finalMode_invalid] at h

private theorem fieldEmpty_ended (returnTo : FieldReturn)
    (input : List TSPSym)
    (h : finalMode (.fieldEmpty returnTo) input = .ended) :
    ∃ value rest,
      input = (encodeBinaryNat value).map TSPSym.bit ++ .fieldEnd :: rest ∧
      finalMode (returned returnTo) rest = .ended := by
  cases input with
  | nil => simp at h
  | cons symbol tail =>
      cases symbol with
      | bit value =>
          cases value with
          | false =>
              have hzero := singleZero_ended returnTo tail (by
                simpa [nextMode] using h)
              rcases hzero with ⟨rest, hshape, hend⟩
              exact ⟨0, rest, by simp [encodeBinaryNat, hshape], hend⟩
          | true =>
              have hpositive := positive_ended returnTo tail (by
                simpa [nextMode] using h)
              rcases hpositive with ⟨bits, rest, hshape, hend⟩
              let payload : List Bool := true :: bits
              have hcanonical : isCanonicalBinaryNat payload = true := rfl
              let value := binaryNatValue payload
              have hdecode : decodeBinaryNat payload = some value := by
                simp [decodeBinaryNat, hcanonical, value]
              have hencode : encodeBinaryNat value = payload :=
                encodeBinaryNat_of_decode_eq_some hdecode
              refine ⟨value, rest, ?_, hend⟩
              rw [hencode]
              simp [payload, hshape]
      | instanceMark | certificateMark | numberMark | fieldEnd | recordEnd =>
          simp [nextMode, finalMode_invalid] at h

private theorem instanceMany_ended (input : List TSPSym)
    (h : finalMode .instanceMany input = .ended) :
    ∃ values, input = encodeTSPFields values ++ [.recordEnd] := by
  cases input with
  | nil => simp at h
  | cons symbol tail =>
      cases symbol with
      | recordEnd =>
          have htail := (finalMode_ended_eq_ended_iff tail).1 (by
            simpa [nextMode] using h)
          subst tail
          exact ⟨[], rfl⟩
      | numberMark =>
          have hfield := fieldEmpty_ended .instanceMany tail (by
            simpa [nextMode] using h)
          rcases hfield with ⟨value, rest, hshape, hend⟩
          rcases instanceMany_ended rest hend with ⟨values, hvalues⟩
          refine ⟨value :: values, ?_⟩
          simp [encodeTSPFields, encodeTSPField, hshape, hvalues,
            List.append_assoc]
      | instanceMark | certificateMark | bit | fieldEnd =>
          simp [nextMode, finalMode_invalid] at h
termination_by input.length
decreasing_by
  simp_all [List.length_append]
  omega

private theorem certificateBetween_ended (input : List TSPSym)
    (h : finalMode .certificateBetween input = .ended) :
    ∃ values, input = encodeTSPFields values ++ [.recordEnd] := by
  cases input with
  | nil => simp at h
  | cons symbol tail =>
      cases symbol with
      | recordEnd =>
          have htail := (finalMode_ended_eq_ended_iff tail).1 (by
            simpa [nextMode] using h)
          subst tail
          exact ⟨[], rfl⟩
      | numberMark =>
          have hfield := fieldEmpty_ended .certificate tail (by
            simpa [nextMode] using h)
          rcases hfield with ⟨value, rest, hshape, hend⟩
          rcases certificateBetween_ended rest hend with ⟨values, hvalues⟩
          refine ⟨value :: values, ?_⟩
          simp [encodeTSPFields, encodeTSPField, hshape, hvalues,
            List.append_assoc]
      | instanceMark | certificateMark | bit | fieldEnd =>
          simp [nextMode, finalMode_invalid] at h
termination_by input.length
decreasing_by
  simp_all [List.length_append]
  omega

private theorem instanceOne_ended (input : List TSPSym)
    (h : finalMode .instanceOne input = .ended) :
    ∃ budget weights,
      input = encodeTSPField budget ++
        (encodeTSPFields weights ++ [.recordEnd]) := by
  cases input with
  | nil => simp at h
  | cons symbol tail =>
      cases symbol with
      | numberMark =>
          have hfield := fieldEmpty_ended .instanceMany tail (by
            simpa [nextMode] using h)
          rcases hfield with ⟨budget, rest, hshape, hend⟩
          rcases instanceMany_ended rest hend with ⟨weights, hweights⟩
          exact ⟨budget, weights, by
            simp [encodeTSPField, hshape, hweights, List.append_assoc]⟩
      | instanceMark | certificateMark | bit | fieldEnd | recordEnd =>
          simp [nextMode, finalMode_invalid] at h

private theorem instanceZero_ended (input : List TSPSym)
    (h : finalMode .instanceZero input = .ended) :
    ∃ vertexCount budget weights,
      input = encodeTSPFields (vertexCount :: budget :: weights) ++
        [.recordEnd] := by
  cases input with
  | nil => simp at h
  | cons symbol tail =>
      cases symbol with
      | numberMark =>
          have hfield := fieldEmpty_ended .instanceOne tail (by
            simpa [nextMode] using h)
          rcases hfield with ⟨vertexCount, rest, hshape, hend⟩
          rcases instanceOne_ended rest hend with
            ⟨budget, weights, hrest⟩
          exact ⟨vertexCount, budget, weights, by
            simp [encodeTSPFields, encodeTSPField, hshape, hrest,
              List.append_assoc]⟩
      | instanceMark | certificateMark | bit | fieldEnd | recordEnd =>
          simp [nextMode, finalMode_invalid] at h

theorem instanceSyntax_eq_true_iff_exists_decode (input : List TSPSym) :
    instanceSyntax input = true ↔ ∃ data, decodeTSPData input = some data := by
  constructor
  · intro hsyntax
    have hfinal : finalMode .instanceStart input = .ended :=
      (modeAccepts_eq_true_iff _).1 (by
        simpa [instanceSyntax_eq] using hsyntax)
    cases input with
    | nil => simp at hfinal
    | cons symbol tail =>
        cases symbol with
        | instanceMark =>
            have hzero : finalMode .instanceZero tail = .ended := by
              simpa [nextMode] using hfinal
            rcases instanceZero_ended tail hzero with
              ⟨vertexCount, budget, weights, htail⟩
            refine ⟨{ vertexCount, budget, weights }, ?_⟩
            rw [htail]
            simp [decodeTSPData, decodeTSPFields_encode]
        | certificateMark | numberMark | bit | fieldEnd | recordEnd =>
            simp [nextMode, finalMode_invalid] at hfinal
  · rintro ⟨data, hdecode⟩
    rw [← encodeTSPData_eq_of_decode_eq_some input data hdecode]
    exact instanceSyntax_encode data

theorem certificateSyntax_eq_true_iff_exists_decode
    (input : List TSPSym) :
    certificateSyntax input = true ↔
      ∃ vertices, decodeTSPCertificate input = some vertices := by
  constructor
  · intro hsyntax
    have hfinal : finalMode .certificateStart input = .ended :=
      (modeAccepts_eq_true_iff _).1 (by
        simpa [certificateSyntax_eq] using hsyntax)
    cases input with
    | nil => simp at hfinal
    | cons symbol tail =>
        cases symbol with
        | certificateMark =>
            have hbetween : finalMode .certificateBetween tail = .ended := by
              simpa [nextMode] using hfinal
            rcases certificateBetween_ended tail hbetween with
              ⟨vertices, htail⟩
            exact ⟨vertices, by
              rw [htail]
              simp [decodeTSPCertificate, decodeTSPFields_encode]⟩
        | instanceMark | numberMark | bit | fieldEnd | recordEnd =>
            simp [nextMode, finalMode_invalid] at hfinal
  · rintro ⟨vertices, hdecode⟩
    rw [← encodeTSPCertificate_eq_of_decode_eq_some input vertices hdecode]
    exact certificateSyntax_encode vertices

end CLRS.Chapter34.Turing.TSPVerifier.Syntax

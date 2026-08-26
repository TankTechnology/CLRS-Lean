import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.SAT.Certificate

/-!
# Total SAT certificate verification

The checker in this module operates directly on the raw serialized formula and
certificate strings.  Its semantics are exact on every input: non-literal
certificate symbols reject, while malformed formula strings retain the total
{lit}`decode` semantics of the public {lit}`SAT` language.
-/

namespace CLRS.Chapter34

/-- Check a finite serialized assignment against a raw encoded SAT formula. -/
def satVerifier (certificate input : List FormulaSym) : Bool :=
  certificate.all isFormulaAssignmentSymbol &&
    Formula.eval (decode input) (formulaAssignmentInputs certificate)

/-- Exact all-input acceptance semantics of the serialized SAT checker. -/
theorem satVerifier_accepts_iff (certificate input : List FormulaSym) :
    satVerifier certificate input = true ↔
      certificate.all isFormulaAssignmentSymbol = true ∧
        Formula.eval (decode input)
          (formulaAssignmentInputs certificate) = true := by
  simp [satVerifier]

/-- Any certificate containing a non-literal formula symbol is rejected. -/
theorem satVerifier_eq_false_of_malformed
    {certificate input : List FormulaSym}
    (hmalformed : certificate.all isFormulaAssignmentSymbol ≠ true) :
    satVerifier certificate input = false := by
  simp [satVerifier, hmalformed]

/-- Membership in raw {lit}`SAT` is exactly acceptance by some canonical assignment
certificate whose length is at most the raw formula length. -/
theorem mem_SAT_iff_exists_bounded_certificate (input : List FormulaSym) :
    input ∈ SAT ↔
      ∃ certificate : List FormulaSym,
        certificate.length ≤ input.length ∧
          satVerifier certificate input = true := by
  constructor
  · rintro ⟨assignment, heval⟩
    let certificate := encodeFormulaAssignment input.length assignment
    refine ⟨certificate, ?_, ?_⟩
    · simp [certificate]
    · apply (satVerifier_accepts_iff certificate input).2
      refine ⟨by simp [certificate], ?_⟩
      have hagree : ∀ index,
          index < numVars (decode input) →
            assignment index = formulaAssignmentInputs certificate index := by
        intro index hindex
        have hlength : index < input.length :=
          lt_of_lt_of_le hindex (numVars_decode_le input)
        symm
        simpa [certificate] using
          formulaAssignmentInputs_encodeFormulaAssignment_of_lt
            input.length assignment index hlength
      have heq := Formula.eval_eq_of_agree
        (decode input) assignment (formulaAssignmentInputs certificate) hagree
      rwa [← heq]
  · rintro ⟨certificate, _hlength, haccept⟩
    refine ⟨formulaAssignmentInputs certificate, ?_⟩
    exact (satVerifier_accepts_iff certificate input).1 haccept |>.2

end CLRS.Chapter34

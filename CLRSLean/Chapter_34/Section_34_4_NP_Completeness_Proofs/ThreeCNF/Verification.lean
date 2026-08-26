import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.ThreeCNF.Certificate

/-!
# Total 3-CNF-SAT certificate verification

This module exposes Boolean checkers for clause evaluation, CNF evaluation,
and the at-most-three shape condition.  Their reflected propositions assemble
into an exact checker for every raw formula and certificate string.
-/

namespace CLRS.Chapter34

/-! ## Boolean reflection of CNF semantics -/

/-- Boolean evaluation of one clause under an assignment. -/
def evalClauseBool (assignment : Nat → Bool) (clause : Clause) : Bool :=
  clause.any (evalLitBool assignment)

/-- Boolean evaluation of a CNF formula under an assignment. -/
def evalCNFBool (assignment : Nat → Bool) (formula : CNF) : Bool :=
  formula.all (evalClauseBool assignment)

/-- Boolean recognition of the project's at-most-three-literals CNF shape. -/
def isThreeCNFBool (formula : CNF) : Bool :=
  formula.all fun clause => decide (clause.length ≤ 3)

@[simp] theorem evalClauseBool_eq_true (assignment : Nat → Bool)
    (clause : Clause) :
    evalClauseBool assignment clause = true ↔
      evalClause assignment clause := by
  simp [evalClauseBool, evalClause, List.any_eq_true]

@[simp] theorem evalCNFBool_eq_true (assignment : Nat → Bool)
    (formula : CNF) :
    evalCNFBool assignment formula = true ↔ evalCNF assignment formula := by
  simp [evalCNFBool, evalCNF, List.all_eq_true]

@[simp] theorem isThreeCNFBool_eq_true (formula : CNF) :
    isThreeCNFBool formula = true ↔ IsThreeCNF formula := by
  simp [isThreeCNFBool, IsThreeCNF, List.all_eq_true]

/-! ## Serialized checker and exact certificate theorem -/

/-- Check a finite serialized assignment against a raw encoded 3-CNF formula. -/
def threeCNFSatVerifier (certificate input : List CNFSym) : Bool :=
  certificate.all isCNFAssignmentSymbol &&
    isThreeCNFBool (decodeCNF input) &&
      evalCNFBool (cnfAssignmentInputs certificate) (decodeCNF input)

/-- Exact all-input acceptance semantics of the serialized 3-CNF-SAT checker. -/
theorem threeCNFSatVerifier_accepts_iff
    (certificate input : List CNFSym) :
    threeCNFSatVerifier certificate input = true ↔
      certificate.all isCNFAssignmentSymbol = true ∧
        IsThreeCNF (decodeCNF input) ∧
          evalCNF (cnfAssignmentInputs certificate) (decodeCNF input) := by
  simp [threeCNFSatVerifier, and_assoc]

/-- Any certificate containing a symbol other than {lit}`posMark` or
{lit}`negMark` is rejected. -/
theorem threeCNFSatVerifier_eq_false_of_malformed
    {certificate input : List CNFSym}
    (hmalformed : certificate.all isCNFAssignmentSymbol ≠ true) :
    threeCNFSatVerifier certificate input = false := by
  simp [threeCNFSatVerifier, hmalformed]

/-- Membership in raw {lit}`ThreeCNFSat` is exactly acceptance by some canonical
assignment certificate whose length is at most the raw formula length. -/
theorem mem_threeCNFSat_iff_exists_bounded_certificate
    (input : List CNFSym) :
    input ∈ ThreeCNFSat ↔
      ∃ certificate : List CNFSym,
        certificate.length ≤ input.length ∧
          threeCNFSatVerifier certificate input = true := by
  constructor
  · rintro ⟨hthree, assignment, heval⟩
    let certificate := encodeCNFAssignment input.length assignment
    refine ⟨certificate, ?_, ?_⟩
    · simp [certificate]
    · apply (threeCNFSatVerifier_accepts_iff certificate input).2
      refine ⟨by simp [certificate], hthree, ?_⟩
      have hagree : ∀ index,
          index < input.length →
            assignment index = cnfAssignmentInputs certificate index := by
        intro index hindex
        symm
        simpa [certificate] using
          cnfAssignmentInputs_encodeCNFAssignment_of_lt
            input.length assignment index hindex
      exact (evalCNF_of_agree assignment (cnfAssignmentInputs certificate)
        input.length (decodeCNF input) (decodeCNF_indices_lt input) hagree).1
          heval
  · rintro ⟨certificate, _hlength, haccept⟩
    rcases (threeCNFSatVerifier_accepts_iff certificate input).1 haccept with
      ⟨_hcertificate, hthree, heval⟩
    exact ⟨hthree, cnfAssignmentInputs certificate, heval⟩

end CLRS.Chapter34

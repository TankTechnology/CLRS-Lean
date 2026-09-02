import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.SatTo3CNFSat

/-!
# 3-CNF-SAT assignment certificates

Boolean assignments for the raw CNF alphabet use {lit}`posMark` for true and
{lit}`negMark` for false.  The parser bounds are proved for the total CNF decoder,
including malformed raw strings, so a certificate of raw-input length always
covers every decoded literal index.
-/

namespace CLRS.Chapter34

/-! ## Canonical finite assignments -/

/-- Recognize the two CNF symbols permitted in an assignment certificate. -/
def isCNFAssignmentSymbol : CNFSym → Bool
  | .posMark | .negMark => true
  | _ => false

/-- Interpret a CNF assignment symbol, defaulting malformed symbols to false. -/
def cnfAssignmentSymbolValue : CNFSym → Bool
  | .posMark => true
  | _ => false

/-- Read variable {lit}`i` from a finite CNF assignment certificate, defaulting to
false beyond its end. -/
def cnfAssignmentInputs (certificate : List CNFSym) (i : Nat) : Bool :=
  match certificate[i]? with
  | some symbol => cnfAssignmentSymbolValue symbol
  | none => false

/-- Encode the first {lit}`n` values of an arbitrary Boolean assignment. -/
def encodeCNFAssignment (n : Nat) (assignment : Nat → Bool) : List CNFSym :=
  List.ofFn fun i : Fin n =>
    if assignment i then .posMark else .negMark

@[simp] theorem encodeCNFAssignment_length (n : Nat)
    (assignment : Nat → Bool) :
    (encodeCNFAssignment n assignment).length = n := by
  simp [encodeCNFAssignment]

@[simp] theorem encodeCNFAssignment_all (n : Nat)
    (assignment : Nat → Bool) :
    (encodeCNFAssignment n assignment).all isCNFAssignmentSymbol = true := by
  rw [List.all_eq_true]
  simp only [encodeCNFAssignment, List.forall_mem_ofFn_iff]
  intro index
  cases assignment index <;> simp [isCNFAssignmentSymbol]

@[simp] theorem cnfAssignmentInputs_encodeCNFAssignment_of_lt
    (n : Nat) (assignment : Nat → Bool) (i : Nat) (hi : i < n) :
    cnfAssignmentInputs (encodeCNFAssignment n assignment) i = assignment i := by
  cases hvalue : assignment i <;>
    simp [cnfAssignmentInputs, encodeCNFAssignment, hi, hvalue,
      cnfAssignmentSymbolValue]

/-! ## Bounds for the total raw CNF decoder -/

/-- The value produced by the unary CNF index parser is at most its initial
offset plus the number of available symbols. -/
theorem decodeCNFVarIdx_value_le (offset : Nat) (symbols : List CNFSym) :
    (decodeCNFVarIdx offset symbols).1 ≤ offset + symbols.length := by
  induction symbols generalizing offset with
  | nil => simp [decodeCNFVarIdx]
  | cons symbol rest ih =>
      by_cases hsymbol : symbol = CNFSym.endMark
      · subst symbol
        simp only [decodeCNFVarIdx]
        have h := ih (offset + 1)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      · simp [decodeCNFVarIdx, hsymbol]

/-- The literal returned from any nonempty raw symbol list has an index below
that list's length, including the junk literal returned on malformed input. -/
theorem decodeLit_index_lt (symbol : CNFSym) (rest : List CNFSym) :
    litIndex (decodeLit (symbol :: rest)).1 < (symbol :: rest).length := by
  by_cases hpos : symbol = CNFSym.posMark
  · subst symbol
    cases rest with
    | nil => simp [decodeLit, litIndex]
    | cons second tail =>
        by_cases hvar : second = CNFSym.varMark
        · subst second
          cases tail with
          | nil => simp [decodeLit, litIndex]
          | cons third suffix =>
              by_cases hend : third = CNFSym.endMark
              · subst third
                simp only [decodeLit, litIndex, List.length_cons]
                have h := decodeCNFVarIdx_value_le 0 suffix
                omega
              · simp [decodeLit, hend, litIndex]
        · simp [decodeLit, hvar, litIndex]
  · by_cases hneg : symbol = CNFSym.negMark
    · subst symbol
      cases rest with
      | nil => simp [decodeLit, litIndex]
      | cons second tail =>
          by_cases hvar : second = CNFSym.varMark
          · subst second
            cases tail with
            | nil => simp [decodeLit, litIndex]
            | cons third suffix =>
                by_cases hend : third = CNFSym.endMark
                · subst third
                  simp only [decodeLit, litIndex, List.length_cons]
                  have h := decodeCNFVarIdx_value_le 0 suffix
                  omega
                · simp [decodeLit, hend, litIndex]
          · simp [decodeLit, hvar, litIndex]
    · simp [decodeLit, hpos, hneg, litIndex]

/-- Every literal returned by the one-clause decoder has index below the length
of the raw suffix from which that clause was decoded. -/
theorem decodeLits_indices_lt (symbols : List CNFSym) :
    ∀ literal ∈ (decodeLits symbols).1,
      litIndex literal < symbols.length := by
  let property : List CNFSym → Prop := fun input =>
    ∀ literal ∈ (decodeLits input).1, litIndex literal < input.length
  have byLength : ∀ n : Nat, ∀ input : List CNFSym,
      input.length = n → property input := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro input hlength
        cases input with
        | nil => simp [property, decodeLits]
        | cons symbol rest =>
            by_cases hclause : symbol = CNFSym.clauseMark
            · subst symbol
              simp [property, decodeLits]
            · rcases hdecode : decodeLit (symbol :: rest) with
                ⟨headLiteral, suffix⟩
              have hsuffix : suffix.length < (symbol :: rest).length := by
                have h := decodeLit_suffix_lt symbol rest
                simpa [hdecode] using h
              have ihSuffix : property suffix :=
                ih suffix.length (by omega) suffix rfl
              change property (symbol :: rest)
              dsimp only [property]
              rw [decodeLits.eq_3]
              · simp only [hdecode, List.mem_cons]
                intro literal hliteral
                rcases hliteral with heq | hliteral
                · subst literal
                  simpa [hdecode] using decodeLit_index_lt symbol rest
                · exact lt_of_lt_of_le (ihSuffix literal hliteral)
                    (Nat.le_of_lt hsuffix)
              · exact hclause
  exact byLength symbols.length symbols rfl

/-- Every literal returned by the total raw CNF decoder has index below the
length of the complete raw input string. -/
theorem decodeCNF_indices_lt (symbols : List CNFSym) :
    ∀ clause ∈ decodeCNF symbols, ∀ literal ∈ clause,
      litIndex literal < symbols.length := by
  let property : List CNFSym → Prop := fun input =>
    ∀ clause ∈ decodeCNF input, ∀ literal ∈ clause,
      litIndex literal < input.length
  have byLength : ∀ n : Nat, ∀ input : List CNFSym,
      input.length = n → property input := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro input hlength
        cases input with
        | nil => simp [property, decodeCNF]
        | cons symbol rest =>
            by_cases hclause : symbol = CNFSym.clauseMark
            · subst symbol
              rcases hdecode : decodeLits rest with ⟨headClause, suffix⟩
              have hsuffixLe : suffix.length ≤ rest.length := by
                have h := decodeLits_suffix_le rest
                simpa [hdecode] using h
              have hsuffixLt : suffix.length <
                  (CNFSym.clauseMark :: rest).length := by
                simp only [List.length_cons]
                omega
              have ihSuffix : property suffix :=
                ih suffix.length (by omega) suffix rfl
              change property (CNFSym.clauseMark :: rest)
              dsimp only [property]
              rw [decodeCNF.eq_2]
              simp only [hdecode, List.mem_cons]
              intro clause hmem literal hliteral
              rcases hmem with heq | hmem
              · subst clause
                have hliteral' : literal ∈ (decodeLits rest).1 := by
                  simpa [hdecode] using hliteral
                exact lt_trans
                  (decodeLits_indices_lt rest literal hliteral') (by simp)
              · exact lt_of_lt_of_le (ihSuffix clause hmem literal hliteral)
                  (Nat.le_of_lt hsuffixLt)
            · have ihRest : property rest :=
                ih rest.length (by simp [← hlength]) rest rfl
              change property (symbol :: rest)
              dsimp only [property]
              rw [decodeCNF.eq_3]
              · intro clause hmem literal hliteral
                exact lt_trans (ihRest clause hmem literal hliteral) (by simp)
              · exact hclause
  exact byLength symbols.length symbols rfl

end CLRS.Chapter34

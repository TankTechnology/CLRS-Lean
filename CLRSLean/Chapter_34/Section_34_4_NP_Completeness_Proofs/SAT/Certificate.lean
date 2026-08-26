import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.SatTo3CNFSat

/-!
# SAT assignment certificates

This module gives serialized SAT assignments a total, canonical meaning.  A
certificate is a list of formula literals; position {lit}`i` stores the Boolean
value of variable {lit}`i`.  Every other formula symbol is rejected by the checker
defined in the companion {lit}`Verification` module.

The decoder bounds below are deliberately stated for arbitrary raw formula
strings.  They show that every variable manufactured by the total junk-on-
malformed-input decoder lies below the raw input length, so one linear-size
certificate suffices even off the canonical encoding image.
-/

namespace CLRS.Chapter34

/-! ## Canonical finite assignments -/

/-- Recognize the two formula symbols permitted in a SAT assignment
certificate. -/
def isFormulaAssignmentSymbol : FormulaSym → Bool
  | .lit _ => true
  | _ => false

/-- Interpret a formula assignment symbol, defaulting malformed symbols to
{lit}`false`.  The verifier separately rejects such symbols. -/
def formulaAssignmentSymbolValue : FormulaSym → Bool
  | .lit value => value
  | _ => false

/-- Read variable {lit}`i` from a finite formula assignment certificate,
defaulting to {lit}`false` beyond the certificate's end. -/
def formulaAssignmentInputs (certificate : List FormulaSym) (i : Nat) : Bool :=
  match certificate[i]? with
  | some symbol => formulaAssignmentSymbolValue symbol
  | none => false

/-- Encode the first {lit}`n` values of an arbitrary Boolean assignment. -/
def encodeFormulaAssignment (n : Nat) (assignment : Nat → Bool) :
    List FormulaSym :=
  List.ofFn fun i : Fin n => .lit (assignment i)

@[simp] theorem encodeFormulaAssignment_length (n : Nat)
    (assignment : Nat → Bool) :
    (encodeFormulaAssignment n assignment).length = n := by
  simp [encodeFormulaAssignment]

@[simp] theorem encodeFormulaAssignment_all (n : Nat)
    (assignment : Nat → Bool) :
    (encodeFormulaAssignment n assignment).all
        isFormulaAssignmentSymbol = true := by
  rw [List.all_eq_true]
  simp [encodeFormulaAssignment, isFormulaAssignmentSymbol]

@[simp] theorem formulaAssignmentInputs_encodeFormulaAssignment_of_lt
    (n : Nat) (assignment : Nat → Bool) (i : Nat) (hi : i < n) :
    formulaAssignmentInputs (encodeFormulaAssignment n assignment) i =
      assignment i := by
  simp [formulaAssignmentInputs, encodeFormulaAssignment, hi,
    formulaAssignmentSymbolValue]

/-! ## Bounds for the total raw formula decoder -/

/-- The variable and suffix returned by the unary-index decoder are bounded by
its initial offset plus the number of available symbols. -/
theorem decodeVarIdx_bounds (offset : Nat) (symbols : List FormulaSym) :
    numVars (decodeVarIdx offset symbols).1 ≤
        offset + symbols.length + 1 ∧
      (decodeVarIdx offset symbols).2.length ≤ symbols.length := by
  induction symbols generalizing offset with
  | nil => simp [decodeVarIdx, numVars]
  | cons symbol rest ih =>
      by_cases hsymbol : symbol = FormulaSym.endMark
      · subst symbol
        have h := ih (offset + 1)
        simp only [decodeVarIdx]
        constructor
        · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.1
        · exact le_trans h.2 (by simp)
      · simp [decodeVarIdx, hsymbol, numVars]

/-- A variable decoded after {lit}`varMark` has index-plus-one at most the number of
symbols available to that variable encoding; the returned suffix never grows. -/
theorem decodeVar_bounds (symbols : List FormulaSym) :
    numVars (decodeVar symbols).1 ≤ symbols.length ∧
      (decodeVar symbols).2.length ≤ symbols.length := by
  cases symbols with
  | nil => simp [decodeVar, numVars]
  | cons symbol rest =>
      by_cases hsymbol : symbol = FormulaSym.endMark
      · subst symbol
        have h := decodeVarIdx_bounds 0 rest
        simp only [decodeVar]
        exact ⟨by simpa using h.1, le_trans h.2 (by simp)⟩
      · simp [decodeVar, hsymbol, numVars]

/-- Every formula and suffix produced by the fuelled total decoder is bounded
by the length of its raw input string. -/
theorem decodeAux_bounds (fuel : Nat) (symbols : List FormulaSym) :
    numVars (decodeAux fuel symbols).1 ≤ symbols.length ∧
      (decodeAux fuel symbols).2.length ≤ symbols.length := by
  induction fuel generalizing symbols with
  | zero => simp [decodeAux, numVars]
  | succ fuel ih =>
      cases symbols with
      | nil => simp [decodeAux, numVars]
      | cons symbol rest =>
          cases symbol with
          | lit value => simp [decodeAux, numVars]
          | varMark =>
              have h := decodeVar_bounds rest
              simp only [decodeAux]
              exact ⟨le_trans h.1 (by simp), le_trans h.2 (by simp)⟩
          | endMark => simp [decodeAux, numVars]
          | notMark =>
              have h := ih rest
              rcases hdecode : decodeAux fuel rest with ⟨formula, suffix⟩
              simpa [decodeAux, hdecode, numVars] using
                And.intro (le_trans h.1 (by simp))
                  (le_trans h.2 (by simp))
          | andMark =>
              rcases hleft : decodeAux fuel rest with ⟨left, middle⟩
              rcases hright : decodeAux fuel middle with ⟨right, suffix⟩
              have hleftBounds := ih rest
              have hrightBounds := ih middle
              simp only [hleft] at hleftBounds
              simp only [hright] at hrightBounds
              simp only [decodeAux, hleft, hright]
              constructor
              · simp only [numVars]
                exact max_le
                  (le_trans hleftBounds.1 (by simp))
                  (le_trans hrightBounds.1
                    (le_trans hleftBounds.2 (by simp)))
              · exact le_trans hrightBounds.2
                  (le_trans hleftBounds.2 (by simp))
          | orMark =>
              rcases hleft : decodeAux fuel rest with ⟨left, middle⟩
              rcases hright : decodeAux fuel middle with ⟨right, suffix⟩
              have hleftBounds := ih rest
              have hrightBounds := ih middle
              simp only [hleft] at hleftBounds
              simp only [hright] at hrightBounds
              simp only [decodeAux, hleft, hright]
              constructor
              · simp only [numVars]
                exact max_le
                  (le_trans hleftBounds.1 (by simp))
                  (le_trans hrightBounds.1
                    (le_trans hleftBounds.2 (by simp)))
              · exact le_trans hrightBounds.2
                  (le_trans hleftBounds.2 (by simp))
          | iffMark =>
              rcases hleft : decodeAux fuel rest with ⟨left, middle⟩
              rcases hright : decodeAux fuel middle with ⟨right, suffix⟩
              have hleftBounds := ih rest
              have hrightBounds := ih middle
              simp only [hleft] at hleftBounds
              simp only [hright] at hrightBounds
              simp only [decodeAux, hleft, hright]
              constructor
              · simp only [numVars]
                exact max_le
                  (le_trans hleftBounds.1 (by simp))
                  (le_trans hrightBounds.1
                    (le_trans hleftBounds.2 (by simp)))
              · exact le_trans hrightBounds.2
                  (le_trans hleftBounds.2 (by simp))

/-- Every variable of a formula decoded from a raw string lies below the raw
string length. -/
theorem numVars_decode_le (symbols : List FormulaSym) :
    numVars (decode symbols) ≤ symbols.length := by
  exact (decodeAux_bounds symbols.length symbols).1

end CLRS.Chapter34

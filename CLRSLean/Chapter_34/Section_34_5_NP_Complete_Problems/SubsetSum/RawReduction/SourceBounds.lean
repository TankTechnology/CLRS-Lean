import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.RawReduction.ItemList

/-! # Size bounds for decoded 3-CNF source data -/

namespace CLRS.Chapter34.SubsetSumReduction

/-- The unary variable-index parser cannot increase its accumulator by more
than the number of source cells it scans. -/
theorem decodeCNFVarIdx_value_le (initial : Nat) (input : List CNFSym) :
    (decodeCNFVarIdx initial input).1 ≤ initial + input.length := by
  induction input generalizing initial with
  | nil => simp [decodeCNFVarIdx]
  | cons symbol rest ih =>
      by_cases hend : symbol = .endMark
      · subst symbol
        simp only [decodeCNFVarIdx]
        have := ih (initial + 1)
        simp only [List.length_cons]
        omega
      · simp [decodeCNFVarIdx, hend]

set_option linter.unusedSimpArgs false

/-- Every variable index returned by the literal parser fits in the unary
source fragment that produced it. -/
theorem literalIndex_decodeLit_lt_length (symbol : CNFSym)
    (rest : List CNFSym) :
    literalIndex (decodeLit (symbol :: rest)).1 <
      (symbol :: rest).length := by
  cases symbol <;> try simp [decodeLit, literalIndex]
  all_goals
    cases rest with
    | nil => simp [decodeLit, literalIndex]
    | cons second tail =>
        cases second <;> try simp [decodeLit, literalIndex]
        case varMark =>
          cases tail with
          | nil => simp [decodeLit, literalIndex]
          | cons third suffix =>
              cases third <;> try simp [decodeLit, literalIndex]
              case endMark =>
                rcases hparse : decodeCNFVarIdx 0 suffix with
                  ⟨index, suffix'⟩
                have hvalue := decodeCNFVarIdx_value_le 0 suffix
                simp only [hparse, Nat.zero_add] at hvalue
                simp only [decodeLit, hparse, literalIndex,
                  List.length_cons]
                omega

set_option linter.unusedSimpArgs true

/-- The largest variable index in a decoded clause is bounded by the source
fragment consumed for that clause. -/
theorem clauseVarCount_decodeLits_le (input : List CNFSym) :
    clauseVarCount (decodeLits input).1 ≤ input.length := by
  let P : List CNFSym → Prop := fun symbols =>
    clauseVarCount (decodeLits symbols).1 ≤ symbols.length
  have hstrong : ∀ n, ∀ symbols : List CNFSym,
      symbols.length = n → P symbols := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro symbols hlength
        cases symbols with
        | nil => simp [P, decodeLits, clauseVarCount]
        | cons symbol rest =>
            by_cases hmark : symbol = .clauseMark
            · subst symbol
              simp [P, decodeLits, clauseVarCount]
            · rcases hdecode : decodeLit (symbol :: rest) with
                ⟨literal, suffix⟩
              have hsuffix : suffix.length < (symbol :: rest).length := by
                have := decodeLit_suffix_lt symbol rest
                simpa [hdecode] using this
              have hsuffixN : suffix.length < n := by omega
              have ihsuffix : P suffix :=
                ih suffix.length hsuffixN suffix rfl
              have hliteral : literalIndex literal <
                  (symbol :: rest).length := by
                have := literalIndex_decodeLit_lt_length symbol rest
                simpa [hdecode] using this
              dsimp [P] at ihsuffix ⊢
              rw [decodeLits.eq_3 symbol rest hmark, hdecode]
              simp only [clauseVarCount]
              rw [Nat.max_le]
              constructor
              · simpa only [List.length_cons] using
                  (Nat.add_one_le_iff.mpr hliteral)
              · exact le_trans ihsuffix (Nat.le_of_lt hsuffix)
  exact hstrong input.length input rfl

/-- Both the clause count and the one-past-largest variable index of a decoded
formula are individually bounded by its raw source length. -/
theorem cnfVarCount_decodeCNF_le (input : List CNFSym) :
    cnfVarCount (decodeCNF input) ≤ input.length := by
  let P : List CNFSym → Prop := fun symbols =>
    cnfVarCount (decodeCNF symbols) ≤ symbols.length
  have hstrong : ∀ n, ∀ symbols : List CNFSym,
      symbols.length = n → P symbols := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro symbols hlength
        cases symbols with
        | nil => simp [P, decodeCNF, cnfVarCount]
        | cons symbol rest =>
            by_cases hmark : symbol = .clauseMark
            · subst symbol
              let suffix := (decodeLits rest).2
              have hsuffixLe : suffix.length ≤ rest.length :=
                decodeLits_suffix_le rest
              have hsuffixN : suffix.length < n := by
                simp only [List.length_cons] at hlength
                omega
              have ihsuffix : P suffix :=
                ih suffix.length hsuffixN suffix rfl
              have hclause := clauseVarCount_decodeLits_le rest
              dsimp [P] at ihsuffix ⊢
              rw [decodeCNF.eq_2]
              simp only [cnfVarCount]
              change max (clauseVarCount (decodeLits rest).1)
                (cnfVarCount (decodeCNF suffix)) ≤ rest.length + 1
              rw [Nat.max_le]
              constructor
              · exact le_trans hclause (Nat.le.step (Nat.le_refl _))
              · exact le_trans ihsuffix
                  (le_trans hsuffixLe (Nat.le.step (Nat.le_refl _)))
            · have ihrest : P rest := by
                apply ih rest.length
                · simp only [List.length_cons] at hlength
                  omega
                · rfl
              dsimp [P] at ihrest ⊢
              rw [decodeCNF.eq_3 symbol rest hmark]
              omega
  exact hstrong input.length input rfl

theorem decodeCNF_length_le (input : List CNFSym) :
    (decodeCNF input).length ≤ input.length := by
  let P : List CNFSym → Prop := fun symbols =>
    (decodeCNF symbols).length ≤ symbols.length
  have hstrong : ∀ n, ∀ symbols : List CNFSym,
      symbols.length = n → P symbols := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro symbols hlength
        cases symbols with
        | nil => simp [P, decodeCNF]
        | cons symbol rest =>
            by_cases hmark : symbol = .clauseMark
            · subst symbol
              let suffix := (decodeLits rest).2
              have hsuffixLe : suffix.length ≤ rest.length :=
                decodeLits_suffix_le rest
              have hsuffixN : suffix.length < n := by
                simp only [List.length_cons] at hlength
                omega
              have ihsuffix : P suffix :=
                ih suffix.length hsuffixN suffix rfl
              dsimp [P] at ihsuffix ⊢
              rw [decodeCNF.eq_2]
              simp only [List.length_cons]
              change (decodeCNF suffix).length + 1 ≤ rest.length + 1
              omega
            · have ihrest : P rest := by
                apply ih rest.length
                · simp only [List.length_cons] at hlength
                  omega
                · rfl
              dsimp [P] at ihrest ⊢
              rw [decodeCNF.eq_3 symbol rest hmark]
              omega
  exact hstrong input.length input rfl

end CLRS.Chapter34.SubsetSumReduction

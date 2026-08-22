import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Language
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Encoding.Length
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Semantics

/-!
# Raw 3-CNF-SAT to general CLIQUE reduction

The total map decodes every source string, checks the project's at-most-three
condition, and emits either the indexed occurrence graph or a fixed well-formed
no-instance.  The semantic theorem is exact on arbitrary raw strings, and the
serialized output has an explicit cubic bound.
-/

namespace CLRS
namespace Chapter34

/-- A fixed well-formed CLIQUE no-instance: selecting both vertices would
require the absent edge. -/
def noCliqueInstance : CliqueInstance where
  vertexCount := 2
  targetSize := 2
  edges := []

theorem noCliqueInstance_wellFormed : noCliqueInstance.WellFormed := by
  native_decide

theorem noCliqueInstance_not_hasClique : ¬ noCliqueInstance.HasClique := by
  rintro ⟨vertices, hcard, hbound, hadj⟩
  have hsubset : vertices ⊆ Finset.range 2 := by
    intro vertex hvertex
    exact Finset.mem_range.mpr (hbound vertex hvertex)
  have heq : vertices = Finset.range 2 := by
    apply Finset.eq_of_subset_of_card_le hsubset
    rw [hcard]
    simp [noCliqueInstance]
  have := hadj 0 (by simp [heq]) 1 (by simp [heq]) (by omega)
  simp [noCliqueInstance, CliqueInstance.Adj] at this

/-- The at-most-three clause-width condition is executable. -/
instance decidableIsThreeCNF (formula : CNF) : Decidable (IsThreeCNF formula) := by
  unfold IsThreeCNF
  infer_instance

/-- Total raw reduction from the source CNF alphabet to the honest CLIQUE
alphabet. -/
def threeCNFToGeneralCliqueMap (input : List CNFSym) : List CliqueSym :=
  let formula := decodeCNF input
  if IsThreeCNF formula then
    encodeCliqueInstance (occurrenceCliqueInstance formula)
  else
    encodeCliqueInstance noCliqueInstance

/-- Exact raw-language correctness of the 3-CNF occurrence reduction. -/
theorem threeCNFToGeneralCliqueMap_mem_iff (input : List CNFSym) :
    threeCNFToGeneralCliqueMap input ∈ GeneralCLIQUE ↔
      input ∈ ThreeCNFSat := by
  unfold threeCNFToGeneralCliqueMap ThreeCNFSat
  by_cases hthree : IsThreeCNF (decodeCNF input)
  · rw [if_pos hthree, encodeCliqueInstance_mem_generalCLIQUE_iff]
    constructor
    · rintro ⟨_, hclique⟩
      exact ⟨hthree,
        (cnfSatisfiable_iff_occurrenceCliqueInstance _).mpr hclique⟩
    · rintro ⟨_, hsatisfiable⟩
      exact ⟨occurrenceCliqueInstance_wellFormed_of_cnfSatisfiable hsatisfiable,
        (cnfSatisfiable_iff_occurrenceCliqueInstance _).mp hsatisfiable⟩
  · rw [if_neg hthree, encodeCliqueInstance_mem_generalCLIQUE_iff]
    simp [noCliqueInstance_not_hasClique, hthree]

/-! ## Source-size and output-size bounds -/

/-- Total number of literal positions in a CNF. -/
def cnfLiteralCount (formula : CNF) : Nat :=
  (formula.map List.length).sum

@[simp]
theorem cnfLiteralCount_cons (clause : Clause) (formula : CNF) :
    cnfLiteralCount (clause :: formula) =
      clause.length + cnfLiteralCount formula := by
  simp [cnfLiteralCount]

theorem indexedOccurrencesFrom_length (start : Nat) (formula : CNF) :
    (indexedOccurrencesFrom start formula).length = cnfLiteralCount formula := by
  induction formula generalizing start with
  | nil => simp [indexedOccurrencesFrom, cnfLiteralCount]
  | cons clause formula ih =>
      simp [indexedOccurrencesFrom, cnfLiteralCount,
        indexedClauseOccurrences_length, ih]

theorem indexedOccurrences_length (formula : CNF) :
    (indexedOccurrences formula).length = cnfLiteralCount formula := by
  exact indexedOccurrencesFrom_length 0 formula

/-- Literal parsing accounts for at least one consumed source symbol per
decoded literal. -/
theorem decodeLits_size_le (input : List CNFSym) :
    (decodeLits input).1.length + (decodeLits input).2.length ≤ input.length := by
  let P : List CNFSym → Prop := fun symbols =>
    (decodeLits symbols).1.length + (decodeLits symbols).2.length ≤ symbols.length
  have hstrong : ∀ n, ∀ symbols : List CNFSym,
      symbols.length = n → P symbols := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro symbols hlength
        cases symbols with
        | nil => simp [P, decodeLits]
        | cons symbol rest =>
            simp only [List.length_cons] at hlength
            by_cases hmark : symbol = CNFSym.clauseMark
            · subst symbol
              simp [P, decodeLits]
            · rcases hliteral : decodeLit (symbol :: rest) with
                ⟨literal, suffix⟩
              have hsuffix : suffix.length < (symbol :: rest).length := by
                have := decodeLit_suffix_lt symbol rest
                simpa [hliteral] using this
              simp only [List.length_cons] at hsuffix
              have hsuffixN : suffix.length < n := by omega
              have ihsuffix : P suffix :=
                ih suffix.length hsuffixN suffix rfl
              dsimp [P]
              rw [decodeLits.eq_3 symbol rest hmark, hliteral]
              simp only [List.length_cons]
              dsimp [P] at ihsuffix
              omega
  exact hstrong input.length input rfl

/-- Clause markers and decoded literals together fit in the source string. -/
theorem decodeCNF_storedSize_le (input : List CNFSym) :
    (decodeCNF input).length + cnfLiteralCount (decodeCNF input) ≤ input.length := by
  let P : List CNFSym → Prop := fun symbols =>
    (decodeCNF symbols).length + cnfLiteralCount (decodeCNF symbols) ≤
      symbols.length
  have hstrong : ∀ n, ∀ symbols : List CNFSym,
      symbols.length = n → P symbols := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro symbols hlength
        cases symbols with
        | nil => simp [P, decodeCNF, cnfLiteralCount]
        | cons symbol rest =>
            simp only [List.length_cons] at hlength
            by_cases hmark : symbol = CNFSym.clauseMark
            · subst symbol
              let literals := (decodeLits rest).1
              let suffix := (decodeLits rest).2
              have hsuffixLe : suffix.length ≤ rest.length := by
                exact decodeLits_suffix_le rest
              have hsuffixLt : suffix.length <
                  (CNFSym.clauseMark :: rest).length := by simp; omega
              simp only [List.length_cons] at hsuffixLt
              have hsuffixN : suffix.length < n := by omega
              have ihsuffix : P suffix :=
                ih suffix.length hsuffixN suffix rfl
              have hliterals : literals.length + suffix.length ≤ rest.length := by
                exact decodeLits_size_le rest
              dsimp [P]
              rw [decodeCNF.eq_2]
              change (literals :: decodeCNF suffix).length +
                  cnfLiteralCount (literals :: decodeCNF suffix) ≤ _
              simp only [List.length_cons, cnfLiteralCount_cons]
              dsimp [P] at ihsuffix
              omega
            · dsimp [P]
              rw [decodeCNF.eq_3 symbol rest hmark]
              have ihrest : P rest :=
                ih rest.length (by
                  omega) rest rfl
              simpa [P] using Nat.le.step ihrest
  exact hstrong input.length input rfl

theorem normalizedPairs_length_le_square (vertexCount : Nat) :
    (normalizedPairs vertexCount).length ≤ vertexCount ^ 2 := by
  induction vertexCount with
  | zero => simp [normalizedPairs]
  | succ vertexCount ih =>
      simp only [normalizedPairs, List.length_append, List.length_map,
        List.length_range]
      nlinarith

theorem occurrenceCliqueEdges_length_le_square (formula : CNF) :
    (occurrenceCliqueEdges formula).length ≤
      (indexedOccurrences formula).length ^ 2 := by
  exact le_trans (List.length_filter_le _ _)
    (normalizedPairs_length_le_square _)

theorem cliqueEdgesEncodingLength_le {edges : List (Nat × Nat)} {bound : Nat}
    (hrange : ∀ edge ∈ edges, edge.1 < edge.2 ∧ edge.2 < bound) :
    cliqueEdgesEncodingLength edges ≤ edges.length * (2 * bound + 3) := by
  induction edges with
  | nil => simp [cliqueEdgesEncodingLength]
  | cons edge edges ih =>
      have hedge := hrange edge (by simp)
      have htail : cliqueEdgesEncodingLength edges ≤
          edges.length * (2 * bound + 3) := by
        apply ih
        intro tailEdge htailEdge
        exact hrange tailEdge (by simp [htailEdge])
      simp only [cliqueEdgesEncodingLength, List.map_cons, List.sum_cons,
        List.length_cons]
      change edge.1 + edge.2 + 3 + cliqueEdgesEncodingLength edges ≤
        (edges.length + 1) * (2 * bound + 3)
      have hhead : edge.1 + edge.2 + 3 ≤ 2 * bound + 3 := by
        omega
      rw [Nat.add_mul]
      omega

theorem occurrenceCliqueEncodingLength_le (formula : CNF) :
    (encodeCliqueInstance (occurrenceCliqueInstance formula)).length ≤
      let vertexCount := (indexedOccurrences formula).length
      vertexCount + formula.length + 3 +
        vertexCount ^ 2 * (2 * vertexCount + 3) := by
  let vertexCount := (indexedOccurrences formula).length
  have hedgeCount := occurrenceCliqueEdges_length_le_square formula
  have hedgeEncoding :
      cliqueEdgesEncodingLength (occurrenceCliqueEdges formula) ≤
        (occurrenceCliqueEdges formula).length * (2 * vertexCount + 3) := by
    apply cliqueEdgesEncodingLength_le
    intro edge hedge
    exact occurrenceCliqueEdges_in_range hedge
  rw [encodeCliqueInstance_length]
  dsimp [occurrenceCliqueInstance]
  exact Nat.add_le_add_left
    (le_trans hedgeEncoding
      (Nat.mul_le_mul_right (2 * vertexCount + 3) hedgeCount)) _

/-- The total raw reduction has cubic serialized output length. -/
theorem threeCNFToGeneralCliqueMap_length (input : List CNFSym) :
    (threeCNFToGeneralCliqueMap input).length ≤
      64 * (input.length + 1) ^ 3 := by
  unfold threeCNFToGeneralCliqueMap
  by_cases hthree : IsThreeCNF (decodeCNF input)
  · rw [if_pos hthree]
    let vertexCount := (indexedOccurrences (decodeCNF input)).length
    have hstored := decodeCNF_storedSize_le input
    rw [← indexedOccurrences_length] at hstored
    have hencoded := occurrenceCliqueEncodingLength_le (decodeCNF input)
    dsimp only at hencoded
    have hvertex : vertexCount ≤ input.length + 1 := by
      dsimp [vertexCount]
      omega
    have hsquare : vertexCount ^ 2 ≤ (input.length + 1) ^ 2 :=
      Nat.pow_le_pow_left hvertex 2
    have hfactor : 2 * vertexCount + 3 ≤ 5 * (input.length + 1) := by
      omega
    have hproduct : vertexCount ^ 2 * (2 * vertexCount + 3) ≤
        (input.length + 1) ^ 2 * (5 * (input.length + 1)) :=
      Nat.mul_le_mul hsquare hfactor
    have hheader : vertexCount + (decodeCNF input).length + 3 ≤
        3 * (input.length + 1) := by
      dsimp [vertexCount]
      omega
    have hcubic : 3 * (input.length + 1) ≤
        3 * (input.length + 1) ^ 3 := by
      nlinarith
    calc
      (encodeCliqueInstance
          (occurrenceCliqueInstance (decodeCNF input))).length
          ≤ vertexCount + (decodeCNF input).length + 3 +
              vertexCount ^ 2 * (2 * vertexCount + 3) := hencoded
      _ ≤ 8 * (input.length + 1) ^ 3 := by
        nlinarith
      _ ≤ 64 * (input.length + 1) ^ 3 := by omega
  · rw [if_neg hthree]
    norm_num [encodeCliqueInstance_length, noCliqueInstance,
      cliqueEdgesEncodingLength]
    have : 0 < (input.length + 1) ^ 3 := by
      exact pow_pos (by omega) 3
    omega

end Chapter34
end CLRS

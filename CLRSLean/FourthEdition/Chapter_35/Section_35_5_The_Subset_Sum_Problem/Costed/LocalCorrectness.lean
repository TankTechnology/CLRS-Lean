import CLRSLean.FourthEdition.Chapter_35.Section_35_5_The_Subset_Sum_Problem.Costed.Definitions

/-!
# CLRS Section 35.5 - Local scan correctness and work

Erasure and linear counter bounds for the concrete list scans used by the
costed APPROX-SUBSET-SUM execution.
-/

noncomputable section

namespace CLRS
namespace ApproxSubsetSum

theorem mapAddWithCost_value (x : Nat) (L : List Nat) :
    (mapAddWithCost x L).value = L.map (fun y => y + x) := by
  induction L with
  | nil => simp [mapAddWithCost]
  | cons y ys ih => simp [mapAddWithCost, ih]

theorem mapAddWithCost_work (x : Nat) (L : List Nat) :
    (mapAddWithCost x L).work = L.length := by
  induction L with
  | nil => simp [mapAddWithCost]
  | cons y ys ih => simp [mapAddWithCost, ih]

theorem mergeWithCost_value (L M : List Nat) :
    (mergeWithCost L M).value = merge L M := by
  induction L generalizing M with
  | nil => simp [mergeWithCost, merge]
  | cons x xs ihL =>
      induction M with
      | nil => simp [mergeWithCost, merge]
      | cons y ys ihM =>
          by_cases hxy : x ≤ y
          · simp [mergeWithCost, merge, hxy, ihL]
          · simp [mergeWithCost, merge, hxy, ihM]

theorem mergeWithCost_length (L M : List Nat) :
    (mergeWithCost L M).value.length = L.length + M.length := by
  induction L generalizing M with
  | nil => simp [mergeWithCost]
  | cons x xs ihL =>
      induction M with
      | nil => simp [mergeWithCost]
      | cons y ys ihM =>
          by_cases hxy : x ≤ y
          · simp only [mergeWithCost, hxy, ↓reduceIte, List.length_cons]
            rw [ihL]
            simp only [List.length_cons]
            omega
          · simp only [mergeWithCost, hxy, ↓reduceIte, List.length_cons]
            rw [ihM]
            simp only [List.length_cons]
            omega

theorem mergeWithCost_work_le (L M : List Nat) :
    (mergeWithCost L M).work ≤ L.length + M.length := by
  induction L generalizing M with
  | nil => simp [mergeWithCost]
  | cons x xs ihL =>
      induction M with
      | nil => simp [mergeWithCost]
      | cons y ys ihM =>
          by_cases hxy : x ≤ y
          · simp only [mergeWithCost, hxy, ↓reduceIte, List.length_cons]
            have h := ihL (y :: ys)
            simp only [List.length_cons] at h
            omega
          · simp only [mergeWithCost, hxy, ↓reduceIte, List.length_cons]
            have h := ihM
            simp only [List.length_cons] at h
            omega

theorem trimAuxWithCost_value (δ : Real) (last : Nat) (ys : List Nat) :
    (trimAuxWithCost δ last ys).value = trimAux δ last ys := by
  induction ys generalizing last with
  | nil => simp [trimAuxWithCost, trimAux]
  | cons y ys ih =>
      by_cases hkeep : (1 + δ) * (last : Real) < (y : Real)
      · simp [trimAuxWithCost, trimAux, hkeep, ih]
      · simp [trimAuxWithCost, trimAux, hkeep, ih]

theorem trimAuxWithCost_work (δ : Real) (last : Nat) (ys : List Nat) :
    (trimAuxWithCost δ last ys).work = ys.length := by
  induction ys generalizing last with
  | nil => simp [trimAuxWithCost]
  | cons y ys ih =>
      by_cases hkeep : (1 + δ) * (last : Real) < (y : Real)
      · simp [trimAuxWithCost, hkeep, ih]
      · simp [trimAuxWithCost, hkeep, ih]

theorem trimWithCost_value (δ : Real) (L : List Nat) :
    (trimWithCost δ L).value = trim δ L := by
  cases L with
  | nil => simp [trimWithCost, trim]
  | cons y ys => simp [trimWithCost, trim, trimAuxWithCost_value]

theorem trimWithCost_work_le (δ : Real) (L : List Nat) :
    (trimWithCost δ L).work ≤ L.length := by
  cases L with
  | nil => simp [trimWithCost]
  | cons y ys => simp [trimWithCost, trimAuxWithCost_work]

theorem trimWithCost_length_le (δ : Real) (L : List Nat) :
    (trimWithCost δ L).value.length ≤ L.length := by
  rw [trimWithCost_value]
  exact (trim_sublist δ L).length_le

theorem filterAtMostWithCost_value (t : Nat) (L : List Nat) :
    (filterAtMostWithCost t L).value = L.filter (fun y => y ≤ t) := by
  induction L with
  | nil => simp [filterAtMostWithCost]
  | cons y ys ih =>
      by_cases hy : y ≤ t
      · simp [filterAtMostWithCost, hy, ih]
      · simp [filterAtMostWithCost, hy, ih]

theorem filterAtMostWithCost_work (t : Nat) (L : List Nat) :
    (filterAtMostWithCost t L).work = L.length := by
  induction L with
  | nil => simp [filterAtMostWithCost]
  | cons y ys ih =>
      by_cases hy : y ≤ t
      · simp [filterAtMostWithCost, hy, ih]
      · simp [filterAtMostWithCost, hy, ih]

theorem filterAtMostWithCost_length_le (t : Nat) (L : List Nat) :
    (filterAtMostWithCost t L).value.length ≤ L.length := by
  rw [filterAtMostWithCost_value]
  exact List.length_filter_le (fun y => y ≤ t) L

theorem maximumAuxWithCost_value (best : Nat) (L : List Nat) :
    (maximumAuxWithCost best L).value = L.foldl max best := by
  induction L generalizing best with
  | nil => simp [maximumAuxWithCost]
  | cons y ys ih => simp [maximumAuxWithCost, ih]

theorem maximumAuxWithCost_work (best : Nat) (L : List Nat) :
    (maximumAuxWithCost best L).work = L.length := by
  induction L generalizing best with
  | nil => simp [maximumAuxWithCost]
  | cons y ys ih => simp [maximumAuxWithCost, ih]

theorem maximumWithCost_value (L : List Nat) :
    (maximumWithCost L).value = L.foldl max 0 := by
  exact maximumAuxWithCost_value 0 L

theorem maximumWithCost_work (L : List Nat) :
    (maximumWithCost L).work = L.length := by
  exact maximumAuxWithCost_work 0 L

end ApproxSubsetSum
end CLRS

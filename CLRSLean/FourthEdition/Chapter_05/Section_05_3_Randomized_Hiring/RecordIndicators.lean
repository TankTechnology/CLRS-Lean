import CLRSLean.FourthEdition.Chapter_05.Section_05_3_Randomized_Hiring

/-!
# Executable hiring as a sum of prefix-record indicators

This file is the operational half of the hiring expectation bridge.  It is
kept separate from the finite permutation counting argument so changes to the
list execution do not force recompilation of the probability proof.
-/

namespace CLRS
namespace Chapter05

/-- Position `i` of `xs` is a strict record relative to the earlier prefix and
an initial best rank. -/
def recordAfter (best : Nat) (xs : List Nat) (i : Fin xs.length) : Prop :=
  best < xs[i.val] ∧ ∀ x ∈ xs.take i.val, x < xs[i.val]

instance recordAfter_decidable (best : Nat) (xs : List Nat) (i : Fin xs.length) :
    Decidable (recordAfter best xs i) := by
  unfold recordAfter
  infer_instance

/-- Executable natural-valued indicator of `recordAfter`. -/
def recordAfterBit (best : Nat) (xs : List Nat) (i : Fin xs.length) : Nat :=
  if recordAfter best xs i then 1 else 0

/-- Adding a head to the scanned list turns tail records into records relative
to the maximum of the previous best and that head. -/
theorem recordAfter_cons_succ_iff (best r : Nat) (rest : List Nat)
    (i : Fin rest.length) :
    recordAfter best (r :: rest) i.succ ↔ recordAfter (max best r) rest i := by
  simp only [recordAfter, List.getElem_cons_succ, Fin.val_succ, List.take_succ_cons,
    List.mem_cons]
  constructor
  · rintro ⟨hbest, hall⟩
    refine ⟨?_, ?_⟩
    · have hr := hall r (Or.inl rfl)
      omega
    · intro x hx
      exact hall x (Or.inr hx)
  · rintro ⟨hmax, hall⟩
    refine ⟨by omega, ?_⟩
    intro x hx
    rcases hx with rfl | hx
    · omega
    · exact hall x hx

/-- The head position is a record exactly when it improves the initial best. -/
theorem recordAfter_cons_zero_iff (best r : Nat) (rest : List Nat) :
    recordAfter best (r :: rest) 0 ↔ best < r := by
  simp [recordAfter]

/-- The executable accumulator is exactly the sum of its strict-record bits. -/
theorem recordsFrom_eq_sum_recordAfterBit (best : Nat) (xs : List Nat) :
    recordsFrom best xs = ∑ i : Fin xs.length, recordAfterBit best xs i := by
  induction xs generalizing best with
  | nil => simp [recordsFrom]
  | cons r rest ih =>
      rw [recordsFrom_step]
      simp only [List.length_cons]
      rw [Fin.sum_univ_succ]
      rw [ih (max best r)]
      have hhead : (if best < r then 1 else 0) =
          recordAfterBit best (r :: rest) 0 := by
        simp [recordAfterBit, recordAfter_cons_zero_iff]
      rw [hhead]
      apply congrArg (fun tail => recordAfterBit best (r :: rest) 0 + tail)
      apply Finset.sum_congr rfl
      intro i _
      unfold recordAfterBit
      exact if_congr (recordAfter_cons_succ_iff best r rest i).symm rfl rfl

/-- Position `i` is a left-to-right maximum of `xs`. -/
def prefixRecordAt (xs : List Nat) (i : Fin xs.length) : Prop :=
  ∀ x ∈ xs.take i.val, x < xs[i.val]

instance prefixRecordAt_decidable (xs : List Nat) (i : Fin xs.length) :
    Decidable (prefixRecordAt xs i) := by
  unfold prefixRecordAt
  infer_instance

/-- Natural-valued prefix-record indicator. -/
def prefixRecordBit (xs : List Nat) (i : Fin xs.length) : Nat :=
  if prefixRecordAt xs i then 1 else 0

/-- HIRE-ASSISTANT is pointwise the sum of its prefix-record indicators. -/
theorem hireAssistant_eq_sum_prefixRecordIndicators (xs : List Nat) :
    hireAssistant xs = ∑ i : Fin xs.length, prefixRecordBit xs i := by
  cases xs with
  | nil => simp [hireAssistant]
  | cons r rest =>
      rw [hireAssistant_cons]
      simp only [List.length_cons]
      rw [Fin.sum_univ_succ]
      rw [recordsFrom_eq_sum_recordAfterBit]
      have hhead : prefixRecordBit (r :: rest) 0 = 1 := by
        simp [prefixRecordBit, prefixRecordAt]
      rw [hhead]
      apply congrArg (fun tail => 1 + tail)
      apply Finset.sum_congr rfl
      intro i _
      unfold prefixRecordBit recordAfterBit prefixRecordAt recordAfter
      simp only [List.getElem_cons_succ, Fin.val_succ, List.take_succ_cons,
        List.mem_cons]
      have hiff :
          (∀ x, x = r ∨ x ∈ rest.take i.val → x < rest[i.val]) ↔
            r < rest[i.val] ∧ ∀ x ∈ rest.take i.val, x < rest[i.val] := by
        constructor
        · intro h
          exact ⟨h r (Or.inl rfl), fun x hx => h x (Or.inr hx)⟩
        · rintro ⟨hr, hrest⟩ x (rfl | hx)
          · exact hr
          · exact hrest x hx
      exact if_congr (by simpa [List.mem_cons] using hiff.symm) rfl rfl

@[simp] theorem permutationRanks_length {n : Nat} (sigma : Equiv.Perm (Fin n)) :
    (permutationRanks sigma).length = n := by
  simp [permutationRanks]

/-- The prefix-record event at a fixed position of a sampled permutation. -/
def permutationPrefixRecordAt {n : Nat} (sigma : Equiv.Perm (Fin n)) (i : Fin n) : Prop :=
  prefixRecordAt (permutationRanks sigma)
    ⟨i.val, by simpa [permutationRanks] using i.isLt⟩

instance permutationPrefixRecordAt_decidable {n : Nat}
    (sigma : Equiv.Perm (Fin n)) (i : Fin n) :
    Decidable (permutationPrefixRecordAt sigma i) := by
  unfold permutationPrefixRecordAt
  infer_instance

/-- A permutation position is a list prefix record exactly when its rank is
strictly larger than every earlier rank. -/
theorem permutationPrefixRecordAt_iff {n : Nat} (sigma : Equiv.Perm (Fin n))
    (i : Fin n) :
    permutationPrefixRecordAt sigma i ↔
      ∀ j : Fin n, j.val < i.val → (sigma j).val < (sigma i).val := by
  unfold permutationPrefixRecordAt prefixRecordAt
  constructor
  · intro h j hji
    have hmem : (sigma j).val ∈ (permutationRanks sigma).take i.val := by
      rw [List.mem_take_iff_getElem]
      refine ⟨j.val, ?_, ?_⟩
      · simp [permutationRanks]
        omega
      · simp [permutationRanks]
    have := h (sigma j).val hmem
    simpa [permutationRanks] using this
  · intro h x hx
    rw [List.mem_take_iff_getElem] at hx
    rcases hx with ⟨j, hj, hx⟩
    have hjn : j < n := by
      simp [permutationRanks] at hj
      omega
    let fj : Fin n := ⟨j, hjn⟩
    have hji : fj.val < i.val := by
      simp [permutationRanks] at hj
      omega
    have hvalue : x = (sigma fj).val := by
      rw [← hx]
      simp [permutationRanks, fj]
    rw [hvalue]
    simpa [permutationRanks] using h fj hji

/-- HIRE-ASSISTANT on a permutation is the sum of its fixed-position record
indicators. -/
theorem hireAssistant_permutationRanks_eq_sum {n : Nat}
    (sigma : Equiv.Perm (Fin n)) :
    hireAssistant (permutationRanks sigma) =
      ∑ i : Fin n, if permutationPrefixRecordAt sigma i then 1 else 0 := by
  rw [hireAssistant_eq_sum_prefixRecordIndicators]
  let e : Fin n ≃ Fin (permutationRanks sigma).length :=
    (Fin.castOrderIso (permutationRanks_length sigma).symm).toEquiv
  rw [← Equiv.sum_comp e
    (fun i : Fin (permutationRanks sigma).length =>
      prefixRecordBit (permutationRanks sigma) i)]
  apply Finset.sum_congr rfl
  intro i _
  unfold prefixRecordBit permutationPrefixRecordAt
  have he : e i =
      (⟨i.val, by simpa [permutationRanks] using i.isLt⟩ :
        Fin (permutationRanks sigma).length) := by
    apply Fin.ext
    simp [e, Fin.castOrderIso_apply]
  rw [he]
  simp

end Chapter05
end CLRS

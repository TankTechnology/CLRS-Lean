import Mathlib

/-!
# 35.5 The Subset-Sum Problem

This section formalizes the subset-sum problem and the fully polynomial-time
approximation scheme **APPROX-SUBSET-SUM** of CLRS §35.5.  Given a finite set
`S = {x₁, ..., xₙ}` of positive integers and a target `t`, the subset-sum
problem asks for the subset whose sum is as large as possible without exceeding
`t`.  The exact algorithm EXACT-SUBSET-SUM builds the sorted list of all
achievable subset sums at most `t` (its last element is the optimum), but its
lists can grow to size `2^n`.  The approximation scheme instead *trims* each
list so that consecutive kept sums differ by a factor of `1 + δ`, retaining a
`(1 + δ)`-representative for every removed value; trimming at each level with
`δ = ε/(2n)` accumulates only a `(1 + ε)`-factor of error over all `n` levels.

Main results:

- Definition `subsetSums`: the set of all subset sums of a list of integers,
  built by the same merge step as EXACT-SUBSET-SUM (`Lᵢ = Lᵢ₋₁ ∪ (Lᵢ₋₁ + xᵢ)`).
- Definition `exactLists`: the output list of EXACT-SUBSET-SUM — the subset
  sums of `S` not exceeding `t`.
- Definition `optimalSum`: the largest achievable subset sum at most `t` (the
  optimum `y*`).
- Definition `merge`: the merge of two sorted lists of sums.
- Definition `trim`/`trimAux`: the greedy TRIM of a sorted list with parameter
  `δ`, keeping the first element and then every element exceeding `(1 + δ)`
  times the last kept element.
- Lemma `trim_rep` (Lemma 35.5): every element of the trimmed list's input is
  represented within a factor `(1 + δ)` by a kept element — for every `y` in a
  sorted `L` there is `z` in `trim δ L` with `z ≤ y ≤ (1 + δ) · z`.
- Definition `approxLists`: the trimmed lists `Lᵢ` of APPROX-SUBSET-SUM.
- Lemma `approxLists_subset_subsetSums`: every value on the trimmed lists is
  still an achievable subset sum at most `t` (trimming never introduces or
  loses validity).
- Lemma `approxLists_prefix_rep`: after `i` levels of trimming with parameter
  `δ`, every achievable sum `y ≤ t` of the first `i` elements has a
  representative `z` in `Lᵢ` with `y ≤ (1 + δ)^i · z` and `z ≤ y` (the
  compounded per-level factor, Exercise 35.5-2).
- Theorem `approxSubsetSum_approx` (Theorem 35.7): APPROX-SUBSET-SUM returns a
  valid subset sum `z* ≤ t` with the explicit bound
  `y* ≤ (1 + ε/(2n))^n · z*`.
- Theorem `approxSubsetSum_approx_lt` (Theorem 35.7): with `0 < ε ≤ 1`, the
  explicit factor is absorbed into `(1 + ε)` via
  `(1 + ε/(2n))^n ≤ e^{ε/2} ≤ 1 + ε`, giving `y* ≤ (1 + ε) · z*`.

**Current gaps:** Theorem 35.8 — that APPROX-SUBSET-SUM runs in time polynomial
in the input size and `1/ε` (the FPTAS running-time analysis, bounding each
trimmed list by `O(n · lg t / ε)` elements via the `1 + ε/(2n)` separation of
consecutive kept values) — is not yet formalized.  As with the other sections
of this chapter, the running-time analysis is left to future work.

Notation conventions used in this section:

- `xs`/`ps` : a list of positive integers (the set `S`, ordered for the
  algorithm); subset sums are order-independent
- `s`, `y` : a candidate subset sum
- `t` : the target sum
- `δ` : the trim parameter (`0 ≤ δ`)
- `ε` : the approximation parameter (`0 < ε ≤ 1`), with `δ = ε/(2n)`
- `L`, `M` : sorted lists of sums
- `y*` : the optimal subset sum (`optimalSum`)
- `z*` : the value returned by APPROX-SUBSET-SUM (`approxSum`)
-/

noncomputable section

open scoped BigOperators
open scoped List
open Finset

namespace CLRS

namespace ApproxSubsetSum

/-! ## The subset-sum problem and EXACT-SUBSET-SUM

CLRS models the set `S = {x₁, ..., xₙ}` of positive integers and builds the
lists `Lᵢ` of all sums obtainable from subsets of `{x₁, ..., xᵢ}`, discarding
every sum exceeding the target `t`.  The recurrence
`Lᵢ = Lᵢ₋₁ ∪ (Lᵢ₋₁ + xᵢ)` is captured by the recursive definition of
`subsetSums`; `exactLists` adds the pruning of sums above `t` and `optimalSum`
is the largest element of the pruned list. -/

/-- The set of all subset sums of a list `xs` of integers.  The recursion
`subsetSums (x :: xs) = subsetSums xs ∪ (subsetSums xs) + x` is exactly the
merge step of EXACT-SUBSET-SUM (CLRS §35.5, line 2). -/
def subsetSums : List ℕ → Finset ℕ
  | [] => {0}
  | x :: xs => subsetSums xs ∪ (subsetSums xs).image (fun s => s + x)

/-- The empty subset has sum `0`, so `0` is always an achievable sum. -/
lemma zero_mem_subsetSums (xs : List ℕ) : 0 ∈ subsetSums xs := by
  induction xs with
  | nil => simp [subsetSums]
  | cons x xs ih => simp [subsetSums, ih]

/-- A sum of `x :: xs` is either a sum of `xs` alone or a sum of `xs` plus
`x`.  This is the CLRS recurrence `Lᵢ = Lᵢ₋₁ ∪ (Lᵢ₋₁ + xᵢ)`. -/
lemma mem_subsetSums_cons {x : ℕ} {xs : List ℕ} {s : ℕ} :
    s ∈ subsetSums (x :: xs) ↔ s ∈ subsetSums xs ∨ ∃ t ∈ subsetSums xs, t + x = s := by
  simp [subsetSums]

/-- Every sum of `xs` is also a sum of `x :: xs` (drop the new element). -/
lemma subsetSums_cons_subset {x : ℕ} {xs : List ℕ} : subsetSums xs ⊆ subsetSums (x :: xs) := by
  intro s hs
  simp [subsetSums, hs]

/-- If `z` is a sum of `xs`, then `z + x` is a sum of `x :: xs`. -/
lemma mem_subsetSums_add {x : ℕ} {xs : List ℕ} {z : ℕ} :
    z ∈ subsetSums xs → z + x ∈ subsetSums (x :: xs) := by
  intro hz
  change z + x ∈ subsetSums xs ∪ (subsetSums xs).image (fun s => s + x)
  rw [Finset.mem_union]
  right
  rw [Finset.mem_image]
  exact ⟨z, hz, rfl⟩

/-- The output of **EXACT-SUBSET-SUM(S, t)**: the set of all subset sums of `S`
not exceeding the target `t` (CLRS §35.5, EXACT-SUBSET-SUM line 5). -/
def exactLists (xs : List ℕ) (t : ℕ) : Finset ℕ :=
  (subsetSums xs).filter (fun s => s ≤ t)

/-- The exact list is nonempty: `0` is always achievable and `0 ≤ t`. -/
lemma exactLists_nonempty (xs : List ℕ) (t : ℕ) : (exactLists xs t).Nonempty := by
  exact ⟨0, by simp [exactLists, zero_mem_subsetSums xs, Nat.zero_le]⟩

/-- The **optimal subset sum** `y*`: the largest achievable subset sum of `xs`
not exceeding `t`.  It is well-defined because `0` is always achievable and
`0 ≤ t`. -/
def optimalSum (xs : List ℕ) (t : ℕ) : ℕ :=
  (exactLists xs t).max' (exactLists_nonempty xs t)

/-- The optimum is an achievable subset sum. -/
lemma optimalSum_mem_subsetSums (xs : List ℕ) (t : ℕ) : optimalSum xs t ∈ subsetSums xs := by
  exact (Finset.mem_filter.mp (Finset.max'_mem (exactLists xs t) (exactLists_nonempty xs t))).1

/-- The optimum does not exceed the target `t`. -/
lemma optimalSum_le_t (xs : List ℕ) (t : ℕ) : optimalSum xs t ≤ t := by
  exact (Finset.mem_filter.mp (Finset.max'_mem (exactLists xs t) (exactLists_nonempty xs t))).2

/-- The optimum of the empty list is `0`. -/
lemma optimalSum_nil (t : ℕ) : optimalSum [] t = 0 := by
  rw [optimalSum]
  apply le_antisymm
  · apply Finset.max'_le
    intro y hy
    simp [exactLists, subsetSums] at hy
    exact le_of_eq hy.1
  · apply Finset.le_max'
    simp [exactLists, subsetSums, Nat.zero_le]

/-! ## The merge of two sorted lists

APPROX-SUBSET-SUM keeps the lists sorted so that TRIM can scan them greedily.
`merge` is the merge of two sorted lists of sums (CLRS MERGE-LISTS). -/

/-- The merge of two sorted lists of natural numbers. -/
def merge : List ℕ → List ℕ → List ℕ
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => if x ≤ y then x :: merge xs (y :: ys) else y :: merge (x :: xs) ys

/-- An element of the merged list is an element of one of the inputs (and
vice versa): `merge` returns the union of its inputs. -/
lemma mem_merge {L M : List ℕ} {z : ℕ} : z ∈ merge L M ↔ z ∈ L ∨ z ∈ M := by
  induction L generalizing M with
  | nil => simp [merge]
  | cons x xs ihL =>
      induction M with
      | nil => simp [merge]
      | cons y ys ihM =>
          by_cases hxy : x ≤ y
          · simp [merge, hxy]
            rw [ihL]
            simp
            tauto
          · simp [merge, hxy]
            rw [ihM]
            simp
            tauto

/-- The merge of two sorted lists is sorted. -/
lemma merge_sorted (L M : List ℕ) (hL : L.Pairwise (· ≤ ·)) (hM : M.Pairwise (· ≤ ·)) :
    (merge L M).Pairwise (· ≤ ·) := by
  induction L generalizing M with
  | nil => simpa [merge] using hM
  | cons x xs ihL =>
      induction M with
      | nil => simpa [merge] using hL
      | cons y ys ihM =>
          by_cases hxy : x ≤ y
          · have hsub : ∀ z ∈ merge xs (y :: ys), x ≤ z := by
              intro z hz
              rw [mem_merge] at hz
              rcases hz with hz | hz
              · exact (List.pairwise_cons.mp hL).1 z hz
              · simp at hz
                rcases hz with hz | hz
                · subst z
                  exact hxy
                · exact le_trans hxy ((List.pairwise_cons.mp hM).1 z hz)
            have hsort : (merge xs (y :: ys)).Pairwise (· ≤ ·) := by
              exact ihL (y :: ys) (List.pairwise_cons.mp hL).2 hM
            simpa [merge, hxy] using (List.pairwise_cons.mpr ⟨hsub, hsort⟩)
          · have hle : y ≤ x := le_of_not_ge hxy
            have hsub : ∀ z ∈ merge (x :: xs) ys, y ≤ z := by
              intro z hz
              rw [mem_merge] at hz
              rcases hz with hz | hz
              · simp at hz
                rcases hz with hz | hz
                · subst z
                  exact hle
                · exact le_trans hle ((List.pairwise_cons.mp hL).1 z hz)
              · exact (List.pairwise_cons.mp hM).1 z hz
            have hsort : (merge (x :: xs) ys).Pairwise (· ≤ ·) := by
              exact ihM (List.pairwise_cons.mp hM).2
            simpa [merge, hxy] using (List.pairwise_cons.mpr ⟨hsub, hsort⟩)

/-- Adding a constant to every element of a sorted list keeps it sorted. -/
lemma map_add_pairwise (x : ℕ) {L : List ℕ} (hL : L.Pairwise (· ≤ ·)) :
    (L.map (fun s => s + x)).Pairwise (· ≤ ·) := by
  exact List.Pairwise.map (fun s => s + x) (by intro a b h; exact Nat.add_le_add_right h x) hL

/-! ## TRIM and Lemma 35.5

TRIM scans a sorted list in increasing order and keeps the first element, then
keeps an element `y` only when `(1 + δ) · last < y`, where `last` is the last
kept element; otherwise `y` is within a factor `(1 + δ)` of `last` and is
dropped.  Lemma 35.5 states the invariant: every element of the input list has
a kept representative within a factor `(1 + δ)` below it. -/

/-- The greedy tail scan of TRIM: with the previously kept element `last`,
keeps `y` iff `(1 + δ) · last < y`, otherwise recurses keeping `last`. -/
def trimAux (δ : ℝ) : ℕ → List ℕ → List ℕ
  | last, [] => []
  | last, y :: ys =>
      if (1 + δ) * (last : ℝ) < (y : ℝ) then
        y :: trimAux δ y ys
      else
        trimAux δ last ys

/-- The **TRIM** of a sorted list `L` with parameter `δ` (CLRS §35.5,
TRIM(L, δ)): keeps the first element and then every element exceeding
`(1 + δ)` times the last kept element. -/
def trim (δ : ℝ) : List ℕ → List ℕ
  | [] => []
  | y :: ys => y :: trimAux δ y ys

/-- Every element of a trimmed tail was an element of that tail. -/
lemma trimAux_mem_subset (δ : ℝ) : ∀ (last : ℕ) {ys : List ℕ} {z : ℕ},
    z ∈ trimAux δ last ys → z ∈ ys := by
  intro last ys z hz
  induction ys generalizing last with
  | nil => simp [trimAux] at hz
  | cons y ys ih =>
      by_cases hkeep : (1 + δ) * (last : ℝ) < (y : ℝ)
      · simp [trimAux, hkeep] at hz
        rcases hz with hz | hz
        · subst z
          simp
        · exact List.mem_cons.mpr (Or.inr (ih y hz))
      · simp [trimAux, hkeep] at hz
        exact List.mem_cons.mpr (Or.inr (ih last hz))

/-- Every kept element of TRIM was an element of the input list. -/
lemma mem_trim_subset (δ : ℝ) {L : List ℕ} {z : ℕ} (hz : z ∈ trim δ L) : z ∈ L := by
  cases L with
  | nil => simp [trim] at hz
  | cons y ys =>
      simp [trim] at hz
      rcases hz with hz | hz
      · subst z
        simp
      · exact List.mem_cons.mpr (Or.inr (trimAux_mem_subset δ y hz))

/-- The tail scan of TRIM returns a sublist of the scanned tail. -/
lemma trimAux_sublist (δ : ℝ) : ∀ (last : ℕ) (ys : List ℕ), trimAux δ last ys <+ ys := by
  intro last ys
  induction ys generalizing last with
  | nil => simp [trimAux]
  | cons y ys ih =>
      by_cases hkeep : (1 + δ) * (last : ℝ) < (y : ℝ)
      · have hsub : trimAux δ y ys <+ ys := ih y
        simpa [trimAux, hkeep] using hsub.cons_cons y
      · simpa [trimAux, hkeep] using (ih last).cons y

/-- TRIM returns a sublist of its input list. -/
lemma trim_sublist (δ : ℝ) : ∀ L : List ℕ, trim δ L <+ L := by
  intro L
  cases L with
  | nil => simp [trim]
  | cons y ys =>
      have hsub : trimAux δ y ys <+ ys := trimAux_sublist δ y ys
      simpa [trim] using hsub.cons_cons y

/-- TRIM keeps a subsequence of a sorted list, so its output is sorted. -/
lemma trim_sorted {δ : ℝ} {L : List ℕ} (hL : L.Pairwise (· ≤ ·)) : (trim δ L).Pairwise (· ≤ ·) := by
  exact List.Pairwise.sublist (trim_sublist δ L) hL

/-- The tail scan represents every element of the scanned tail: for every `y`
in the tail, some `z` among the tail scan's output plus the reference `last`
satisfies `z ≤ y ≤ (1 + δ) · z`.  This is the induction core of Lemma 35.5. -/
lemma trimAux_rep {δ : ℝ} (hδ : 0 ≤ δ) :
    ∀ (last : ℕ) {ys : List ℕ}, ys.Pairwise (· ≤ ·) →
      (∀ y ∈ ys, (last : ℝ) ≤ (y : ℝ)) →
      ∀ y ∈ ys, ∃ z ∈ last :: trimAux δ last ys,
        (z : ℝ) ≤ (y : ℝ) ∧ (y : ℝ) ≤ (1 + δ) * (z : ℝ) := by
  intro last ys
  induction ys generalizing last with
  | nil => intro hys hle y hy; simp at hy
  | cons x xs ih =>
      intro hys hle y hy
      simp at hy
      rcases hy with hy | hy
      · subst y
        by_cases hkeep : (1 + δ) * (last : ℝ) < (x : ℝ)
        · refine ⟨x, by simp [trimAux, hkeep], ?_⟩
          have hx0 : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast Nat.zero_le x
          constructor
          · rfl
          · nlinarith
        · refine ⟨last, by simp [trimAux, hkeep], ?_⟩
          have hlastx : (last : ℝ) ≤ (x : ℝ) := by exact_mod_cast (hle x (by simp))
          exact ⟨hlastx, le_of_not_gt hkeep⟩
      · by_cases hkeep : (1 + δ) * (last : ℝ) < (x : ℝ)
        · rcases (ih x (List.pairwise_cons.mp hys).2
            (by intro z hz; exact_mod_cast (List.pairwise_cons.mp hys).1 z hz) y hy) with ⟨z, hz, hlo, hhi⟩
          exact ⟨z, by simp [trimAux, hkeep, hz], hlo, hhi⟩
        · rcases (ih last (List.pairwise_cons.mp hys).2
            (by intro z hz; exact_mod_cast (hle z (by simp [hz]))) y hy) with ⟨z, hz, hlo, hhi⟩
          exact ⟨z, by simp [trimAux, hkeep, hz], hlo, hhi⟩

/--
**Lemma 35.5 (TRIM).**  For a sorted list `L` and `δ ≥ 0`, every element `y` of
`L` is represented in `TRIM(L, δ)` by some `z` with `z ≤ y ≤ (1 + δ) · z`: a
kept element represents itself and a dropped element is within a factor
`(1 + δ)` of the last kept element below it (CLRS §35.5, Lemma 35.5).
-/
lemma trim_rep {δ : ℝ} (hδ : 0 ≤ δ) {L : List ℕ} (hL : L.Pairwise (· ≤ ·)) :
    ∀ y ∈ L, ∃ z ∈ trim δ L, (z : ℝ) ≤ (y : ℝ) ∧ (y : ℝ) ≤ (1 + δ) * (z : ℝ) := by
  induction L with
  | nil => intro y hy; simp at hy
  | cons x xs ih =>
      intro y hy
      simp at hy
      rcases hy with hy | hy
      · subst y
        refine ⟨x, by simp [trim], ?_⟩
        have hx0 : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast Nat.zero_le x
        constructor
        · rfl
        · nlinarith
      · rcases (trimAux_rep hδ x (List.pairwise_cons.mp hL).2
            (by intro z hz; exact_mod_cast (List.pairwise_cons.mp hL).1 z hz) y hy)
          with ⟨z, hz, hlo, hhi⟩
        exact ⟨z, by simp [trim, hz], hlo, hhi⟩

/-! ## APPROX-SUBSET-SUM and its approximation guarantee

APPROX-SUBSET-SUM runs the exact algorithm but inserts `Lᵢ ← TRIM(Lᵢ, ε/(2n))`
after each merge and then drops every element exceeding `t`; it returns the
largest element `z*` of the final list.  The trimmed lists never lose a value
beyond a compounded `(1 + ε/(2n))^i` factor, which gives Theorem 35.7. -/

/-- The trimmed lists `Lᵢ` of APPROX-SUBSET-SUM: after processing the whole
list, every element exceeding `t` is dropped.  `approxLists δ t xs` is the
final list `Lₙ` for `S = xs` with trim parameter `δ`. -/
def approxLists (δ : ℝ) (t : ℕ) : List ℕ → List ℕ
  | [] => [0]
  | x :: xs =>
      let L := approxLists δ t xs
      (trim δ (merge L (L.map (fun s => s + x)))).filter (fun s => s ≤ t)

/-- The trimmed lists stay sorted. -/
lemma approxLists_sorted (δ : ℝ) (t : ℕ) : ∀ xs : List ℕ, (approxLists δ t xs).Pairwise (· ≤ ·) := by
  intro xs
  induction xs with
  | nil => simp [approxLists]
  | cons x xs ih =>
      have hmerge : (merge (approxLists δ t xs) ((approxLists δ t xs).map (fun s => s + x))).Pairwise (· ≤ ·) :=
        merge_sorted _ _ ih (map_add_pairwise x ih)
      have htrim : (trim δ (merge (approxLists δ t xs) ((approxLists δ t xs).map (fun s => s + x)))).Pairwise (· ≤ ·) :=
        trim_sorted hmerge
      have hfilter : ((trim δ (merge (approxLists δ t xs) ((approxLists δ t xs).map (fun s => s + x)))).filter (fun s => s ≤ t)).Pairwise (· ≤ ·) :=
        List.Pairwise.filter (fun s => s ≤ t) htrim
      simpa [approxLists] using hfilter

/-- If `0` belongs to a sorted list, TRIM keeps it (it is the least element,
hence the head). -/
lemma zero_mem_trim {δ : ℝ} {L : List ℕ} (hL : L.Pairwise (· ≤ ·)) (h0 : 0 ∈ L) :
    0 ∈ trim δ L := by
  cases L with
  | nil => simp at h0
  | cons y ys =>
      have hy0 : y = 0 := by
        simp at h0
        rcases h0 with h0 | h0
        · exact h0.symm
        · have hyz : y ≤ 0 := (List.pairwise_cons.mp hL).1 0 h0
          exact le_antisymm hyz (Nat.zero_le y)
      subst y
      simp [trim]

/-- `0` is always present on the trimmed lists (the empty subset is never
lost and never exceeds the target). -/
lemma zero_mem_approxLists (δ : ℝ) (t : ℕ) (xs : List ℕ) : 0 ∈ approxLists δ t xs := by
  induction xs with
  | nil => simp [approxLists]
  | cons x xs ih =>
      have h0L : 0 ∈ approxLists δ t xs := ih
      have h0merged : 0 ∈ merge (approxLists δ t xs) ((approxLists δ t xs).map (fun s => s + x)) := by
        exact (mem_merge).2 (Or.inl h0L)
      have h0trim : 0 ∈ trim δ (merge (approxLists δ t xs) ((approxLists δ t xs).map (fun s => s + x))) := by
        exact zero_mem_trim
          (merge_sorted _ _ (approxLists_sorted δ t xs) (map_add_pairwise x (approxLists_sorted δ t xs))) h0merged
      exact List.mem_filter.mpr ⟨h0trim, by simp⟩

/-- Every value on the trimmed lists is an achievable subset sum of the input
list (TRIM only drops values and MERGE only combines existing values), so
APPROX-SUBSET-SUM never returns a sum that is not a subset sum. -/
lemma approxLists_subset_subsetSums (δ : ℝ) (t : ℕ) :
    ∀ xs : List ℕ, ∀ z ∈ approxLists δ t xs, z ∈ subsetSums xs := by
  intro xs
  induction xs with
  | nil => intro z hz; simp [approxLists] at hz; subst z; simp [subsetSums]
  | cons x xs ih =>
      intro z hz
      simp [approxLists] at hz
      rcases hz with ⟨hztrim, hzle⟩
      have hzmerge : z ∈ merge (approxLists δ t xs) ((approxLists δ t xs).map (fun s => s + x)) :=
        mem_trim_subset δ hztrim
      rw [mem_merge] at hzmerge
      rcases hzmerge with hzL | hzLx
      · exact subsetSums_cons_subset (ih z hzL)
      · rcases (List.mem_map.mp hzLx) with ⟨s, hsL, hs⟩
        subst z
        exact mem_subsetSums_add (ih s hsL)

/-- Every value on the trimmed lists is at most the target `t` (they pass the
`≤ t` filter of APPROX-SUBSET-SUM). -/
lemma mem_approxLists_le_t (δ : ℝ) (t : ℕ) :
    ∀ xs : List ℕ, ∀ z ∈ approxLists δ t xs, z ≤ t := by
  intro xs
  induction xs with
  | nil => intro z hz; simp [approxLists] at hz; subst z; exact Nat.zero_le t
  | cons x xs ih =>
      intro z hz
      simp [approxLists] at hz
      exact hz.2

/--
After `i` levels of trimming with parameter `δ`, every achievable sum
`y ≤ t` of the first `i` elements has a representative `z` in `Lᵢ` with
`y ≤ (1 + δ)^i · z` and `z ≤ y`.  Each level of TRIM contributes one factor
`(1 + δ)`; the factor compounds over the `i` merges (CLRS §35.5,
Exercise 35.5-2).
-/
lemma approxLists_prefix_rep {δ : ℝ} (hδ : 0 ≤ δ) (t : ℕ) :
    ∀ ps : List ℕ, ∀ y ∈ subsetSums ps, y ≤ t →
      ∃ z ∈ approxLists δ t ps,
        ((y : ℝ) ≤ (1 + δ) ^ ps.length * (z : ℝ)) ∧ ((z : ℝ) ≤ (y : ℝ)) := by
  intro ps
  induction ps with
  | nil =>
      intro y hy hle
      have hy0 : y = 0 := by
        simpa [subsetSums] using hy
      subst y
      refine ⟨0, by simp [approxLists], ?_⟩
      simp
  | cons x xs ih =>
      intro y hy hle
      rcases (mem_subsetSums_cons.mp hy) with hyxs | ⟨s, hsxs, hs⟩
      · rcases (ih y hyxs hle) with ⟨z0, hz0, hlo0, hhi0⟩
        have hz0merged : z0 ∈ merge (approxLists δ t xs) ((approxLists δ t xs).map (fun s => s + x)) := by
          exact (mem_merge).2 (Or.inl hz0)
        rcases (trim_rep hδ
            (merge_sorted _ _ (approxLists_sorted δ t xs) (map_add_pairwise x (approxLists_sorted δ t xs)))
            z0 hz0merged) with ⟨z, hztrim, hzle_z0, hz0_le⟩
        have hzle_t : z ≤ t := by
          exact le_trans (by exact_mod_cast (hzle_z0.trans hhi0)) hle
        refine ⟨z, by simp [approxLists, hztrim, hzle_t], ?_⟩
        constructor
        · rw [List.length_cons]
          have hpow0 : 0 ≤ (1 + δ) ^ xs.length := pow_nonneg (by linarith) _
          have hscale : (1 + δ) ^ xs.length * (z0 : ℝ) ≤ (1 + δ) ^ xs.length * ((1 + δ) * (z : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hz0_le hpow0
          calc
            (y : ℝ) ≤ (1 + δ) ^ xs.length * (z0 : ℝ) := hlo0
            _ ≤ (1 + δ) ^ xs.length * ((1 + δ) * (z : ℝ)) := hscale
            _ = (1 + δ) ^ (xs.length + 1) * (z : ℝ) := by
              rw [pow_succ]
              ring
        · exact hzle_z0.trans hhi0
      · subst y
        have hsle : s ≤ t := by omega
        rcases (ih s hsxs hsle) with ⟨z0, hz0, hlo0, hhi0⟩
        let w : ℕ := z0 + x
        have hwmerged : w ∈ merge (approxLists δ t xs) ((approxLists δ t xs).map (fun s => s + x)) := by
          apply (mem_merge).2
          right
          exact List.mem_map.mpr ⟨z0, hz0, rfl⟩
        rcases (trim_rep hδ
            (merge_sorted _ _ (approxLists_sorted δ t xs) (map_add_pairwise x (approxLists_sorted δ t xs)))
            w hwmerged) with ⟨z, hztrim, hzle_w, hw_le⟩
        have hzle_t : z ≤ t := by
          have hwy : w ≤ s + x := by
            dsimp [w]
            exact Nat.add_le_add_right (by exact_mod_cast hhi0) x
          exact le_trans (by exact_mod_cast (hzle_w.trans (by exact_mod_cast hwy : (w : ℝ) ≤ (s + x : ℝ)))) hle
        refine ⟨z, by simp [approxLists, hztrim, hzle_t], ?_⟩
        constructor
        · rw [List.length_cons]
          have hpow0 : 0 ≤ (1 + δ) ^ xs.length := pow_nonneg (by linarith) _
          have hpowge1 : (1 : ℝ) ≤ (1 + δ) ^ xs.length := by
            simpa using (pow_le_pow_left₀ (a := (1 : ℝ)) (b := (1 + δ)) (by norm_num) (by linarith) xs.length)
          have hzx_le : (z0 : ℝ) + (x : ℝ) ≤ (1 + δ) * (z : ℝ) := by
            have hw_eq : (z0 : ℝ) + (x : ℝ) = (w : ℝ) := by
              exact_mod_cast (show z0 + x = w by rfl)
            rw [hw_eq]
            exact hw_le
          have hxscale : (x : ℝ) ≤ (1 + δ) ^ xs.length * (x : ℝ) := by
            exact le_mul_of_one_le_left (by exact_mod_cast Nat.zero_le x) hpowge1
          have hz0x_le : (1 + δ) ^ xs.length * (z0 : ℝ) + (x : ℝ) ≤ (1 + δ) ^ xs.length * ((z0 : ℝ) + (x : ℝ)) := by
            nlinarith [hxscale]
          calc
            ↑(s + x) ≤ (1 + δ) ^ xs.length * (z0 : ℝ) + (x : ℝ) := by
              have hdist : ↑(s + x) = (s : ℝ) + (x : ℝ) := by norm_num
              rw [hdist]
              simpa [add_comm] using add_le_add_right hlo0 (x : ℝ)
            _ ≤ (1 + δ) ^ xs.length * ((z0 : ℝ) + (x : ℝ)) := hz0x_le
            _ ≤ (1 + δ) ^ xs.length * ((1 + δ) * (z : ℝ)) := by
              exact mul_le_mul_of_nonneg_left hzx_le hpow0
            _ = (1 + δ) ^ (xs.length + 1) * (z : ℝ) := by
              rw [pow_succ]
              ring
        · have hwy : w ≤ s + x := by
            dsimp [w]
            exact Nat.add_le_add_right (by exact_mod_cast hhi0) x
          exact (by exact_mod_cast hzle_w : (z : ℝ) ≤ (w : ℝ)).trans (by exact_mod_cast hwy)

/-- The value `z*` returned by **APPROX-SUBSET-SUM(S, t, ε)**: the largest
element of the final trimmed list, computed with trim parameter `ε/(2n)`
(CLRS §35.5, APPROX-SUBSET-SUM line 8). -/
def approxSum (xs : List ℕ) (t : ℕ) (ε : ℝ) : ℕ :=
  ((approxLists (ε / (2 * (xs.length : ℝ))) t xs).toFinset).max' (by
    exact ⟨0, by simpa [zero_mem_approxLists]⟩)

/-- The value `z*` belongs to the final trimmed list of APPROX-SUBSET-SUM. -/
lemma approxSum_mem (xs : List ℕ) (t : ℕ) (ε : ℝ) :
    approxSum xs t ε ∈ approxLists (ε / (2 * (xs.length : ℝ))) t xs := by
  have hm : approxSum xs t ε ∈ (approxLists (ε / (2 * (xs.length : ℝ))) t xs).toFinset := by
    dsimp [approxSum]
    exact Finset.max'_mem (approxLists (ε / (2 * (xs.length : ℝ))) t xs).toFinset
      (by exact ⟨0, by simp [zero_mem_approxLists]⟩)
  simpa using hm

/-- The value returned for the empty list is `0`. -/
lemma approxSum_nil (t : ℕ) (ε : ℝ) : approxSum [] t ε = 0 := by
  simp [approxSum, approxLists]

/-- APPROX-SUBSET-SUM returns a value `z*` that is an achievable subset sum:
`z* ∈ subsetSums xs` (Theorem 35.7, correctness). -/
lemma approxSum_mem_subsetSums (xs : List ℕ) (t : ℕ) (ε : ℝ) :
    approxSum xs t ε ∈ subsetSums xs := by
  exact approxLists_subset_subsetSums (ε / (2 * (xs.length : ℝ))) t xs (approxSum xs t ε)
    (approxSum_mem xs t ε)

/-- APPROX-SUBSET-SUM returns a value `z*` not exceeding the target `t`
(Theorem 35.7, correctness). -/
lemma approxSum_le_t (xs : List ℕ) (t : ℕ) (ε : ℝ) : approxSum xs t ε ≤ t := by
  exact mem_approxLists_le_t (ε / (2 * (xs.length : ℝ))) t xs (approxSum xs t ε)
    (approxSum_mem xs t ε)

/--
**Theorem 35.7 (explicit factor).**  APPROX-SUBSET-SUM(S, t, ε) returns a value
`z*` such that the optimum `y*` satisfies
`y* ≤ (1 + ε/(2n))^n · z*`, where `n = |S|`.  This is the compounded
`(1 + ε/(2n))^n` representation error over all `n` trimming levels (CLRS §35.5,
Theorem 35.7).
-/
theorem approxSubsetSum_approx (xs : List ℕ) (t : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    (optimalSum xs t : ℝ) ≤
      (1 + ε / (2 * (xs.length : ℝ))) ^ xs.length * (approxSum xs t ε : ℝ) := by
  let δ : ℝ := ε / (2 * (xs.length : ℝ))
  have hδ : 0 ≤ δ := by
    dsimp [δ]
    exact div_nonneg hε (by positivity)
  have hrep := approxLists_prefix_rep (δ := δ) (hδ := hδ) t xs
  rcases hrep (optimalSum xs t) (optimalSum_mem_subsetSums xs t) (optimalSum_le_t xs t)
      with ⟨z, hz, hlo, hhi⟩
  have hzle : (z : ℝ) ≤ (approxSum xs t ε : ℝ) := by
    have hzs : z ∈ (approxLists (ε / (2 * (xs.length : ℝ))) t xs).toFinset := by
      simpa [δ] using hz
    have hzleN : z ≤ approxSum xs t ε := by
      exact Finset.le_max' (approxLists (ε / (2 * (xs.length : ℝ))) t xs).toFinset z hzs
    exact_mod_cast hzleN
  have hpow0 : 0 ≤ (1 + δ) ^ xs.length := pow_nonneg (by linarith) _
  calc
    (optimalSum xs t : ℝ) ≤ (1 + δ) ^ xs.length * (z : ℝ) := hlo
    _ ≤ (1 + δ) ^ xs.length * (approxSum xs t ε : ℝ) := by
      exact mul_le_mul_of_nonneg_left hzle hpow0

/-! ## The `(1 + ε)` bound (Theorem 35.7, final form)

To reach the clean `(1 + ε)` factor of CLRS Theorem 35.7, the compounded error
`(1 + ε/(2n))^n` must be absorbed: since `(1 + ε/(2n)) ≤ e^{ε/(2n)}`, raising to
the `n`-th power gives `(1 + ε/(2n))^n ≤ e^{ε/2}`, and `e^{ε/2} ≤ 1 + ε` for
`0 ≤ ε ≤ 1`. -/

/-- For `0 ≤ ε ≤ 1`, `(1 + ε/(2n))^n ≤ 1 + ε`: the compounded per-level error
`(1 + ε/(2n))^n` of the `n` trims is bounded by `e^{ε/2} ≤ 1 + ε`
(CLRS §35.5, inequalities (35.26)-(35.29)). -/
lemma pow_one_add_half_le_one_add {ε : ℝ} {n : ℕ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (1 + ε / (2 * (n : ℝ))) ^ n ≤ 1 + ε := by
  by_cases hn : n = 0
  · subst n
    simp [hε0]
  · have hstep1 : (1 + ε / (2 * (n : ℝ))) ^ n ≤ Real.exp (ε / 2) := by
      have hδnz : 0 ≤ 1 + ε / (2 * (n : ℝ)) := by positivity
      have hbase : 1 + ε / (2 * (n : ℝ)) ≤ Real.exp (ε / (2 * (n : ℝ))) := by
        simpa [add_comm] using (Real.add_one_le_exp (ε / (2 * (n : ℝ))))
      have hpow : (1 + ε / (2 * (n : ℝ))) ^ n ≤ (Real.exp (ε / (2 * (n : ℝ)))) ^ n := by
        exact pow_le_pow_left₀ hδnz hbase n
      have htwo : (2 * (n : ℝ)) ≠ 0 := by
        exact_mod_cast (show (2 * n : ℕ) ≠ 0 by omega)
      calc
        (1 + ε / (2 * (n : ℝ))) ^ n ≤ (Real.exp (ε / (2 * (n : ℝ)))) ^ n := hpow
        _ = Real.exp (n * (ε / (2 * (n : ℝ)))) := by rw [Real.exp_nat_mul]
        _ = Real.exp (ε / 2) := by
          congr 1
          field_simp [htwo]
    have hstep2 : Real.exp (ε / 2) ≤ 1 + ε := by
      have hx0 : 0 ≤ ε / 2 := by linarith
      have hx1 : ε / 2 ≤ 1 := by linarith
      have hx2 : |ε / 2| ≤ 1 := by
        rw [abs_of_nonneg hx0]
        exact hx1
      have hb := Real.abs_exp_sub_one_sub_id_le (x := ε / 2) hx2
      have hb' : Real.exp (ε / 2) - 1 - ε / 2 ≤ (ε / 2) ^ 2 := (abs_le.mp hb).2
      have hexp : Real.exp (ε / 2) ≤ 1 + ε / 2 + (ε / 2) ^ 2 := by linarith
      have hsq : (ε / 2) ^ 2 ≤ ε / 2 := by
        have hmul := mul_le_mul_of_nonneg_left hx1 hx0
        nlinarith
      have htail : 1 + ε / 2 + (ε / 2) ^ 2 ≤ 1 + ε := by
        nlinarith [hsq]
      exact le_trans hexp htail
    exact le_trans hstep1 hstep2

/--
**Theorem 35.7.**  For `0 < ε ≤ 1`, APPROX-SUBSET-SUM(S, t, ε) is a
`(1 + ε)`-approximation of the subset-sum problem: the optimum `y*` satisfies
`y* ≤ (1 + ε) · z*` for the returned value `z*` (CLRS §35.5, Theorem 35.7).
-/
theorem approxSubsetSum_approx_lt (xs : List ℕ) (t : ℕ) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (optimalSum xs t : ℝ) ≤ (1 + ε) * (approxSum xs t ε : ℝ) := by
  by_cases hn : xs.length = 0
  · have hlen : xs = [] := by simpa using hn
    subst xs
    rw [optimalSum_nil, approxSum_nil]
    simp
  · have hεnz : 0 ≤ ε := le_of_lt hε0
    have hpow := pow_one_add_half_le_one_add (ε := ε) (n := xs.length) hεnz hε1
    have hmain := approxSubsetSum_approx xs t ε hεnz
    have hz0 : 0 ≤ (approxSum xs t ε : ℝ) := by exact_mod_cast Nat.zero_le (approxSum xs t ε)
    calc
      (optimalSum xs t : ℝ) ≤ (1 + ε / (2 * (xs.length : ℝ))) ^ xs.length * (approxSum xs t ε : ℝ) := hmain
      _ ≤ (1 + ε) * (approxSum xs t ε : ℝ) := by
        exact mul_le_mul_of_nonneg_right hpow hz0

end ApproxSubsetSum

end CLRS

import Mathlib
import CLRSLean.Chapter_03.Section_03_1_Asymptotic_Notation
import CLRSLean.FourthEdition.Chapter_32.Section_32_1_String_Model

/-!
# Section 32.5 - Suffix arrays

This section formalizes the suffix-array data structure of CLRS §32.5: the
array of starting positions of a text's suffixes sorted into lexicographic
order, together with suffix-array-based pattern search.

A suffix array is a permutation of the positions `0 .. n-1` such that reading
the positions in order lists the suffixes in non-decreasing lexicographic
order.  Once the suffixes are sorted, every position at which a pattern `p`
occurs corresponds to a suffix that begins with `p`, so a single linear pass
recovers exactly the occurrence set.

Main results:

- Definition {lit}`suffixAt`: the suffix of a text starting at a given position.
- Definition {lit}`suffixLe`: the lexicographic order on suffixes, with ties
  broken by starting position (a total order, so the construction is
  well-defined even when a text has repeated suffixes).
- Definition {lit}`SuffixArrayValid`: the validity predicate — a permutation of
  the positions that is sorted by {lit}`suffixLe`.
- Definition {lit}`suffixArray`: an executable construction (insertion sort of
  the positions by {lit}`suffixLe`).
- Theorem {lit}`suffixArray_valid`: the construction returns a valid suffix
  array.
- Definition {lit}`suffixArraySearch`: suffix-array-based pattern search.
- Theorem {lit}`suffixArraySearch_mem_iff`: the search result is *sound and
  complete* — an index `i` is returned exactly when `p` is a prefix of
  {lit}`suffixAt t i` (i.e. `p` occurs at position `i`).

## Complexity

The baseline construction sorts `n` positions by insertion sort (`O(n³)`
worst-case work) and the scan search costs `O(n · |p|)`.  This section also
adds the textbook-complexity construction layer: {lit}`suffixArrayFast` (merge
sort under a comparison model) with an explicit `O(n log n)` work theorem
({lit}`suffixArrayFast_work_isBigO_nlogn`), proved valid by
{lit}`suffixArrayFast_valid` against the same {lit}`SuffixArrayValid`
specification.  The `O(|p| log n)` binary-search range query remains recorded
as remaining work.

Notation conventions used in this section:

- `t` : the text (a {lit}`Text α`, i.e. `List α`)
- `p` : a pattern (also a `List α`)
- `n` : `t.length`
- `i`, `j` : positions (natural numbers, `0`-indexed)
-/

namespace CLRS
namespace Chapter32

open Chapter03

variable {α : Type} [LinearOrder α]

/-- The suffix of `t` starting at position `i` (the substring `t[i:]`). -/
def suffixAt (t : Text α) (i : ℕ) : Text α := t.drop i

/-- Lexicographic order on suffixes, with ties broken by the starting index:
`suffix t i < suffix t j`, or equal suffixes with `i ≤ j`. -/
def suffixLe (t : Text α) (i j : ℕ) : Prop :=
  suffixAt t i < suffixAt t j ∨ (suffixAt t i = suffixAt t j ∧ i ≤ j)

/-- `suffixLe` is decidable. -/
instance suffixLe_decidable (t : Text α) : DecidableRel (suffixLe t) :=
  fun i j => by unfold suffixLe suffixAt; infer_instance

/-- `suffixLe` is total: any two indices are comparable by suffix order. -/
instance suffixLe_total (t : Text α) : Std.Total (suffixLe t) :=
  ⟨fun i j => by
    rcases trichotomous_of (· < ·) (suffixAt t i) (suffixAt t j) with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases le_total i j with hij | hji
      · exact Or.inl (Or.inr ⟨h, hij⟩)
      · exact Or.inr (Or.inr ⟨h.symm, hji⟩)
    · exact Or.inr (Or.inl h)⟩

/-- `suffixLe` is transitive. -/
instance suffixLe_trans (t : Text α) : IsTrans ℕ (suffixLe t) :=
  ⟨fun i j k hij hjk => by
    rcases hij with h1 | h1
    · rcases hjk with h2 | h2
      · exact Or.inl (List.lt_trans h1 h2)
      · rcases h2 with ⟨hjk_eq, _⟩
        exact Or.inl (by simpa [hjk_eq] using h1)
    · rcases h1 with ⟨hij_eq, hij_le⟩
      rcases hjk with h2 | h2
      · exact Or.inl (by simpa [hij_eq] using h2)
      · rcases h2 with ⟨hjk_eq, hjk_le⟩
        exact Or.inr ⟨hij_eq.trans hjk_eq, le_trans hij_le hjk_le⟩⟩

/-- The suffix array of `t`: the indices `0..t.length-1` sorted by their
suffix's lexicographic order. -/
def suffixArray (t : Text α) : List ℕ :=
  List.insertionSort (suffixLe t) (List.range t.length)

/-- A list is a valid suffix array for `t` when it is a permutation of the
indices and is sorted by the suffix order. -/
def SuffixArrayValid (t : Text α) (sa : List ℕ) : Prop :=
  sa.Perm (List.range t.length) ∧ List.Pairwise (suffixLe t) sa

/-- The suffix-array construction is valid: it is a sorted permutation of the
indices. -/
theorem suffixArray_valid (t : Text α) : SuffixArrayValid t (suffixArray t) := by
  constructor
  · exact List.perm_insertionSort (suffixLe t) (List.range t.length)
  · exact List.pairwise_insertionSort (suffixLe t) (List.range t.length)

omit [LinearOrder α] in
/-- A pattern is a prefix of a text iff the text's prefix of the pattern's
length equals the pattern. -/
theorem isPrefix_iff_take_eq (p s : Text α) : isPrefix p s ↔ s.take p.length = p := by
  constructor
  · rintro ⟨t, ht⟩
    rw [← ht]
    simp
  · intro h
    refine ⟨s.drop p.length, ?_⟩
    exact (congrArg (fun x => x ++ s.drop p.length) h.symm).trans (List.take_append_drop p.length s)

/-- Suffix-array pattern search: all indices whose suffix begins with `p`,
in suffix-array order. -/
def suffixArraySearch (t : Text α) (p : Text α) : List ℕ :=
  (suffixArray t).filter (fun i => decide ((suffixAt t i).take p.length = p))

/-- **Soundness and completeness of suffix-array search.**  An index `i` is
returned iff `i` is a valid position and `p` is a prefix of `suffixAt t i`
(equivalently, `p` occurs at position `i`). -/
theorem suffixArraySearch_mem_iff (t : Text α) (p : Text α) (i : ℕ) :
    i ∈ suffixArraySearch t p ↔ i < t.length ∧ isPrefix p (suffixAt t i) := by
  unfold suffixArraySearch
  rw [List.mem_filter]
  rw [(suffixArray_valid t).1.mem_iff]
  rw [List.mem_range]
  constructor
  · rintro ⟨hi, hpref⟩
    exact ⟨hi, (isPrefix_iff_take_eq p (suffixAt t i)).mpr (of_decide_eq_true hpref)⟩
  · rintro ⟨hi, hpref⟩
    exact ⟨hi, decide_eq_true ((isPrefix_iff_take_eq p (suffixAt t i)).mp hpref)⟩

/-! ## Textbook-complexity construction

The baseline above proves correctness but uses insertion sort.  This section
adds a comparison-model construction: the suffix array is produced by merge
sort, and a unit of work is charged for each lexicographic suffix comparison.
The construction cost is proved to be `O(n log n)` comparisons, and the result
is proved to satisfy the same {lit}`SuffixArrayValid` specification.
-/

/-- One lexicographic suffix comparison, charged as a single unit of work in the
comparison model. -/
def suffixCompare (t : Text α) (i j : ℕ) : Bool := decide (suffixLe t i j)

/-- `suffixCompare` is equivalent to `suffixLe`. -/
theorem suffixCompare_eq_true_iff (t : Text α) (i j : ℕ) :
    suffixCompare t i j = true ↔ suffixLe t i j := by
  simp [suffixCompare]

/-- `suffixCompare` is transitive (so merge sort returns a sorted list). -/
theorem suffixCompare_trans (t : Text α) (i j k : ℕ)
    (hij : suffixCompare t i j = true) (hjk : suffixCompare t j k = true) :
    suffixCompare t i k = true := by
  have hij' : suffixLe t i j := (suffixCompare_eq_true_iff t i j).mp hij
  have hjk' : suffixLe t j k := (suffixCompare_eq_true_iff t j k).mp hjk
  exact decide_eq_true ((inferInstance : IsTrans ℕ (suffixLe t)).trans i j k hij' hjk')

/-- `suffixCompare` is total (so merge sort compares any two suffixes). -/
theorem suffixCompare_total (t : Text α) (i j : ℕ) :
    (suffixCompare t i j || suffixCompare t j i) = true := by
  rcases (suffixLe_total (t := t)).total i j with h | h
  · simp [suffixCompare, decide_eq_true h]
  · simp [suffixCompare, decide_eq_true h]

/-- Costed merge: merges two sorted lists and charges one comparison per step. -/
def mergeWithCost (t : Text α) : List ℕ → List ℕ → List ℕ × Nat
  | [], ys => (ys, 0)
  | xs, [] => (xs, 0)
  | x :: xs, y :: ys =>
      if suffixCompare t x y then
        let r := mergeWithCost t xs (y :: ys)
        (x :: r.1, r.2 + 1)
      else
        let r := mergeWithCost t (x :: xs) ys
        (y :: r.1, r.2 + 1)

/-- Costed merge sort, splitting at `(n+1)/2` exactly like {lit}`List.mergeSort`. -/
def mergeSortWithCost (t : Text α) : List ℕ → List ℕ × Nat
  | [] => ([], 0)
  | [x] => ([x], 0)
  | a :: b :: xs =>
      let lr := (a :: b :: xs).splitAt (((a :: b :: xs).length + 1) / 2)
      let sl := mergeSortWithCost t lr.1
      let sr := mergeSortWithCost t lr.2
      let sm := mergeWithCost t sl.1 sr.1
      (sm.1, sl.2 + sr.2 + sm.2)
  termination_by xs => xs.length

/-- Erasing the merge cost recovers {lit}`List.merge`. -/
theorem mergeWithCost_result (t : Text α) (xs ys : List ℕ) :
    (mergeWithCost t xs ys).1 = List.merge xs ys (suffixCompare t) := by
  induction h : xs.length + ys.length using Nat.strong_induction_on generalizing xs ys with
  | h n ih =>
      cases xs with
      | nil => simp [mergeWithCost]
      | cons x xs =>
          cases ys with
          | nil => simp [mergeWithCost]
          | cons y ys =>
              by_cases hc : suffixCompare t x y
              · simp [mergeWithCost, hc]
                apply ih (xs.length + (y :: ys).length) ?_ xs (y :: ys) rfl
                simp [List.length_cons] at *
                omega
              · simp [mergeWithCost, hc]
                apply ih ((x :: xs).length + ys.length) ?_ (x :: xs) ys rfl
                simp [List.length_cons] at *
                omega

/-- A merge preserves the multiset of the two input lists. -/
theorem mergeWithCost_perm (t : Text α) (xs ys : List ℕ) :
    (mergeWithCost t xs ys).1.Perm (xs ++ ys) := by
  rw [mergeWithCost_result]
  exact List.merge_perm_append (suffixCompare t)

/-- A merge of two sorted lists is sorted. -/
theorem mergeWithCost_sorted (t : Text α) {xs ys : List ℕ}
    (hxs : List.Pairwise (suffixLe t) xs) (hys : List.Pairwise (suffixLe t) ys) :
    List.Pairwise (suffixLe t) (mergeWithCost t xs ys).1 := by
  rw [mergeWithCost_result]
  have hxs' : List.Pairwise (fun a b => suffixCompare t a b = true) xs :=
    hxs.imp (fun {a b} (hab : suffixLe t a b) =>
      (suffixCompare_eq_true_iff t a b).mpr hab)
  have hys' : List.Pairwise (fun a b => suffixCompare t a b = true) ys :=
    hys.imp (fun {a b} (hab : suffixLe t a b) =>
      (suffixCompare_eq_true_iff t a b).mpr hab)
  have h := List.pairwise_merge (suffixCompare_trans t) (suffixCompare_total t) xs ys hxs' hys'
  exact h.imp (fun {a b} (hab : suffixCompare t a b = true) =>
    (suffixCompare_eq_true_iff t a b).mp hab)

/-- `(n + 1) / 2 < n` for `2 ≤ n`. -/
theorem half_succ_lt_self (n : ℕ) (hn : 2 ≤ n) : (n + 1) / 2 < n := by omega

/-- `n - (n + 1) / 2 = n / 2`. -/
theorem sub_half_succ_eq_half (n : ℕ) : n - (n + 1) / 2 = n / 2 := by omega

/-- `n / 2 < n` for `1 ≤ n`. -/
theorem div_two_lt_self (n : ℕ) (hn : 1 ≤ n) : n / 2 < n := by omega

/-- Merge sort is a permutation. -/
theorem mergeSortWithCost_perm (t : Text α) (xs : List ℕ) :
    (mergeSortWithCost t xs).1.Perm xs := by
  induction h : xs.length using Nat.strong_induction_on generalizing xs with
  | h n ih =>
      cases xs with
      | nil => simp [mergeSortWithCost]
      | cons a rest =>
          cases rest with
          | nil => simp [mergeSortWithCost]
          | cons b rest =>
              simp only [mergeSortWithCost]
              rw [List.splitAt_eq]
              let l1 := (a :: b :: rest).take (((a :: b :: rest).length + 1) / 2)
              let l2 := (a :: b :: rest).drop (((a :: b :: rest).length + 1) / 2)
              change (mergeWithCost t (mergeSortWithCost t l1).1
                  (mergeSortWithCost t l2).1).1.Perm (a :: b :: rest)
              have hlt1 : l1.length < n := by
                have hL : 2 ≤ (a :: b :: rest).length := by simp [List.length_cons]
                calc
                  l1.length ≤ ((a :: b :: rest).length + 1) / 2 := by simp [l1, List.length_take]
                  _ < (a :: b :: rest).length := half_succ_lt_self _ hL
                  _ = n := h
              have hlt2 : l2.length < n := by
                have hL : 1 ≤ (a :: b :: rest).length := by simp [List.length_cons]
                calc
                  l2.length = (a :: b :: rest).length - ((a :: b :: rest).length + 1) / 2 := by
                    simp [l2, List.length_drop]
                  _ = (a :: b :: rest).length / 2 := sub_half_succ_eq_half _
                  _ < (a :: b :: rest).length := div_two_lt_self _ hL
                  _ = n := h
              have h1 : (mergeSortWithCost t l1).1.Perm l1 := ih l1.length hlt1 l1 rfl
              have h2 : (mergeSortWithCost t l2).1.Perm l2 := ih l2.length hlt2 l2 rfl
              have hmerge := mergeWithCost_perm t (mergeSortWithCost t l1).1
                (mergeSortWithCost t l2).1
              exact hmerge.trans ((h1.append h2).trans (by
                rw [List.take_append_drop]))

/-- Merge sort returns a sorted list. -/
theorem mergeSortWithCost_sorted (t : Text α) (xs : List ℕ) :
    List.Pairwise (suffixLe t) (mergeSortWithCost t xs).1 := by
  induction h : xs.length using Nat.strong_induction_on generalizing xs with
  | h n ih =>
      cases xs with
      | nil => simp [mergeSortWithCost]
      | cons a rest =>
          cases rest with
          | nil => simp [mergeSortWithCost]
          | cons b rest =>
              simp only [mergeSortWithCost]
              rw [List.splitAt_eq]
              let l1 := (a :: b :: rest).take (((a :: b :: rest).length + 1) / 2)
              let l2 := (a :: b :: rest).drop (((a :: b :: rest).length + 1) / 2)
              change List.Pairwise (suffixLe t)
                (mergeWithCost t (mergeSortWithCost t l1).1 (mergeSortWithCost t l2).1).1
              have hlt1 : l1.length < n := by
                have hL : 2 ≤ (a :: b :: rest).length := by simp [List.length_cons]
                calc
                  l1.length ≤ ((a :: b :: rest).length + 1) / 2 := by simp [l1, List.length_take]
                  _ < (a :: b :: rest).length := half_succ_lt_self _ hL
                  _ = n := h
              have hlt2 : l2.length < n := by
                have hL : 1 ≤ (a :: b :: rest).length := by simp [List.length_cons]
                calc
                  l2.length = (a :: b :: rest).length - ((a :: b :: rest).length + 1) / 2 := by
                    simp [l2, List.length_drop]
                  _ = (a :: b :: rest).length / 2 := sub_half_succ_eq_half _
                  _ < (a :: b :: rest).length := div_two_lt_self _ hL
                  _ = n := h
              have h1 : List.Pairwise (suffixLe t) (mergeSortWithCost t l1).1 :=
                ih l1.length hlt1 l1 rfl
              have h2 : List.Pairwise (suffixLe t) (mergeSortWithCost t l2).1 :=
                ih l2.length hlt2 l2 rfl
              exact mergeWithCost_sorted t h1 h2

/-- A merge charges at most one comparison per merged element. -/
theorem mergeWithCost_cost_le (t : Text α) (xs ys : List ℕ) :
    (mergeWithCost t xs ys).2 ≤ xs.length + ys.length := by
  induction h : xs.length + ys.length using Nat.strong_induction_on generalizing xs ys with
  | h n ih =>
      cases xs with
      | nil => simp [mergeWithCost]
      | cons x xs =>
          cases ys with
          | nil => simp [mergeWithCost]
          | cons y ys =>
              by_cases hc : suffixCompare t x y
              · simp [mergeWithCost, hc]
                have hrec := ih (xs.length + (y :: ys).length) (by
                  simp [List.length_cons] at *; omega) xs (y :: ys) rfl
                simp [List.length_cons] at *
                omega
              · simp [mergeWithCost, hc]
                have hrec := ih ((x :: xs).length + ys.length) (by
                  simp [List.length_cons] at *; omega) (x :: xs) ys rfl
                simp [List.length_cons] at *
                omega

/-- `Nat.clog 2 n ≤ Nat.log 2 n + 1`. -/
theorem clog_two_le_log_two_add_one (n : ℕ) :
    Nat.clog 2 n ≤ Nat.log 2 n + 1 := by
  rw [Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)]
  exact Nat.le_of_lt (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n)

/-- Halving drops the ceiling-log by one (for `n ≥ 2`). -/
theorem clog_two_ceil_half_le_pred (n : ℕ) (hn : 2 ≤ n) :
    Nat.clog 2 ((n + 1) / 2) ≤ Nat.clog 2 n - 1 := by
  have h := Nat.clog_of_two_le (by norm_num : 1 < 2) hn
  have h' : n + 2 - 1 = n + 1 := by omega
  rw [h'] at h
  rw [h]
  omega

/-- The floor half also drops the ceiling-log by one (for `n ≥ 2`). -/
theorem clog_two_floor_half_le_pred (n : ℕ) (hn : 2 ≤ n) :
    Nat.clog 2 (n / 2) ≤ Nat.clog 2 n - 1 := by
  have hdiv : n / 2 ≤ (n + 1) / 2 := Nat.div_le_div_right (by omega : n ≤ n + 1)
  exact (Nat.clog_mono_right 2 hdiv).trans (clog_two_ceil_half_le_pred n hn)

/-- Merge sort performs at most `length · ⌈log₂ length⌉` comparisons. -/
theorem mergeSortWithCost_cost_le_clog (t : Text α) (xs : List ℕ) :
    (mergeSortWithCost t xs).2 ≤ xs.length * Nat.clog 2 xs.length := by
  induction h : xs.length using Nat.strong_induction_on generalizing xs with
  | h n ih =>
      cases xs with
      | nil => simp [mergeSortWithCost]
      | cons a rest =>
          cases rest with
          | nil => simp [mergeSortWithCost]
          | cons b rest =>
              simp only [mergeSortWithCost]
              rw [List.splitAt_eq]
              let l1 := List.take (((a :: b :: rest).length + 1) / 2) (a :: b :: rest)
              let l2 := List.drop (((a :: b :: rest).length + 1) / 2) (a :: b :: rest)
              change (mergeSortWithCost t l1).2 + (mergeSortWithCost t l2).2 +
                  (mergeWithCost t (mergeSortWithCost t l1).1 (mergeSortWithCost t l2).1).2 ≤
                  n * Nat.clog 2 n
              have hlen1 : l1.length = ((a :: b :: rest).length + 1) / 2 := by
                simp [l1, List.length_take]; omega
              have hlen2 : l2.length = (a :: b :: rest).length / 2 := by
                simp [l2, List.length_drop]; omega
              have hlt1 : l1.length < n := by
                have hL : 2 ≤ (a :: b :: rest).length := by simp [List.length_cons]
                calc
                  l1.length ≤ ((a :: b :: rest).length + 1) / 2 := by simp [l1, List.length_take]
                  _ < (a :: b :: rest).length := half_succ_lt_self _ hL
                  _ = n := h
              have hlt2 : l2.length < n := by
                have hL : 1 ≤ (a :: b :: rest).length := by simp [List.length_cons]
                calc
                  l2.length = (a :: b :: rest).length - ((a :: b :: rest).length + 1) / 2 := by
                    simp [l2, List.length_drop]
                  _ = (a :: b :: rest).length / 2 := sub_half_succ_eq_half _
                  _ < (a :: b :: rest).length := div_two_lt_self _ hL
                  _ = n := h
              have h1 := ih l1.length hlt1 l1 rfl
              have h2 := ih l2.length hlt2 l2 rfl
              have hmerge := mergeWithCost_cost_le t (mergeSortWithCost t l1).1
                (mergeSortWithCost t l2).1
              have hlen1' : (mergeSortWithCost t l1).1.length = l1.length :=
                (mergeSortWithCost_perm t l1).length_eq
              have hlen2' : (mergeSortWithCost t l2).1.length = l2.length :=
                (mergeSortWithCost_perm t l2).length_eq
              have hclog1 : Nat.clog 2 l1.length + 1 ≤ Nat.clog 2 (a :: b :: rest).length := by
                have hpos : 1 ≤ Nat.clog 2 (a :: b :: rest).length :=
                  Nat.clog_pos (by norm_num) (by simp [List.length_cons])
                have hc := clog_two_ceil_half_le_pred (a :: b :: rest).length (by simp)
                rw [hlen1]
                omega
              have hclog2 : Nat.clog 2 l2.length + 1 ≤ Nat.clog 2 (a :: b :: rest).length := by
                have hpos : 1 ≤ Nat.clog 2 (a :: b :: rest).length :=
                  Nat.clog_pos (by norm_num) (by simp [List.length_cons])
                have hc := clog_two_floor_half_le_pred (a :: b :: rest).length (by simp)
                rw [hlen2]
                omega
              have hlen_sum : l1.length + l2.length = (a :: b :: rest).length := by
                rw [hlen1, hlen2]; simp; omega
              have h1c : (mergeSortWithCost t l1).2 + l1.length ≤
                  l1.length * Nat.clog 2 (a :: b :: rest).length := by
                have hdist : l1.length * Nat.clog 2 l1.length + l1.length =
                    l1.length * (Nat.clog 2 l1.length + 1) := by ring
                nlinarith [h1, hclog1]
              have h2c : (mergeSortWithCost t l2).2 + l2.length ≤
                  l2.length * Nat.clog 2 (a :: b :: rest).length := by
                nlinarith [h2, hclog2]
              have hmerge' : (mergeWithCost t (mergeSortWithCost t l1).1
                  (mergeSortWithCost t l2).1).2 ≤ l1.length + l2.length := by
                simpa [hlen1', hlen2'] using hmerge
              calc
                (mergeSortWithCost t l1).2 + (mergeSortWithCost t l2).2 +
                    (mergeWithCost t (mergeSortWithCost t l1).1
                      (mergeSortWithCost t l2).1).2 ≤
                    (mergeSortWithCost t l1).2 + (mergeSortWithCost t l2).2 +
                      (l1.length + l2.length) := Nat.add_le_add_left hmerge' _
                _ ≤ l1.length * Nat.clog 2 (a :: b :: rest).length +
                      l2.length * Nat.clog 2 (a :: b :: rest).length := by
                    nlinarith [h1c, h2c]
                _ = n * Nat.clog 2 n := by
                    rw [← Nat.add_mul, hlen_sum, h]

/-- Merge sort performs at most `length · (⌊log₂ length⌋ + 1)` comparisons. -/
theorem mergeSortWithCost_cost_le_log (t : Text α) (xs : List ℕ) :
    (mergeSortWithCost t xs).2 ≤ xs.length * Nat.log 2 xs.length + xs.length := by
  have h := Nat.mul_le_mul_left xs.length (clog_two_le_log_two_add_one xs.length)
  nlinarith [mergeSortWithCost_cost_le_clog t xs, h]

/-- The fast suffix-array construction (comparison model, merge sort). -/
def suffixArrayFast (t : Text α) : List ℕ :=
  (mergeSortWithCost t (List.range t.length)).1

/-- The comparison work of the fast suffix-array construction. -/
def suffixArrayBuildWork (t : Text α) : Nat :=
  (mergeSortWithCost t (List.range t.length)).2

/-- The fast construction is a valid suffix array. -/
theorem suffixArrayFast_valid (t : Text α) :
    SuffixArrayValid t (suffixArrayFast t) := by
  constructor
  · exact (mergeSortWithCost_perm t (List.range t.length))
  · exact mergeSortWithCost_sorted t (List.range t.length)

/-- The fast construction performs at most `n · (⌊log₂ n⌋ + 1)` comparisons. -/
theorem suffixArrayFast_work_le (t : Text α) :
    suffixArrayBuildWork t ≤ t.length * (Nat.log 2 t.length + 1) := by
  unfold suffixArrayBuildWork
  have h := mergeSortWithCost_cost_le_log t (List.range t.length)
  rw [List.length_range] at h
  nlinarith

/-- The fast construction is `O(n log n)` under the comparison model. -/
theorem suffixArrayFast_work_isBigO_nlogn :
    isBigO (fun n : ℕ => (n * Nat.log 2 n + n : ℝ))
      (fun n : ℕ => (n : ℝ) * (Nat.log 2 n : ℝ)) := by
  rw [isBigO_iff]
  refine ⟨2, by norm_num, 2, fun n hn => ?_⟩
  have hlog : (1 : ℝ) ≤ (Nat.log 2 n : ℝ) := by
    exact_mod_cast (Nat.log_pos (by norm_num : 1 < 2) hn)
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  have hn' : (0 : ℝ) ≤ n := by positivity
  have hmul : (n : ℝ) ≤ (n : ℝ) * (Nat.log 2 n : ℝ) := by
    calc
      (n : ℝ) = 1 * (n : ℝ) := by ring
      _ ≤ (Nat.log 2 n : ℝ) * (n : ℝ) := mul_le_mul_of_nonneg_right hlog hn'
      _ = (n : ℝ) * (Nat.log 2 n : ℝ) := by ring
  calc
    (n : ℝ) * (Nat.log 2 n : ℝ) + (n : ℝ) ≤
        (n : ℝ) * (Nat.log 2 n : ℝ) + (n : ℝ) * (Nat.log 2 n : ℝ) :=
      add_le_add_right hmul ((n : ℝ) * (Nat.log 2 n : ℝ))
    _ = 2 * ((n : ℝ) * (Nat.log 2 n : ℝ)) := by ring

/-! ## Textbook-complexity range query

The binary-search range query (`O(|p| log n)`) is recorded as remaining work in
the chapter ledger; the scan-based {lit}`suffixArraySearch` above already
provides a complete, proved correctness baseline.
-/

end Chapter32
end CLRS

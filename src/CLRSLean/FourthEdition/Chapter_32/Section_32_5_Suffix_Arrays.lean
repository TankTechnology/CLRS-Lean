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
adds the textbook-complexity layers:

- {lit}`suffixArrayFast` (merge sort under a comparison model) with an explicit
  `O(n log n)` work theorem ({lit}`suffixArrayFast_work_isBigO_nlogn`), proved
  valid by {lit}`suffixArrayFast_valid` against the same {lit}`SuffixArrayValid`
  specification.
- {lit}`suffixArrayRange`, the binary-search range query: two binary searches
  over the sorted suffix array find the lower/upper bounds of the pattern's
  interval.  {lit}`suffixArrayRange_mem_iff` proves the returned range is sound
  and complete, and {lit}`suffixArrayQueryWork_le` bounds the query work by
  `2 · (|p| + 1) · (⌊log₂ n⌋ + 2)` character comparisons under the stated
  string-comparison model (jointly `O(|p| log n)`, via
  {lit}`suffixArrayQueryWork_isBigO_logn`).

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

The `O(n log n)` construction above gives a sorted suffix array.  This section
adds the other half of CLRS §32.5: a pattern search that finds every occurrence
of `p` by *two* binary searches over that array.  Each probe compares `p`
against one suffix; in the stated string-comparison model a probe costs at most
`|p| + 1` character comparisons, so the whole query runs in `O(|p| log n)`.

A suffix begins with `p` exactly when it lies between the two bounds

- {lit}`patternLE p s`: `p ≤ s` lexicographically (the lower-bound predicate),
  and
- {lit}`patternGT p s`: `p < s` and `p` is not a prefix of `s` (the
  upper-bound predicate).

Because the suffix array is sorted by {lit}`suffixLe`, both predicates are
monotone along it, so each bound is found by binary search.
-/

/-- `p` is at-or-before suffix `s` in lexicographic order: the lower-bound
predicate of the range query. -/
def patternLE (p s : Text α) : Prop := p ≤ s

/-- `s` is strictly after every suffix that begins with `p`: the upper-bound
predicate of the range query. -/
def patternGT (p s : Text α) : Prop := p < s ∧ s.take p.length ≠ p

/-- `patternLE` is decidable. -/
instance patternLE_decidable (p s : Text α) : Decidable (patternLE p s) := by
  unfold patternLE; infer_instance

/-- `patternGT` is decidable. -/
instance patternGT_decidable (p s : Text α) : Decidable (patternGT p s) := by
  unfold patternGT; infer_instance

/-- The empty list is at-or-before every list in lexicographic order. -/
theorem nil_le (l : Text α) : [] ≤ l := by
  rcases l with _ | ⟨b, l⟩
  · exact le_rfl
  · exact le_of_lt ((List.lt_iff_lex_lt [] (b :: l)).mp List.Lex.nil)

/-- Taking a prefix is monotone with respect to lexicographic order. -/
theorem take_lex_le {s₁ s₂ : Text α} (hlex : List.Lex (· < ·) s₁ s₂) :
    ∀ k, s₁.take k ≤ s₂.take k := by
  induction hlex with
  | nil =>
      rename_i b l
      intro k
      simpa using (nil_le ((b :: l).take k))
  | rel hlt => intro k; cases k with
      | zero => simp
      | succ k => exact le_of_lt ((List.lt_iff_lex_lt _ _).mp (List.Lex.rel hlt))
  | cons h ih => intro k; cases k with
      | zero => simp
      | succ k => exact List.cons_le_cons _ (ih k)

/-- Taking a prefix is monotone with respect to lexicographic order. -/
theorem take_le_take {s₁ s₂ : Text α} (h : s₁ ≤ s₂) : ∀ k, s₁.take k ≤ s₂.take k := by
  rcases lt_or_eq_of_le h with hlt | rfl
  · exact take_lex_le ((List.lt_iff_lex_lt s₁ s₂).mp hlt)
  · intro k; rfl

/-- A prefix is at-or-before its extension in lexicographic order. -/
theorem le_of_isPrefix {p s : Text α} (h : isPrefix p s) : p ≤ s := by
  rcases h with ⟨r, rfl⟩
  exact le_iff_lt_or_eq.mpr <| match r with
    | [] => Or.inr (by simp)
    | b :: r' =>
        Or.inl ((List.lt_iff_lex_lt p (p ++ b :: r')).mp
          (by simpa using (List.Lex.append_left (· < ·)
            (List.Lex.nil : List.Lex (· < ·) [] (b :: r')) p)))

/-- If `p ≤ s₁ ≤ s₂` and `p` is a prefix of `s₂`, then `p` is a prefix of `s₁`. -/
theorem isPrefix_of_le_of_isPrefix {p s₁ s₂ : Text α}
    (hps : p ≤ s₁) (hss : s₁ ≤ s₂) (hp₂ : isPrefix p s₂) : isPrefix p s₁ := by
  have ht : s₂.take p.length = p := (isPrefix_iff_take_eq p s₂).mp hp₂
  have h₁ : s₁.take p.length ≤ s₂.take p.length := take_le_take hss p.length
  have h₂ : p ≤ s₁.take p.length := by simpa using (take_le_take hps p.length)
  have : s₁.take p.length = p := le_antisymm (by simpa [ht] using h₁) h₂
  exact (isPrefix_iff_take_eq p s₁).mpr this

/-- `patternLE` is monotone in the suffix argument. -/
theorem patternLE_mono {p s₁ s₂ : Text α} (h₁ : patternLE p s₁) (hss : s₁ ≤ s₂) :
    patternLE p s₂ := le_trans h₁ hss

/-- `patternGT` is monotone in the suffix argument. -/
theorem patternGT_mono {p s₁ s₂ : Text α} (h₁ : patternGT p s₁) (hss : s₁ ≤ s₂) :
    patternGT p s₂ := by
  rcases h₁ with ⟨hlt, hne⟩
  constructor
  · exact lt_of_lt_of_le hlt hss
  · intro htake
    have hpfx : isPrefix p s₂ := (isPrefix_iff_take_eq p s₂).mpr htake
    have hpfx₁ : isPrefix p s₁ := isPrefix_of_le_of_isPrefix (le_of_lt hlt) hss hpfx
    exact hne ((isPrefix_iff_take_eq p s₁).mp hpfx₁)

/-- A pattern is a prefix of `s` exactly when it lies between the lower and
upper bounds. -/
theorem isPrefix_iff_patternLE_and_not_patternGT (p s : Text α) :
    isPrefix p s ↔ patternLE p s ∧ ¬ patternGT p s := by
  constructor
  · intro hpfx
    constructor
    · exact le_of_isPrefix hpfx
    · intro hgt
      exact hgt.2 ((isPrefix_iff_take_eq p s).mp hpfx)
  · intro h
    rcases h with ⟨hle, hngt⟩
    rcases lt_or_eq_of_le hle with hlt | heq
    · by_cases hpfx : s.take p.length = p
      · exact (isPrefix_iff_take_eq p s).mpr hpfx
      · exact False.elim (hngt ⟨hlt, hpfx⟩)
    · subst s; exact ⟨[], by simp⟩

/-- `suffixLe` orders suffixes by their lexicographic order. -/
theorem suffixAt_le_of_suffixLe {t : Text α} {i j : ℕ} (h : suffixLe t i j) :
    suffixAt t i ≤ suffixAt t j := by
  rcases h with hlt | ⟨heq, _⟩
  · exact le_of_lt hlt
  · exact le_of_eq heq

/-- In a suffix-array-sorted list, suffixes at smaller positions are at-or-before
suffixes at larger positions. -/
theorem sorted_suffixAt_le {t : Text α} {sa : List ℕ}
    (hsorted : List.Pairwise (suffixLe t) sa) {i j : ℕ}
    (hi : i < sa.length) (hj : j < sa.length) (hij : i < j) :
    suffixAt t sa[i] ≤ suffixAt t sa[j] := by
  exact suffixAt_le_of_suffixLe
    (List.Pairwise.rel_get_of_lt hsorted (a := ⟨i, hi⟩) (b := ⟨j, hj⟩) hij)

/-! ### Binary search

A single reusable costed binary search finds the first index in a list where a
monotone boolean predicate turns true.
-/

/-- Costed binary search for the first index `k` in `[lo, hi)` with
`P (sa.getD k 0)` true, charging one probe per comparison. -/
def binarySearchFirstCostAux (P : ℕ → Bool) (sa : List ℕ) (lo hi : ℕ) : ℕ × Nat :=
  if lo < hi then
    let mid := (lo + hi) / 2
    if P (sa.getD mid 0) then
      let r := binarySearchFirstCostAux P sa lo mid
      (r.1, r.2 + 1)
    else
      let r := binarySearchFirstCostAux P sa (mid + 1) hi
      (r.1, r.2 + 1)
  else
    (lo, 0)
termination_by hi - lo

/-- The pure binary search, erasing the probe count. -/
def binarySearchFirstAux (P : ℕ → Bool) (sa : List ℕ) (lo hi : ℕ) : ℕ :=
  if lo < hi then
    let mid := (lo + hi) / 2
    if P (sa.getD mid 0) then
      binarySearchFirstAux P sa lo mid
    else
      binarySearchFirstAux P sa (mid + 1) hi
  else
    lo
termination_by hi - lo

/-- Erasing the cost recovers the pure binary search. -/
theorem binarySearchFirstCostAux_fst (P : ℕ → Bool) (sa : List ℕ) (lo hi : ℕ) :
    (binarySearchFirstCostAux P sa lo hi).1 = binarySearchFirstAux P sa lo hi := by
  induction h : hi - lo using Nat.strong_induction_on generalizing lo hi with
  | h d ih =>
    unfold binarySearchFirstCostAux binarySearchFirstAux
    by_cases hlt : lo < hi
    · simp only [hlt, ↓reduceIte]
      by_cases hP : P (sa.getD ((lo + hi) / 2) 0)
      · simp only [hP, ↓reduceIte]
        exact ih (((lo + hi) / 2) - lo) (by omega) lo ((lo + hi) / 2) rfl
      · simp only [hP, ↓reduceIte]
        exact ih (hi - ((lo + hi) / 2 + 1)) (by omega) ((lo + hi) / 2 + 1) hi rfl
    · simp only [hlt, ↓reduceIte]

/-- `r` is the first index in `[lo, hi]` where `P` holds along `sa`. -/
def BinarySearchSpec (P : ℕ → Bool) (sa : List ℕ) (lo hi r : ℕ) : Prop :=
  lo ≤ r ∧ r ≤ hi ∧
    (∀ k, lo ≤ k → k < r → P (sa.getD k 0) = false) ∧
    (r < hi → P (sa.getD r 0) = true)

/-- The binary search returns the first index with `P` true (or `hi` if none). -/
theorem binarySearchFirstAux_spec (P : ℕ → Bool) (sa : List ℕ)
    (hmono : ∀ ⦃i j⦄, i < j → j < sa.length →
      P (sa.getD i 0) = true → P (sa.getD j 0) = true) :
    ∀ lo hi, lo ≤ hi → hi ≤ sa.length →
      (∀ k, k < lo → P (sa.getD k 0) = false) →
      (∀ k, hi ≤ k → k < sa.length → P (sa.getD k 0) = true) →
      BinarySearchSpec P sa lo hi (binarySearchFirstAux P sa lo hi) := by
  intro lo hi
  induction h : hi - lo using Nat.strong_induction_on generalizing lo hi with
  | h d ih =>
    intro hle hhi hL hR
    unfold binarySearchFirstAux
    by_cases hlt : lo < hi
    · have hmid_lo : lo ≤ (lo + hi) / 2 := by
        exact (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr (by omega)
      have hmid_hi : (lo + hi) / 2 < hi := by
        exact (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr (by omega)
      have hmid_len : (lo + hi) / 2 < sa.length := lt_of_lt_of_le hmid_hi hhi
      simp only [hlt, ↓reduceIte]
      by_cases hP : P (sa.getD ((lo + hi) / 2) 0) = true
      · rw [if_pos hP]
        have hR' : ∀ k, (lo + hi) / 2 ≤ k → k < sa.length → P (sa.getD k 0) = true := by
          intro k hkmid hkl
          by_cases hk : k = (lo + hi) / 2
          · subst k; exact hP
          · have hmid_lt_k : (lo + hi) / 2 < k := lt_of_le_of_ne hkmid (Ne.symm hk)
            exact hmono hmid_lt_k hkl hP
        have hspec := ih ((lo + hi) / 2 - lo) (by omega) lo ((lo + hi) / 2) rfl
          hmid_lo (le_of_lt hmid_len) hL hR'
        rcases hspec with ⟨hrlo, hrhi, hfalse, htrue⟩
        constructor
        · exact hrlo
        constructor
        · exact le_trans hrhi (le_of_lt hmid_hi)
        constructor
        · exact hfalse
        · intro hrhi'
          by_cases hrm : binarySearchFirstAux P sa lo ((lo + hi) / 2) < (lo + hi) / 2
          · exact htrue hrm
          · have hreq : binarySearchFirstAux P sa lo ((lo + hi) / 2) = (lo + hi) / 2 :=
              le_antisymm hrhi (le_of_not_gt hrm)
            simpa [hreq] using hP
      · rw [if_neg hP]
        have hPfalse : P (sa.getD ((lo + hi) / 2) 0) = false := by
          simpa [Bool.not_eq_true] using hP
        have hmid1_hi : (lo + hi) / 2 + 1 ≤ hi := by omega
        have hL' : ∀ k, k < (lo + hi) / 2 + 1 → P (sa.getD k 0) = false := by
          intro k hklt
          by_cases hklo : k < lo
          · exact hL k hklo
          · have hk_le_mid : k ≤ (lo + hi) / 2 := by omega
            by_cases hkm : k = (lo + hi) / 2
            · subst k; exact hPfalse
            · have hk_lt_mid : k < (lo + hi) / 2 := lt_of_le_of_ne hk_le_mid hkm
              have hkmid_true : P (sa.getD k 0) = true → False := by
                intro hkP
                exact hP (hmono hk_lt_mid hmid_len hkP)
              by_cases hc : P (sa.getD k 0) = true
              · exact (hkmid_true hc).elim
              · exact (Bool.not_eq_true _).mp hc
        have hspec := ih (hi - ((lo + hi) / 2 + 1)) (by omega) ((lo + hi) / 2 + 1) hi rfl
          hmid1_hi hhi hL' hR
        rcases hspec with ⟨hrlo, hrhi, hfalse, htrue⟩
        constructor
        · exact le_trans hmid_lo (le_trans (by omega) hrlo)
        constructor
        · exact hrhi
        constructor
        · intro k hklo hkr
          by_cases hk_mid : k ≤ (lo + hi) / 2
          · exact hL' k (by omega)
          · have hmid1_k : (lo + hi) / 2 + 1 ≤ k := by omega
            exact hfalse k hmid1_k hkr
        · exact htrue
    · simp only [hlt, ↓reduceIte]
      constructor
      · omega
      constructor
      · omega
      constructor
      · intro k hklo hkr; omega
      · intro hrhi; omega

/-- Halving a ceiling-log: `clog 2 (n/2 + 1) ≤ clog 2 (n+1) - 1` for `n ≥ 1`. -/
theorem clog_two_half_add_one_le_pred (n : ℕ) (hn : 1 ≤ n) :
    Nat.clog 2 (n / 2 + 1) ≤ Nat.clog 2 (n + 1) - 1 := by
  have hh := clog_two_ceil_half_le_pred (n + 1) (by omega : 2 ≤ n + 1)
  have hhalf : (n + 1 + 1) / 2 = n / 2 + 1 := by omega
  simpa [hhalf] using hh

/-- The costed binary search performs at most `⌈log₂ (hi - lo + 1)⌉` probes. -/
theorem binarySearchFirstCostAux_cost_le (P : ℕ → Bool) (sa : List ℕ) (lo hi : ℕ) :
    (binarySearchFirstCostAux P sa lo hi).2 ≤ Nat.clog 2 (hi - lo + 1) := by
  induction h : hi - lo using Nat.strong_induction_on generalizing lo hi with
  | h d ih =>
    unfold binarySearchFirstCostAux
    by_cases hlt : lo < hi
    · have hmid_lo : lo ≤ (lo + hi) / 2 := by
        exact (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr (by omega)
      have hmid_hi : (lo + hi) / 2 < hi := by
        exact (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr (by omega)
      simp only [hlt, ↓reduceIte]
      by_cases hP : P (sa.getD ((lo + hi) / 2) 0) = true
      · rw [if_pos hP, ← h]
        have hrec := ih (((lo + hi) / 2) - lo) (by omega) lo ((lo + hi) / 2) rfl
        have hmid_eq : (lo + hi) / 2 - lo = (hi - lo) / 2 := by omega
        rw [hmid_eq] at hrec
        have hclogpos : 1 ≤ Nat.clog 2 (hi - lo + 1) := by
          exact Nat.succ_le_of_lt (Nat.clog_pos (by decide : 1 < 2) (by omega : 2 ≤ hi - lo + 1))
        have hclog : Nat.clog 2 ((hi - lo) / 2 + 1) ≤ Nat.clog 2 (hi - lo + 1) - 1 := by
          exact clog_two_half_add_one_le_pred (hi - lo) (by omega)
        have hstep : Nat.clog 2 ((hi - lo) / 2 + 1) + 1 ≤ Nat.clog 2 (hi - lo + 1) :=
          Nat.add_le_of_le_sub hclogpos hclog
        calc
          (binarySearchFirstCostAux P sa lo ((lo + hi) / 2)).2 + 1
              ≤ Nat.clog 2 ((hi - lo) / 2 + 1) + 1 := Nat.add_le_add_right hrec 1
          _ ≤ Nat.clog 2 (hi - lo + 1) := hstep
      · rw [if_neg hP, ← h]
        have hrec := ih (hi - ((lo + hi) / 2 + 1)) (by omega) ((lo + hi) / 2 + 1) hi rfl
        have hsub_le : hi - ((lo + hi) / 2 + 1) ≤ (hi - lo) / 2 := by omega
        have hclogpos : 1 ≤ Nat.clog 2 (hi - lo + 1) := by
          exact Nat.succ_le_of_lt (Nat.clog_pos (by decide : 1 < 2) (by omega : 2 ≤ hi - lo + 1))
        have hclog' : Nat.clog 2 (hi - ((lo + hi) / 2 + 1) + 1) ≤ Nat.clog 2 ((hi - lo) / 2 + 1) := by
          exact Nat.clog_mono_right 2 (by omega)
        have hclog : Nat.clog 2 ((hi - lo) / 2 + 1) ≤ Nat.clog 2 (hi - lo + 1) - 1 := by
          exact clog_two_half_add_one_le_pred (hi - lo) (by omega)
        have hstep : Nat.clog 2 ((hi - lo) / 2 + 1) + 1 ≤ Nat.clog 2 (hi - lo + 1) :=
          Nat.add_le_of_le_sub hclogpos hclog
        calc
          (binarySearchFirstCostAux P sa ((lo + hi) / 2 + 1) hi).2 + 1
              ≤ Nat.clog 2 (hi - ((lo + hi) / 2 + 1) + 1) + 1 := Nat.add_le_add_right hrec 1
          _ ≤ Nat.clog 2 ((hi - lo) / 2 + 1) + 1 := Nat.add_le_add_right hclog' 1
          _ ≤ Nat.clog 2 (hi - lo + 1) := hstep
    · simp only [hlt, ↓reduceIte]
      exact Nat.zero_le _

/-- Binary search for the first index in a whole list with `P` true. -/
def binarySearchFirst (P : ℕ → Bool) (sa : List ℕ) : ℕ :=
  binarySearchFirstAux P sa 0 sa.length

/-- The costed binary search over a whole list. -/
def binarySearchFirstCost (P : ℕ → Bool) (sa : List ℕ) : ℕ × Nat :=
  binarySearchFirstCostAux P sa 0 sa.length

/-- The whole-list binary search returns the first index with `P` true. -/
theorem binarySearchFirst_spec (P : ℕ → Bool) (sa : List ℕ)
    (hmono : ∀ ⦃i j⦄, i < j → j < sa.length →
      P (sa.getD i 0) = true → P (sa.getD j 0) = true) :
    (binarySearchFirst P sa) ≤ sa.length ∧
      (∀ k, k < binarySearchFirst P sa → P (sa.getD k 0) = false) ∧
      (binarySearchFirst P sa < sa.length → P (sa.getD (binarySearchFirst P sa) 0) = true) := by
  have hspec := binarySearchFirstAux_spec P sa hmono 0 sa.length
    (Nat.zero_le _) le_rfl (by intro k hk; omega) (by intro k hk hkl; omega)
  rcases hspec with ⟨hrlo, hrhi, hfalse, htrue⟩
  constructor
  · exact hrhi
  constructor
  · intro k hkr
    exact hfalse k (Nat.zero_le _) hkr
  · exact htrue

/-- The whole-list costed binary search performs at most `⌈log₂ (n+1)⌉` probes. -/
theorem binarySearchFirstCost_cost_le (P : ℕ → Bool) (sa : List ℕ) :
    (binarySearchFirstCost P sa).2 ≤ Nat.clog 2 (sa.length + 1) := by
  unfold binarySearchFirstCost
  exact binarySearchFirstCostAux_cost_le P sa 0 sa.length

/-! ### The range query -/

/-- The decidable lower-bound probe: does the suffix at position `x` reach the
pattern? -/
def lowerDecide (t : Text α) (p : Text α) (x : ℕ) : Bool :=
  decide (patternLE p (suffixAt t x))

/-- The decidable upper-bound probe: is the suffix at position `x` strictly past
every suffix beginning with `p`? -/
def upperDecide (t : Text α) (p : Text α) (x : ℕ) : Bool :=
  decide (patternGT p (suffixAt t x))

/-- `lowerDecide` is monotone along a sorted suffix array. -/
theorem lowerDecide_mono {t : Text α} {p : Text α} {sa : List ℕ}
    (hsorted : List.Pairwise (suffixLe t) sa) (i j : ℕ)
    (hij : i < j) (hj : j < sa.length) :
    lowerDecide t p (sa.getD i 0) = true → lowerDecide t p (sa.getD j 0) = true := by
  intro hi
  have hi_lt : i < sa.length := lt_trans hij hj
  have hle : suffixAt t (sa.getD i 0) ≤ suffixAt t (sa.getD j 0) := by
    have hg : suffixAt t sa[i] ≤ suffixAt t sa[j] :=
      sorted_suffixAt_le hsorted hi_lt hj hij
    have hiD : sa.getD i 0 = sa[i] := List.getD_eq_getElem sa 0 hi_lt
    have hjD : sa.getD j 0 = sa[j] := List.getD_eq_getElem sa 0 hj
    simpa only [hiD, hjD] using hg
  have hle' : patternLE p (suffixAt t (sa.getD i 0)) := of_decide_eq_true hi
  have hle'' : patternLE p (suffixAt t (sa.getD j 0)) := patternLE_mono hle' hle
  exact decide_eq_true hle''

/-- `upperDecide` is monotone along a sorted suffix array. -/
theorem upperDecide_mono {t : Text α} {p : Text α} {sa : List ℕ}
    (hsorted : List.Pairwise (suffixLe t) sa) (i j : ℕ)
    (hij : i < j) (hj : j < sa.length) :
    upperDecide t p (sa.getD i 0) = true → upperDecide t p (sa.getD j 0) = true := by
  intro hi
  have hi_lt : i < sa.length := lt_trans hij hj
  have hle : suffixAt t (sa.getD i 0) ≤ suffixAt t (sa.getD j 0) := by
    have hg : suffixAt t sa[i] ≤ suffixAt t sa[j] :=
      sorted_suffixAt_le hsorted hi_lt hj hij
    have hiD : sa.getD i 0 = sa[i] := List.getD_eq_getElem sa 0 hi_lt
    have hjD : sa.getD j 0 = sa[j] := List.getD_eq_getElem sa 0 hj
    simpa only [hiD, hjD] using hg
  have hle' : patternGT p (suffixAt t (sa.getD i 0)) := of_decide_eq_true hi
  have hle'' : patternGT p (suffixAt t (sa.getD j 0)) := patternGT_mono hle' hle
  exact decide_eq_true hle''

/-- The lower bound of the pattern's interval in the fast suffix array. -/
def suffixArrayLower (t : Text α) (p : Text α) : ℕ :=
  binarySearchFirst (lowerDecide t p) (suffixArrayFast t)

/-- The upper bound of the pattern's interval in the fast suffix array. -/
def suffixArrayUpper (t : Text α) (p : Text α) : ℕ :=
  binarySearchFirst (upperDecide t p) (suffixArrayFast t)

/-- The lower bound is at most the upper bound. -/
theorem suffixArrayLower_le_upper (t : Text α) (p : Text α) :
    suffixArrayLower t p ≤ suffixArrayUpper t p := by
  let sa := suffixArrayFast t
  have hsorted : List.Pairwise (suffixLe t) sa := (suffixArrayFast_valid t).2
  have hlower := binarySearchFirst_spec (lowerDecide t p) sa
    (lowerDecide_mono (t := t) (p := p) hsorted)
  have hupper := binarySearchFirst_spec (upperDecide t p) sa
    (upperDecide_mono (t := t) (p := p) hsorted)
  have hlo_len : suffixArrayLower t p ≤ sa.length := hlower.1
  by_contra hgt
  have hupper_lt_lo : suffixArrayUpper t p < suffixArrayLower t p := lt_of_not_ge hgt
  have hupper_len : suffixArrayUpper t p < sa.length := lt_of_lt_of_le hupper_lt_lo hlo_len
  have hupper_true : upperDecide t p (sa.getD (suffixArrayUpper t p) 0) = true := hupper.2.2 hupper_len
  have hlower_false : lowerDecide t p (sa.getD (suffixArrayUpper t p) 0) = false :=
    hlower.2.1 (suffixArrayUpper t p) hupper_lt_lo
  have hgt_p : patternGT p (suffixAt t (sa.getD (suffixArrayUpper t p) 0)) :=
    of_decide_eq_true hupper_true
  have hle_p : patternLE p (suffixAt t (sa.getD (suffixArrayUpper t p) 0)) :=
    le_of_lt hgt_p.1
  have hlower_true : lowerDecide t p (sa.getD (suffixArrayUpper t p) 0) = true :=
    decide_eq_true hle_p
  exact Bool.noConfusion (hlower_false.symm.trans hlower_true)

/-- The fast range query: the slice of the fast suffix array whose suffixes
begin with `p`. -/
def suffixArrayRange (t : Text α) (p : Text α) : List ℕ :=
  let sa := suffixArrayFast t
  (sa.drop (suffixArrayLower t p)).take (suffixArrayUpper t p - suffixArrayLower t p)

/-- The character-comparison work of the fast range query: two binary searches,
each probe charged `|p| + 1` character comparisons. -/
def suffixArrayQueryWork (t : Text α) (p : Text α) : Nat :=
  let sa := suffixArrayFast t
  let lo := binarySearchFirstCost (lowerDecide t p) sa
  let hi := binarySearchFirstCost (upperDecide t p) sa
  (lo.2 + hi.2) * (p.length + 1)

/-- The lower bound of the interval is where suffixes first reach `p`. -/
theorem suffixArrayLower_spec (t : Text α) (p : Text α) :
    (suffixArrayLower t p ≤ (suffixArrayFast t).length ∧
      (∀ k, k < suffixArrayLower t p → lowerDecide t p ((suffixArrayFast t).getD k 0) = false) ∧
      (suffixArrayLower t p < (suffixArrayFast t).length →
        lowerDecide t p ((suffixArrayFast t).getD (suffixArrayLower t p) 0) = true)) := by
  exact binarySearchFirst_spec (lowerDecide t p) (suffixArrayFast t)
    (lowerDecide_mono (t := t) (p := p) ((suffixArrayFast_valid t).2))

/-- The upper bound of the interval is where suffixes first move past `p`. -/
theorem suffixArrayUpper_spec (t : Text α) (p : Text α) :
    (suffixArrayUpper t p ≤ (suffixArrayFast t).length ∧
      (∀ k, k < suffixArrayUpper t p → upperDecide t p ((suffixArrayFast t).getD k 0) = false) ∧
      (suffixArrayUpper t p < (suffixArrayFast t).length →
        upperDecide t p ((suffixArrayFast t).getD (suffixArrayUpper t p) 0) = true)) := by
  exact binarySearchFirst_spec (upperDecide t p) (suffixArrayFast t)
    (upperDecide_mono (t := t) (p := p) ((suffixArrayFast_valid t).2))

/-- Membership in the slice `(l.drop lo).take (hi - lo)`. -/
theorem mem_drop_take_iff (l : List ℕ) (lo hi x : ℕ) (hlo : lo ≤ hi) :
    x ∈ (l.drop lo).take (hi - lo) ↔ ∃ j, lo ≤ j ∧ j < hi ∧ l[j]? = some x := by
  rw [List.mem_iff_getElem?]
  constructor
  · rintro ⟨k, hk⟩
    rw [List.getElem?_take, List.getElem?_drop] at hk
    have hklt : k < hi - lo := by
      by_cases h : k < hi - lo
      · exact h
      · simp [h] at hk
    have hsome : l[lo + k]? = some x := by
      simpa [hklt] using hk
    refine ⟨lo + k, by omega, by omega, hsome⟩
  · rintro ⟨j, hjlo, hjhi, hsome⟩
    refine ⟨j - lo, ?_⟩
    have hjlt : j - lo < hi - lo := by omega
    rw [List.getElem?_take, List.getElem?_drop]
    simp [hjlt]
    have : lo + (j - lo) = j := by omega
    simpa [this] using hsome

/-- **Soundness and completeness of the fast range query.**  An index `i` is
returned by `suffixArrayRange` exactly when `p` is a prefix of the suffix at
`i` (equivalently, `p` occurs at position `i`). -/
theorem suffixArrayRange_mem_iff (t : Text α) (p : Text α) (i : ℕ) :
    i ∈ suffixArrayRange t p ↔ i < t.length ∧ isPrefix p (suffixAt t i) := by
  let sa := suffixArrayFast t
  have hperm : sa.Perm (List.range t.length) := (suffixArrayFast_valid t).1
  have hlo_hi : suffixArrayLower t p ≤ suffixArrayUpper t p := suffixArrayLower_le_upper t p
  have hlower := suffixArrayLower_spec t p
  have hupper := suffixArrayUpper_spec t p
  unfold suffixArrayRange
  rw [mem_drop_take_iff sa (suffixArrayLower t p) (suffixArrayUpper t p) i hlo_hi]
  constructor
  · rintro ⟨j, hjlo, hjhi, hsome⟩
    have hj : j < sa.length := lt_of_lt_of_le hjhi hupper.1
    have hsai : sa[j] = i := by
      rw [List.getElem?_eq_some_iff] at hsome
      exact hsome.2
    have hlower_true_j : lowerDecide t p (sa.getD j 0) = true := by
      by_cases hlo_eq : suffixArrayLower t p = j
      · have hgoal : lowerDecide t p (sa.getD (suffixArrayLower t p) 0) = true :=
          hlower.2.2 (by simpa [hlo_eq] using hj)
        simpa only [hlo_eq] using hgoal
      · have hlo_lt : suffixArrayLower t p < sa.length := lt_of_le_of_lt hjlo hj
        have hlo_true : lowerDecide t p (sa.getD (suffixArrayLower t p) 0) = true :=
          hlower.2.2 hlo_lt
        have hlo_lt_j : suffixArrayLower t p < j := lt_of_le_of_ne hjlo hlo_eq
        have hmono := lowerDecide_mono (t := t) (p := p) ((suffixArrayFast_valid t).2)
        exact hmono (suffixArrayLower t p) j hlo_lt_j hj hlo_true
    have hupper_false_j : upperDecide t p (sa.getD j 0) = false := hupper.2.1 j hjhi
    have hle : patternLE p (suffixAt t (sa.getD j 0)) := of_decide_eq_true hlower_true_j
    have hngt : ¬ patternGT p (suffixAt t (sa.getD j 0)) := of_decide_eq_false hupper_false_j
    have hpfx : isPrefix p (suffixAt t (sa.getD j 0)) :=
      (isPrefix_iff_patternLE_and_not_patternGT p (suffixAt t (sa.getD j 0))).mpr ⟨hle, hngt⟩
    have hget : sa.getD j 0 = i := by
      rw [List.getD_eq_getElem sa 0 hj]
      exact hsai
    constructor
    · have hmem : i ∈ List.range t.length := by
        rw [← hperm.mem_iff]
        exact List.mem_iff_getElem?.mpr ⟨j, by simpa only [hget] using hsome⟩
      simpa using hmem
    · simpa only [hget] using hpfx
  · rintro ⟨hi_len, hpfx⟩
    have himem : i ∈ sa := by
      rw [hperm.mem_iff]
      simpa using (List.mem_range.mpr hi_len)
    rcases List.mem_iff_getElem?.mp himem with ⟨j, hsome⟩
    rw [List.getElem?_eq_some_iff] at hsome
    have hj : j < sa.length := hsome.1
    have hji : sa[j] = i := hsome.2
    have hgetD : sa.getD j 0 = i := by
      rw [List.getD_eq_getElem sa 0 hj]
      exact hji
    have hpfx_j : isPrefix p (suffixAt t (sa.getD j 0)) := by
      simpa only [hgetD] using hpfx
    have hboth := (isPrefix_iff_patternLE_and_not_patternGT p (suffixAt t (sa.getD j 0))).mp hpfx_j
    have hlower_true : lowerDecide t p (sa.getD j 0) = true := decide_eq_true hboth.1
    have hupper_false : upperDecide t p (sa.getD j 0) = false :=
      decide_eq_false hboth.2
    have hlo_le_j : suffixArrayLower t p ≤ j := by
      by_contra hneg
      have hj_lt_lo : j < suffixArrayLower t p := lt_of_not_ge hneg
      have hlo_false : lowerDecide t p (sa.getD j 0) = false := hlower.2.1 j hj_lt_lo
      exact Bool.noConfusion (hlo_false.symm.trans hlower_true)
    have hj_lt_hi : j < suffixArrayUpper t p := by
      by_contra hneg
      have hhi_le_j : suffixArrayUpper t p ≤ j := le_of_not_gt hneg
      have hmono := upperDecide_mono (t := t) (p := p) ((suffixArrayFast_valid t).2)
      have hhi_true : upperDecide t p (sa.getD j 0) = true := by
        by_cases hhj : suffixArrayUpper t p = j
        · subst hhj
          exact hupper.2.2 hj
        · have hhi_lt_j : suffixArrayUpper t p < j := lt_of_le_of_ne hhi_le_j hhj
          have hhi_len : suffixArrayUpper t p < sa.length := lt_of_lt_of_le hhi_lt_j (Nat.le_of_lt hj)
          exact hmono (suffixArrayUpper t p) j hhi_lt_j hj (hupper.2.2 hhi_len)
      exact Bool.noConfusion (hupper_false.symm.trans hhi_true)
    refine ⟨j, hlo_le_j, hj_lt_hi, ?_⟩
    rw [List.getElem?_eq_some_iff]
    exact ⟨hj, hji⟩

/-- `Nat.log 2 (n+1) ≤ Nat.log 2 n + 1`. -/
theorem log_succ_le_log_add_one (n : ℕ) : Nat.log 2 (n + 1) ≤ Nat.log 2 n + 1 := by
  by_cases h : n = 0
  · subst n; norm_num [Nat.log]
  · have h1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero h)
    have hle : n + 1 ≤ n * 2 := by omega
    have hlog : Nat.log 2 (n + 1) ≤ Nat.log 2 (n * 2) := Nat.log_monotone (b := 2) hle
    have hlog2 : Nat.log 2 (n * 2) = Nat.log 2 n + 1 := Nat.log_mul_base (by norm_num : 1 < 2) h
    rw [hlog2] at hlog
    exact hlog

/-- `Nat.clog 2 (n+1) ≤ Nat.log 2 n + 2`. -/
theorem clog_succ_le_log_add_two (n : ℕ) : Nat.clog 2 (n + 1) ≤ Nat.log 2 n + 2 := by
  have h := clog_two_le_log_two_add_one (n + 1)
  have h' := Nat.add_le_add_right (log_succ_le_log_add_one n) 1
  omega

/-- The fast range query performs at most `2 · (|p| + 1) · (⌊log₂ n⌋ + 2)`
character comparisons. -/
theorem suffixArrayQueryWork_le (t : Text α) (p : Text α) :
    suffixArrayQueryWork t p ≤ 2 * (p.length + 1) * (Nat.log 2 t.length + 2) := by
  let sa := suffixArrayFast t
  have hlen : sa.length = t.length := by
    exact ((suffixArrayFast_valid t).1).length_eq.trans (List.length_range (n := t.length))
  unfold suffixArrayQueryWork
  have hlo := binarySearchFirstCost_cost_le (lowerDecide t p) sa
  have hhi := binarySearchFirstCost_cost_le (upperDecide t p) sa
  have hclog : Nat.clog 2 (sa.length + 1) ≤ Nat.log 2 t.length + 2 := by
    rw [hlen]
    exact clog_succ_le_log_add_two t.length
  calc
    ((binarySearchFirstCost (lowerDecide t p) sa).2 +
        (binarySearchFirstCost (upperDecide t p) sa).2) * (p.length + 1)
        ≤ (Nat.clog 2 (sa.length + 1) + Nat.clog 2 (sa.length + 1)) * (p.length + 1) :=
          Nat.mul_le_mul_right (p.length + 1) (Nat.add_le_add hlo hhi)
    _ = 2 * (p.length + 1) * Nat.clog 2 (sa.length + 1) := by ring
    _ ≤ 2 * (p.length + 1) * (Nat.log 2 t.length + 2) :=
          Nat.mul_le_mul_left (2 * (p.length + 1)) hclog

/-- For a fixed pattern length `m`, the query work is `O(log n)` in the text
length under the comparison model, with the `|p|` factor carried in the
constant — jointly `O(|p| log n)`. -/
theorem suffixArrayQueryWork_isBigO_logn (m : ℕ) :
    isBigO (fun n : ℕ => (2 * ((m : ℝ) + 1) * (((Nat.log 2 n : ℕ) : ℝ) + 2)))
      (fun n : ℕ => ((m : ℝ) + 1) * ((Nat.log 2 n : ℕ) : ℝ)) := by
  rw [isBigO_iff]
  refine ⟨8, by norm_num, 2, fun n hn => ?_⟩
  have hlog : (1 : ℝ) ≤ (Nat.log 2 n : ℝ) := by
    exact_mod_cast (Nat.log_pos (by norm_num : 1 < 2) (by omega : 2 ≤ n))
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  have hm : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
  nlinarith

end Chapter32
end CLRS

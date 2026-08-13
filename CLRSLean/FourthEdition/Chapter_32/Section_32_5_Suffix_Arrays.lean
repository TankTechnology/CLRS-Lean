import Mathlib
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

## Complexity (honest statement)

The construction sorts `n` positions by insertion sort, so it performs
`O(n²)` suffix comparisons, each of which compares two suffixes of length at
most `n` and therefore costs `O(n)`; the construction is thus `O(n³)` in the
worst case.  The search scans the suffix array once, doing one prefix check of
length `|p|` per position, for `O(n · |p|)` time.  This section deliberately
proves *correctness* of a straightforward executable construction; the
textbook `O(n log n)`-time suffix-array construction and the `O(|p| log n)`
binary-search range query are not yet formalized and are recorded as remaining
optimization work.

Notation conventions used in this section:

- `t` : the text (a {lit}`Text α`, i.e. `List α`)
- `p` : a pattern (also a `List α`)
- `n` : `t.length`
- `i`, `j` : positions (natural numbers, `0`-indexed)
-/

namespace CLRS
namespace Chapter32

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

end Chapter32
end CLRS

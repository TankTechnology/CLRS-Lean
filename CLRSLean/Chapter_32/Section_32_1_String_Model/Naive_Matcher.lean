import Mathlib
import CLRSLean.Chapter_32.Section_32_1_String_Model

/-! # Section 32.1 — Naive String-Matching Algorithm

The naive string-matching algorithm (CLRS §32.1) finds all occurrences of a
pattern `P` of length `m` in a text `T` of length `n` by trying every possible
shift `s = 0, 1, …, n-m` and checking whether `P` matches `T` at that
position.  The worst-case running time is `Θ((n-m+1)·m)` = `O(m·n)`.

## Key definitions

- {lit}`matchesAt T P s` — pattern `P` occurs in text `T` starting at shift `s`.
- {lit}`naiveMatcher T P` — returns the list of all shifts where `P` occurs in `T`.
- {lit}`noMatch` — convenience abbreviation for the empty match list.

## Notation

This file uses {lit}`Text α = List α` from {lit}`Section_32_1_String_Model`
and standard {lit}`Nat`-based lengths.

-/

namespace CLRS
namespace Chapter32

variable {α : Type} [BEq α] [DecidableEq α]

/-- Pattern `P` matches text `T` at shift `s`: the substring of `T` from
position `s` of length `|P|` equals `P`.  Formally,
`(T.drop s).take |P| = P`. -/
def matchesAt (T P : Text α) (s : ℕ) : Bool :=
  if s + P.length ≤ T.length then
    (T.drop s).take P.length == P
  else
    false

/-- The naive string matcher: enumerate all shifts `s ∈ [0, n-m]` and
return those where the pattern matches. -/
def naiveMatcher (T P : Text α) : List ℕ :=
  if P.length = 0 then
    List.range (T.length + 1)
  else
    let n := T.length
    let m := P.length
    let maxShift := n - m
    (List.range (maxShift + 1)).filter fun s => matchesAt T P s

/-- Convenience abbreviation for "no match". -/
abbrev noMatch : List ℕ := []

/-- If a shift `s` is in `naiveMatcher T P`, then `matchesAt T P s` is true. -/
theorem naiveMatcher_sound (T P : Text α) (s : ℕ) (h : s ∈ naiveMatcher T P) :
    matchesAt T P s := by
  unfold naiveMatcher at h
  split at h
  · -- case: P.length = 0
    rename_i hzero
    have hempty : P = [] := by
      cases P
      · rfl
      · simp at hzero
    subst hempty
    unfold matchesAt
    have hs : s ≤ T.length := by
      have := List.mem_range.mp h
      omega
    simp [hs]
  · -- case: P.length ≠ 0
    have hmem := List.mem_filter.mp h
    exact hmem.2

/-- If `matchesAt T P s` is true, then `s` is in `naiveMatcher T P`. -/
theorem naiveMatcher_complete (T P : Text α) (s : ℕ) (hmatch : matchesAt T P s) :
    s ∈ naiveMatcher T P := by
  unfold naiveMatcher
  by_cases hzero : P.length = 0
  · -- empty pattern: all shifts are included, need s ≤ T.length from hmatch
    have hempty : P = [] := by
      cases P
      · rfl
      · simp at hzero
    subst hempty
    unfold matchesAt at hmatch
    -- hmatch: (if s + 0 ≤ T.length then [] == [] else false) = true
    simp at hmatch
    -- hmatch now gives s ≤ T.length
    have hs : s < T.length + 1 := by omega
    simp [hs]
  · -- non-empty pattern
    have hbound : s + P.length ≤ T.length := by
      unfold matchesAt at hmatch
      split at hmatch
      · assumption
      · simp at hmatch
    have hshift : s ≤ T.length - P.length := by
      omega
    have hle : s < (T.length - P.length) + 1 := by omega
    have hmatch' : matchesAt T P s = true := hmatch
    simpa [hzero] using
      List.mem_filter.mpr ⟨List.mem_range.mpr hle, hmatch'⟩

/-- The empty pattern matches at every position. -/
@[simp]
theorem naiveMatcher_empty (T : Text α) : naiveMatcher T [] = List.range (T.length + 1) := by
  unfold naiveMatcher; simp

/-- If the pattern is longer than the text, there are no matches. -/
theorem naiveMatcher_pattern_too_long (T P : Text α) (h : T.length < P.length) :
    naiveMatcher T P = noMatch := by
  unfold naiveMatcher noMatch
  by_cases hzero : P.length = 0
  · -- P is empty, impossible because T.length < 0 would be contradiction
    have : T.length < 0 := by simpa [hzero] using h
    omega
  · have hsub : T.length - P.length = 0 := by omega
    simp [hzero, hsub]
    -- Need to show: filter (matchesAt T P) (range 1) = []
    -- range 1 = [0], and matchesAt T P 0 = false because 0+P.length > T.length
    have hfalse : matchesAt T P 0 = false := by
      unfold matchesAt
      simp
      omega
    simp [hfalse]

/-- Shifts returned by `naiveMatcher` are within bounds. -/
theorem naiveMatcher_shifts_valid (T P : Text α) (s : ℕ) (h : s ∈ naiveMatcher T P) :
    s + P.length ≤ T.length := by
  have hmatch := naiveMatcher_sound T P s h
  unfold matchesAt at hmatch
  split at hmatch
  · assumption
  · simp at hmatch

end Chapter32
end CLRS

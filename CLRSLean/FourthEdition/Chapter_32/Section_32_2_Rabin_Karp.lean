import Mathlib
import CLRSLean.FourthEdition.Chapter_32.Section_32_1_String_Model.Naive_Matcher

/-! # Section 32.2 — The Rabin–Karp Algorithm

The Rabin–Karp algorithm (CLRS §32.2) finds all occurrences of a pattern `P`
in a text `T` by hashing the pattern and every `|P|`-length window of `T`,
and comparing the hashes modulo `q`.  A shift whose hash matches but whose
string does not is a *spurious hit*: the algorithm rules it out with an
explicit character-by-character comparison (`matchesAt`), so it remains
correct for every choice of modulus.

## Key definitions

- {lit}`hash d q val w` — the base-`d` modular hash of `w` over the numeric
  values `val c`, computed by Horner's rule modulo `q`.
- {lit}`rabinKarpMatcher T P d q val` — returns the list of all shifts where
  `P` occurs in `T` (hash match plus explicit comparison), mirroring
  {lit}`naiveMatcher`.

## Main results

- Theorem {lit}`hash_snoc` — the O(1) incremental update
  `hash (w ++ [c]) = (hash w · d + val c) mod q`.
- Theorem {lit}`hash_eq_of_text_eq` — equal strings have equal hashes; hence a
  real match is never discarded as a spurious hit.
- Theorem {lit}`rabinKarp_sound` — every shift returned by `rabinKarpMatcher`
  is a valid match.
- Theorem {lit}`rabinKarp_complete` — every valid match is returned by
  `rabinKarpMatcher`.
- Theorem {lit}`rabinKarp_correct` — `rabinKarpMatcher` agrees with
  `naiveMatcher` on every shift.

The full CLRS window-slide recurrence (eq. (32.3)) is left as a named gap; the
O(1) right-extend step `hash_snoc` covers the incremental update used to seed
the hashes.

Notation conventions used in this section:

- `T` : the text being searched
- `P` : the pattern being searched for
- `d` : the radix of the numeric alphabet
- `q` : the modulus (CLRS assumes `0 < q`)
- `val` : assigns each alphabet symbol a numeric value in `ℕ`
-/

namespace CLRS
namespace Chapter32

variable {α : Type} [BEq α] [DecidableEq α] [LawfulBEq α]

/--
The base-`d` modular hash of `w` over the numeric values `val c`, computed by
Horner's rule modulo `q` (CLRS §32.2).  For `w = [a₀, …, a_{k-1}]` this is
`((⋯((val a₀ · d + val a₁) · d + …) · d + val a_{k-1}) mod q`.  The function
is total (`x % 0 = 0`); CLRS assumes a modulus `0 < q`.
-/
def hash (d q : ℕ) (val : α → ℕ) (w : Text α) : ℕ :=
  w.foldl (fun acc c => (acc * d + val c) % q) 0

/--
The O(1) incremental update: appending a character to a string costs one
multiplication, one addition and one modulus, rather than a full re-hash.
This is the step used to seed the Rabin–Karp hashes (CLRS §32.2).
-/
theorem hash_snoc (d q : ℕ) (val : α → ℕ) (w : Text α) (c : α) :
    hash d q val (w ++ [c]) = (hash d q val w * d + val c) % q := by
  unfold hash
  rw [List.foldl_append]
  simp

/-- Equal strings have equal hashes, for any radix, modulus and value map. -/
theorem hash_eq_of_text_eq (d q : ℕ) (val : α → ℕ) {w₁ w₂ : Text α} (h : w₁ = w₂) :
    hash d q val w₁ = hash d q val w₂ := by
  subst h
  rfl

/--
If the pattern matches at shift `s`, then the window's hash equals the
pattern's hash: a real match is never discarded as a spurious hit.  This is
the completeness half of the hash test.
-/
lemma hash_beq_of_matchesAt (T P : Text α) (d q : ℕ) (val : α → ℕ) (s : ℕ)
    (hm : matchesAt T P s = true) :
    (hash d q val ((T.drop s).take P.length) == hash d q val P) = true := by
  have hwind : ((T.drop s).take P.length == P) = true := by
    unfold matchesAt at hm
    split at hm
    · simpa using hm
    · contradiction
  have hwindEq : (T.drop s).take P.length = P := by
    exact beq_iff_eq.mp hwind
  rw [hash_eq_of_text_eq d q val hwindEq]
  simp

/--
The Rabin–Karp acceptance test for shift `s`: the hash of the window
`(T.drop s).take |P|` equals the hash of `P`, *and* the window literally
equals `P`.  The second conjunct filters out spurious hits, keeping the test
sound for every modulus.
-/
def rabinKarpShift (T P : Text α) (d q : ℕ) (val : α → ℕ) (s : ℕ) : Bool :=
  (hash d q val ((T.drop s).take P.length) == hash d q val P) && matchesAt T P s

/--
The Rabin–Karp string matcher: enumerate all shifts and return those that
pass `rabinKarpShift`.  For an empty pattern it returns every shift, exactly
like `naiveMatcher`.
-/
def rabinKarpMatcher (T P : Text α) (d q : ℕ) (val : α → ℕ) : List ℕ :=
  if P.length = 0 then
    List.range (T.length + 1)
  else
    let n := T.length
    let m := P.length
    (List.range (n - m + 1)).filter (rabinKarpShift T P d q val)

/--
The Rabin–Karp acceptance test agrees with the plain match test on every
shift: when the pattern matches, the hash equality is automatic, and when it
does not, the explicit comparison rejects the shift regardless of the hash.
-/
lemma rabinKarpShift_eq_matchesAt (T P : Text α) (d q : ℕ) (val : α → ℕ) (s : ℕ) :
    rabinKarpShift T P d q val s = matchesAt T P s := by
  unfold rabinKarpShift
  by_cases h : matchesAt T P s = true
  · have hb := hash_beq_of_matchesAt T P d q val s h
    simp [h, hb]
  · have hf : matchesAt T P s = false := by
      cases hb : matchesAt T P s
      · rfl
      · exact False.elim (h hb)
    simp [hf]

/-- If a shift `s` is in `rabinKarpMatcher`, then `matchesAt T P s` is true. -/
theorem rabinKarp_sound (T P : Text α) (d q : ℕ) (val : α → ℕ) (s : ℕ)
    (h : s ∈ rabinKarpMatcher T P d q val) : matchesAt T P s := by
  unfold rabinKarpMatcher at h
  split at h
  · rename_i hzero
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
  · have hmem := List.mem_filter.mp h
    simpa [rabinKarpShift_eq_matchesAt T P d q val s] using hmem.2

/-- If `matchesAt T P s` is true, then `s` is in `rabinKarpMatcher`. -/
theorem rabinKarp_complete (T P : Text α) (d q : ℕ) (val : α → ℕ) (s : ℕ)
    (hmatch : matchesAt T P s) : s ∈ rabinKarpMatcher T P d q val := by
  unfold rabinKarpMatcher
  by_cases hzero : P.length = 0
  · have hempty : P = [] := by
      cases P
      · rfl
      · simp at hzero
    subst hempty
    unfold matchesAt at hmatch
    simp at hmatch
    have hs : s < T.length + 1 := by omega
    simp [hs]
  · have hbound : s + P.length ≤ T.length := by
      unfold matchesAt at hmatch
      split at hmatch
      · assumption
      · simp at hmatch
    have hle : s < (T.length - P.length) + 1 := by omega
    have hmatch' : matchesAt T P s = true := hmatch
    have hshift : rabinKarpShift T P d q val s = true := by
      rw [rabinKarpShift_eq_matchesAt T P d q val s, hmatch']
    simpa [hzero] using
      List.mem_filter.mpr ⟨List.mem_range.mpr hle, hshift⟩

/--
**Correctness of Rabin–Karp.**  `rabinKarpMatcher` returns exactly the shifts
that `naiveMatcher` returns, for every text, pattern, radix, modulus and
numeric value map.  Soundness is by construction (the explicit comparison);
completeness uses the fact that equal strings have equal hashes, so a valid
match can never be filtered out as a spurious hit.
-/
theorem rabinKarp_correct (T P : Text α) (d q : ℕ) (val : α → ℕ) :
    rabinKarpMatcher T P d q val = naiveMatcher T P := by
  by_cases hzero : P.length = 0
  · simp [hzero, rabinKarpMatcher, naiveMatcher]
  · simp [hzero, rabinKarpMatcher, naiveMatcher]
    apply List.filter_congr
    intro s hs
    exact rabinKarpShift_eq_matchesAt T P d q val s

end Chapter32
end CLRS

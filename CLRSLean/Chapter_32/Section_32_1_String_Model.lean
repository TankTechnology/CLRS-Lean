import Mathlib

/-! # Section 32.1 - String Model

This section defines the string/text model used throughout Chapter 32:
string matching.  A string is a list of elements drawn from an alphabet.
We define the basic operations — length, prefix, suffix, and the
corresponding predicates — that the finite-automaton and KMP constructions
rely on.

The definitions are parameterized over the element type {lit}`α`; for concrete
executability, instantiate {lit}`α := Char` or {lit}`α := UInt8`.

## Key definitions

- {lit}`Text α`: a string (alias for {lit}`List α`).
- {lit}`length`: number of characters.
- {lit}`textPrefix t k`: the first {lit}`k` characters of {lit}`t`.
- {lit}`suffix t k`: the last {lit}`k` characters of {lit}`t`.
- {lit}`isPrefix p t`: {lit}`p` is a prefix of {lit}`t`.
- {lit}`isSuffix p t`: {lit}`p` is a suffix of {lit}`t`.

All operations are zero-indexed: the first character is at position 0,
and taking a prefix of length 0 yields the empty list.
-/

namespace CLRS
namespace Chapter32

/-- A text (string) is a list of elements from an alphabet.  Use `α := Char`
for concrete text, or a generic `α` for abstract reasoning. -/
abbrev Text (α : Type) := List α

variable {α : Type}

/-- The length of a text. -/
abbrev length (t : Text α) : ℕ := t.length

/-- The prefix of `t` of length `k`.  If `k` exceeds the text length, the
result is the full text. -/
def textPrefix (t : Text α) (k : ℕ) : Text α :=
  t.take k

/-- The suffix of `t` of length `k`.  If `k` exceeds the text length, the
result is the full text. -/
def suffix (t : Text α) (k : ℕ) : Text α :=
  t.drop (t.length - k)

/-- `p` is a prefix of `t`. -/
def isPrefix (p t : Text α) : Prop :=
  ∃ s, p ++ s = t

/-- `p` is a suffix of `t`. -/
def isSuffix (p t : Text α) : Prop :=
  ∃ s, s ++ p = t

/-- `p` is a proper prefix of `t`: a prefix that is strictly shorter than `t`. -/
def isProperPrefix (p t : Text α) : Prop :=
  isPrefix p t ∧ p.length < t.length

/-- `p` is a proper suffix of `t`: a suffix that is strictly shorter than `t`. -/
def isProperSuffix (p t : Text α) : Prop :=
  isSuffix p t ∧ p.length < t.length

/-- The empty text is a prefix of every text. -/
theorem isPrefix_empty (t : Text α) : isPrefix [] t :=
  ⟨t, by simp [isPrefix]⟩

/-- The empty text is a suffix of every text. -/
theorem isSuffix_empty (t : Text α) : isSuffix [] t :=
  ⟨t, by simp [isSuffix]⟩

/-- Every text is a prefix of itself. -/
theorem isPrefix_self (t : Text α) : isPrefix t t :=
  ⟨[], by simp [isPrefix]⟩

/-- Every text is a suffix of itself. -/
theorem isSuffix_self (t : Text α) : isSuffix t t :=
  ⟨[], by simp [isSuffix]⟩

/-- If `p` is a prefix of `t`, then `p.length ≤ t.length`. -/
theorem isPrefix_length_le (hp : isPrefix p t) : p.length ≤ t.length := by
  rcases hp with ⟨s, h⟩
  have := calc
    t.length = (p ++ s).length := by rw [h]
    _ = p.length + s.length := by simp
  omega

/-- If `p` is a suffix of `t`, then `p.length ≤ t.length`. -/
theorem isSuffix_length_le (hp : isSuffix p t) : p.length ≤ t.length := by
  rcases hp with ⟨s, h⟩
  have := calc
    t.length = (s ++ p).length := by rw [h]
    _ = s.length + p.length := by simp
  omega

/-- The prefix of length 0 is the empty list. -/
@[simp]
theorem textPrefix_zero (t : Text α) : textPrefix t 0 = [] := by
  simp [textPrefix]

/-- Taking the prefix of length equal to the text length returns the whole text. -/
@[simp]
theorem textPrefix_length (t : Text α) : textPrefix t t.length = t := by
  simp [textPrefix]

/-- The suffix of length 0 is the empty list. -/
@[simp]
theorem suffix_zero (t : Text α) : suffix t 0 = [] := by
  simp [suffix]

/-- Taking the suffix of length equal to the text length returns the whole text. -/
@[simp]
theorem suffix_length (t : Text α) : suffix t t.length = t := by
  simp [suffix]

/-- The empty text has no non-empty prefix. -/
theorem textPrefix_nil_of_length_eq_zero (t : Text α) (h : length t = 0) (k : ℕ) : textPrefix t k = [] := by
  have : t = [] := by simpa [length] using h
  subst this; simp [textPrefix]

/-- The empty text has no non-empty suffix. -/
theorem suffix_nil_of_length_eq_zero (t : Text α) (h : length t = 0) (k : ℕ) : suffix t k = [] := by
  have : t = [] := by simpa [length] using h
  subst this; simp [suffix]

/-- `textPrefix` is a prefix of the original text. -/
theorem isPrefix_textPrefix (t : Text α) (k : ℕ) : isPrefix (textPrefix t k) t := by
  refine ⟨t.drop k, ?_⟩
  simp [isPrefix, textPrefix, List.take_append_drop]

/-- `suffix` is a suffix of the original text. -/
theorem isSuffix_suffix (t : Text α) (k : ℕ) : isSuffix (suffix t k) t := by
  refine ⟨t.take (t.length - k), ?_⟩
  simp [isSuffix, suffix, List.take_append_drop, add_comm]

end Chapter32
end CLRS

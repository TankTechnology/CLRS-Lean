import Mathlib

/-!
# CLRS Section 15.4 - Longest common subsequence

This section adds the first LCS correctness interface.  It does not yet verify a
bottom-up table implementation.  Instead it packages the mathematical
certificate that a sequence is a longest common subsequence: it is a common
subsequence, and every other common subsequence has length at most its length.

Current gaps:

* The dynamic-programming table recurrence and reconstruction algorithm are
  future refinements.
-/

namespace CLRS
namespace Chapter15

/-- A sequence is common to {lit}`xs` and {lit}`ys` when it is a subsequence of both. -/
def IsCommonSubsequence {α : Type u} (xs ys zs : List α) : Prop :=
  List.Sublist zs xs ∧ List.Sublist zs ys

/-- A certificate that {lit}`seq` is a longest common subsequence of two lists. -/
structure LCSCertificate {α : Type u} (xs ys : List α) where
  seq : List α
  common : IsCommonSubsequence xs ys seq
  optimal : ∀ zs, IsCommonSubsequence xs ys zs → zs.length ≤ seq.length

namespace LCSCertificate

variable {α : Type u} {xs ys : List α}

/-- The length certified by an LCS certificate. -/
def length (cert : LCSCertificate xs ys) : Nat :=
  cert.seq.length

/-- The certified sequence is a common subsequence. -/
theorem seq_common (cert : LCSCertificate xs ys) :
    IsCommonSubsequence xs ys cert.seq :=
  cert.common

/-- Every common subsequence has length at most the certified LCS length. -/
theorem commonSubsequence_length_le (cert : LCSCertificate xs ys)
    {zs : List α} (hzs : IsCommonSubsequence xs ys zs) :
    zs.length ≤ cert.length := by
  exact cert.optimal zs hzs

/-- Any two LCS certificates for the same inputs certify the same length. -/
theorem length_eq_of_certificates
    (left right : LCSCertificate xs ys) :
    left.length = right.length := by
  apply le_antisymm
  · exact commonSubsequence_length_le right left.common
  · exact commonSubsequence_length_le left right.common

end LCSCertificate

/-- Swapping the two input sequences preserves common-subsequence status. -/
theorem isCommonSubsequence_comm {xs ys zs : List α} :
    IsCommonSubsequence xs ys zs ↔ IsCommonSubsequence ys xs zs := by
  constructor
  · intro h
    exact ⟨h.2, h.1⟩
  · intro h
    exact ⟨h.2, h.1⟩

end Chapter15
end CLRS

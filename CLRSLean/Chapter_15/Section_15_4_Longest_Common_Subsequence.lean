import Mathlib

/-!
# CLRS Section 15.4 - Longest common subsequence

This section adds the first LCS correctness interface.  It does not yet verify a
bottom-up table implementation.  Instead it packages the mathematical
certificate that a sequence is a longest common subsequence: it is a common
subsequence, and every other common subsequence has length at most its length.
It also records the usual dynamic-programming table recurrence and a
certificate theorem: an exact reconstruction from a table with a global
upper-bound certificate is an LCS.

Current gaps:

* The dynamic-programming recurrence is specified as a table certificate here.
  A concrete bottom-up table-filling implementation and executable
  reconstruction procedure are future refinements.
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

/-! ## Table recurrence certificate -/

/--
The CLRS LCS dynamic-programming recurrence for a supplied table.  The table is
indexed by the remaining suffixes of the two input lists.
-/
def LCSTableRecurrence {α : Type u} [DecidableEq α]
    (table : List α → List α → Nat) : Prop :=
  (∀ ys, table [] ys = 0) ∧
    (∀ xs, table xs [] = 0) ∧
      ∀ a xs b ys,
        table (a :: xs) (b :: ys) =
          if a = b then
            table xs ys + 1
          else
            max (table xs (b :: ys)) (table (a :: xs) ys)

namespace LCSTableRecurrence

variable {α : Type u} [DecidableEq α]
variable {table : List α → List α → Nat}

/-- The empty-left boundary row of an LCS table is zero. -/
theorem nil_left (h : LCSTableRecurrence table) (ys : List α) :
    table [] ys = 0 :=
  h.1 ys

/-- The empty-right boundary column of an LCS table is zero. -/
theorem nil_right (h : LCSTableRecurrence table) (xs : List α) :
    table xs [] = 0 :=
  h.2.1 xs

/-- The cons/cons recurrence in its raw conditional form. -/
theorem cons_cons (h : LCSTableRecurrence table)
    (a : α) (xs : List α) (b : α) (ys : List α) :
    table (a :: xs) (b :: ys) =
      if a = b then
        table xs ys + 1
      else
        max (table xs (b :: ys)) (table (a :: xs) ys) :=
  h.2.2 a xs b ys

/-- Matching heads use the diagonal table entry plus one. -/
theorem cons_cons_of_eq (h : LCSTableRecurrence table)
    {a b : α} (hab : a = b) (xs ys : List α) :
    table (a :: xs) (b :: ys) = table xs ys + 1 := by
  simpa [hab] using h.cons_cons a xs b ys

/-- Distinct heads use the maximum of the two one-sided subproblems. -/
theorem cons_cons_of_ne (h : LCSTableRecurrence table)
    {a b : α} (hab : a ≠ b) (xs ys : List α) :
    table (a :: xs) (b :: ys) =
      max (table xs (b :: ys)) (table (a :: xs) ys) := by
  simpa [hab] using h.cons_cons a xs b ys

end LCSTableRecurrence

/--
A certified LCS table satisfies the CLRS recurrence and bounds the length of
every common subsequence from above.
-/
structure LCSTableCertificate {α : Type u} [DecidableEq α]
    (table : List α → List α → Nat) where
  recurrence : LCSTableRecurrence table
  upper_bound :
    ∀ {xs ys zs : List α}, IsCommonSubsequence xs ys zs → zs.length ≤ table xs ys

namespace LCSTableCertificate

variable {α : Type u} [DecidableEq α]
variable {table : List α → List α → Nat}

/-- A table certificate supplies the global upper bound promised by the table. -/
theorem commonSubsequence_length_le (cert : LCSTableCertificate table)
    {xs ys zs : List α} (hzs : IsCommonSubsequence xs ys zs) :
    zs.length ≤ table xs ys :=
  cert.upper_bound hzs

end LCSTableCertificate

/--
If a reconstructed common subsequence has exactly the value stored in a
certified LCS table, then no common subsequence is longer.
-/
theorem lcsTable_reconstruction_optimal {α : Type u} [DecidableEq α]
    {table : List α → List α → Nat} (cert : LCSTableCertificate table)
    {xs ys seq : List α}
    (hlen : seq.length = table xs ys) :
    ∀ zs, IsCommonSubsequence xs ys zs → zs.length ≤ seq.length := by
  intro zs hzs
  calc
    zs.length ≤ table xs ys := cert.commonSubsequence_length_le hzs
    _ = seq.length := hlen.symm

/--
If a reconstructed common subsequence has exactly the value stored in a
certified LCS table, then it packages as an LCS certificate.
-/
def lcsCertificate_of_table_reconstruction {α : Type u} [DecidableEq α]
    {table : List α → List α → Nat} (cert : LCSTableCertificate table)
    {xs ys seq : List α}
    (hcommon : IsCommonSubsequence xs ys seq)
    (hlen : seq.length = table xs ys) :
    LCSCertificate xs ys where
  seq := seq
  common := hcommon
  optimal := lcsTable_reconstruction_optimal cert hlen

end Chapter15
end CLRS

import Mathlib

/-!
# CLRS Section 15.4 - Longest common subsequence

This section formalizes the CLRS longest-common-subsequence dynamic program.
It defines the mathematical LCS certificate, the table recurrence, and an
executable bottom-up length computation with a reconstruction procedure.  The
main theorem proves that the reconstructed sequence is indeed a longest common
subsequence.

Main results:

* Theorem {lit}`lcsLength_recurrence`: the executable length function satisfies
  the CLRS recurrence.
* Theorem {lit}`lcsLength_upper_bound`: every common subsequence has length at
  most the table entry.
* Theorem {lit}`lcsReconstruct_length_eq`: the reconstructed sequence's length
  equals the computed table entry.
* Theorem {lit}`lcsReconstruct_common`: the reconstructed sequence is a common
  subsequence of both inputs.
* Theorem {lit}`lcs_correct`: there exists a longest common subsequence, and
  the reconstruction procedure computes one.

Status: `proved` for the functional LCS correctness layer.

Deferred refinements:

* Mutable-array cost-table implementation and linear-space optimization remain
  future implementation-level targets beyond the current mathematical-correctness
  scope.
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
  · intro h; exact ⟨h.2, h.1⟩
  · intro h; exact ⟨h.2, h.1⟩

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

/-- Equal heads use the diagonal table entry plus one. -/
theorem cons_cons_self (h : LCSTableRecurrence table)
    (a : α) (xs ys : List α) :
    table (a :: xs) (a :: ys) = table xs ys + 1 := by
  exact h.cons_cons_of_eq rfl xs ys

/-- Matching heads strictly increase the diagonal subproblem value. -/
theorem diagonal_lt_cons_cons_of_eq (h : LCSTableRecurrence table)
    {a b : α} (hab : a = b) (xs ys : List α) :
    table xs ys < table (a :: xs) (b :: ys) := by
  rw [h.cons_cons_of_eq hab xs ys]
  omega

/-- Distinct heads use the maximum of the two one-sided subproblems. -/
theorem cons_cons_of_ne (h : LCSTableRecurrence table)
    {a b : α} (hab : a ≠ b) (xs ys : List α) :
    table (a :: xs) (b :: ys) =
      max (table xs (b :: ys)) (table (a :: xs) ys) := by
  simpa [hab] using h.cons_cons a xs b ys

/-- In the nonmatching-head case, dropping the left head gives a lower subproblem. -/
theorem drop_left_le_of_ne (h : LCSTableRecurrence table)
    {a b : α} (hab : a ≠ b) (xs ys : List α) :
    table xs (b :: ys) ≤ table (a :: xs) (b :: ys) := by
  rw [h.cons_cons_of_ne hab xs ys]
  exact Nat.le_max_left _ _

/-- In the nonmatching-head case, dropping the right head gives a lower subproblem. -/
theorem drop_right_le_of_ne (h : LCSTableRecurrence table)
    {a b : α} (hab : a ≠ b) (xs ys : List α) :
    table (a :: xs) ys ≤ table (a :: xs) (b :: ys) := by
  rw [h.cons_cons_of_ne hab xs ys]
  exact Nat.le_max_right _ _

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

/-- A certified table has a zero empty-left boundary row. -/
theorem nil_left (cert : LCSTableCertificate table) (ys : List α) :
    table [] ys = 0 := by
  exact cert.recurrence.nil_left ys

/-- A certified table has a zero empty-right boundary column. -/
theorem nil_right (cert : LCSTableCertificate table) (xs : List α) :
    table xs [] = 0 := by
  exact cert.recurrence.nil_right xs

/-- A certified table satisfies the raw cons/cons CLRS recurrence. -/
theorem cons_cons (cert : LCSTableCertificate table)
    (a : α) (xs : List α) (b : α) (ys : List α) :
    table (a :: xs) (b :: ys) =
      if a = b then
        table xs ys + 1
      else
        max (table xs (b :: ys)) (table (a :: xs) ys) := by
  exact cert.recurrence.cons_cons a xs b ys

/-- In a certified table, matching heads use the diagonal entry plus one. -/
theorem cons_cons_of_eq (cert : LCSTableCertificate table)
    {a b : α} (hab : a = b) (xs ys : List α) :
    table (a :: xs) (b :: ys) = table xs ys + 1 := by
  exact cert.recurrence.cons_cons_of_eq hab xs ys

/-- In a certified table, equal heads use the diagonal entry plus one. -/
theorem cons_cons_self (cert : LCSTableCertificate table)
    (a : α) (xs ys : List α) :
    table (a :: xs) (a :: ys) = table xs ys + 1 := by
  exact cert.recurrence.cons_cons_self a xs ys

/-- In a certified table, matching heads strictly increase the diagonal subproblem value. -/
theorem diagonal_lt_cons_cons_of_eq (cert : LCSTableCertificate table)
    {a b : α} (hab : a = b) (xs ys : List α) :
    table xs ys < table (a :: xs) (b :: ys) := by
  exact cert.recurrence.diagonal_lt_cons_cons_of_eq hab xs ys

/-- In a certified table, distinct heads use the maximum one-sided entry. -/
theorem cons_cons_of_ne (cert : LCSTableCertificate table)
    {a b : α} (hab : a ≠ b) (xs ys : List α) :
    table (a :: xs) (b :: ys) =
      max (table xs (b :: ys)) (table (a :: xs) ys) := by
  exact cert.recurrence.cons_cons_of_ne hab xs ys

/-- In a certified table, dropping the left head is bounded by the nonmatching case. -/
theorem drop_left_le_of_ne (cert : LCSTableCertificate table)
    {a b : α} (hab : a ≠ b) (xs ys : List α) :
    table xs (b :: ys) ≤ table (a :: xs) (b :: ys) := by
  exact cert.recurrence.drop_left_le_of_ne hab xs ys

/-- In a certified table, dropping the right head is bounded by the nonmatching case. -/
theorem drop_right_le_of_ne (cert : LCSTableCertificate table)
    {a b : α} (hab : a ≠ b) (xs ys : List α) :
    table (a :: xs) ys ≤ table (a :: xs) (b :: ys) := by
  exact cert.recurrence.drop_right_le_of_ne hab xs ys

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

/--
The LCS certificate produced from a table reconstruction certifies exactly the
table entry as its length.
-/
theorem lcsCertificate_of_table_reconstruction_length
    {α : Type u} [DecidableEq α]
    {table : List α → List α → Nat} (cert : LCSTableCertificate table)
    {xs ys seq : List α}
    (hcommon : IsCommonSubsequence xs ys seq)
    (hlen : seq.length = table xs ys) :
    (lcsCertificate_of_table_reconstruction cert hcommon hlen).length =
      table xs ys := by
  simpa [lcsCertificate_of_table_reconstruction, LCSCertificate.length] using hlen

/-! ## Bottom-up LCS length computation -/

/--
The executable bottom-up LCS length function, directly implementing the CLRS
recurrence by structural recursion over the two input lists.
-/
def lcsLength {α : Type u} [DecidableEq α] : List α → List α → Nat
  | [], _ => 0
  | _, [] => 0
  | a :: xs, b :: ys =>
      if a = b then
        lcsLength xs ys + 1
      else
        max (lcsLength xs (b :: ys)) (lcsLength (a :: xs) ys)

/-- {name}`lcsLength` satisfies the CLRS LCS table recurrence. -/
theorem lcsLength_recurrence {α : Type u} [DecidableEq α] :
    LCSTableRecurrence (lcsLength (α := α)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ys; simp [lcsLength]
  · intro xs; cases xs <;> simp [lcsLength]
  · intro a xs b ys; simp [lcsLength]

private lemma sublist_of_cons_sublist {α : Type u} {a : α} {l m : List α}
    (h : List.Sublist (a :: l) m) : List.Sublist l m := by
  cases h
  case cons h' =>
    have ih := sublist_of_cons_sublist h'
    exact ih.cons _
  case cons_cons h' =>
    exact h'.cons a

/--
Any common subsequence is bounded by `lcsLength`.  The proof uses Nat strong
induction on `|xs| + |ys|` and case analysis via `List.cons_sublist_cons'`
to avoid dependent pattern matching on `List.Sublist`.
-/
theorem lcsLength_upper_bound {α : Type u} [DecidableEq α]
    {xs ys zs : List α} (h : IsCommonSubsequence xs ys zs) :
    zs.length ≤ lcsLength xs ys := by
  obtain ⟨hsub_xs, hsub_ys⟩ := h
  let P (n : ℕ) : Prop := ∀ (xs ys zs : List α),
    xs.length + ys.length = n → List.Sublist zs xs → List.Sublist zs ys → zs.length ≤ lcsLength xs ys
  have hP : ∀ n, (∀ m < n, P m) → P n := by
    intro n ih xs ys zs hn hsub_xs hsub_ys
    match xs, ys with
    | [], _ => cases hsub_xs; simp [lcsLength]
    | _, [] => cases hsub_ys; simp [lcsLength]
    | a :: xs', b :: ys' =>
      match zs with
      | [] => simp [lcsLength]
      | z :: zs' =>
        have hx_cases := (List.cons_sublist_cons' (a := z) (b := a) (l₁ := zs') (l₂ := xs')).mp hsub_xs
        rcases hx_cases with (hx_skip | ⟨hz_eq_a, hx_match⟩)
        · -- Skip a in first list: (z :: zs') <+ xs'
          by_cases hab : a = b
          · subst hab
            have hy_cases' := (List.cons_sublist_cons' (a := z) (b := a) (l₁ := zs') (l₂ := ys')).mp hsub_ys
            rcases hy_cases' with (hy_skip' | ⟨hz_eq_a', hy_match'⟩)
            · -- (z :: zs') <+ ys': common subseq of xs', ys'
              have h_lt : xs'.length + ys'.length < n := by
                have h_lt' : xs'.length + ys'.length < (a :: xs').length + (a :: ys').length := by
                  calc
                    xs'.length + ys'.length < xs'.length + ys'.length + 2 := by omega
                    _ = (xs'.length + 1) + (ys'.length + 1) := by omega
                    _ = (a :: xs').length + (a :: ys').length := by simp
                exact lt_of_lt_of_eq h_lt' hn
              have hlen := ih (xs'.length + ys'.length) h_lt xs' ys' (z :: zs') rfl hx_skip hy_skip'
              simpa [lcsLength] using hlen.trans (Nat.le_add_right _ 1)
            · -- z = a and zs' <+ ys'
              rw [hz_eq_a'] at *
              have hsub_tail : List.Sublist zs' xs' := sublist_of_cons_sublist hx_skip
              have h_lt : xs'.length + ys'.length < n := by
                have h_lt' : xs'.length + ys'.length < (a :: xs').length + (a :: ys').length := by
                  calc
                    xs'.length + ys'.length < xs'.length + ys'.length + 2 := by omega
                    _ = (xs'.length + 1) + (ys'.length + 1) := by omega
                    _ = (a :: xs').length + (a :: ys').length := by simp
                exact lt_of_lt_of_eq h_lt' hn
              have hlen := ih (xs'.length + ys'.length) h_lt xs' ys' zs' rfl hsub_tail hy_match'
              simpa [lcsLength, List.length_cons] using Nat.add_le_add_right hlen 1
          · -- a ≠ b
            have h_lt : xs'.length + (b :: ys').length < n := by
              have h_lt' : xs'.length + (b :: ys').length < (a :: xs').length + (b :: ys').length := by
                calc
                  xs'.length + (b :: ys').length < (xs'.length + (b :: ys').length) + 1 := by omega
                  _ = (xs'.length + 1) + (b :: ys').length := by omega
                  _ = (a :: xs').length + (b :: ys').length := by simp
              exact lt_of_lt_of_eq h_lt' hn
            have hlen := ih (xs'.length + (b :: ys').length) h_lt xs' (b :: ys') (z :: zs') rfl hx_skip hsub_ys
            simpa [lcsLength, hab] using hlen.trans (Nat.le_max_left _ _)
        · -- z = a and zs' <+ xs'
          rw [hz_eq_a] at hsub_ys ⊢
          have hy_cases := (List.cons_sublist_cons' (a := a) (b := b) (l₁ := zs') (l₂ := ys')).mp hsub_ys
          rcases hy_cases with (hy_skip | ⟨ha_eq_b, hy_match⟩)
          · -- (a :: zs') <+ ys' (skip b)
            by_cases hab : a = b
            · subst hab
              have hsub_tail : List.Sublist zs' ys' := sublist_of_cons_sublist hy_skip
              have h_lt : xs'.length + ys'.length < n := by
                have h_lt' : xs'.length + ys'.length < (a :: xs').length + (a :: ys').length := by
                  calc
                    xs'.length + ys'.length < xs'.length + ys'.length + 2 := by omega
                    _ = (xs'.length + 1) + (ys'.length + 1) := by omega
                    _ = (a :: xs').length + (a :: ys').length := by simp
                exact lt_of_lt_of_eq h_lt' hn
              have hlen := ih (xs'.length + ys'.length) h_lt xs' ys' zs' rfl hx_match hsub_tail
              simpa [lcsLength, List.length_cons] using Nat.add_le_add_right hlen 1
            · -- a ≠ b
              have h_lt : (a :: xs').length + ys'.length < n := by
                have h_lt' : (a :: xs').length + ys'.length < (a :: xs').length + (b :: ys').length := by
                  calc
                    (a :: xs').length + ys'.length < (a :: xs').length + ys'.length + 1 := by omega
                    _ = (a :: xs').length + (ys'.length + 1) := by omega
                    _ = (a :: xs').length + (b :: ys').length := by simp
                exact lt_of_lt_of_eq h_lt' hn
              have hlen := ih ((a :: xs').length + ys'.length) h_lt (a :: xs') ys' (a :: zs') rfl
                (List.Sublist.cons_cons a hx_match) hy_skip
              simpa [lcsLength, hab] using hlen.trans (Nat.le_max_right _ _)
          · -- a = b, zs' <+ ys'
            subst ha_eq_b
            have h_lt : xs'.length + ys'.length < n := by
              have h_lt' : xs'.length + ys'.length < (a :: xs').length + (a :: ys').length := by
                calc
                    xs'.length + ys'.length < xs'.length + ys'.length + 2 := by omega
                    _ = (xs'.length + 1) + (ys'.length + 1) := by omega
                    _ = (a :: xs').length + (a :: ys').length := by simp
              exact lt_of_lt_of_eq h_lt' hn
            have hlen := ih (xs'.length + ys'.length) h_lt xs' ys' zs' rfl hx_match hy_match
            simpa [lcsLength, List.length_cons] using Nat.add_le_add_right hlen 1
  let n := xs.length + ys.length
  have h_result : P n := Nat.strong_induction_on n hP
  exact h_result xs ys zs rfl hsub_xs hsub_ys

/--
{name}`lcsLength` paired with its upper-bound proof forms a certified LCS table.
-/
def lcsTable_certificate {α : Type u} [DecidableEq α] :
    LCSTableCertificate (lcsLength (α := α)) where
  recurrence := lcsLength_recurrence
  upper_bound := lcsLength_upper_bound

/-! ## Executable LCS reconstruction -/

/--
Trace back through the computed length table to reconstruct one longest common
subsequence.  The reconstruction follows the CLRS textbook procedure: start from
{lit}`lcsLength xs ys` and, at each step, decide whether the current characters
match (emit the character) or whether the length came from the left or upper
subproblem.
-/
def lcsReconstruct {α : Type u} [DecidableEq α] : List α → List α → List α
  | [], _ => []
  | _, [] => []
  | a :: xs, b :: ys =>
      if a = b then
        a :: lcsReconstruct xs ys
      else if lcsLength xs (b :: ys) ≥ lcsLength (a :: xs) ys then
        lcsReconstruct xs (b :: ys)
      else
        lcsReconstruct (a :: xs) ys

/--
The reconstruction produces a sequence whose length equals the table entry.
-/
theorem lcsReconstruct_length_eq {α : Type u} [DecidableEq α] (xs ys : List α) :
    (lcsReconstruct xs ys).length = lcsLength xs ys := by
  induction xs generalizing ys with
  | nil => simp [lcsReconstruct, lcsLength]
  | cons a xs ih_xs =>
      induction ys with
      | nil => simp [lcsReconstruct, lcsLength]
      | cons b ys ih_ys =>
          simp [lcsReconstruct, lcsLength]
          by_cases hab : a = b
          · subst hab; simp; simp [ih_xs ys]
          · simp [hab]
            split
            · next hge =>
                have h_max : max (lcsLength xs (b :: ys)) (lcsLength (a :: xs) ys) =
                    lcsLength xs (b :: ys) := Nat.max_eq_left hge
                rw [h_max]
                simp [ih_xs (b :: ys)]
            · next hlt =>
                have h_max : max (lcsLength xs (b :: ys)) (lcsLength (a :: xs) ys) =
                    lcsLength (a :: xs) ys :=
                  Nat.max_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge hlt))
                rw [h_max]
                simp [ih_ys]

/--
The reconstructed sequence is a common subsequence of both inputs.
-/
theorem lcsReconstruct_common {α : Type u} [DecidableEq α] (xs ys : List α) :
    IsCommonSubsequence xs ys (lcsReconstruct xs ys) := by
  induction xs generalizing ys with
  | nil => simp [lcsReconstruct, IsCommonSubsequence]
  | cons a xs ih_xs =>
      induction ys with
      | nil => simp [lcsReconstruct, IsCommonSubsequence]
      | cons b ys ih_ys =>
          simp [lcsReconstruct, IsCommonSubsequence]
          by_cases hab : a = b
          · subst hab
            obtain ⟨hx, hy⟩ := ih_xs ys
            have hpair : List.Sublist (a :: lcsReconstruct xs ys) (a :: xs) ∧
                        List.Sublist (a :: lcsReconstruct xs ys) (a :: ys) :=
              ⟨List.Sublist.cons_cons a hx, List.Sublist.cons_cons a hy⟩
            simpa [lcsReconstruct, IsCommonSubsequence] using hpair
          · simp [hab]
            split
            · next =>
                obtain ⟨hx, hy⟩ := ih_xs (b :: ys)
                exact ⟨List.Sublist.cons a hx, hy⟩
            · next =>
                obtain ⟨hx, hy⟩ := ih_ys
                exact ⟨hx, List.Sublist.cons b hy⟩

/--
**Theorem (LCS correctness).**  There exists a longest common subsequence of
{lit}`xs` and {lit}`ys`, and the executable reconstruction procedure
computes one such sequence.  This corresponds to the CLRS LCS
optimal-substructure theorem (Theorem 15.1).
-/
theorem lcs_correct {α : Type u} [DecidableEq α] (xs ys : List α) :
    ∃ seq : List α,
      IsCommonSubsequence xs ys seq ∧
      ∀ zs, IsCommonSubsequence xs ys zs → zs.length ≤ seq.length := by
  refine ⟨lcsReconstruct xs ys, ?_, ?_⟩
  · exact lcsReconstruct_common xs ys
  · intro zs hzs
    calc
      zs.length ≤ lcsLength xs ys := lcsLength_upper_bound hzs
      _ = (lcsReconstruct xs ys).length := (lcsReconstruct_length_eq xs ys).symm

end Chapter15
end CLRS

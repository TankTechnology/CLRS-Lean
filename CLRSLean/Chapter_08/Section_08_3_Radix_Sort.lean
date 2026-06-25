import CLRSLean.Chapter_08.Section_08_2_Counting_Sort

/-!
# CLRS Section 8.3 - Radix sort

This file proves the pure correctness spine for radix sort from the stable
counting-sort theorem in Section 8.2.

The model is intentionally abstract.  A list of digit functions is supplied in
least-significant to most-significant order, and each pass is a stable
{lit}`countingSortBy` over the current digit.  The final theorems say that the
result is ordered by the corresponding most-significant-first lexicographic
relation, preserves membership, preserves the input order inside each complete
digit signature, and hence captures the CLRS stable-pass proof spine.

This isolates the CLRS proof idea from low-level numeric encodings and cost
models.  Concrete base-{lit}`b` digit extraction can later refine this
interface.
-/

namespace CLRS
namespace Chapter08

universe u
variable {α : Type u}

/-! ## Relation-ordered lists and digit lexicographic order -/

/--
Pairwise list ordering by a relation.  This is stronger than adjacent ordering
and is convenient for stable bucket proofs, since filtering a pairwise-ordered
list preserves the order relation.
-/
abbrev OrderedRel (rel : α → α → Prop) (xs : List α) : Prop :=
  xs.Pairwise rel

/-- A single higher-priority digit extends an existing lower-priority order. -/
def LexWith (digit : α → Nat) (rel : α → α → Prop) (x y : α) : Prop :=
  digit x < digit y ∨ (digit x = digit y ∧ rel x y)

/--
Accumulate a radix lexicographic relation from digits supplied
least-significant first.  Each later digit becomes higher priority.
-/
def RadixRel : List (α → Nat) → (α → α → Prop) → α → α → Prop
  | [], rel => rel
  | digit :: digits, rel => RadixRel digits (LexWith digit rel)

/-- The public lexicographic relation induced by low-to-high radix digits. -/
def RadixLex (digitsLow : List (α → Nat)) : α → α → Prop :=
  RadixRel digitsLow (fun _ _ => True)

theorem orderedRel_trivial (xs : List α) :
    OrderedRel (fun _ _ => True) xs := by
  induction xs with
  | nil =>
      exact List.Pairwise.nil
  | cons _ xs ih =>
      exact List.Pairwise.cons (by simp) ih

theorem orderedRel_append_of_rel {rel : α → α → Prop} {xs ys : List α}
    (hxs : OrderedRel rel xs) (hys : OrderedRel rel ys)
    (hrel : ∀ x ∈ xs, ∀ y ∈ ys, rel x y) :
    OrderedRel rel (xs ++ ys) := by
  exact List.pairwise_append.mpr ⟨hxs, hys, hrel⟩

theorem orderedRel_bucket {rel : α → α → Prop} {key : α → Nat}
    {xs : List α} (k : Nat) (hxs : OrderedRel rel xs) :
    OrderedRel rel (bucket key xs k) := by
  exact List.Pairwise.filter (fun x => key x == k) hxs

theorem orderedRel_of_same_digit {rel : α → α → Prop} {digit : α → Nat}
    {xs : List α} {k : Nat}
    (hxs : OrderedRel rel xs) (hall : ∀ x ∈ xs, digit x = k) :
    OrderedRel (LexWith digit rel) xs := by
  induction xs with
  | nil =>
      exact List.Pairwise.nil
  | cons x xs ih =>
      cases hxs with
      | cons hhead htail =>
          refine List.Pairwise.cons ?_ (ih htail ?_)
          · intro y hy
            exact Or.inr ⟨by rw [hall x (by simp), hall y (by simp [hy])],
              hhead y hy⟩
          · intro y hy
            exact hall y (by simp [hy])

/-! ## One stable radix pass -/

/--
A stable counting-sort pass by a new digit upgrades a lower-priority relation
to a lexicographic relation with the new digit as the most significant
criterion.
-/
theorem radixPass_orderedRel
    (maxDigit : Nat) (digit : α → Nat) (rel : α → α → Prop) (xs : List α)
    (hxs : OrderedRel rel xs) :
    OrderedRel (LexWith digit rel) (countingSortBy maxDigit digit xs) := by
  induction maxDigit with
  | zero =>
      simpa [countingSortBy] using
        orderedRel_of_same_digit
          (orderedRel_bucket (key := digit) 0 hxs)
          (bucket_all_keys_eq digit xs 0)
  | succ maxDigit ih =>
      rw [countingSortBy_succ]
      refine orderedRel_append_of_rel ih ?_ ?_
      · exact orderedRel_of_same_digit
          (orderedRel_bucket (key := digit) (maxDigit + 1) hxs)
          (bucket_all_keys_eq digit xs (maxDigit + 1))
      · intro x hx y hy
        have hxle : digit x ≤ maxDigit :=
          countingSortBy_allKeysLe maxDigit digit xs x hx
        have hykey : digit y = maxDigit + 1 := (mem_bucket_iff.mp hy).2
        exact Or.inl (Nat.lt_of_le_of_lt hxle (by simp [hykey]))

/-! ## Radix sort -/

/--
Radix sort by stable counting-sort passes.  Digits are supplied in
least-significant to most-significant order.
-/
def radixSortBy (maxDigit : Nat) : List (α → Nat) → List α → List α
  | [], xs => xs
  | digit :: digits, xs =>
      radixSortBy maxDigit digits (countingSortBy maxDigit digit xs)

/-- All digit functions are bounded by the declared maximum digit. -/
def AllDigitsLe (digitsLow : List (α → Nat)) (xs : List α)
    (maxDigit : Nat) : Prop :=
  ∀ digit ∈ digitsLow, AllKeysLe digit xs maxDigit

/-! ## Stability by complete digit signatures -/

/--
The subsequence of elements whose values match {lit}`sample` on every radix
digit, preserving the ambient list order.

Equality of this list before and after radix sort is the direct stability
statement: items with the same complete digit signature appear in their
original relative order.
-/
def digitClass (digitsLow : List (α → Nat)) (sample : α) (xs : List α) :
    List α :=
  xs.filter fun x => digitsLow.all fun digit => digit x == digit sample

theorem digitClass_cons_filter (digit : α → Nat)
    (digitsLow : List (α → Nat)) (sample : α) (xs : List α) :
    digitClass (digit :: digitsLow) sample xs =
      (digitClass digitsLow sample xs).filter
        (fun x => digit x == digit sample) := by
  simp [digitClass, List.filter_filter]

theorem digitClass_cons_bucket (digit : α → Nat)
    (digitsLow : List (α → Nat)) (sample : α) (xs : List α) :
    digitClass (digit :: digitsLow) sample xs =
      digitClass digitsLow sample (bucket digit xs (digit sample)) := by
  simp [digitClass, bucket, List.filter_filter, Bool.and_comm]

theorem countingSortBy_digitClass_cons_eq
    (maxDigit : Nat) (digit : α → Nat) (digitsLow : List (α → Nat))
    (sample : α) (xs : List α) (hxs : AllKeysLe digit xs maxDigit) :
    digitClass (digit :: digitsLow) sample
        (countingSortBy maxDigit digit xs) =
      digitClass (digit :: digitsLow) sample xs := by
  rw [digitClass_cons_bucket, countingSortBy_bucket_eq maxDigit digit xs hxs,
    digitClass_cons_bucket]

theorem allDigitsLe_of_mem_iff {digitsLow : List (α → Nat)}
    {xs ys : List α} {maxDigit : Nat}
    (h : AllDigitsLe digitsLow xs maxDigit)
    (hmem : ∀ x, x ∈ ys ↔ x ∈ xs) :
    AllDigitsLe digitsLow ys maxDigit := by
  intro digit hdigit x hx
  exact h digit hdigit x ((hmem x).mp hx)

theorem radixSortBy_ordered_aux
    (maxDigit : Nat) (digitsLow : List (α → Nat))
    (rel : α → α → Prop) (xs : List α)
    (hxs : OrderedRel rel xs) :
    OrderedRel (RadixRel digitsLow rel)
      (radixSortBy maxDigit digitsLow xs) := by
  induction digitsLow generalizing rel xs with
  | nil =>
      simpa [radixSortBy, RadixRel] using hxs
  | cons digit digits ih =>
      have hpass : OrderedRel (LexWith digit rel)
          (countingSortBy maxDigit digit xs) :=
        radixPass_orderedRel maxDigit digit rel xs hxs
      simpa [radixSortBy, RadixRel] using
        ih (LexWith digit rel) (countingSortBy maxDigit digit xs) hpass

/-- Radix sort returns a list ordered by the induced digit lexicographic order. -/
theorem radixSortBy_ordered
    (maxDigit : Nat) (digitsLow : List (α → Nat)) (xs : List α) :
    OrderedRel (RadixLex digitsLow)
      (radixSortBy maxDigit digitsLow xs) := by
  simpa [RadixLex] using
    radixSortBy_ordered_aux maxDigit digitsLow (fun _ _ => True) xs
      (orderedRel_trivial xs)

theorem radixSortBy_mem_iff
    (maxDigit : Nat) :
    ∀ (digitsLow : List (α → Nat)) (xs : List α),
      AllDigitsLe digitsLow xs maxDigit →
      ∀ x, x ∈ radixSortBy maxDigit digitsLow xs ↔ x ∈ xs := by
  intro digitsLow
  induction digitsLow with
  | nil =>
      intro xs _ x
      simp [radixSortBy]
  | cons digit digits ih =>
      intro xs hdigits x
      have hdigit : AllKeysLe digit xs maxDigit :=
        hdigits digit (by simp)
      have hpass_mem :
          ∀ y, y ∈ countingSortBy maxDigit digit xs ↔ y ∈ xs :=
        countingSortBy_mem_iff maxDigit digit xs hdigit
      have hrest : AllDigitsLe digits
          (countingSortBy maxDigit digit xs) maxDigit := by
        refine allDigitsLe_of_mem_iff ?_ hpass_mem
        intro d hd
        exact hdigits d (by simp [hd])
      have htail := ih (countingSortBy maxDigit digit xs) hrest x
      exact htail.trans (hpass_mem x)

theorem radixSortBy_perm [DecidableEq α]
    (maxDigit : Nat) :
    ∀ (digitsLow : List (α → Nat)) (xs : List α),
      AllDigitsLe digitsLow xs maxDigit →
      (radixSortBy maxDigit digitsLow xs).Perm xs := by
  intro digitsLow
  induction digitsLow with
  | nil =>
      intro xs _
      simp [radixSortBy]
  | cons digit digits ih =>
      intro xs hdigits
      have hdigit : AllKeysLe digit xs maxDigit :=
        hdigits digit (by simp)
      have hpass_perm : (countingSortBy maxDigit digit xs).Perm xs :=
        countingSortBy_perm maxDigit digit xs hdigit
      have hpass_mem :
          ∀ y, y ∈ countingSortBy maxDigit digit xs ↔ y ∈ xs := by
        intro y
        exact hpass_perm.mem_iff
      have hrest : AllDigitsLe digits
          (countingSortBy maxDigit digit xs) maxDigit := by
        refine allDigitsLe_of_mem_iff ?_ hpass_mem
        intro d hd
        exact hdigits d (by simp [hd])
      exact (ih (countingSortBy maxDigit digit xs) hrest).trans hpass_perm

theorem radixSortBy_digitClass_eq
    (maxDigit : Nat) :
    ∀ (digitsLow : List (α → Nat)) (xs : List α),
      AllDigitsLe digitsLow xs maxDigit →
      ∀ sample,
        digitClass digitsLow sample (radixSortBy maxDigit digitsLow xs) =
          digitClass digitsLow sample xs := by
  intro digitsLow
  induction digitsLow with
  | nil =>
      intro xs _ sample
      simp [radixSortBy, digitClass]
  | cons digit digits ih =>
      intro xs hdigits sample
      let pass := countingSortBy maxDigit digit xs
      have hdigit : AllKeysLe digit xs maxDigit :=
        hdigits digit (by simp)
      have hpass_mem :
          ∀ y, y ∈ pass ↔ y ∈ xs := by
        intro y
        exact countingSortBy_mem_iff maxDigit digit xs hdigit y
      have hrest : AllDigitsLe digits pass maxDigit := by
        refine allDigitsLe_of_mem_iff ?_ hpass_mem
        intro d hd
        exact hdigits d (by simp [hd])
      have htail :
          digitClass digits sample (radixSortBy maxDigit digits pass) =
            digitClass digits sample pass :=
        ih pass hrest sample
      calc
        digitClass (digit :: digits) sample
            (radixSortBy maxDigit (digit :: digits) xs)
            =
          digitClass (digit :: digits) sample
            (radixSortBy maxDigit digits pass) := by
              simp [radixSortBy, pass]
        _ =
          (digitClass digits sample
              (radixSortBy maxDigit digits pass)).filter
            (fun x => digit x == digit sample) := by
              rw [digitClass_cons_filter]
        _ =
          (digitClass digits sample pass).filter
            (fun x => digit x == digit sample) := by
              rw [htail]
        _ = digitClass (digit :: digits) sample pass := by
              rw [digitClass_cons_filter]
        _ = digitClass (digit :: digits) sample xs :=
              countingSortBy_digitClass_cons_eq maxDigit digit digits sample xs
                hdigit

/--
Radix sort is stable with respect to complete digit signatures: filtering the
output to all elements matching a fixed sample on every digit gives exactly the
same ordered subsequence as filtering the input.
-/
theorem radixSortBy_stable
    (maxDigit : Nat) (digitsLow : List (α → Nat)) (xs : List α)
    (hdigits : AllDigitsLe digitsLow xs maxDigit) (sample : α) :
    digitClass digitsLow sample (radixSortBy maxDigit digitsLow xs) =
      digitClass digitsLow sample xs :=
  radixSortBy_digitClass_eq maxDigit digitsLow xs hdigits sample

/-- Reader-facing correctness theorem for abstract radix sort. -/
theorem radixSortBy_correct [DecidableEq α]
    (maxDigit : Nat) (digitsLow : List (α → Nat)) (xs : List α)
    (hdigits : AllDigitsLe digitsLow xs maxDigit) :
    OrderedRel (RadixLex digitsLow)
        (radixSortBy maxDigit digitsLow xs) ∧
      (∀ x, x ∈ radixSortBy maxDigit digitsLow xs ↔ x ∈ xs) ∧
      (radixSortBy maxDigit digitsLow xs).Perm xs :=
  ⟨radixSortBy_ordered maxDigit digitsLow xs,
    radixSortBy_mem_iff maxDigit digitsLow xs hdigits,
    radixSortBy_perm maxDigit digitsLow xs hdigits⟩

/-- Reader-facing correctness theorem including the explicit stability clause. -/
theorem radixSortBy_correct_stable [DecidableEq α]
    (maxDigit : Nat) (digitsLow : List (α → Nat)) (xs : List α)
    (hdigits : AllDigitsLe digitsLow xs maxDigit) :
    OrderedRel (RadixLex digitsLow)
        (radixSortBy maxDigit digitsLow xs) ∧
      (∀ sample,
        digitClass digitsLow sample (radixSortBy maxDigit digitsLow xs) =
          digitClass digitsLow sample xs) ∧
      (∀ x, x ∈ radixSortBy maxDigit digitsLow xs ↔ x ∈ xs) ∧
      (radixSortBy maxDigit digitsLow xs).Perm xs :=
  ⟨radixSortBy_ordered maxDigit digitsLow xs,
    radixSortBy_stable maxDigit digitsLow xs hdigits,
    radixSortBy_mem_iff maxDigit digitsLow xs hdigits,
    radixSortBy_perm maxDigit digitsLow xs hdigits⟩

end Chapter08
end CLRS

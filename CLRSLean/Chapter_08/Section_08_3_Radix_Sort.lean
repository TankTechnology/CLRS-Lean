import CLRSLean.Chapter_08.Section_08_2_Counting_Sort
import CLRSLean.Chapter_08.Section_08_2_Counting_Sort.MutableOutputArray

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

The final layer instantiates the abstract digit interface with concrete
base-{lit}`b` digits for natural-number keys, packages ordinary key ordering
behind a named digit-order bridge, and discharges that bridge for bounded
fixed-width keys.  The final concrete theorem therefore says radix sort returns
a list ordered by the ordinary natural-number key when every key is represented
inside the supplied digit window.

A running-time / cost layer then instruments the abstract radix sort:

* {lit}`radixSortByWithCost` charges each stable counting-sort pass the mutable
  counting-sort work {lit}`MutableOutput.countingSortArrayCost maxDigit
  (input length)` and erases back to {lit}`radixSortBy`;
* {lit}`radixSortNatByCost` is the concrete {lit}`digitCount`-pass cost, and
  {lit}`radixSortNatByCost_bigO` proves the {lit}`O(d(n+k))` bound with
  {lit}`k = base`.
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

/--
Turn a pairwise relation order into the adjacent key-order predicate used by
the counting-sort section, provided the relation implies key monotonicity on
the same list.
-/
theorem orderedBy_of_orderedRel_on {rel : α → α → Prop} {key : α → Nat}
    {xs : List α} (hxs : OrderedRel rel xs)
    (hrel : ∀ x ∈ xs, ∀ y ∈ xs, rel x y → key x ≤ key y) :
    OrderedBy key xs := by
  induction xs with
  | nil =>
      trivial
  | cons x xs ih =>
      cases xs with
      | nil =>
          trivial
      | cons y ys =>
          cases hxs with
          | cons hhead htail =>
              refine ⟨?_, ih htail ?_⟩
              · exact hrel x (by simp) y (by simp) (hhead y (by simp))
              · intro a ha b hb hab
                exact hrel a (by simp [ha]) b (by simp [hb]) hab

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

/-! ## Concrete base-b digit extraction -/

/--
The {lit}`i`th least-significant base-{lit}`base` digit of a natural number.

For example, digit {lit}`0` is the units digit and digit {lit}`1` is the next
more significant digit.  The definition is intentionally small so the abstract
radix-sort theorem above can be reused without changing its proof.
-/
def baseDigit (base i n : Nat) : Nat :=
  (n / base ^ i) % base

/-- The low-to-high list of concrete base-{lit}`base` digit functions. -/
def baseDigitsLow (base digitCount : Nat) (key : α → Nat) :
    List (α → Nat) :=
  (List.range digitCount).map fun i x => baseDigit base i (key x)

/-- Every extracted base digit is bounded by {lit}`base - 1`. -/
theorem baseDigit_le_max (base i n : Nat) (hbase : 0 < base) :
    baseDigit base i n ≤ base - 1 := by
  simpa [baseDigit, Nat.pred_eq_sub_one] using
    Nat.le_pred_of_lt (Nat.mod_lt (n / base ^ i) hbase)

/-- For a one-digit key smaller than the base, the extracted digit is the key. -/
theorem baseDigit_zero_eq_self_of_lt {base n : Nat} (hn : n < base) :
    baseDigit base 0 n = n := by
  simpa [baseDigit] using Nat.mod_eq_of_lt hn

/-- The concrete digit list satisfies the abstract bounded-digit hypothesis. -/
theorem baseDigitsLow_allDigitsLe
    (base digitCount : Nat) (key : α → Nat) (xs : List α)
    (hbase : 0 < base) :
    AllDigitsLe (baseDigitsLow base digitCount key) xs (base - 1) := by
  intro digit hdigit x _hx
  rw [baseDigitsLow] at hdigit
  rcases List.mem_map.mp hdigit with ⟨i, _hi, rfl⟩
  exact baseDigit_le_max base i (key x) hbase

/--
Reinterpreting the first {lit}`digitCount` extracted low-to-high digits gives
the corresponding residue modulo {lit}`base ^ digitCount`.
-/
theorem baseDigitsLow_value_eq_mod_pow
    (base digitCount : Nat) (key : α → Nat) (x : α) :
    Nat.ofDigits base
        ((baseDigitsLow base digitCount key).map fun digit => digit x) =
      key x % base ^ digitCount := by
  simp [baseDigitsLow]
  induction digitCount with
  | zero =>
      simp [Nat.mod_one]
  | succ k ih =>
      rw [List.range_succ, List.map_append, Nat.ofDigits_append, ih]
      simp [baseDigit, Nat.pow_succ]
      conv_rhs =>
        rw [← Nat.mod_add_div ((key x) % (base ^ k * base)) (base ^ k)]
      rw [Nat.mod_mul_right_mod, Nat.mod_mul_right_div_self]

/--
If a key fits into the declared fixed-width digit window, the extracted digits
reconstruct the key exactly.
-/
theorem baseDigitsLow_value_eq_self_of_lt
    (base digitCount : Nat) (key : α → Nat) (x : α)
    (hkey : key x < base ^ digitCount) :
    Nat.ofDigits base
        ((baseDigitsLow base digitCount key).map fun digit => digit x) =
      key x := by
  rw [baseDigitsLow_value_eq_mod_pow, Nat.mod_eq_of_lt hkey]

/--
Accumulator form of the radix lexicographic value lemma.  The accumulator
{lit}`low` stores lower-priority digits and is assumed to be smaller than the
current place-value scale.
-/
theorem radixRel_accValue_le
    (base scale : Nat) (digitsLow : List (α → Nat))
    (low : α → Nat) (rel : α → α → Prop)
    (hbase : 0 < base) (hscale : 0 < scale)
    (hlow : ∀ z, low z < scale)
    (hrel : ∀ ⦃x y⦄, rel x y → low x ≤ low y)
    (hdigits : ∀ digit ∈ digitsLow, ∀ z, digit z < base) :
    ∀ ⦃x y : α⦄,
      RadixRel digitsLow rel x y →
        low x + scale * Nat.ofDigits base
            (digitsLow.map fun digit => digit x) ≤
        low y + scale * Nat.ofDigits base
            (digitsLow.map fun digit => digit y) := by
  induction digitsLow generalizing low rel scale with
  | nil =>
      intro x y hxy
      simpa using hrel hxy
  | cons digit digits ih =>
      intro x y hxy
      have hdigit : ∀ z, digit z < base := hdigits digit (by simp)
      have hdigits_tail : ∀ d ∈ digits, ∀ z, d z < base := by
        intro d hd z
        exact hdigits d (by simp [hd]) z
      have hscale' : 0 < scale * base := Nat.mul_pos hscale hbase
      have hlow' :
          ∀ z, low z + scale * digit z < scale * base := by
        intro z
        have hlt1 :
            low z + scale * digit z < scale * (digit z + 1) := by
          simpa [Nat.mul_succ, Nat.add_comm, Nat.add_left_comm,
            Nat.add_assoc] using
            Nat.add_lt_add_right (hlow z) (scale * digit z)
        have hle2 : scale * (digit z + 1) ≤ scale * base :=
          Nat.mul_le_mul_left scale (Nat.succ_le_of_lt (hdigit z))
        exact Nat.lt_of_lt_of_le hlt1 hle2
      have hrel' :
          ∀ ⦃a b⦄, LexWith digit rel a b →
            low a + scale * digit a ≤ low b + scale * digit b := by
        intro a b hab
        rcases hab with hlt | ⟨heq, hr⟩
        · have hlt1 :
              low a + scale * digit a < scale * (digit a + 1) := by
            simpa [Nat.mul_succ, Nat.add_comm, Nat.add_left_comm,
              Nat.add_assoc] using
              Nat.add_lt_add_right (hlow a) (scale * digit a)
          have hle2 : scale * (digit a + 1) ≤ scale * digit b :=
            Nat.mul_le_mul_left scale (Nat.succ_le_of_lt hlt)
          exact Nat.le_trans (Nat.le_of_lt hlt1)
            (Nat.le_trans hle2 (Nat.le_add_left _ _))
        · rw [heq]
          exact Nat.add_le_add_right (hrel hr) _
      have hmain := ih (low := fun z => low z + scale * digit z)
        (rel := LexWith digit rel) (scale := scale * base)
        hscale' hlow' hrel' hdigits_tail hxy
      simpa [Nat.ofDigits, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hmain

/--
Radix lexicographic order on bounded digits is monotone for the natural number
obtained by reinterpreting the low-to-high digit list.
-/
theorem radixLex_value_le
    (base : Nat) (digitsLow : List (α → Nat)) (x y : α)
    (hbase : 0 < base)
    (hdigits : ∀ digit ∈ digitsLow, ∀ z, digit z < base)
    (hxy : RadixLex digitsLow x y) :
    Nat.ofDigits base (digitsLow.map fun digit => digit x) ≤
      Nat.ofDigits base (digitsLow.map fun digit => digit y) := by
  have hmain := radixRel_accValue_le base 1 digitsLow
    (fun _ : α => 0) (fun _ _ : α => True)
    hbase (by decide) (by intro _; decide)
    (by intro _ _ _; exact Nat.zero_le _) hdigits hxy
  simpa using hmain

/--
Concrete base digits satisfy the bounded-digit side condition needed by
{name}`radixLex_value_le`.
-/
theorem baseDigitsLow_digits_lt
    (base digitCount : Nat) (key : α → Nat) (hbase : 0 < base) :
    ∀ digit ∈ baseDigitsLow base digitCount key, ∀ z, digit z < base := by
  intro digit hdigit z
  rw [baseDigitsLow] at hdigit
  rcases List.mem_map.mp hdigit with ⟨i, _hi, rfl⟩
  simpa [baseDigit] using Nat.mod_lt (key z / base ^ i) hbase

/--
The arithmetic bridge needed to turn digit-lexicographic order into ordinary
key order on a concrete input domain.
-/
def RadixDigitOrderRespectsKey
    (base digitCount : Nat) (key : α → Nat) (domain : List α) : Prop :=
  ∀ x ∈ domain, ∀ y ∈ domain,
    RadixLex (baseDigitsLow base digitCount key) x y → key x ≤ key y

/--
For fixed-width bounded keys, the concrete radix digit order respects ordinary
natural-number key order.
-/
theorem radixDigitOrderRespectsKey_of_bounded
    (base digitCount : Nat) (key : α → Nat) (xs : List α)
    (hbase : 0 < base)
    (hkeys : ∀ x ∈ xs, key x < base ^ digitCount) :
    RadixDigitOrderRespectsKey base digitCount key xs := by
  intro x hx y hy hxy
  have hvalue := radixLex_value_le base
    (baseDigitsLow base digitCount key) x y hbase
    (baseDigitsLow_digits_lt base digitCount key hbase) hxy
  rw [baseDigitsLow_value_eq_self_of_lt base digitCount key x
      (hkeys x hx),
    baseDigitsLow_value_eq_self_of_lt base digitCount key y
      (hkeys y hy)] at hvalue
  exact hvalue

/--
Concrete radix sort for natural-number keys, using the low-to-high base digits
of {lit}`key`.
-/
def radixSortNatBy (base digitCount : Nat) (key : α → Nat) (xs : List α) :
    List α :=
  radixSortBy (base - 1) (baseDigitsLow base digitCount key) xs

/--
Reader-facing concrete radix-sort correctness theorem.

The ordering clause is still the digit-lexicographic relation induced by the
chosen concrete digits.  A later arithmetic refinement can identify this
relation with ordinary natural-number ordering under a bounded-key hypothesis.
-/
theorem radixSortNatBy_correct_stable [DecidableEq α]
    (base digitCount : Nat) (key : α → Nat) (xs : List α)
    (hbase : 0 < base) :
    OrderedRel (RadixLex (baseDigitsLow base digitCount key))
        (radixSortNatBy base digitCount key xs) ∧
      (∀ sample,
        digitClass (baseDigitsLow base digitCount key) sample
          (radixSortNatBy base digitCount key xs) =
          digitClass (baseDigitsLow base digitCount key) sample xs) ∧
      (∀ x, x ∈ radixSortNatBy base digitCount key xs ↔ x ∈ xs) ∧
      (radixSortNatBy base digitCount key xs).Perm xs := by
  simpa [radixSortNatBy] using
    radixSortBy_correct_stable (base - 1) (baseDigitsLow base digitCount key)
      xs (baseDigitsLow_allDigitsLe base digitCount key xs hbase)

/--
If every key in the input fits in one base-{lit}`base` digit, then the concrete
radix digit order is already ordinary key order.
-/
theorem radixDigitOrderRespectsKey_singleDigit
    (base : Nat) (key : α → Nat) (xs : List α)
    (hkeys : ∀ x ∈ xs, key x < base) :
    RadixDigitOrderRespectsKey base 1 key xs := by
  intro x hx y hy hxy
  have hx_digit :
      baseDigit base 0 (key x) = key x :=
    baseDigit_zero_eq_self_of_lt (hkeys x hx)
  have hy_digit :
      baseDigit base 0 (key y) = key y :=
    baseDigit_zero_eq_self_of_lt (hkeys y hy)
  change LexWith (fun z => baseDigit base 0 (key z)) (fun _ _ => True) x y at hxy
  dsimp [LexWith] at hxy
  rw [hx_digit, hy_digit] at hxy
  rcases hxy with hlt | ⟨heq, _⟩
  · exact Nat.le_of_lt hlt
  · exact Nat.le_of_eq heq

/--
If the concrete digit lexicographic relation respects the natural key order on
the input domain, concrete radix sort returns a list ordered by that key.
-/
theorem radixSortNatBy_keyOrdered_of_digitOrder [DecidableEq α]
    (base digitCount : Nat) (key : α → Nat) (xs : List α)
    (hbase : 0 < base)
    (hdigit_order : RadixDigitOrderRespectsKey base digitCount key xs) :
    OrderedBy key (radixSortNatBy base digitCount key xs) := by
  have hcorrect := radixSortNatBy_correct_stable base digitCount key xs hbase
  have hmem :
      ∀ x, x ∈ radixSortNatBy base digitCount key xs ↔ x ∈ xs :=
    hcorrect.2.2.1
  exact orderedBy_of_orderedRel_on hcorrect.1
    (by
      intro x hx y hy hxy
      exact hdigit_order x ((hmem x).mp hx) y ((hmem y).mp hy) hxy)

/--
Concrete radix-sort correctness theorem with ordinary key ordering separated
from the remaining base-{lit}`b` arithmetic obligation.
-/
theorem radixSortNatBy_correct_keyOrdered_of_digitOrder [DecidableEq α]
    (base digitCount : Nat) (key : α → Nat) (xs : List α)
    (hbase : 0 < base)
    (hdigit_order : RadixDigitOrderRespectsKey base digitCount key xs) :
    OrderedBy key (radixSortNatBy base digitCount key xs) ∧
      (∀ sample,
        digitClass (baseDigitsLow base digitCount key) sample
          (radixSortNatBy base digitCount key xs) =
          digitClass (baseDigitsLow base digitCount key) sample xs) ∧
      (∀ x, x ∈ radixSortNatBy base digitCount key xs ↔ x ∈ xs) ∧
      (radixSortNatBy base digitCount key xs).Perm xs := by
  have hcorrect := radixSortNatBy_correct_stable base digitCount key xs hbase
  exact ⟨radixSortNatBy_keyOrdered_of_digitOrder base digitCount key xs hbase
      hdigit_order,
    hcorrect.2.1,
    hcorrect.2.2.1,
    hcorrect.2.2.2⟩

/--
Concrete one-pass radix-sort correctness when all keys are already below the
base.  This is the smallest arithmetic discharge of
{name}`RadixDigitOrderRespectsKey`.
-/
theorem radixSortNatBy_correct_keyOrdered_singleDigit [DecidableEq α]
    (base : Nat) (key : α → Nat) (xs : List α)
    (hbase : 0 < base) (hkeys : ∀ x ∈ xs, key x < base) :
    OrderedBy key (radixSortNatBy base 1 key xs) ∧
      (∀ sample,
        digitClass (baseDigitsLow base 1 key) sample
          (radixSortNatBy base 1 key xs) =
          digitClass (baseDigitsLow base 1 key) sample xs) ∧
      (∀ x, x ∈ radixSortNatBy base 1 key xs ↔ x ∈ xs) ∧
      (radixSortNatBy base 1 key xs).Perm xs :=
  radixSortNatBy_correct_keyOrdered_of_digitOrder base 1 key xs hbase
    (radixDigitOrderRespectsKey_singleDigit base key xs hkeys)

/--
Concrete fixed-width radix-sort correctness for bounded natural-number keys.
The bound {lit}`key x < base ^ digitCount` says the supplied digit window is
wide enough to represent every input key.
-/
theorem radixSortNatBy_correct_keyOrdered_of_bounded [DecidableEq α]
    (base digitCount : Nat) (key : α → Nat) (xs : List α)
    (hbase : 0 < base)
    (hkeys : ∀ x ∈ xs, key x < base ^ digitCount) :
    OrderedBy key (radixSortNatBy base digitCount key xs) ∧
      (∀ sample,
        digitClass (baseDigitsLow base digitCount key) sample
          (radixSortNatBy base digitCount key xs) =
          digitClass (baseDigitsLow base digitCount key) sample xs) ∧
      (∀ x, x ∈ radixSortNatBy base digitCount key xs ↔ x ∈ xs) ∧
      (radixSortNatBy base digitCount key xs).Perm xs :=
  radixSortNatBy_correct_keyOrdered_of_digitOrder base digitCount key xs hbase
    (radixDigitOrderRespectsKey_of_bounded base digitCount key xs hbase hkeys)

/-! ## Running-time / cost layer -/

/-- Counting sort preserves length when every key is at most {lit}`maxKey`. -/
theorem countingSortBy_length_eq_of_allKeysLe [DecidableEq α]
    (maxKey : Nat) (key : α → Nat) (xs : List α) (hxs : AllKeysLe key xs maxKey) :
    (countingSortBy maxKey key xs).length = xs.length :=
  (countingSortBy_perm maxKey key xs hxs).length_eq

/--
Costed radix sort.  Each stable counting-sort pass is charged the mutable
counting-sort work {lit}`MutableOutput.countingSortArrayCost maxDigit
(input length)`, and the per-pass costs accumulate.  The first component is
exactly {lit}`radixSortBy`.
-/
def radixSortByWithCost (maxDigit : Nat) :
    List (α → Nat) → List α → List α × Nat
  | [], xs => (xs, 0)
  | digit :: digits, xs =>
      let rest := radixSortByWithCost maxDigit digits
        (countingSortBy maxDigit digit xs)
      (rest.1, MutableOutput.countingSortArrayCost maxDigit xs.length + rest.2)

/-- Erasing the cost recovers the existing {lit}`radixSortBy`. -/
theorem radixSortByWithCost_result (maxDigit : Nat)
    (digitsLow : List (α → Nat)) (xs : List α) :
    (radixSortByWithCost maxDigit digitsLow xs).1 =
      radixSortBy maxDigit digitsLow xs := by
  induction digitsLow generalizing xs with
  | nil =>
      simp [radixSortByWithCost, radixSortBy]
  | cons digit digits ih =>
      simp only [radixSortByWithCost, radixSortBy]
      exact ih _

/--
Under the bounded-digit hypothesis the cost of the costed radix sort is exactly
{lit}`digitsLow.length` copies of the per-pass mutable counting-sort work: each
pass preserves the input length, so every pass is charged the same amount.
-/
theorem radixSortByWithCost_cost_eq [DecidableEq α] (maxDigit : Nat)
    (digitsLow : List (α → Nat)) (xs : List α)
    (hdigits : AllDigitsLe digitsLow xs maxDigit) :
    (radixSortByWithCost maxDigit digitsLow xs).2 =
      digitsLow.length * MutableOutput.countingSortArrayCost maxDigit xs.length := by
  induction digitsLow generalizing xs with
  | nil =>
      simp [radixSortByWithCost]
  | cons digit digits ih =>
      simp only [radixSortByWithCost]
      have hdigit : AllKeysLe digit xs maxDigit := hdigits digit (by simp)
      have hlen : (countingSortBy maxDigit digit xs).length = xs.length :=
        countingSortBy_length_eq_of_allKeysLe maxDigit digit xs hdigit
      have hrest : AllDigitsLe digits (countingSortBy maxDigit digit xs) maxDigit := by
        intro d hd x hx
        exact hdigits d (by simp [hd]) x
          ((countingSortBy_mem_iff maxDigit digit xs hdigit x).mp hx)
      rw [ih (countingSortBy maxDigit digit xs) hrest, hlen]
      simp only [List.length_cons]
      ring

/--
Total mutable counting-sort work of concrete base-{lit}`base` radix sort over
{lit}`n` keys: {lit}`digitCount` passes, each a mutable counting sort with
alphabet size {lit}`base`.
-/
def radixSortNatByCost (base digitCount n : Nat) : Nat :=
  digitCount * MutableOutput.countingSortArrayCost (base - 1) n

/--
The concrete cost equals the cost of the costed radix-sort execution on the
concrete digit list.  The bounded-digit hypothesis is discharged by
{lit}`baseDigitsLow_allDigitsLe`.
-/
theorem radixSortNatBy_cost_eq [DecidableEq α] (base digitCount : Nat)
    (key : α → Nat) (xs : List α) (hbase : 0 < base) :
    (radixSortByWithCost (base - 1) (baseDigitsLow base digitCount key) xs).2 =
      radixSortNatByCost base digitCount xs.length := by
  unfold radixSortNatByCost
  rw [radixSortByWithCost_cost_eq (base - 1) (baseDigitsLow base digitCount key) xs
    (baseDigitsLow_allDigitsLe base digitCount key xs hbase)]
  simp [baseDigitsLow]

/-- The mutable counting-sort work for alphabet size {lit}`base` is at most
{lit}`2 * (n + base + 1)`. -/
theorem countingSortArrayCost_le_two_mul (base n : Nat) :
    MutableOutput.countingSortArrayCost (base - 1) n ≤ 2 * (n + base + 1) := by
  calc
    MutableOutput.countingSortArrayCost (base - 1) n
        ≤ 2 * (n + ((base - 1) + 1)) :=
          MutableOutput.countingSortArrayCost_le (base - 1) n
    _ ≤ 2 * (n + base + 1) := by
      apply Nat.mul_le_mul_left
      omega

/-- The concrete radix-sort cost is at most {lit}`2 * (digitCount * (n + base + 1))`. -/
theorem radixSortNatByCost_le (base digitCount n : Nat) :
    radixSortNatByCost base digitCount n ≤ 2 * (digitCount * (n + base + 1)) := by
  unfold radixSortNatByCost
  have h := countingSortArrayCost_le_two_mul base n
  calc
    digitCount * MutableOutput.countingSortArrayCost (base - 1) n
        ≤ digitCount * (2 * (n + base + 1)) := Nat.mul_le_mul_left digitCount h
    _ = 2 * (digitCount * (n + base + 1)) := by ring

/--
**Linear {lit}`O(d(n+k))` work bound.**  There is a constant {lit}`c` (here
{lit}`2`) such that the concrete radix-sort work is at most
{lit}`c * (d * (n + k + 1))` for every alphabet size {lit}`k = base`, digit
count {lit}`d = digitCount`, and input length {lit}`n`.
-/
theorem radixSortNatByCost_bigO :
    ∃ c : Nat, ∀ base digitCount n : Nat,
      radixSortNatByCost base digitCount n ≤ c * (digitCount * (n + base + 1)) := by
  refine ⟨2, ?_⟩
  intro base digitCount n
  exact radixSortNatByCost_le base digitCount n

end Chapter08
end CLRS

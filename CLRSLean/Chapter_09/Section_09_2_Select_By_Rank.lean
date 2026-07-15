import Mathlib

/-!
# CLRS Section 9.2 - Selection in expected linear time

This file gives the first Chapter 9 correctness interface: a selector returns
an element with the requested zero-based order statistic.  The implementation is
the simple specification program obtained by sorting and indexing.  The
randomized and deterministic linear-time SELECT developments refine this
shared rank-certificate interface.

The public certificate is phrased by counts, so duplicates are handled in the
usual order-statistic way: if the selected value is {lit}`x`, then at most
{lit}`k` elements are strictly smaller than {lit}`x`, and more than {lit}`k`
elements are at most {lit}`x`.

## Expected-time analysis

The uniform-pivot recurrence, fresh per-call stochastic execution, and CLRS
Theorem 9.2 expected linear comparison bound are proved on a support page that
remains available outside the main sidebar:

* [Randomized SELECT Expected Time](CLRSLean/Chapter_09/Section_09_3_Deterministic_Select/Randomized_Select/)
-/

namespace CLRS
namespace Chapter09

/-! ## Specification selector and rank certificate -/

/-- A sorted copy of the input, used as the executable specification. -/
def sortedCopy (xs : List Nat) : List Nat :=
  xs.mergeSort (fun x y => decide (x ≤ y))

/-- Number of input elements strictly smaller than {lit}`x`. -/
def ltCount (x : Nat) (xs : List Nat) : Nat :=
  (xs.filter (fun y => decide (y < x))).length

/-- Number of input elements at most {lit}`x`. -/
def leCount (x : Nat) (xs : List Nat) : Nat :=
  (xs.filter (fun y => decide (y ≤ x))).length

/-- Number of input elements at least {lit}`x`. -/
def geCount (x : Nat) (xs : List Nat) : Nat :=
  (xs.filter (fun y => decide (x ≤ y))).length

/-- Number of input elements strictly greater than {lit}`x`. -/
def gtCount (x : Nat) (xs : List Nat) : Nat :=
  (xs.filter (fun y => decide (x < y))).length

/-- Select the zero-based rank {lit}`k`, if the input has that many elements. -/
def selectByRank? (k : Nat) (xs : List Nat) : Option Nat :=
  (sortedCopy xs)[k]?

/--
Rank certificate for order statistics with duplicates.  The selected value
{lit}`x` is present in the input, the number of values below it is at most
{lit}`k`, and the number of values at most it is greater than {lit}`k`.
-/
def RankCertificate (xs : List Nat) (k x : Nat) : Prop :=
  x ∈ xs ∧ ltCount x xs ≤ k ∧ k < leCount x xs

theorem sortedCopy_perm (xs : List Nat) :
    (sortedCopy xs).Perm xs := by
  simpa [sortedCopy] using
    List.mergeSort_perm xs (fun x y => decide (x ≤ y))

theorem sortedCopy_pairwise (xs : List Nat) :
    (sortedCopy xs).Pairwise (fun x y => x ≤ y) := by
  simpa [sortedCopy] using
    List.pairwise_mergeSort' (r := fun x y : Nat => x ≤ y) xs

/-! ## List lemmas for the rank proof -/

theorem getElem?_eq_some_iff_split {α : Type u} :
    ∀ {xs : List α} {k : Nat} {x : α},
      xs[k]? = some x ↔
        ∃ lo hi, xs = lo ++ x :: hi ∧ lo.length = k := by
  intro xs k x
  constructor
  · intro h
    induction k generalizing xs with
    | zero =>
        cases xs with
        | nil =>
            simp at h
        | cons y ys =>
            simp at h
            subst y
            exact ⟨[], ys, by simp, rfl⟩
    | succ k ih =>
        cases xs with
        | nil =>
            simp at h
        | cons y ys =>
            simp at h
            rcases ih h with ⟨lo, hi, hys, hlen⟩
            refine ⟨y :: lo, hi, ?_, ?_⟩
            · simp [hys]
            · simp [hlen]
  · rintro ⟨lo, hi, rfl, hlen⟩
    have hget : (lo ++ x :: hi)[lo.length]? = some x := by
      induction lo with
      | nil =>
          simp
      | cons _ lo ih =>
          simp
    rw [← hlen]
    exact hget

theorem pairwise_split_bounds {lo hi : List Nat} {x : Nat}
    (h : (lo ++ x :: hi).Pairwise (fun x y => x ≤ y)) :
    (∀ y ∈ lo, y ≤ x) ∧ (∀ y ∈ hi, x ≤ y) := by
  rcases (List.pairwise_append.mp h) with ⟨_, hxhi, hcross⟩
  constructor
  · intro y hy
    exact hcross y hy x (by simp)
  · cases hxhi with
    | cons hhead _ =>
        intro y hy
        exact hhead y hy

theorem ltCount_eq_of_perm {xs ys : List Nat} {x : Nat}
    (h : xs.Perm ys) :
    ltCount x xs = ltCount x ys := by
  unfold ltCount
  exact (h.filter (fun y => decide (y < x))).length_eq

theorem leCount_eq_of_perm {xs ys : List Nat} {x : Nat}
    (h : xs.Perm ys) :
    leCount x xs = leCount x ys := by
  unfold leCount
  exact (h.filter (fun y => decide (y ≤ x))).length_eq

theorem geCount_eq_length_sub_ltCount (x : Nat) :
    ∀ xs : List Nat, geCount x xs = xs.length - ltCount x xs := by
  intro xs
  induction xs with
  | nil =>
      simp [geCount, ltCount]
  | cons y ys ih =>
      unfold geCount ltCount at *
      by_cases hlt : y < x
      · have hnle : ¬ x ≤ y := Nat.not_le_of_gt hlt
        simp [hlt, hnle, ih]
      · have hge : x ≤ y := Nat.le_of_not_gt hlt
        have hfilter_le :
            (ys.filter (fun y => decide (y < x))).length ≤ ys.length :=
          List.length_filter_le (fun y => decide (y < x)) ys
        simp [hlt, hge, ih]
        omega

theorem gtCount_eq_length_sub_leCount (x : Nat) :
    ∀ xs : List Nat, gtCount x xs = xs.length - leCount x xs := by
  intro xs
  induction xs with
  | nil =>
      simp [gtCount, leCount]
  | cons y ys ih =>
      unfold gtCount leCount at *
      by_cases hgt : x < y
      · have hnle : ¬ y ≤ x := Nat.not_le_of_gt hgt
        have hfilter_le :
            (ys.filter (fun y => decide (y ≤ x))).length ≤ ys.length :=
          List.length_filter_le (fun y => decide (y ≤ x)) ys
        simp [hgt, hnle, ih]
        omega
      · have hle : y ≤ x := Nat.le_of_not_gt hgt
        simp [hgt, hle, ih]

theorem leCount_append (x : Nat) (xs ys : List Nat) :
    leCount x (xs ++ ys) = leCount x xs + leCount x ys := by
  unfold leCount
  rw [List.filter_append, List.length_append]

theorem geCount_append (x : Nat) (xs ys : List Nat) :
    geCount x (xs ++ ys) = geCount x xs + geCount x ys := by
  unfold geCount
  rw [List.filter_append, List.length_append]

theorem leCount_le_of_sublist {x : Nat} {xs ys : List Nat}
    (hsub : xs.Sublist ys) :
    leCount x xs ≤ leCount x ys := by
  unfold leCount
  exact (hsub.filter (fun y => decide (y ≤ x))).length_le

theorem geCount_le_of_sublist {x : Nat} {xs ys : List Nat}
    (hsub : xs.Sublist ys) :
    geCount x xs ≤ geCount x ys := by
  unfold geCount
  exact (hsub.filter (fun y => decide (x ≤ y))).length_le

theorem leCount_cons_of_le {x y : Nat} {ys : List Nat} (h : y ≤ x) :
    leCount x (y :: ys) = leCount x ys + 1 := by
  simp [leCount, h, Nat.add_comm]

theorem leCount_cons_of_not_le {x y : Nat} {ys : List Nat} (h : ¬ y ≤ x) :
    leCount x (y :: ys) = leCount x ys := by
  simp [leCount, h]

theorem geCount_cons_of_le {x y : Nat} {ys : List Nat} (h : x ≤ y) :
    geCount x (y :: ys) = geCount x ys + 1 := by
  simp [geCount, h, Nat.add_comm]

theorem geCount_cons_of_not_le {x y : Nat} {ys : List Nat} (h : ¬ x ≤ y) :
    geCount x (y :: ys) = geCount x ys := by
  simp [geCount, h]

theorem leCount_mono_of_le {low high : Nat} (h : low ≤ high) :
    ∀ xs : List Nat, leCount low xs ≤ leCount high xs := by
  intro xs
  induction xs with
  | nil =>
      simp [leCount]
  | cons y ys ih =>
      unfold leCount at *
      by_cases hlow : y ≤ low
      · have hhigh : y ≤ high := Nat.le_trans hlow h
        simp [hlow, hhigh, ih]
      · by_cases hhigh : y ≤ high
        · simp [hlow, hhigh]
          exact Nat.le_succ_of_le ih
        · simp [hlow, hhigh, ih]

theorem geCount_anti_mono_of_le {low high : Nat} (h : low ≤ high) :
    ∀ xs : List Nat, geCount high xs ≤ geCount low xs := by
  intro xs
  induction xs with
  | nil =>
      simp [geCount]
  | cons y ys ih =>
      unfold geCount at *
      by_cases hhigh : high ≤ y
      · have hlow : low ≤ y := Nat.le_trans h hhigh
        simp [hhigh, hlow, ih]
      · by_cases hlow : low ≤ y
        · simp [hhigh, hlow]
          exact Nat.le_succ_of_le ih
        · simp [hhigh, hlow, ih]

theorem ltCount_le_of_sorted_split {ys lo hi : List Nat} {x : Nat}
    (hsplit : ys = lo ++ x :: hi)
    (_hlo : ∀ y ∈ lo, y ≤ x)
    (hhi : ∀ y ∈ hi, x ≤ y) :
    ltCount x ys ≤ lo.length := by
  subst ys
  unfold ltCount
  have hhi_empty :
      hi.filter (fun y => decide (y < x)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro y hy
    simp [not_lt_of_ge (hhi y hy)]
  have hfilter :
      (lo ++ x :: hi).filter (fun y => decide (y < x)) =
        lo.filter (fun y => decide (y < x)) := by
    rw [List.filter_append]
    simp [hhi_empty]
  rw [hfilter]
  exact List.length_filter_le (fun y => decide (y < x)) lo

theorem lt_length_leCount_of_sorted_split {ys lo hi : List Nat} {x : Nat}
    (hsplit : ys = lo ++ x :: hi)
    (hlo : ∀ y ∈ lo, y ≤ x)
    (_hhi : ∀ y ∈ hi, x ≤ y) :
    lo.length < leCount x ys := by
  subst ys
  unfold leCount
  have hlo_self :
      lo.filter (fun y => decide (y ≤ x)) = lo := by
    rw [List.filter_eq_self]
    intro y hy
    simp [hlo y hy]
  have hfilter :
      (lo ++ x :: hi).filter (fun y => decide (y ≤ x)) =
        lo ++ x :: hi.filter (fun y => decide (y ≤ x)) := by
    rw [List.filter_append]
    simp [hlo_self]
  rw [hfilter]
  simp

/-! ## Pivot-style selection -/

/--
Fuelled quickselect over lists of natural numbers.

The first element is used as the pivot.  The recursive calls keep only the
values strictly below or strictly above the pivot; the middle pivot block is
represented by the count interval
{lit}`ltCount pivot xs ≤ k < leCount pivot xs`.
-/
def quickSelectFuel? : Nat → Nat → List Nat → Option Nat
  | 0, _, _ => none
  | _ + 1, _, [] => none
  | fuel + 1, k, pivot :: tail =>
      let xs := pivot :: tail
      if k < ltCount pivot xs then
        quickSelectFuel? fuel k (xs.filter fun y => decide (y < pivot))
      else if k < leCount pivot xs then
        some pivot
      else
        quickSelectFuel? fuel (k - leCount pivot xs)
          (xs.filter fun y => decide (pivot < y))

/-- Public quickselect wrapper with exactly one unit of fuel per input element. -/
def quickSelect? (k : Nat) (xs : List Nat) : Option Nat :=
  quickSelectFuel? xs.length k xs

theorem filter_length_lt_of_mem_false {α : Type u}
    (p : α → Bool) {xs : List α} {x : α}
    (hx : x ∈ xs) (hpx : p x = false) :
    (xs.filter p).length < xs.length := by
  have hle : (xs.filter p).length ≤ xs.length := List.length_filter_le p xs
  have hne : (xs.filter p).length ≠ xs.length := by
    intro heq
    have hall := (List.length_filter_eq_length_iff.mp heq) x hx
    rw [hpx] at hall
    contradiction
  exact Nat.lt_of_le_of_ne hle hne

theorem ltCount_filter_lt_eq (xs : List Nat) {x pivot : Nat}
    (hxp : x < pivot) :
    ltCount x xs = ltCount x (xs.filter fun y => decide (y < pivot)) := by
  unfold ltCount
  congr 1
  rw [List.filter_filter]
  apply List.filter_congr
  intro y _hy
  by_cases hyx : y < x
  · simp [hyx, Nat.lt_trans hyx hxp]
  · simp [hyx]

theorem leCount_filter_lt_eq (xs : List Nat) {x pivot : Nat}
    (hxp : x < pivot) :
    leCount x xs = leCount x (xs.filter fun y => decide (y < pivot)) := by
  unfold leCount
  congr 1
  rw [List.filter_filter]
  apply List.filter_congr
  intro y _hy
  by_cases hyx : y ≤ x
  · simp [hyx, Nat.lt_of_le_of_lt hyx hxp]
  · simp [hyx]

theorem ltCount_high_split (xs : List Nat) {pivot x : Nat}
    (hp : pivot < x) :
    leCount pivot xs + ltCount x (xs.filter fun y => decide (pivot < y)) =
      ltCount x xs := by
  unfold ltCount leCount
  induction xs with
  | nil =>
      simp
  | cons y ys ih =>
      have ih' :
          (ys.filter (fun y => decide (y ≤ pivot))).length +
              (ys.filter (fun a => decide (a < x) && decide (pivot < a))).length =
            (ys.filter (fun y => decide (y < x))).length := by
        simpa [List.filter_filter] using ih
      by_cases hyp : y ≤ pivot
      · have hyx : y < x := Nat.lt_of_le_of_lt hyp hp
        have hynot : ¬ pivot < y := not_lt_of_ge hyp
        simp [hyp, hyx, hynot]
        omega
      · have hpy : pivot < y := Nat.lt_of_not_ge hyp
        by_cases hyx : y < x
        · simp [hyp, hpy, hyx]
          omega
        · simp [hyp, hpy, hyx]
          omega

theorem leCount_high_split (xs : List Nat) {pivot x : Nat}
    (hp : pivot < x) :
    leCount pivot xs + leCount x (xs.filter fun y => decide (pivot < y)) =
      leCount x xs := by
  unfold leCount
  induction xs with
  | nil =>
      simp
  | cons y ys ih =>
      have ih' :
          (ys.filter (fun y => decide (y ≤ pivot))).length +
              (ys.filter (fun a => decide (a ≤ x) && decide (pivot < a))).length =
            (ys.filter (fun y => decide (y ≤ x))).length := by
        simpa [List.filter_filter] using ih
      by_cases hyp : y ≤ pivot
      · have hyx : y ≤ x := Nat.le_trans hyp (Nat.le_of_lt hp)
        have hynot : ¬ pivot < y := not_lt_of_ge hyp
        simp [hyp, hyx, hynot]
        omega
      · have hpy : pivot < y := Nat.lt_of_not_ge hyp
        by_cases hyx : y ≤ x
        · simp [hyp, hpy, hyx]
          omega
        · simp [hyp, hpy, hyx]
          omega

theorem rankCertificate_low_lift {xs : List Nat} {pivot k x : Nat}
    (hrank : RankCertificate (xs.filter fun y => decide (y < pivot)) k x) :
    RankCertificate xs k x := by
  have hxmem_low : x ∈ xs.filter fun y => decide (y < pivot) := hrank.1
  have hxmem : x ∈ xs := (List.mem_filter.mp hxmem_low).1
  have hxp : x < pivot := by
    have hxbool := (List.mem_filter.mp hxmem_low).2
    simpa using hxbool
  refine ⟨hxmem, ?_, ?_⟩
  · rw [ltCount_filter_lt_eq xs hxp]
    exact hrank.2.1
  · rw [leCount_filter_lt_eq xs hxp]
    exact hrank.2.2

theorem rankCertificate_pivot {xs : List Nat} {pivot k : Nat}
    (hpivot : pivot ∈ xs)
    (hlo : ¬ k < ltCount pivot xs)
    (hle : k < leCount pivot xs) :
    RankCertificate xs k pivot :=
  ⟨hpivot, Nat.le_of_not_gt hlo, hle⟩

theorem rankCertificate_high_lift {xs : List Nat} {pivot k x : Nat}
    (hge : leCount pivot xs ≤ k)
    (hrank :
      RankCertificate (xs.filter fun y => decide (pivot < y))
        (k - leCount pivot xs) x) :
    RankCertificate xs k x := by
  have hxmem_high : x ∈ xs.filter fun y => decide (pivot < y) := hrank.1
  have hxmem : x ∈ xs := (List.mem_filter.mp hxmem_high).1
  have hpx : pivot < x := by
    have hxbool := (List.mem_filter.mp hxmem_high).2
    simpa using hxbool
  refine ⟨hxmem, ?_, ?_⟩
  · have hsplit := ltCount_high_split xs hpx
    have hbound :
        leCount pivot xs +
            ltCount x (xs.filter fun y => decide (pivot < y)) ≤
          leCount pivot xs + (k - leCount pivot xs) :=
      Nat.add_le_add_left hrank.2.1 (leCount pivot xs)
    have hsum : leCount pivot xs + (k - leCount pivot xs) = k :=
      Nat.add_sub_of_le hge
    rw [hsum] at hbound
    rw [← hsplit]
    exact hbound
  · have hsplit := leCount_high_split xs hpx
    have hbound :
        leCount pivot xs + (k - leCount pivot xs) <
          leCount pivot xs +
            leCount x (xs.filter fun y => decide (pivot < y)) :=
      Nat.add_lt_add_left hrank.2.2 (leCount pivot xs)
    have hsum : leCount pivot xs + (k - leCount pivot xs) = k :=
      Nat.add_sub_of_le hge
    rw [hsum, hsplit] at hbound
    exact hbound

theorem quickSelectFuel?_rankCorrect :
    ∀ (fuel k : Nat) (xs : List Nat) {x : Nat}, xs.length ≤ fuel →
      quickSelectFuel? fuel k xs = some x →
        RankCertificate xs k x := by
  intro fuel
  induction fuel with
  | zero =>
      intro k xs selected _hlen hsel
      simp [quickSelectFuel?] at hsel
  | succ fuel ih =>
      intro k xs selected hlen hsel
      cases xs with
      | nil =>
          simp [quickSelectFuel?] at hsel
      | cons pivot tail =>
          let xs : List Nat := pivot :: tail
          have hlow_len :
              (xs.filter fun y => decide (y < pivot)).length ≤ fuel := by
            have hstrict :
                (xs.filter fun y => decide (y < pivot)).length < xs.length :=
              filter_length_lt_of_mem_false (fun y => decide (y < pivot))
                (xs := xs) (x := pivot) (by simp [xs]) (by simp)
            have hlt_fuel : (xs.filter fun y => decide (y < pivot)).length < fuel + 1 :=
              Nat.lt_of_lt_of_le hstrict (by simpa [xs] using hlen)
            exact Nat.lt_succ_iff.mp hlt_fuel
          have hhigh_len :
              (xs.filter fun y => decide (pivot < y)).length ≤ fuel := by
            have hstrict :
                (xs.filter fun y => decide (pivot < y)).length < xs.length :=
              filter_length_lt_of_mem_false (fun y => decide (pivot < y))
                (xs := xs) (x := pivot) (by simp [xs]) (by simp)
            have hlt_fuel : (xs.filter fun y => decide (pivot < y)).length < fuel + 1 :=
              Nat.lt_of_lt_of_le hstrict (by simpa [xs] using hlen)
            exact Nat.lt_succ_iff.mp hlt_fuel
          by_cases hlo : k < ltCount pivot xs
          · have hsel_low :
                quickSelectFuel? fuel k (xs.filter fun y => decide (y < pivot)) =
                  some selected := by
              simpa [quickSelectFuel?, xs, hlo] using hsel
            exact rankCertificate_low_lift (ih k (xs.filter fun y => decide (y < pivot))
              hlow_len hsel_low)
          · by_cases hle : k < leCount pivot xs
            · have hx : selected = pivot := by
                exact Eq.symm (by simpa [quickSelectFuel?, xs, hlo, hle] using hsel)
              subst selected
              exact rankCertificate_pivot (xs := xs) (pivot := pivot)
                (by simp [xs]) hlo hle
            · have hsel_high :
                  quickSelectFuel? fuel (k - leCount pivot xs)
                      (xs.filter fun y => decide (pivot < y)) =
                    some selected := by
                simpa [quickSelectFuel?, xs, hlo, hle] using hsel
              have hge : leCount pivot xs ≤ k := Nat.le_of_not_gt hle
              exact rankCertificate_high_lift hge
                (ih (k - leCount pivot xs)
                  (xs.filter fun y => decide (pivot < y)) hhigh_len hsel_high)

/-! ## Selection correctness -/

theorem selectByRank?_rankCorrect {k : Nat} {xs : List Nat} {x : Nat}
    (hsel : selectByRank? k xs = some x) :
    RankCertificate xs k x := by
  unfold selectByRank? at hsel
  rcases (getElem?_eq_some_iff_split.mp hsel) with
    ⟨lo, hi, hsplit, hlen⟩
  have hpair :
      (lo ++ x :: hi).Pairwise (fun x y => x ≤ y) := by
    rw [← hsplit]
    exact sortedCopy_pairwise xs
  rcases pairwise_split_bounds hpair with ⟨hlo, hhi⟩
  have hxSorted : x ∈ sortedCopy xs := by
    rw [hsplit]
    simp
  have hperm : (sortedCopy xs).Perm xs := sortedCopy_perm xs
  refine ⟨(hperm.mem_iff.mp hxSorted), ?_, ?_⟩
  · have hltSorted :
        ltCount x (sortedCopy xs) ≤ lo.length :=
      ltCount_le_of_sorted_split hsplit hlo hhi
    have hltEq : ltCount x (sortedCopy xs) = ltCount x xs :=
      ltCount_eq_of_perm hperm
    rw [← hltEq, ← hlen]
    exact hltSorted
  · have hleSorted :
        lo.length < leCount x (sortedCopy xs) :=
      lt_length_leCount_of_sorted_split hsplit hlo hhi
    have hleEq : leCount x (sortedCopy xs) = leCount x xs :=
      leCount_eq_of_perm hperm
    rw [← hleEq, ← hlen]
    exact hleSorted

theorem selectByRank?_mem {k : Nat} {xs : List Nat} {x : Nat}
    (hsel : selectByRank? k xs = some x) :
    x ∈ xs :=
  (selectByRank?_rankCorrect hsel).1

/-- The specification selector succeeds whenever the requested rank is in range. -/
theorem selectByRank?_isSome_of_lt {k : Nat} {xs : List Nat}
    (hk : k < xs.length) :
    ∃ x, selectByRank? k xs = some x := by
  unfold selectByRank?
  have hlen : (sortedCopy xs).length = xs.length :=
    (sortedCopy_perm xs).length_eq
  have hk' : k < (sortedCopy xs).length := by
    simpa [hlen] using hk
  exact ⟨(sortedCopy xs)[k], by simp [List.getElem?_eq_getElem hk']⟩

/-- Reader-facing correctness wrapper for the specification selector. -/
theorem selectByRank?_correct {k : Nat} {xs : List Nat} {x : Nat}
    (hsel : selectByRank? k xs = some x) :
    RankCertificate xs k x :=
  selectByRank?_rankCorrect hsel

theorem quickSelect?_rankCorrect {k : Nat} {xs : List Nat} {x : Nat}
    (hsel : quickSelect? k xs = some x) :
    RankCertificate xs k x := by
  exact quickSelectFuel?_rankCorrect xs.length k xs (Nat.le_refl xs.length) hsel

theorem quickSelect?_mem {k : Nat} {xs : List Nat} {x : Nat}
    (hsel : quickSelect? k xs = some x) :
    x ∈ xs :=
  (quickSelect?_rankCorrect hsel).1

/-- Reader-facing correctness wrapper for the pivot-style quickselect model. -/
theorem quickSelect?_correct {k : Nat} {xs : List Nat} {x : Nat}
    (hsel : quickSelect? k xs = some x) :
    RankCertificate xs k x :=
  quickSelect?_rankCorrect hsel

end Chapter09
end CLRS

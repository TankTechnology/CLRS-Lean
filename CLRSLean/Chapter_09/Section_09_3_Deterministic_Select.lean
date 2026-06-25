import CLRSLean.Chapter_09.Section_09_2_Select_By_Rank

/-!
# CLRS Section 9.3 - Deterministic selection

This file factors the Chapter 9 selection proof through a pivot-parametric
interface.  The key point is pure correctness rather than running time: any
pivot rule that returns an element of the current input list yields a selector
whose successful result satisfies the same count-based rank certificate used in
Section 9.2.

Main results:

* Theorem {lit}`selectWithPivot?_correct`: a pivot-parametric SELECT is rank
  correct whenever the pivot rule returns members of the current list.
* Theorem {lit}`medianOfFive?_certificate`: the median selected from a
  five-element group has at least three elements below it weakly and at least
  three elements above it weakly.
* Theorems {lit}`medianGroupCertificates_leCount_lower_bound` and
  {lit}`medianGroupCertificates_geCount_lower_bound`: a collection of certified
  five-element groups contributes three original elements for every group
  median on the corresponding side of a pivot.
* Theorem {lit}`fullGroupsOfFive_medianPivot_split_counts`: the executable
  full-grouping wrapper constructs the certificates and obtains the split
  counts for a median of the group medians.
* Theorem {lit}`fullGroupsOfFive_medianPivot_fullInput_split_counts`: the
  grouped split counts lift to the original input list because the flattened
  full groups are a sublist of the input.
* Theorem {lit}`deterministicSelect?_correct`: a deterministic median-pivot
  instance is rank correct.

Current gaps:

* This is not yet the CLRS linear-time median-of-medians cost theorem.  The
  local five-element median certificate, executable grouping wrapper, grouped
  split-count core, and full-input median-pivot split-count wrapper are proved
  below; the remaining hard proof is the familiar {lit}`7n/10` partition-size
  arithmetic and the associated linear recurrence.
-/

namespace CLRS
namespace Chapter09

/-! ## Pivot-parametric selection -/

/--
A pivot function is membership-safe when every pivot it returns is an element
of the current input list.
-/
def PivotMembership (choosePivot? : List Nat → Option Nat) : Prop :=
  ∀ {xs : List Nat} {pivot : Nat}, choosePivot? xs = some pivot → pivot ∈ xs

/--
Fuelled SELECT with an abstract deterministic pivot rule.

The algorithm mirrors the CLRS three-way partition around the chosen pivot:
recurse on elements below the pivot, return the pivot block when the requested
rank falls inside it, or recurse on elements above the pivot after shifting the
rank by the number of elements at most the pivot.
-/
def selectWithPivotFuel? (choosePivot? : List Nat → Option Nat) :
    Nat → Nat → List Nat → Option Nat
  | 0, _, _ => none
  | fuel + 1, k, xs =>
      match choosePivot? xs with
      | none => none
      | some pivot =>
          if k < ltCount pivot xs then
            selectWithPivotFuel? choosePivot? fuel k
              (xs.filter fun y => decide (y < pivot))
          else if k < leCount pivot xs then
            some pivot
          else
            selectWithPivotFuel? choosePivot? fuel (k - leCount pivot xs)
              (xs.filter fun y => decide (pivot < y))

/-- Public SELECT wrapper using one unit of fuel per input element. -/
def selectWithPivot? (choosePivot? : List Nat → Option Nat)
    (k : Nat) (xs : List Nat) : Option Nat :=
  selectWithPivotFuel? choosePivot? xs.length k xs

/--
Correctness of the fuelled pivot-parametric SELECT.

If the pivot function is membership-safe and the computation returns {lit}`x`,
then {lit}`x` is a valid zero-based order statistic certificate for the
original input.
-/
theorem selectWithPivotFuel?_rankCorrect
    (choosePivot? : List Nat → Option Nat)
    (hpivot : PivotMembership choosePivot?) :
    ∀ (fuel k : Nat) (xs : List Nat) {x : Nat}, xs.length ≤ fuel →
      selectWithPivotFuel? choosePivot? fuel k xs = some x →
        RankCertificate xs k x := by
  intro fuel
  induction fuel with
  | zero =>
      intro k xs selected _hlen hsel
      simp [selectWithPivotFuel?] at hsel
  | succ fuel ih =>
      intro k xs selected hlen hsel
      cases hchoose : choosePivot? xs with
      | none =>
          simp [selectWithPivotFuel?, hchoose] at hsel
      | some pivot =>
          have hpivot_mem : pivot ∈ xs := hpivot hchoose
          have hlow_len :
              (xs.filter fun y => decide (y < pivot)).length ≤ fuel := by
            have hstrict :
                (xs.filter fun y => decide (y < pivot)).length < xs.length :=
              filter_length_lt_of_mem_false (fun y => decide (y < pivot))
                (xs := xs) (x := pivot) hpivot_mem (by simp)
            have hlt_fuel :
                (xs.filter fun y => decide (y < pivot)).length < fuel + 1 :=
              Nat.lt_of_lt_of_le hstrict hlen
            exact Nat.lt_succ_iff.mp hlt_fuel
          have hhigh_len :
              (xs.filter fun y => decide (pivot < y)).length ≤ fuel := by
            have hstrict :
                (xs.filter fun y => decide (pivot < y)).length < xs.length :=
              filter_length_lt_of_mem_false (fun y => decide (pivot < y))
                (xs := xs) (x := pivot) hpivot_mem (by simp)
            have hlt_fuel :
                (xs.filter fun y => decide (pivot < y)).length < fuel + 1 :=
              Nat.lt_of_lt_of_le hstrict hlen
            exact Nat.lt_succ_iff.mp hlt_fuel
          by_cases hlo : k < ltCount pivot xs
          · have hsel_low :
                selectWithPivotFuel? choosePivot? fuel k
                    (xs.filter fun y => decide (y < pivot)) =
                  some selected := by
              simpa [selectWithPivotFuel?, hchoose, hlo] using hsel
            exact rankCertificate_low_lift
              (ih k (xs.filter fun y => decide (y < pivot))
                hlow_len hsel_low)
          · by_cases hle : k < leCount pivot xs
            · have hx : selected = pivot := by
                exact Eq.symm
                  (by
                    simpa [selectWithPivotFuel?, hchoose, hlo, hle] using hsel)
              subst selected
              exact rankCertificate_pivot (xs := xs) (pivot := pivot)
                hpivot_mem hlo hle
            · have hsel_high :
                  selectWithPivotFuel? choosePivot? fuel
                      (k - leCount pivot xs)
                      (xs.filter fun y => decide (pivot < y)) =
                    some selected := by
                simpa [selectWithPivotFuel?, hchoose, hlo, hle] using hsel
              have hge : leCount pivot xs ≤ k := Nat.le_of_not_gt hle
              exact rankCertificate_high_lift hge
                (ih (k - leCount pivot xs)
                  (xs.filter fun y => decide (pivot < y))
                  hhigh_len hsel_high)

/-- Rank-correctness theorem for the public pivot-parametric SELECT wrapper. -/
theorem selectWithPivot?_rankCorrect
    (choosePivot? : List Nat → Option Nat)
    (hpivot : PivotMembership choosePivot?) {k : Nat} {xs : List Nat}
    {x : Nat} (hsel : selectWithPivot? choosePivot? k xs = some x) :
    RankCertificate xs k x := by
  exact selectWithPivotFuel?_rankCorrect choosePivot? hpivot xs.length k xs
    (Nat.le_refl xs.length) hsel

/-- Membership projection for pivot-parametric SELECT. -/
theorem selectWithPivot?_mem
    (choosePivot? : List Nat → Option Nat)
    (hpivot : PivotMembership choosePivot?) {k : Nat} {xs : List Nat}
    {x : Nat} (hsel : selectWithPivot? choosePivot? k xs = some x) :
    x ∈ xs :=
  (selectWithPivot?_rankCorrect choosePivot? hpivot hsel).1

/-- Reader-facing correctness wrapper for pivot-parametric SELECT. -/
theorem selectWithPivot?_correct
    (choosePivot? : List Nat → Option Nat)
    (hpivot : PivotMembership choosePivot?) {k : Nat} {xs : List Nat}
    {x : Nat} (hsel : selectWithPivot? choosePivot? k xs = some x) :
    RankCertificate xs k x :=
  selectWithPivot?_rankCorrect choosePivot? hpivot hsel

/-! ## Five-element median certificate -/

/-- Correctness-oriented median selector for a five-element group. -/
def medianOfFive? (xs : List Nat) : Option Nat :=
  selectByRank? 2 xs

/--
Local certificate used by the CLRS median-of-medians split argument.

For a five-element group, the selected median is an input member, at least
three group elements are at most it, and at least three group elements are at
least it.
-/
def MedianFiveCertificate (xs : List Nat) (median : Nat) : Prop :=
  xs.length = 5 ∧ median ∈ xs ∧ 3 ≤ leCount median xs ∧ 3 ≤ geCount median xs

/--
The rank-2 selector on a five-element group supplies the local 3/3 median
certificate needed by the deterministic SELECT split-size proof.
-/
theorem medianOfFive?_certificate {xs : List Nat} {median : Nat}
    (hlen : xs.length = 5) (hsel : medianOfFive? xs = some median) :
    MedianFiveCertificate xs median := by
  have hrank : RankCertificate xs 2 median := by
    exact selectByRank?_rankCorrect (by simpa [medianOfFive?] using hsel)
  refine ⟨hlen, hrank.1, ?_, ?_⟩
  · exact Nat.succ_le_of_lt hrank.2.2
  · have hlt : ltCount median xs ≤ 2 := hrank.2.1
    rw [geCount_eq_length_sub_ltCount, hlen]
    omega

/--
Certificates pairing each full five-element group with its selected median.

The theorem layer below intentionally does not require the groups to be
computed by a particular chunking function.  That keeps the split-size argument
usable for both executable median-of-medians code and later lower-level array
refinements.
-/
def MedianGroupCertificates (groups : List (List Nat)) (medians : List Nat) :
    Prop :=
  groups.length = medians.length ∧
    ∀ {group : List Nat} {median : Nat}, (group, median) ∈ groups.zip medians →
      MedianFiveCertificate group median

/-! ## Executable five-element grouping -/

/--
Fuelled grouping into full five-element blocks, dropping any trailing block of
fewer than five elements.

The fuel is only a termination device; the public wrapper below uses
{lit}`xs.length`, so the function is executable while keeping the proof
obligations straightforward.
-/
def fullGroupsOfFiveFuel : Nat → List Nat → List (List Nat)
  | 0, _ => []
  | fuel + 1, a :: b :: c :: d :: e :: rest =>
      [a, b, c, d, e] :: fullGroupsOfFiveFuel fuel rest
  | _ + 1, _ => []

/-- Executable full five-element grouping used by the median-of-medians layer. -/
def fullGroupsOfFive (xs : List Nat) : List (List Nat) :=
  fullGroupsOfFiveFuel xs.length xs

theorem fullGroupsOfFiveFuel_lengths {fuel : Nat} :
    ∀ {xs group : List Nat}, group ∈ fullGroupsOfFiveFuel fuel xs →
      group.length = 5 := by
  induction fuel with
  | zero =>
      intro xs group hmem
      simp [fullGroupsOfFiveFuel] at hmem
  | succ fuel ih =>
      intro xs group hmem
      cases xs with
      | nil =>
          simp [fullGroupsOfFiveFuel] at hmem
      | cons a xs =>
          cases xs with
          | nil =>
              simp [fullGroupsOfFiveFuel] at hmem
          | cons b xs =>
              cases xs with
              | nil =>
                  simp [fullGroupsOfFiveFuel] at hmem
              | cons c xs =>
                  cases xs with
                  | nil =>
                      simp [fullGroupsOfFiveFuel] at hmem
                  | cons d xs =>
                      cases xs with
                      | nil =>
                          simp [fullGroupsOfFiveFuel] at hmem
                      | cons e rest =>
                          simp [fullGroupsOfFiveFuel] at hmem
                          rcases hmem with rfl | htail
                          · simp
                          · exact ih htail

/-- Every executable full group has length five. -/
theorem fullGroupsOfFive_lengths {xs group : List Nat}
    (hmem : group ∈ fullGroupsOfFive xs) :
    group.length = 5 :=
  fullGroupsOfFiveFuel_lengths hmem

theorem fullGroupsOfFiveFuel_length_mul_five_le {fuel : Nat} :
    ∀ xs : List Nat, 5 * (fullGroupsOfFiveFuel fuel xs).length ≤ xs.length := by
  induction fuel with
  | zero =>
      intro xs
      simp [fullGroupsOfFiveFuel]
  | succ fuel ih =>
      intro xs
      cases xs with
      | nil =>
          simp [fullGroupsOfFiveFuel]
      | cons a xs =>
          cases xs with
          | nil =>
              simp [fullGroupsOfFiveFuel]
          | cons b xs =>
              cases xs with
              | nil =>
                  simp [fullGroupsOfFiveFuel]
              | cons c xs =>
                  cases xs with
                  | nil =>
                      simp [fullGroupsOfFiveFuel]
                  | cons d xs =>
                      cases xs with
                      | nil =>
                          simp [fullGroupsOfFiveFuel]
                      | cons e rest =>
                          have htail := ih rest
                          simp [fullGroupsOfFiveFuel]
                          omega

theorem fullGroupsOfFive_length_mul_five_le (xs : List Nat) :
    5 * (fullGroupsOfFive xs).length ≤ xs.length :=
  fullGroupsOfFiveFuel_length_mul_five_le xs

theorem fullGroupsOfFiveFuel_length_near {fuel : Nat} :
    ∀ {xs : List Nat}, xs.length ≤ fuel →
      xs.length ≤ 5 * (fullGroupsOfFiveFuel fuel xs).length + 4 := by
  induction fuel with
  | zero =>
      intro xs hlen
      cases xs with
      | nil =>
          simp [fullGroupsOfFiveFuel]
      | cons x xs =>
          simp at hlen
  | succ fuel ih =>
      intro xs hlen
      cases xs with
      | nil =>
          simp
      | cons a xs =>
          cases xs with
          | nil =>
              simp [fullGroupsOfFiveFuel]
          | cons b xs =>
              cases xs with
              | nil =>
                  simp [fullGroupsOfFiveFuel]
              | cons c xs =>
                  cases xs with
                  | nil =>
                      simp [fullGroupsOfFiveFuel]
                  | cons d xs =>
                      cases xs with
                      | nil =>
                          simp [fullGroupsOfFiveFuel]
                      | cons e rest =>
                          have hrest : rest.length ≤ fuel := by
                            simp at hlen
                            omega
                          have htail := ih hrest
                          simp [fullGroupsOfFiveFuel]
                          omega

theorem fullGroupsOfFive_length_near (xs : List Nat) :
    xs.length ≤ 5 * (fullGroupsOfFive xs).length + 4 :=
  fullGroupsOfFiveFuel_length_near (Nat.le_refl xs.length)

theorem fullGroupsOfFiveFuel_flatten_sublist {fuel : Nat} :
    ∀ xs : List Nat, (List.flatten (fullGroupsOfFiveFuel fuel xs)).Sublist xs := by
  induction fuel with
  | zero =>
      intro xs
      simp [fullGroupsOfFiveFuel]
  | succ fuel ih =>
      intro xs
      cases xs with
      | nil =>
          simp [fullGroupsOfFiveFuel]
      | cons a xs =>
          cases xs with
          | nil =>
              simp [fullGroupsOfFiveFuel]
          | cons b xs =>
              cases xs with
              | nil =>
                  simp [fullGroupsOfFiveFuel]
              | cons c xs =>
                  cases xs with
                  | nil =>
                      simp [fullGroupsOfFiveFuel]
                  | cons d xs =>
                      cases xs with
                      | nil =>
                          simp [fullGroupsOfFiveFuel]
                      | cons e rest =>
                          have htail := ih rest
                          simpa [fullGroupsOfFiveFuel] using
                            List.Sublist.cons_cons a
                              (List.Sublist.cons_cons b
                                (List.Sublist.cons_cons c
                                  (List.Sublist.cons_cons d
                                    (List.Sublist.cons_cons e htail))))

theorem fullGroupsOfFive_flatten_sublist (xs : List Nat) :
    (List.flatten (fullGroupsOfFive xs)).Sublist xs :=
  fullGroupsOfFiveFuel_flatten_sublist xs

/--
Map the five-element median selector across a list of groups, failing if any
group is not a valid five-element median input.
-/
def medianOfFiveGroups? : List (List Nat) → Option (List Nat)
  | [] => some []
  | group :: groups =>
      match medianOfFive? group, medianOfFiveGroups? groups with
      | some median, some medians => some (median :: medians)
      | _, _ => none

/--
If every group has length five, then the executable median-map produces exactly
the certificate package required by the grouped split-count theorem.
-/
theorem medianOfFiveGroups?_certificates {groups : List (List Nat)}
    {medians : List Nat}
    (hall : ∀ group ∈ groups, group.length = 5)
    (hsel : medianOfFiveGroups? groups = some medians) :
    MedianGroupCertificates groups medians := by
  induction groups generalizing medians with
  | nil =>
      simp [medianOfFiveGroups?] at hsel
      subst medians
      simp [MedianGroupCertificates]
  | cons group groups ih =>
      cases hhead : medianOfFive? group with
      | none =>
          simp [medianOfFiveGroups?, hhead] at hsel
      | some median =>
          cases htail : medianOfFiveGroups? groups with
          | none =>
              simp [medianOfFiveGroups?, hhead, htail] at hsel
          | some tailMedians =>
              simp [medianOfFiveGroups?, hhead, htail] at hsel
              subst medians
              have hhead_len : group.length = 5 := hall group (by simp)
              have hhead_cert : MedianFiveCertificate group median :=
                medianOfFive?_certificate hhead_len hhead
              have htail_all : ∀ tailGroup ∈ groups, tailGroup.length = 5 := by
                intro tailGroup hmem
                exact hall tailGroup (by simp [hmem])
              have htail_cert :
                  MedianGroupCertificates groups tailMedians :=
                ih htail_all htail
              rcases htail_cert with ⟨htail_len, htail_cert⟩
              refine ⟨by simp [htail_len], ?_⟩
              intro certGroup certMedian hmem
              simp at hmem
              rcases hmem with hhead_pair | htail_mem
              · rcases hhead_pair with ⟨rfl, rfl⟩
                exact hhead_cert
              · exact htail_cert htail_mem

/--
The executable full-grouping plus median-map automatically constructs the
abstract grouped certificate layer.
-/
theorem fullGroupsOfFive_medianGroupCertificates {xs medians : List Nat}
    (hsel : medianOfFiveGroups? (fullGroupsOfFive xs) = some medians) :
    MedianGroupCertificates (fullGroupsOfFive xs) medians :=
  medianOfFiveGroups?_certificates
    (fun _ hmem => fullGroupsOfFive_lengths hmem) hsel

/--
Every certified group whose median is at most {lit}`pivot` contributes at least
three original group elements at most {lit}`pivot`.
-/
theorem medianGroupCertificates_leCount_lower_bound {groups : List (List Nat)}
    {medians : List Nat} {pivot : Nat}
    (hcerts : MedianGroupCertificates groups medians) :
    3 * leCount pivot medians ≤ leCount pivot (List.flatten groups) := by
  induction groups generalizing medians with
  | nil =>
      rcases hcerts with ⟨hlen, _hcert⟩
      cases medians with
      | nil =>
          simp [leCount]
      | cons median medians =>
          simp at hlen
  | cons group groups ih =>
      cases medians with
      | nil =>
          rcases hcerts with ⟨hlen, _hcert⟩
          simp at hlen
      | cons median medians =>
          rcases hcerts with ⟨hlen, hcert⟩
          have htail_len : groups.length = medians.length := by
            simpa using hlen
          have hhead_cert : MedianFiveCertificate group median := by
            exact hcert (by simp)
          have htail_cert :
              MedianGroupCertificates groups medians := by
            refine ⟨htail_len, ?_⟩
            intro tailGroup tailMedian hmem
            exact hcert (by simp [hmem])
          have htail_bound :
              3 * leCount pivot medians ≤ leCount pivot (List.flatten groups) :=
            ih htail_cert
          by_cases hmedian : median ≤ pivot
          · have hhead_mono :
                leCount median group ≤ leCount pivot group :=
              leCount_mono_of_le hmedian group
            have hhead_bound : 3 ≤ leCount pivot group :=
              le_trans hhead_cert.2.2.1 hhead_mono
            simp [leCount_append, leCount_cons_of_le hmedian]
            omega
          · simp [leCount_append, leCount_cons_of_not_le hmedian]
            omega

/--
Every certified group whose median is at least {lit}`pivot` contributes at
least three original group elements at least {lit}`pivot`.
-/
theorem medianGroupCertificates_geCount_lower_bound {groups : List (List Nat)}
    {medians : List Nat} {pivot : Nat}
    (hcerts : MedianGroupCertificates groups medians) :
    3 * geCount pivot medians ≤ geCount pivot (List.flatten groups) := by
  induction groups generalizing medians with
  | nil =>
      rcases hcerts with ⟨hlen, _hcert⟩
      cases medians with
      | nil =>
          simp [geCount]
      | cons median medians =>
          simp at hlen
  | cons group groups ih =>
      cases medians with
      | nil =>
          rcases hcerts with ⟨hlen, _hcert⟩
          simp at hlen
      | cons median medians =>
          rcases hcerts with ⟨hlen, hcert⟩
          have htail_len : groups.length = medians.length := by
            simpa using hlen
          have hhead_cert : MedianFiveCertificate group median := by
            exact hcert (by simp)
          have htail_cert :
              MedianGroupCertificates groups medians := by
            refine ⟨htail_len, ?_⟩
            intro tailGroup tailMedian hmem
            exact hcert (by simp [hmem])
          have htail_bound :
              3 * geCount pivot medians ≤ geCount pivot (List.flatten groups) :=
            ih htail_cert
          by_cases hmedian : pivot ≤ median
          · have hhead_mono :
                geCount median group ≤ geCount pivot group :=
              geCount_anti_mono_of_le hmedian group
            have hhead_bound : 3 ≤ geCount pivot group :=
              le_trans hhead_cert.2.2.2 hhead_mono
            simp [geCount_append, geCount_cons_of_le hmedian]
            omega
          · simp [geCount_append, geCount_cons_of_not_le hmedian]
            omega

/--
If {lit}`pivot` has rank certificate {lit}`k` among the group medians, then the
original grouped values have at least {lit}`3 * (k + 1)` elements at most the
pivot and at least {lit}`3 * (medians.length - k)` elements at least the pivot.

This is the reusable counting core of the CLRS median-of-medians split-size
argument; converting it to the familiar {lit}`7n/10` recurrence bound is a
separate arithmetic packaging step.
-/
theorem medianGroupCertificates_selectPivot_split_counts
    {groups : List (List Nat)} {medians : List Nat} {pivot k : Nat}
    (hcerts : MedianGroupCertificates groups medians)
    (hrank : RankCertificate medians k pivot) :
    3 * (k + 1) ≤ leCount pivot (List.flatten groups) ∧
      3 * (medians.length - k) ≤ geCount pivot (List.flatten groups) := by
  constructor
  · have hmedian_count : k + 1 ≤ leCount pivot medians :=
      Nat.succ_le_of_lt hrank.2.2
    have hscale :
        3 * (k + 1) ≤ 3 * leCount pivot medians :=
      Nat.mul_le_mul_left 3 hmedian_count
    exact le_trans hscale (medianGroupCertificates_leCount_lower_bound hcerts)
  · have hge_medians : medians.length - k ≤ geCount pivot medians := by
      have hlt_bound : ltCount pivot medians ≤ k := hrank.2.1
      rw [geCount_eq_length_sub_ltCount]
      omega
    have hscale :
        3 * (medians.length - k) ≤ 3 * geCount pivot medians :=
      Nat.mul_le_mul_left 3 hge_medians
    exact le_trans hscale (medianGroupCertificates_geCount_lower_bound hcerts)

/--
Executable-grouping version of the median-of-medians split-count core.
-/
theorem fullGroupsOfFive_selectPivot_split_counts
    {xs medians : List Nat} {pivot k : Nat}
    (hmedians : medianOfFiveGroups? (fullGroupsOfFive xs) = some medians)
    (hrank : RankCertificate medians k pivot) :
    3 * (k + 1) ≤ leCount pivot (List.flatten (fullGroupsOfFive xs)) ∧
      3 * (medians.length - k) ≤
        geCount pivot (List.flatten (fullGroupsOfFive xs)) :=
  medianGroupCertificates_selectPivot_split_counts
    (fullGroupsOfFive_medianGroupCertificates hmedians) hrank

/--
When the pivot is selected as the median of the executable group medians, the
flattened full groups inherit the standard three-per-median split counts.
-/
theorem fullGroupsOfFive_medianPivot_split_counts
    {xs medians : List Nat} {pivot : Nat}
    (hmedians : medianOfFiveGroups? (fullGroupsOfFive xs) = some medians)
    (hpivot : selectByRank? (medians.length / 2) medians = some pivot) :
    3 * (medians.length / 2 + 1) ≤
        leCount pivot (List.flatten (fullGroupsOfFive xs)) ∧
      3 * (medians.length - medians.length / 2) ≤
        geCount pivot (List.flatten (fullGroupsOfFive xs)) := by
  exact fullGroupsOfFive_selectPivot_split_counts hmedians
    (selectByRank?_rankCorrect hpivot)

/--
Full-input version of the executable median-of-medians split-count theorem.

The counts first proved on the flattened full groups lift to the original
input because that flattening is a sublist of the input.  The final CLRS
{lit}`7n/10` statement still requires packaging these count lower bounds with
the group-count arithmetic above.
-/
theorem fullGroupsOfFive_medianPivot_fullInput_split_counts
    {xs medians : List Nat} {pivot : Nat}
    (hmedians : medianOfFiveGroups? (fullGroupsOfFive xs) = some medians)
    (hpivot : selectByRank? (medians.length / 2) medians = some pivot) :
    3 * (medians.length / 2 + 1) ≤ leCount pivot xs ∧
      3 * (medians.length - medians.length / 2) ≤ geCount pivot xs := by
  have hgrouped := fullGroupsOfFive_medianPivot_split_counts hmedians hpivot
  have hsub : (List.flatten (fullGroupsOfFive xs)).Sublist xs :=
    fullGroupsOfFive_flatten_sublist xs
  constructor
  · exact le_trans hgrouped.1 (leCount_le_of_sublist hsub)
  · exact le_trans hgrouped.2 (geCount_le_of_sublist hsub)

/-! ## Deterministic median-pivot instance -/

/--
Deterministic pivot rule that chooses the median of the current list according
to the specification selector.

This is a correctness-oriented pivot rule.  It deliberately separates the rank
proof from the harder CLRS median-of-medians running-time argument.
-/
def deterministicPivot? (xs : List Nat) : Option Nat :=
  selectByRank? (xs.length / 2) xs

/-- The deterministic median-pivot rule returns only members of its input. -/
theorem deterministicPivot?_mem :
    PivotMembership deterministicPivot? := by
  intro xs pivot hsel
  exact selectByRank?_mem (by simpa [deterministicPivot?] using hsel)

/-- Deterministic SELECT using the specification median as its pivot rule. -/
def deterministicSelect? (k : Nat) (xs : List Nat) : Option Nat :=
  selectWithPivot? deterministicPivot? k xs

/-- Rank-correctness theorem for deterministic median-pivot SELECT. -/
theorem deterministicSelect?_rankCorrect {k : Nat} {xs : List Nat} {x : Nat}
    (hsel : deterministicSelect? k xs = some x) :
    RankCertificate xs k x := by
  exact selectWithPivot?_rankCorrect deterministicPivot? deterministicPivot?_mem
    (by simpa [deterministicSelect?] using hsel)

/-- Membership projection for deterministic median-pivot SELECT. -/
theorem deterministicSelect?_mem {k : Nat} {xs : List Nat} {x : Nat}
    (hsel : deterministicSelect? k xs = some x) :
    x ∈ xs :=
  (deterministicSelect?_rankCorrect hsel).1

/-- Reader-facing correctness wrapper for deterministic median-pivot SELECT. -/
theorem deterministicSelect?_correct {k : Nat} {xs : List Nat} {x : Nat}
    (hsel : deterministicSelect? k xs = some x) :
    RankCertificate xs k x :=
  deterministicSelect?_rankCorrect hsel

end Chapter09
end CLRS

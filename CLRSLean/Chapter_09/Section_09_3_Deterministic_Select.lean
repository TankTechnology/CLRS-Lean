import CLRSLean.Chapter_09.Section_09_2_Select_By_Rank

/-!
# CLRS Section 9.3 - Selection in worst-case linear time

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
* Theorem {lit}`fullGroupsOfFive_medianPivot_partition_size_bound`: both
  strict recursive branches around the pivot satisfy the familiar
  {lit}`7n/10 + O(1)` CLRS size bound.
* Theorem {lit}`selectRecurrence_linear_step`: a pure {lean}`Nat`
  substitution step
  for closing a linear envelope from one one-fifth median subproblem, one
  {lit}`7n/10 + O(1)` strict branch, and local-work slack.
* Theorem {lit}`medianOfMediansPivot?_recursive_branch_size_bound`: the
  proved count bound specialized to the actual filtered recursive branch
  lists.
* Theorems {lit}`medianOfMediansPivot?_low_branch_linear_work_step` and
  {lit}`medianOfMediansPivot?_high_branch_linear_work_step`: executable
  branch wrappers that connect the median-of-medians pivot bound to the
  linear-work recurrence step.
* Theorem {lit}`deterministicSelect?_correct`: a deterministic median-pivot
  instance is rank correct.
* Theorem {lit}`selectRecurrence_linear_induction`: a threshold-parametric
  strong induction that lifts {lit}`selectRecurrence_linear_step` to the full
  recursion tree for any cost function satisfying the CLRS subproblem-size
  bounds.
* Theorem {lit}`medianOfMedians_linear_bound`: a concrete instantiation with
  the standard median-of-medians branch sizes {lit}`n/5` and {lit}`(7n+12)/10`,
  proving linear cost whenever the per-element work coefficient is bounded
  relative to the overall constant.
* Theorem {lit}`clrsSelectRecurrence_linear_bound`: a CLRS-facing name for the
  same linear-time SELECT recurrence closure.
* Definition {lit}`selectCostFuel` and wrapper {lit}`selectCost`: an executable
  {lit}`Nat`-valued cost counter that mirrors the {lit}`selectWithPivotFuel?`
  recursion, charging a parametric local-work term at each level.
* Theorems {lit}`selectCostFuel_linear_bound` and {lit}`selectCost_linear_bound`:
  the concrete cost is linear ({lit}`≤ 17 * a * n`) whenever the pivot rule
  satisfies the CLRS {lit}`10 * branch ≤ 7 * n + 12` bound and the local work is
  linear.
* Definition {lit}`medianOfMediansPartitionPathCost` and theorem
  {lit}`medianOfMediansPartitionPathCost_linear_bound`: the partition scans on
  the selector's outer recursion path obey the explicit linear bound
  {lit}`medianOfMediansPartitionPathCost k xs ≤ 17 * xs.length`.
* Theorems {lit}`recursiveMedianOfMediansPivot?_partition_size_bound`,
  {lit}`recursiveMedianOfMediansSelect?_isSome_of_lt`, and
  {lit}`recursiveMedianOfMediansSelect?_correct`: a recursively computed
  median-of-medians pivot retains the CLRS branch bound and yields a total,
  rank-correct selector.
* Definition {lit}`recursiveMedianOfMediansComparisonCost` and theorem
  {lit}`recursiveMedianOfMediansComparisonCost_linear_bound`: the complete
  comparison cost includes five-element grouping, recursive pivot selection,
  the current partition, and the selected strict branch, and is at most
  {lit}`100 * xs.length`.

## Implementation details

The randomized-selection analysis remains available outside the main sidebar:

* [Randomized SELECT Expected Time](CLRSLean/Chapter_09/Section_09_3_Deterministic_Select/Randomized_Select/)

Completion boundary: the section proves pure functional correctness and a
complete CLRS comparison-cost model.  In-place array partitioning and
hardware-level RAM accounting are lower-level refinements.
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

/-- A pivot rule is total when it returns a pivot for every nonempty input. -/
def PivotTotal (choosePivot? : List Nat → Option Nat) : Prop :=
  ∀ {xs : List Nat}, xs ≠ [] → ∃ pivot, choosePivot? xs = some pivot

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

/--
A membership-safe, total pivot rule makes the fuelled selector succeed for
every in-range rank.  This is the termination half of total correctness; the
returned value's rank certificate is supplied by
{lit}`selectWithPivotFuel?_rankCorrect`.
-/
theorem selectWithPivotFuel?_isSome_of_lt
    (choosePivot? : List Nat → Option Nat)
    (hpivot : PivotMembership choosePivot?)
    (htotal : PivotTotal choosePivot?) :
    ∀ (fuel k : Nat) (xs : List Nat), xs.length ≤ fuel → k < xs.length →
      ∃ x, selectWithPivotFuel? choosePivot? fuel k xs = some x := by
  intro fuel
  induction fuel with
  | zero =>
      intro k xs hlen hk
      omega
  | succ fuel ih =>
      intro k xs hlen hk
      have hxs : xs ≠ [] := by
        intro hnil
        subst xs
        simp at hk
      rcases htotal hxs with ⟨pivot, hchoose⟩
      have hpivot_mem : pivot ∈ xs := hpivot hchoose
      have hlow_len :
          (xs.filter fun y => decide (y < pivot)).length ≤ fuel := by
        have hstrict :
            (xs.filter fun y => decide (y < pivot)).length < xs.length :=
          filter_length_lt_of_mem_false (fun y => decide (y < pivot))
            hpivot_mem (by simp)
        exact Nat.lt_succ_iff.mp (Nat.lt_of_lt_of_le hstrict hlen)
      have hhigh_len :
          (xs.filter fun y => decide (pivot < y)).length ≤ fuel := by
        have hstrict :
            (xs.filter fun y => decide (pivot < y)).length < xs.length :=
          filter_length_lt_of_mem_false (fun y => decide (pivot < y))
            hpivot_mem (by simp)
        exact Nat.lt_succ_iff.mp (Nat.lt_of_lt_of_le hstrict hlen)
      by_cases hlo : k < ltCount pivot xs
      · have hk_low :
            k < (xs.filter fun y => decide (y < pivot)).length := by
          simpa [ltCount] using hlo
        rcases ih k (xs.filter fun y => decide (y < pivot)) hlow_len hk_low with
          ⟨x, hrun⟩
        exact ⟨x, by simp [selectWithPivotFuel?, hchoose, hlo, hrun]⟩
      · by_cases hmid : k < leCount pivot xs
        · exact ⟨pivot, by simp [selectWithPivotFuel?, hchoose, hlo, hmid]⟩
        · have hge : leCount pivot xs ≤ k := Nat.le_of_not_gt hmid
          have hk_high :
              k - leCount pivot xs <
                (xs.filter fun y => decide (pivot < y)).length := by
            change k - leCount pivot xs < gtCount pivot xs
            rw [gtCount_eq_length_sub_leCount]
            omega
          rcases ih (k - leCount pivot xs)
              (xs.filter fun y => decide (pivot < y)) hhigh_len hk_high with
            ⟨x, hrun⟩
          exact ⟨x, by simp [selectWithPivotFuel?, hchoose, hlo, hmid, hrun]⟩

/-- A total safe pivot rule makes public SELECT succeed on every valid rank. -/
theorem selectWithPivot?_isSome_of_lt
    (choosePivot? : List Nat → Option Nat)
    (hpivot : PivotMembership choosePivot?)
    (htotal : PivotTotal choosePivot?) {k : Nat} {xs : List Nat}
    (hk : k < xs.length) :
    ∃ x, selectWithPivot? choosePivot? k xs = some x := by
  exact selectWithPivotFuel?_isSome_of_lt choosePivot? hpivot htotal
    xs.length k xs (Nat.le_refl xs.length) hk

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

/-- The five-element median selector succeeds on any five-element input. -/
theorem medianOfFive?_isSome_of_length_eq_five {xs : List Nat}
    (hlen : xs.length = 5) :
    ∃ median, medianOfFive? xs = some median := by
  exact selectByRank?_isSome_of_lt (by simp [hlen])

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
Every median returned by the executable median-map comes from the flattened
input groups.
-/
theorem medianOfFiveGroups?_mem_flatten {groups : List (List Nat)}
    {medians : List Nat}
    (hsel : medianOfFiveGroups? groups = some medians) {median : Nat}
    (hmem : median ∈ medians) :
    median ∈ List.flatten groups := by
  induction groups generalizing medians with
  | nil =>
      simp [medianOfFiveGroups?] at hsel
      subst medians
      simp at hmem
  | cons group groups ih =>
      cases hhead : medianOfFive? group with
      | none =>
          simp [medianOfFiveGroups?, hhead] at hsel
      | some headMedian =>
          cases htail : medianOfFiveGroups? groups with
          | none =>
              simp [medianOfFiveGroups?, hhead, htail] at hsel
          | some tailMedians =>
              simp [medianOfFiveGroups?, hhead, htail] at hsel
              subst medians
              simp at hmem
              rcases hmem with hhead_mem | htail_mem
              · subst median
                have hrank : RankCertificate group 2 headMedian := by
                  exact selectByRank?_rankCorrect
                    (by simpa [medianOfFive?] using hhead)
                simp [hrank.1]
              · have htail_flat : median ∈ List.flatten groups :=
                  ih htail htail_mem
                simp [htail_flat]

/-- The executable median-map succeeds when every group has length five. -/
theorem medianOfFiveGroups?_isSome_of_all_lengths {groups : List (List Nat)}
    (hall : ∀ group ∈ groups, group.length = 5) :
    ∃ medians, medianOfFiveGroups? groups = some medians := by
  induction groups with
  | nil =>
      exact ⟨[], by simp [medianOfFiveGroups?]⟩
  | cons group groups ih =>
      rcases medianOfFive?_isSome_of_length_eq_five
          (hall group (by simp)) with
        ⟨median, hmedian⟩
      have htail_all : ∀ tailGroup ∈ groups, tailGroup.length = 5 := by
        intro tailGroup hmem
        exact hall tailGroup (by simp [hmem])
      rcases ih htail_all with ⟨medians, hmedians⟩
      exact ⟨median :: medians,
        by simp [medianOfFiveGroups?, hmedian, hmedians]⟩

/--
The executable full-grouping plus median-map automatically constructs the
abstract grouped certificate layer.
-/
theorem fullGroupsOfFive_medianGroupCertificates {xs medians : List Nat}
    (hsel : medianOfFiveGroups? (fullGroupsOfFive xs) = some medians) :
    MedianGroupCertificates (fullGroupsOfFive xs) medians :=
  medianOfFiveGroups?_certificates
    (fun _ hmem => fullGroupsOfFive_lengths hmem) hsel

/-- The executable median-map always succeeds on the executable full groups. -/
theorem fullGroupsOfFive_medianOfFiveGroups?_isSome (xs : List Nat) :
    ∃ medians, medianOfFiveGroups? (fullGroupsOfFive xs) = some medians :=
  medianOfFiveGroups?_isSome_of_all_lengths
    (fun _ hmem => fullGroupsOfFive_lengths hmem)

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
argument; the executable wrappers below convert it to the familiar
{lit}`7n/10 + O(1)` branch-size bound.
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
input because that flattening is a sublist of the input.  The partition-size
wrapper below packages these count lower bounds with the group-count arithmetic
above.
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

/--
The strict recursive branches around a median-of-medians pivot are bounded by
the input length minus the certified opposite-side mass.
-/
theorem fullGroupsOfFive_medianPivot_partition_lengths
    {xs medians : List Nat} {pivot : Nat}
    (hmedians : medianOfFiveGroups? (fullGroupsOfFive xs) = some medians)
    (hpivot : selectByRank? (medians.length / 2) medians = some pivot) :
    ltCount pivot xs ≤
        xs.length - 3 * (medians.length - medians.length / 2) ∧
      gtCount pivot xs ≤ xs.length - 3 * (medians.length / 2 + 1) := by
  have hsplit :=
    fullGroupsOfFive_medianPivot_fullInput_split_counts hmedians hpivot
  have hlt_len : ltCount pivot xs ≤ xs.length := by
    unfold ltCount
    exact List.length_filter_le (fun y => decide (y < pivot)) xs
  have hle_len : leCount pivot xs ≤ xs.length := by
    unfold leCount
    exact List.length_filter_le (fun y => decide (y ≤ pivot)) xs
  constructor
  · rw [geCount_eq_length_sub_ltCount] at hsplit
    omega
  · rw [gtCount_eq_length_sub_leCount]
    omega

/--
CLRS-style partition-size packaging for any rank-correct median of the
executable group medians.
-/
theorem fullGroupsOfFive_rankPivot_partition_size_bound
    {xs medians : List Nat} {pivot : Nat}
    (hmedians : medianOfFiveGroups? (fullGroupsOfFive xs) = some medians)
    (hrank : RankCertificate medians (medians.length / 2) pivot) :
    10 * ltCount pivot xs ≤ 7 * xs.length + 12 ∧
      10 * gtCount pivot xs ≤ 7 * xs.length + 12 := by
  have hgrouped := fullGroupsOfFive_selectPivot_split_counts hmedians hrank
  have hsub : (List.flatten (fullGroupsOfFive xs)).Sublist xs :=
    fullGroupsOfFive_flatten_sublist xs
  have hsplit :
      3 * (medians.length / 2 + 1) ≤ leCount pivot xs ∧
        3 * (medians.length - medians.length / 2) ≤ geCount pivot xs :=
    ⟨le_trans hgrouped.1 (leCount_le_of_sublist hsub),
      le_trans hgrouped.2 (geCount_le_of_sublist hsub)⟩
  have hlt_len : ltCount pivot xs ≤ xs.length := by
    unfold ltCount
    exact List.length_filter_le (fun y => decide (y < pivot)) xs
  have hle_len : leCount pivot xs ≤ xs.length := by
    unfold leCount
    exact List.length_filter_le (fun y => decide (y ≤ pivot)) xs
  have hparts :
      ltCount pivot xs ≤
          xs.length - 3 * (medians.length - medians.length / 2) ∧
        gtCount pivot xs ≤ xs.length - 3 * (medians.length / 2 + 1) := by
    constructor
    · rw [geCount_eq_length_sub_ltCount] at hsplit
      omega
    · rw [gtCount_eq_length_sub_leCount]
      omega
  have hcert := fullGroupsOfFive_medianGroupCertificates hmedians
  have hnear : xs.length ≤ 5 * medians.length + 4 := by
    have hbase := fullGroupsOfFive_length_near xs
    simpa [hcert.1] using hbase
  constructor
  · omega
  · omega

/--
CLRS-style partition-size packaging for the sorting-backed median wrapper.

Both strict recursive branches have size at most {lit}`7n/10 + O(1)`, stated
without division as {lit}`10 * branchSize ≤ 7 * n + 12`.
-/
theorem fullGroupsOfFive_medianPivot_partition_size_bound
    {xs medians : List Nat} {pivot : Nat}
    (hmedians : medianOfFiveGroups? (fullGroupsOfFive xs) = some medians)
    (hpivot : selectByRank? (medians.length / 2) medians = some pivot) :
    10 * ltCount pivot xs ≤ 7 * xs.length + 12 ∧
      10 * gtCount pivot xs ≤ 7 * xs.length + 12 :=
  fullGroupsOfFive_rankPivot_partition_size_bound hmedians
    (selectByRank?_rankCorrect hpivot)

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

/-- The specification-median pivot exists on every nonempty input. -/
theorem deterministicPivot?_isSome_of_ne_nil :
    PivotTotal deterministicPivot? := by
  intro xs hxs
  apply selectByRank?_isSome_of_lt
  have hpos : 0 < xs.length := by
    cases xs with
    | nil => contradiction
    | cons _ _ => simp
  omega

/-- A specification median leaves at most half of the input on either strict side. -/
theorem deterministicPivot?_half_partition_size_bound {xs : List Nat}
    {pivot : Nat} (hsel : deterministicPivot? xs = some pivot) :
    2 * ltCount pivot xs ≤ xs.length ∧
      2 * gtCount pivot xs ≤ xs.length := by
  have hrank : RankCertificate xs (xs.length / 2) pivot :=
    selectByRank?_rankCorrect (by simpa [deterministicPivot?] using hsel)
  have hlt : ltCount pivot xs ≤ xs.length / 2 := hrank.2.1
  have hle : xs.length / 2 < leCount pivot xs := hrank.2.2
  have hdiv : 2 * (xs.length / 2) ≤ xs.length := by omega
  constructor
  · exact le_trans (Nat.mul_le_mul_left 2 hlt) hdiv
  · rw [gtCount_eq_length_sub_leCount]
    omega

/-- The specification median also satisfies the looser CLRS `7n/10 + O(1)` bound. -/
theorem deterministicPivot?_partition_size_bound {xs : List Nat}
    {pivot : Nat} (hsel : deterministicPivot? xs = some pivot) :
    10 * ltCount pivot xs ≤ 7 * xs.length + 12 ∧
      10 * gtCount pivot xs ≤ 7 * xs.length + 12 := by
  have hhalf := deterministicPivot?_half_partition_size_bound hsel
  constructor <;> omega

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

/-! ## Median-of-medians pivot instance -/

/--
CLRS-style median-of-medians pivot rule.

For inputs with at least one full five-element group, this chooses the median
of the executable group medians.  For shorter inputs, it falls back to the
specification median pivot so that the pivot-parametric SELECT wrapper remains
usable on every nonempty input.
-/
def medianOfMediansPivot? (xs : List Nat) : Option Nat :=
  match medianOfFiveGroups? (fullGroupsOfFive xs) with
  | some (median :: medians) =>
      selectByRank? ((median :: medians).length / 2) (median :: medians)
  | _ => deterministicPivot? xs

/-- Every median-of-medians pivot returned by the wrapper belongs to the input. -/
theorem medianOfMediansPivot?_mem :
    PivotMembership medianOfMediansPivot? := by
  intro xs pivot hsel
  unfold medianOfMediansPivot? at hsel
  cases hgroups : medianOfFiveGroups? (fullGroupsOfFive xs) with
  | none =>
      exact deterministicPivot?_mem (by simpa [hgroups] using hsel)
  | some medians =>
      cases medians with
      | nil =>
          exact deterministicPivot?_mem (by simpa [hgroups] using hsel)
      | cons median medians =>
          have hpivot_medians :
              pivot ∈ median :: medians :=
            selectByRank?_mem (by simpa [hgroups] using hsel)
          have hpivot_flat :
              pivot ∈ List.flatten (fullGroupsOfFive xs) :=
            medianOfFiveGroups?_mem_flatten hgroups hpivot_medians
          exact (fullGroupsOfFive_flatten_sublist xs).subset hpivot_flat

/-- The median-of-medians pivot wrapper succeeds on every nonempty input. -/
theorem medianOfMediansPivot?_isSome_of_ne_nil :
    PivotTotal medianOfMediansPivot? := by
  intro xs hxs
  unfold medianOfMediansPivot?
  cases hgroups : medianOfFiveGroups? (fullGroupsOfFive xs) with
  | none =>
      rcases fullGroupsOfFive_medianOfFiveGroups?_isSome xs with
        ⟨medians, hmedians⟩
      rw [hgroups] at hmedians
      contradiction
  | some medians =>
      cases medians with
      | nil =>
          exact deterministicPivot?_isSome_of_ne_nil hxs
      | cons median medians =>
          apply selectByRank?_isSome_of_lt
          simp only [List.length_cons]
          omega

/--
Any pivot returned by the median-of-medians pivot rule satisfies the proved
CLRS branch-size bound.  The fallback branch can only occur when there are no
full five-element groups, hence the input has length at most four.
-/
theorem medianOfMediansPivot?_partition_size_bound {xs : List Nat}
    {pivot : Nat} (hsel : medianOfMediansPivot? xs = some pivot) :
    10 * ltCount pivot xs ≤ 7 * xs.length + 12 ∧
      10 * gtCount pivot xs ≤ 7 * xs.length + 12 := by
  unfold medianOfMediansPivot? at hsel
  cases hgroups : medianOfFiveGroups? (fullGroupsOfFive xs) with
  | none =>
      rcases fullGroupsOfFive_medianOfFiveGroups?_isSome xs with
        ⟨medians, hmedians⟩
      rw [hgroups] at hmedians
      contradiction
  | some medians =>
      cases medians with
      | nil =>
          have hcert :
              MedianGroupCertificates (fullGroupsOfFive xs) [] :=
            fullGroupsOfFive_medianGroupCertificates hgroups
          have hgroups_len : (fullGroupsOfFive xs).length = 0 := by
            simpa using hcert.1
          have hxs_small : xs.length ≤ 4 := by
            have hnear := fullGroupsOfFive_length_near xs
            rw [hgroups_len] at hnear
            omega
          have hlt_len : ltCount pivot xs ≤ xs.length := by
            unfold ltCount
            exact List.length_filter_le (fun y => decide (y < pivot)) xs
          have hgt_len : gtCount pivot xs ≤ xs.length := by
            unfold gtCount
            exact List.length_filter_le (fun y => decide (pivot < y)) xs
          constructor <;> omega
      | cons median medians =>
          exact fullGroupsOfFive_medianPivot_partition_size_bound
            (xs := xs) (medians := median :: medians) (pivot := pivot)
            hgroups (by simpa [hgroups] using hsel)

/-! ## Recursive median-of-medians pivot -/

/--
Fuelled recursive median-of-medians pivot construction.

For a nonempty list of full-group medians, the pivot is selected by the same
pivot-parametric selector using the previous fuel level as its pivot rule.
Thus the group-median subproblem is solved recursively instead of by sorting.
The specification median is used only when the fuel is exhausted or there is
no full group (the input then has fewer than five elements).
-/
def recursiveMedianOfMediansPivotFuel? : Nat → List Nat → Option Nat
  | 0, xs => deterministicPivot? xs
  | fuel + 1, xs =>
      if xs.length < 50 then
        deterministicPivot? xs
      else
        match medianOfFiveGroups? (fullGroupsOfFive xs) with
        | some (median :: medians) =>
            selectWithPivot? (recursiveMedianOfMediansPivotFuel? fuel)
              ((median :: medians).length / 2) (median :: medians)
        | _ => deterministicPivot? xs

/-- Every fuel level of the recursive pivot construction returns an input member. -/
theorem recursiveMedianOfMediansPivotFuel?_mem (fuel : Nat) :
    PivotMembership (recursiveMedianOfMediansPivotFuel? fuel) := by
  induction fuel with
  | zero =>
      intro xs pivot hsel
      exact deterministicPivot?_mem
        (by simpa [recursiveMedianOfMediansPivotFuel?] using hsel)
  | succ fuel ih =>
      intro xs pivot hsel
      simp only [recursiveMedianOfMediansPivotFuel?] at hsel
      by_cases hsmall : xs.length < 50
      · exact deterministicPivot?_mem (by simpa [hsmall] using hsel)
      · simp only [hsmall, ↓reduceIte] at hsel
        cases hgroups : medianOfFiveGroups? (fullGroupsOfFive xs) with
        | none =>
            exact deterministicPivot?_mem (by simpa [hgroups] using hsel)
        | some medians =>
            cases medians with
            | nil =>
                exact deterministicPivot?_mem (by simpa [hgroups] using hsel)
            | cons median medians =>
                have hpivot_medians : pivot ∈ median :: medians :=
                  selectWithPivot?_mem
                    (recursiveMedianOfMediansPivotFuel? fuel) ih
                    (by simpa [hgroups] using hsel)
                have hpivot_flat : pivot ∈ List.flatten (fullGroupsOfFive xs) :=
                  medianOfFiveGroups?_mem_flatten hgroups hpivot_medians
                exact (fullGroupsOfFive_flatten_sublist xs).subset hpivot_flat

/-- Every fuel level of the recursive pivot construction succeeds on nonempty input. -/
theorem recursiveMedianOfMediansPivotFuel?_isSome_of_ne_nil (fuel : Nat) :
    PivotTotal (recursiveMedianOfMediansPivotFuel? fuel) := by
  induction fuel with
  | zero =>
      intro xs hxs
      simpa [recursiveMedianOfMediansPivotFuel?] using
        (deterministicPivot?_isSome_of_ne_nil hxs)
  | succ fuel ih =>
      intro xs hxs
      simp only [recursiveMedianOfMediansPivotFuel?]
      by_cases hsmall : xs.length < 50
      · simpa [hsmall] using deterministicPivot?_isSome_of_ne_nil hxs
      · simp only [hsmall, ↓reduceIte]
        cases hgroups : medianOfFiveGroups? (fullGroupsOfFive xs) with
        | none =>
            rcases fullGroupsOfFive_medianOfFiveGroups?_isSome xs with
              ⟨medians, hmedians⟩
            rw [hgroups] at hmedians
            contradiction
        | some medians =>
            cases medians with
            | nil =>
                exact deterministicPivot?_isSome_of_ne_nil hxs
            | cons median medians =>
                apply selectWithPivot?_isSome_of_lt
                  (recursiveMedianOfMediansPivotFuel? fuel)
                  (recursiveMedianOfMediansPivotFuel?_mem fuel) ih
                simp only [List.length_cons]
                omega

/-- Public recursive pivot with enough fuel for every nested median subproblem. -/
def recursiveMedianOfMediansPivot? (xs : List Nat) : Option Nat :=
  recursiveMedianOfMediansPivotFuel? xs.length xs

/-- The public recursive median-of-medians pivot always belongs to its input. -/
theorem recursiveMedianOfMediansPivot?_mem :
    PivotMembership recursiveMedianOfMediansPivot? := by
  intro xs pivot hsel
  exact recursiveMedianOfMediansPivotFuel?_mem xs.length
    (by simpa [recursiveMedianOfMediansPivot?] using hsel)

/-- The public recursive median-of-medians pivot succeeds on nonempty input. -/
theorem recursiveMedianOfMediansPivot?_isSome_of_ne_nil :
    PivotTotal recursiveMedianOfMediansPivot? := by
  intro xs hxs
  simpa [recursiveMedianOfMediansPivot?] using
    (recursiveMedianOfMediansPivotFuel?_isSome_of_ne_nil xs.length hxs)

/-- Every fuel level of the recursive pivot satisfies the CLRS branch bound. -/
theorem recursiveMedianOfMediansPivotFuel?_partition_size_bound (fuel : Nat)
    {xs : List Nat} {pivot : Nat}
    (hsel : recursiveMedianOfMediansPivotFuel? fuel xs = some pivot) :
    10 * ltCount pivot xs ≤ 7 * xs.length + 12 ∧
      10 * gtCount pivot xs ≤ 7 * xs.length + 12 := by
  induction fuel with
  | zero =>
      exact deterministicPivot?_partition_size_bound
        (by simpa [recursiveMedianOfMediansPivotFuel?] using hsel)
  | succ fuel ih =>
      simp only [recursiveMedianOfMediansPivotFuel?] at hsel
      by_cases hsmall : xs.length < 50
      · exact deterministicPivot?_partition_size_bound
          (by simpa [hsmall] using hsel)
      · simp only [hsmall, ↓reduceIte] at hsel
        cases hgroups : medianOfFiveGroups? (fullGroupsOfFive xs) with
        | none =>
            exact deterministicPivot?_partition_size_bound
              (by simpa [hgroups] using hsel)
        | some medians =>
            cases medians with
            | nil =>
                exact deterministicPivot?_partition_size_bound
                  (by simpa [hgroups] using hsel)
            | cons median medians =>
                have hrank :
                    RankCertificate (median :: medians)
                      ((median :: medians).length / 2) pivot :=
                  selectWithPivot?_rankCorrect
                    (recursiveMedianOfMediansPivotFuel? fuel)
                    (recursiveMedianOfMediansPivotFuel?_mem fuel)
                    (by simpa [hgroups] using hsel)
                exact fullGroupsOfFive_rankPivot_partition_size_bound
                  hgroups hrank

/-- The public recursively computed pivot satisfies the CLRS strict-branch bound. -/
theorem recursiveMedianOfMediansPivot?_partition_size_bound {xs : List Nat}
    {pivot : Nat} (hsel : recursiveMedianOfMediansPivot? xs = some pivot) :
    10 * ltCount pivot xs ≤ 7 * xs.length + 12 ∧
      10 * gtCount pivot xs ≤ 7 * xs.length + 12 := by
  exact recursiveMedianOfMediansPivotFuel?_partition_size_bound xs.length
    (by simpa [recursiveMedianOfMediansPivot?] using hsel)

/-! ## Recurrence-size wrappers -/

/--
Pure arithmetic substitution step for the median-of-medians recurrence.

If the median subproblem has size at most one fifth of the input, the selected
strict branch satisfies the proved {lit}`7n/10 + O(1)` bound, and the local
work plus the additive split slack fits in the remaining tenth, then the two
recursive calls plus local work are bounded by the same linear envelope.
-/
theorem selectRecurrence_linear_step
    {n medianBranch strictBranch localWork C : Nat}
    (hmedian : 5 * medianBranch ≤ n)
    (hbranch : 10 * strictBranch ≤ 7 * n + 12)
    (hlocal : 10 * localWork + 12 * C ≤ C * n) :
    C * medianBranch + C * strictBranch + localWork ≤ C * n := by
  have hmedian_scaled : C * (5 * medianBranch) ≤ C * n :=
    Nat.mul_le_mul_left C hmedian
  have hmedian_part : 10 * (C * medianBranch) ≤ 2 * (C * n) := by
    nlinarith
  have hbranch_scaled : C * (10 * strictBranch) ≤ C * (7 * n + 12) :=
    Nat.mul_le_mul_left C hbranch
  have hbranch_part : 10 * (C * strictBranch) ≤ 7 * (C * n) + 12 * C := by
    nlinarith
  have htotal :
      10 * (C * medianBranch + C * strictBranch + localWork) ≤
        10 * (C * n) := by
    nlinarith
  exact Nat.le_of_mul_le_mul_left htotal (by decide : 0 < 10)

/-- The actual strict recursive SELECT branch lists have the CLRS bound. -/
theorem medianOfMediansPivot?_recursive_branch_size_bound {xs : List Nat}
    {pivot : Nat} (hsel : medianOfMediansPivot? xs = some pivot) :
    10 * (xs.filter fun y => decide (y < pivot)).length ≤
        7 * xs.length + 12 ∧
      10 * (xs.filter fun y => decide (pivot < y)).length ≤
        7 * xs.length + 12 := by
  simpa [ltCount, gtCount] using
    (medianOfMediansPivot?_partition_size_bound hsel)

/--
Linear-work recurrence step for the low recursive branch of
median-of-medians SELECT.
-/
theorem medianOfMediansPivot?_low_branch_linear_work_step
    {xs medians : List Nat} {pivot localWork C : Nat}
    (hmedians : medianOfFiveGroups? (fullGroupsOfFive xs) = some medians)
    (hsel : medianOfMediansPivot? xs = some pivot)
    (hlocal : 10 * localWork + 12 * C ≤ C * xs.length) :
    C * medians.length +
        C * (xs.filter fun y => decide (y < pivot)).length + localWork ≤
      C * xs.length := by
  have hmedian_size : 5 * medians.length ≤ xs.length := by
    have hgroups_size := fullGroupsOfFive_length_mul_five_le xs
    have hcert := fullGroupsOfFive_medianGroupCertificates hmedians
    simpa [hcert.1] using hgroups_size
  exact selectRecurrence_linear_step hmedian_size
    (medianOfMediansPivot?_recursive_branch_size_bound hsel).1 hlocal

/--
Linear-work recurrence step for the high recursive branch of
median-of-medians SELECT.
-/
theorem medianOfMediansPivot?_high_branch_linear_work_step
    {xs medians : List Nat} {pivot localWork C : Nat}
    (hmedians : medianOfFiveGroups? (fullGroupsOfFive xs) = some medians)
    (hsel : medianOfMediansPivot? xs = some pivot)
    (hlocal : 10 * localWork + 12 * C ≤ C * xs.length) :
    C * medians.length +
        C * (xs.filter fun y => decide (pivot < y)).length + localWork ≤
      C * xs.length := by
  have hmedian_size : 5 * medians.length ≤ xs.length := by
    have hgroups_size := fullGroupsOfFive_length_mul_five_le xs
    have hcert := fullGroupsOfFive_medianGroupCertificates hmedians
    simpa [hcert.1] using hgroups_size
  exact selectRecurrence_linear_step hmedian_size
    (medianOfMediansPivot?_recursive_branch_size_bound hsel).2 hlocal

/-! ## Full recurrence induction -/

/--
**Recurrence induction for median-of-medians cost.**

Given a cost function {lit}`T : Nat → Nat`, subproblem-size functions {lit}`g` (median
subproblem) and {lit}`h` (strict recursive branch), a local-work function {lit}`f`, and
a base threshold {lit}`t`, this theorem proves {lit}`T n ≤ C * n` for all {lit}`n` whenever
the following hold for all {lit}`n ≥ t`:

1. The subproblem sizes satisfy the CLRS partition bounds:
   {lit}`5 * g n ≤ n` and {lit}`10 * h n ≤ 7 * n + 12`;
2. The local work is small enough:
   {lit}`10 * f n + 12 * C ≤ C * n`;
3. {lit}`T` satisfies the one-level recurrence
   {lit}`T n ≤ T (g n) + T (h n) + f n`;
4. Base cases {lit}`n < t` respect the linear bound: {lit}`T n ≤ C * n`.

The proof chains {lit}`selectRecurrence_linear_step` through strong induction
to lift the single-level substitution to the full recursion tree.

Corresponds to the substitution-method closure in CLRS Section 9.3.
-/
theorem selectRecurrence_linear_induction
    {C t : Nat}
    (ht_bound : 5 ≤ t)
    (f g h : Nat → Nat)
    (hmedian_size : ∀ n, t ≤ n → 5 * g n ≤ n)
    (hstrict_size : ∀ n, t ≤ n → 10 * h n ≤ 7 * n + 12)
    (hlocal_work : ∀ n, t ≤ n → 10 * f n + 12 * C ≤ C * n)
    (T : Nat → Nat)
    (hT_step : ∀ n, t ≤ n → T n ≤ T (g n) + T (h n) + f n)
    (hT_base : ∀ n, n < t → T n ≤ C * n) :
    ∀ n, T n ≤ C * n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hnt : n < t
    · exact hT_base n hnt
    · have hnt' : t ≤ n := Nat.le_of_not_gt hnt
      have hpos_n : 0 < n := by omega
      have hg_lt : g n < n := by
        have hg_bound := hmedian_size n hnt'
        by_contra! hge
        -- hge : n ≤ g n, so 5*n ≤ 5*g n ≤ n, impossible for n > 0
        have hmul : 5 * n ≤ 5 * g n := Nat.mul_le_mul_left 5 hge
        have hchain : 5 * n ≤ n := le_trans hmul hg_bound
        omega
      have hh_lt : h n < n := by
        have hh_bound := hstrict_size n hnt'
        by_contra! hge
        -- hge : n ≤ h n, so 10*n ≤ 10*h n ≤ 7*n+12, impossible for n ≥ t > 0
        have hmul : 10 * n ≤ 10 * h n := Nat.mul_le_mul_left 10 hge
        have hchain : 10 * n ≤ 7 * n + 12 := le_trans hmul hh_bound
        omega
      have hTg : T (g n) ≤ C * (g n) := ih (g n) hg_lt
      have hTh : T (h n) ≤ C * (h n) := ih (h n) hh_lt
      have hsubst : C * (g n) + C * (h n) + f n ≤ C * n :=
        selectRecurrence_linear_step (hmedian_size n hnt')
          (hstrict_size n hnt') (hlocal_work n hnt')
      have hstep := hT_step n hnt'
      have hsum : T (g n) + T (h n) ≤ C * (g n) + C * (h n) :=
        add_le_add hTg hTh
      have htotal : T (g n) + T (h n) + f n ≤ C * (g n) + C * (h n) + f n :=
        add_le_add hsum (le_refl (f n))
      calc
        T n ≤ T (g n) + T (h n) + f n := hstep
        _ ≤ C * (g n) + C * (h n) + f n := htotal
        _ ≤ C * n := hsubst

/--
**Concrete linear bound for the median-of-medians recurrence.**

Corollary of {lit}`selectRecurrence_linear_induction` with the standard CLRS
subproblem sizes: the median subproblem is {lit}`⌊n/5⌋`, the strict branch is
{lit}`⌊(7n+12)/10⌋`, and the local work is bounded by {lit}`a*n` where {lit}`20*a ≤ C`
(so that the one-level algebraic slack closes).

The base threshold is 50, which is large enough to absorb the additive
constants from the partition bound.
-/
theorem medianOfMedians_linear_bound
    {C a : Nat}
    (hCpos : 0 < C)
    (ha_bound : 20 * a ≤ C)
    (T : Nat → Nat)
    (hT_step : ∀ n, 50 ≤ n →
      T n ≤ T (n / 5) + T ((7 * n + 12) / 10) + a * n)
    (hT_base : ∀ n, n < 50 → T n ≤ C * n) :
    ∀ n, T n ≤ C * n := by
  set g : Nat → Nat := fun n => n / 5
  set h : Nat → Nat := fun n => (7 * n + 12) / 10
  set f : Nat → Nat := fun n => a * n
  have hmedian_size : ∀ n, 50 ≤ n → 5 * g n ≤ n := by
    intro n hn
    unfold g
    exact Nat.mul_div_le n 5
  have hstrict_size : ∀ n, 50 ≤ n → 10 * h n ≤ 7 * n + 12 := by
    intro n hn
    unfold h
    exact Nat.mul_div_le (7 * n + 12) 10
  have hlocal_work : ∀ n, 50 ≤ n → 10 * f n + 12 * C ≤ C * n := by
    intro n hn50
    unfold f
    -- Goal: 10*(a*n) + 12*C ≤ C*n
    -- Scale by 2 to avoid division, then use Nat.le_of_mul_le_mul_left
    have hscale : (10 * (a * n) + 12 * C) * 2 ≤ (C * n) * 2 := by
      calc
        (10 * (a * n) + 12 * C) * 2 = 20 * a * n + 24 * C := by ring
        _ ≤ C * n + 24 * C := by
          have h : 20 * a ≤ C := ha_bound
          nlinarith
        _ ≤ C * n + C * n := by
          have : 24 ≤ n := by omega
          nlinarith
        _ = (C * n) * 2 := by ring
    -- hscale : (stuff)*2 ≤ (other)*2, use right-multiplied form
    have hgoal : 10 * (a * n) + 12 * C ≤ C * n := by
      apply Nat.le_of_mul_le_mul_right (c := 2) ?_ (by omega)
      -- hscale has the terms commuted relative to what the lemma expects
      simpa [mul_comm, mul_left_comm, mul_assoc] using hscale
    exact hgoal
  have hT_step_wrapped : ∀ n, 50 ≤ n → T n ≤ T (g n) + T (h n) + f n := by
    intro n hn50
    unfold g h f
    exact hT_step n hn50
  exact selectRecurrence_linear_induction (by omega) f g h
    hmedian_size hstrict_size hlocal_work T hT_step_wrapped hT_base

/--
CLRS-facing linear-time SELECT recurrence theorem.

If a cost function satisfies the standard median-of-medians recurrence with
subproblem sizes {lit}`⌊n/5⌋` and {lit}`⌊(7n+12)/10⌋`, and if the base cases
respect the same linear envelope, then the cost is globally linear.

This theorem is intentionally still an abstract recurrence wrapper: connecting
the executable {lit}`medianOfMediansSelect?` implementation to a concrete cost
function remains a separate refinement target.
-/
theorem clrsSelectRecurrence_linear_bound
    {C a : Nat}
    (hCpos : 0 < C)
    (ha_bound : 20 * a ≤ C)
    (T : Nat → Nat)
    (hT_step : ∀ n, 50 ≤ n →
      T n ≤ T (n / 5) + T ((7 * n + 12) / 10) + a * n)
    (hT_base : ∀ n, n < 50 → T n ≤ C * n) :
    ∀ n, T n ≤ C * n :=
  medianOfMedians_linear_bound hCpos ha_bound T hT_step hT_base

/-- SELECT specialized to the executable median-of-medians pivot rule. -/
def medianOfMediansSelect? (k : Nat) (xs : List Nat) : Option Nat :=
  selectWithPivot? medianOfMediansPivot? k xs

/-- Median-of-medians SELECT succeeds whenever the requested rank is valid. -/
theorem medianOfMediansSelect?_isSome_of_lt {k : Nat} {xs : List Nat}
    (hk : k < xs.length) :
    ∃ x, medianOfMediansSelect? k xs = some x := by
  simpa [medianOfMediansSelect?] using
    (selectWithPivot?_isSome_of_lt medianOfMediansPivot?
      medianOfMediansPivot?_mem medianOfMediansPivot?_isSome_of_ne_nil hk)

/-- Rank-correctness theorem for median-of-medians SELECT. -/
theorem medianOfMediansSelect?_rankCorrect {k : Nat} {xs : List Nat}
    {x : Nat} (hsel : medianOfMediansSelect? k xs = some x) :
    RankCertificate xs k x := by
  exact selectWithPivot?_rankCorrect medianOfMediansPivot?
    medianOfMediansPivot?_mem
    (by simpa [medianOfMediansSelect?] using hsel)

/-- Membership projection for median-of-medians SELECT. -/
theorem medianOfMediansSelect?_mem {k : Nat} {xs : List Nat} {x : Nat}
    (hsel : medianOfMediansSelect? k xs = some x) :
    x ∈ xs :=
  (medianOfMediansSelect?_rankCorrect hsel).1

/-- Reader-facing correctness wrapper for median-of-medians SELECT. -/
theorem medianOfMediansSelect?_correct {k : Nat} {xs : List Nat} {x : Nat}
    (hsel : medianOfMediansSelect? k xs = some x) :
    RankCertificate xs k x :=
  medianOfMediansSelect?_rankCorrect hsel

/-! ## Recursive median-of-medians selector -/

/--
Executable SELECT whose pivot construction recursively selects the median of
the full-group medians.
-/
def recursiveMedianOfMediansSelect? (k : Nat) (xs : List Nat) : Option Nat :=
  selectWithPivot? recursiveMedianOfMediansPivot? k xs

/-- The recursive median-of-medians selector succeeds for every valid rank. -/
theorem recursiveMedianOfMediansSelect?_isSome_of_lt {k : Nat} {xs : List Nat}
    (hk : k < xs.length) :
    ∃ x, recursiveMedianOfMediansSelect? k xs = some x := by
  simpa [recursiveMedianOfMediansSelect?] using
    (selectWithPivot?_isSome_of_lt recursiveMedianOfMediansPivot?
      recursiveMedianOfMediansPivot?_mem
      recursiveMedianOfMediansPivot?_isSome_of_ne_nil hk)

/-- Successful recursive median-of-medians SELECT runs are rank-correct. -/
theorem recursiveMedianOfMediansSelect?_correct {k : Nat} {xs : List Nat}
    {x : Nat} (hsel : recursiveMedianOfMediansSelect? k xs = some x) :
    RankCertificate xs k x := by
  exact selectWithPivot?_correct recursiveMedianOfMediansPivot?
    recursiveMedianOfMediansPivot?_mem
    (by simpa [recursiveMedianOfMediansSelect?] using hsel)

/-! ## Concrete executable cost semantics

This section supplies an **executable
{lit}`Nat`-valued cost function** for the pivot-parametric selector and a proved
explicit bound {lit}`cost n ≤ 17 * n` for its outer partition path.

The cost counter {lit}`selectCostFuel` mirrors the recursion of
{lit}`selectWithPivotFuel?` exactly: at every recursion level it charges a local
work term {lit}`stepCost xs` (for the deterministic instance this is one
comparison per element, i.e. the linear partition scan) and then recurses on the
single strict branch that {lit}`selectWithPivotFuel?` actually visits.  Because
{lit}`SELECT` follows only one partition side, the cost is the sum of the local work
along one root-to-leaf path of the recursion tree.

The explicit constant {lit}`17` comes from the CLRS branch bound
{lit}`10 * branch ≤ 7 * n + 12`: for the substitution guess {lit}`cost ≤ 17 a n`
the one-level slack {lit}`a n + 17 a b ≤ 17 a n` reduces to the pure {lit}`Nat` fact
{lit}`17 b ≤ 16 n`, which {tactic}`omega` derives from
{lit}`10 * b ≤ 7 * n + 12` together with the strict-sublist fact {lit}`b < n`.

The pivot-selection work is excluded from this legacy diagnostic counter.  The
complete composed counter and its linear theorem are
{lit}`recursiveMedianOfMediansComparisonCost` and
{lit}`recursiveMedianOfMediansComparisonCost_linear_bound` below.
-/

/--
Pure {lit}`Nat` substitution slack for the concrete cost recurrence.

For the substitution guess {lit}`cost ≤ 17 a n`, one recursion level with local
work at most {lit}`a n` and strict branch of size {lit}`b` satisfying the CLRS
bound {lit}`10 b ≤ 7 n + 12` and {lit}`b < n` fits under the same envelope:
{lit}`a n + 17 a b ≤ 17 a n`.  The core is the pivot-free arithmetic fact
{lit}`17 b ≤ 16 n`, discharged by {tactic}`omega`.
-/
theorem selectCost_linear_step {a n b : Nat}
    (hb : 10 * b ≤ 7 * n + 12) (hlt : b < n) :
    a * n + 17 * a * b ≤ 17 * a * n := by
  have h : n + 17 * b ≤ 17 * n := by omega
  calc a * n + 17 * a * b = a * (n + 17 * b) := by ring
    _ ≤ a * (17 * n) := Nat.mul_le_mul (le_refl a) h
    _ = 17 * a * n := by ring

/--
Fuelled cost counter for the pivot-parametric selector.

The recursion is byte-for-byte parallel to {lit}`selectWithPivotFuel?`: it uses
the same pivot rule, the same three-way branch conditions, and recurses on the
same strict sublist.  At each visited level it charges {lit}`stepCost xs` local
work; the pivot-block branch stops (charging only the local work) and the two
strict branches recurse with one unit of fuel removed.
-/
def selectCostFuel (choosePivot? : List Nat → Option Nat) (stepCost : List Nat → Nat) :
    Nat → Nat → List Nat → Nat
  | 0, _, _ => 0
  | fuel + 1, k, xs =>
      match choosePivot? xs with
      | none => 0
      | some pivot =>
          stepCost xs +
            (if k < ltCount pivot xs then
              selectCostFuel choosePivot? stepCost fuel k
                (xs.filter fun y => decide (y < pivot))
            else if k < leCount pivot xs then
              0
            else
              selectCostFuel choosePivot? stepCost fuel (k - leCount pivot xs)
                (xs.filter fun y => decide (pivot < y)))

/--
**Linear bound for the fuelled cost counter.**

If the pivot rule is membership-safe, every chosen pivot satisfies the CLRS
strict-branch bound {lit}`10 * branch ≤ 7 * n + 12`, and the local work is
linear ({lit}`stepCost ys ≤ a * ys.length`), then the accumulated cost along the
recursion path is linear: {lit}`selectCostFuel … ≤ 17 * a * xs.length`.

The proof is strong induction on the fuel, closing each level with
{lit}`selectCost_linear_step`.
-/
theorem selectCostFuel_linear_bound
    (choosePivot? : List Nat → Option Nat) (stepCost : List Nat → Nat) {a : Nat}
    (hpivot : PivotMembership choosePivot?)
    (hbound : ∀ (ys : List Nat) (pivot : Nat), choosePivot? ys = some pivot →
      10 * ltCount pivot ys ≤ 7 * ys.length + 12 ∧
      10 * gtCount pivot ys ≤ 7 * ys.length + 12)
    (hstep : ∀ ys : List Nat, stepCost ys ≤ a * ys.length) :
    ∀ (fuel k : Nat) (xs : List Nat), xs.length ≤ fuel →
      selectCostFuel choosePivot? stepCost fuel k xs ≤ 17 * a * xs.length := by
  intro fuel
  induction fuel with
  | zero =>
      intro k xs _hlen
      simp [selectCostFuel]
  | succ fuel ih =>
      intro k xs hlen
      cases hchoose : choosePivot? xs with
      | none =>
          simp [selectCostFuel, hchoose]
      | some pivot =>
          have hmem : pivot ∈ xs := hpivot hchoose
          have hbnd := hbound xs pivot hchoose
          by_cases hlo : k < ltCount pivot xs
          · have hunfold :
                selectCostFuel choosePivot? stepCost (fuel + 1) k xs =
                  stepCost xs +
                    selectCostFuel choosePivot? stepCost fuel k
                      (xs.filter fun y => decide (y < pivot)) := by
              simp [selectCostFuel, hchoose, hlo]
            have hbranch_len_lt :
                (xs.filter fun y => decide (y < pivot)).length < xs.length :=
              filter_length_lt_of_mem_false (fun y => decide (y < pivot))
                hmem (by simp)
            have hbranch_le_fuel :
                (xs.filter fun y => decide (y < pivot)).length ≤ fuel :=
              Nat.lt_succ_iff.mp (Nat.lt_of_lt_of_le hbranch_len_lt hlen)
            have hih := ih k (xs.filter fun y => decide (y < pivot)) hbranch_le_fuel
            have hkey :
                a * xs.length +
                    17 * a * (xs.filter fun y => decide (y < pivot)).length ≤
                  17 * a * xs.length :=
              selectCost_linear_step hbnd.1 hbranch_len_lt
            rw [hunfold]
            exact le_trans (Nat.add_le_add (hstep xs) hih) hkey
          · by_cases hmid : k < leCount pivot xs
            · have hunfold :
                  selectCostFuel choosePivot? stepCost (fuel + 1) k xs =
                    stepCost xs := by
                simp [selectCostFuel, hchoose, hlo, hmid]
              have hmid_bound : a * xs.length ≤ 17 * a * xs.length := by
                have h17 : a ≤ 17 * a := by omega
                exact Nat.mul_le_mul h17 (le_refl xs.length)
              rw [hunfold]
              exact le_trans (hstep xs) hmid_bound
            · have hunfold :
                  selectCostFuel choosePivot? stepCost (fuel + 1) k xs =
                    stepCost xs +
                      selectCostFuel choosePivot? stepCost fuel
                        (k - leCount pivot xs)
                        (xs.filter fun y => decide (pivot < y)) := by
                simp [selectCostFuel, hchoose, hlo, hmid]
              have hbranch_len_lt :
                  (xs.filter fun y => decide (pivot < y)).length < xs.length :=
                filter_length_lt_of_mem_false (fun y => decide (pivot < y))
                  hmem (by simp)
              have hbranch_le_fuel :
                  (xs.filter fun y => decide (pivot < y)).length ≤ fuel :=
                Nat.lt_succ_iff.mp (Nat.lt_of_lt_of_le hbranch_len_lt hlen)
              have hih := ih (k - leCount pivot xs)
                (xs.filter fun y => decide (pivot < y)) hbranch_le_fuel
              have hkey :
                  a * xs.length +
                      17 * a * (xs.filter fun y => decide (pivot < y)).length ≤
                    17 * a * xs.length :=
                selectCost_linear_step hbnd.2 hbranch_len_lt
              rw [hunfold]
              exact le_trans (Nat.add_le_add (hstep xs) hih) hkey

/--
Public cost wrapper: run the fuelled cost counter with one unit of fuel per
input element, matching the {lit}`selectWithPivot?` wrapper.
-/
def selectCost (choosePivot? : List Nat → Option Nat) (stepCost : List Nat → Nat)
    (k : Nat) (xs : List Nat) : Nat :=
  selectCostFuel choosePivot? stepCost xs.length k xs

/--
Linear bound for the public cost wrapper, obtained from
{lit}`selectCostFuel_linear_bound` with the canonical fuel {lit}`xs.length`.
-/
theorem selectCost_linear_bound
    (choosePivot? : List Nat → Option Nat) (stepCost : List Nat → Nat) {a : Nat}
    (hpivot : PivotMembership choosePivot?)
    (hbound : ∀ (ys : List Nat) (pivot : Nat), choosePivot? ys = some pivot →
      10 * ltCount pivot ys ≤ 7 * ys.length + 12 ∧
      10 * gtCount pivot ys ≤ 7 * ys.length + 12)
    (hstep : ∀ ys : List Nat, stepCost ys ≤ a * ys.length)
    (k : Nat) (xs : List Nat) :
    selectCost choosePivot? stepCost k xs ≤ 17 * a * xs.length :=
  selectCostFuel_linear_bound choosePivot? stepCost hpivot hbound hstep
    xs.length k xs (Nat.le_refl xs.length)

/-! ## End-to-end recursive median-of-medians comparison cost -/

/--
Comparison charge for constructing a recursive median-of-medians pivot.

Below the fixed CLRS base threshold, `n²` comparisons cover a simple local
comparison sort.  Above the threshold, {lit}`2n` covers forming and selecting the
medians of the full five-element groups (at most ten comparisons per group),
and the remaining term is the complete recursive SELECT cost on the list of
group medians.  Its step charge contains both the partition scan and the next
nested pivot construction, so no recursive pivot work is omitted.
-/
def recursiveMedianOfMediansPivotComparisonCostFuel : Nat → List Nat → Nat
  | 0, xs => xs.length * xs.length
  | fuel + 1, xs =>
      if xs.length < 50 then
        xs.length * xs.length
      else
        match medianOfFiveGroups? (fullGroupsOfFive xs) with
        | some (median :: medians) =>
            2 * xs.length +
              selectCost (recursiveMedianOfMediansPivotFuel? fuel)
                (fun ys => ys.length +
                  recursiveMedianOfMediansPivotComparisonCostFuel fuel ys)
                ((median :: medians).length / 2) (median :: medians)
        | _ => xs.length * xs.length

/-- Public pivot-construction comparison charge, using the pivot's canonical fuel. -/
def recursiveMedianOfMediansPivotComparisonCost (xs : List Nat) : Nat :=
  recursiveMedianOfMediansPivotComparisonCostFuel xs.length xs

/--
End-to-end comparison cost of the executable recursive median-of-medians
selector.  Every visited SELECT node charges its partition scan plus the full
recursive cost of constructing that node's pivot.
-/
def recursiveMedianOfMediansComparisonCost (k : Nat) (xs : List Nat) : Nat :=
  selectCost recursiveMedianOfMediansPivot?
    (fun ys => ys.length + recursiveMedianOfMediansPivotComparisonCost ys) k xs

/-- Arithmetic closure for a recursive (non-base) SELECT node. -/
private theorem recursiveMedianOfMediansComparisonCost_large_step
    {n medianBranch strictBranch : Nat}
    (hn : 50 ≤ n) (hmedian : 5 * medianBranch ≤ n)
    (hbranch : 10 * strictBranch ≤ 7 * n + 12) :
    n + (2 * n + 100 * medianBranch) + 100 * strictBranch ≤ 100 * n := by
  have hlocal : 10 * (3 * n) + 12 * 100 ≤ 100 * n := by omega
  have h := selectRecurrence_linear_step (C := 100) hmedian hbranch hlocal
  nlinarith

/-- Arithmetic closure for a base-case median SELECT node. -/
private theorem recursiveMedianOfMediansComparisonCost_small_step
    {n strictBranch : Nat} (hn : n < 50)
    (hbranch : 2 * strictBranch ≤ n) :
    n + n * n + 100 * strictBranch ≤ 100 * n := by
  nlinarith

/--
Linear bound for SELECT using a fixed recursive-pivot fuel.  The hypotheses
say that both the input and the SELECT recursion fit in their available fuel.
This is the strengthened induction needed by the nested median subproblem.
-/
private theorem recursiveMedianOfMediansFixedComparisonCostFuel_linear_bound :
    ∀ n : Nat, ∀ (xs : List Nat) (pivotFuel selectorFuel k : Nat),
      xs.length = n → xs.length ≤ pivotFuel → xs.length ≤ selectorFuel →
        selectCostFuel (recursiveMedianOfMediansPivotFuel? pivotFuel)
          (fun ys => ys.length +
            recursiveMedianOfMediansPivotComparisonCostFuel pivotFuel ys)
          selectorFuel k xs ≤ 100 * xs.length := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro xs pivotFuel selectorFuel k hlen hpivotFuel hselectorFuel
      cases selectorFuel with
      | zero =>
          simp [selectCostFuel]
      | succ selectorFuel =>
          cases hchoose : recursiveMedianOfMediansPivotFuel? pivotFuel xs with
          | none =>
              simp [selectCostFuel, hchoose]
          | some pivot =>
              have hpivotMem : pivot ∈ xs :=
                recursiveMedianOfMediansPivotFuel?_mem pivotFuel hchoose
              have hpivotBound :=
                recursiveMedianOfMediansPivotFuel?_partition_size_bound
                  pivotFuel hchoose
              have hselectorSucc : n ≤ selectorFuel + 1 := by
                simpa [hlen] using hselectorFuel
              by_cases hsmall : n < 50
              · have hpivotCost :
                    recursiveMedianOfMediansPivotComparisonCostFuel pivotFuel xs =
                      n * n := by
                  cases pivotFuel with
                  | zero =>
                      simp [recursiveMedianOfMediansPivotComparisonCostFuel, hlen]
                  | succ fuel =>
                      simp [recursiveMedianOfMediansPivotComparisonCostFuel,
                        hlen, hsmall]
                have hdet : deterministicPivot? xs = some pivot := by
                  cases pivotFuel with
                  | zero =>
                      simpa [recursiveMedianOfMediansPivotFuel?] using hchoose
                  | succ fuel =>
                      simpa [recursiveMedianOfMediansPivotFuel?, hlen, hsmall]
                        using hchoose
                have hhalf := deterministicPivot?_half_partition_size_bound hdet
                by_cases hlo : k < ltCount pivot xs
                · let low := xs.filter fun y => decide (y < pivot)
                  have hlowLt : low.length < xs.length :=
                    filter_length_lt_of_mem_false
                      (fun y => decide (y < pivot)) hpivotMem (by simp)
                  have hlowLtN : low.length < n := by simpa [hlen] using hlowLt
                  have hlowPivotFuel : low.length ≤ pivotFuel := by
                    omega
                  have hlowSelectorFuel : low.length ≤ selectorFuel := by
                    omega
                  have hih := ih low.length hlowLtN low pivotFuel selectorFuel k
                    rfl hlowPivotFuel hlowSelectorFuel
                  have hclose :
                      n + n * n + 100 * low.length ≤ 100 * n :=
                    recursiveMedianOfMediansComparisonCost_small_step hsmall
                      (by simpa [hlen, low, ltCount] using hhalf.1)
                  simp only [selectCostFuel, hchoose, hlo, if_pos, hpivotCost]
                  calc
                    xs.length + n * n +
                        selectCostFuel
                          (recursiveMedianOfMediansPivotFuel? pivotFuel)
                          (fun ys => ys.length +
                            recursiveMedianOfMediansPivotComparisonCostFuel
                              pivotFuel ys)
                          selectorFuel k
                          (xs.filter fun y => decide (y < pivot))
                        ≤ n + n * n + 100 * low.length := by
                            simpa [hlen, low] using
                              Nat.add_le_add_left hih (n + n * n)
                    _ ≤ 100 * n := hclose
                    _ = 100 * xs.length := by rw [hlen]
                · by_cases hmid : k < leCount pivot xs
                  · simp only [selectCostFuel, hchoose, hlo, hmid, if_false,
                      if_pos, hpivotCost]
                    have hclose : n + n * n ≤ 100 * n := by
                      have := recursiveMedianOfMediansComparisonCost_small_step
                        (strictBranch := 0) hsmall (by omega)
                      simpa using this
                    simpa [hlen] using hclose
                  · let high := xs.filter fun y => decide (pivot < y)
                    have hhighLt : high.length < xs.length :=
                      filter_length_lt_of_mem_false
                        (fun y => decide (pivot < y)) hpivotMem (by simp)
                    have hhighLtN : high.length < n := by
                      simpa [hlen] using hhighLt
                    have hhighPivotFuel : high.length ≤ pivotFuel := by omega
                    have hhighSelectorFuel : high.length ≤ selectorFuel := by omega
                    have hih := ih high.length hhighLtN high pivotFuel selectorFuel
                      (k - leCount pivot xs) rfl hhighPivotFuel hhighSelectorFuel
                    have hclose :
                        n + n * n + 100 * high.length ≤ 100 * n :=
                      recursiveMedianOfMediansComparisonCost_small_step hsmall
                        (by simpa [hlen, high, gtCount] using hhalf.2)
                    simp only [selectCostFuel, hchoose, hlo, hmid, if_false,
                      hpivotCost]
                    calc
                      xs.length + n * n +
                          selectCostFuel
                            (recursiveMedianOfMediansPivotFuel? pivotFuel)
                            (fun ys => ys.length +
                              recursiveMedianOfMediansPivotComparisonCostFuel
                                pivotFuel ys)
                            selectorFuel (k - leCount pivot xs)
                            (xs.filter fun y => decide (pivot < y))
                          ≤ n + n * n + 100 * high.length := by
                              simpa [hlen, high] using
                                Nat.add_le_add_left hih (n + n * n)
                      _ ≤ 100 * n := hclose
                      _ = 100 * xs.length := by rw [hlen]
              · have hnlarge : 50 ≤ n := Nat.le_of_not_gt hsmall
                cases pivotFuel with
                | zero =>
                    have : n = 0 := by omega
                    omega
                | succ fuel =>
                    cases hgroups : medianOfFiveGroups? (fullGroupsOfFive xs) with
                    | none =>
                        rcases fullGroupsOfFive_medianOfFiveGroups?_isSome xs with
                          ⟨medians, hmedians⟩
                        rw [hgroups] at hmedians
                        contradiction
                    | some medians =>
                        cases medians with
                        | nil =>
                            have hcert :
                                MedianGroupCertificates (fullGroupsOfFive xs) [] :=
                              fullGroupsOfFive_medianGroupCertificates hgroups
                            have hgroupsLen : (fullGroupsOfFive xs).length = 0 := by
                              simpa using hcert.1
                            have hnear := fullGroupsOfFive_length_near xs
                            rw [hgroupsLen] at hnear
                            omega
                        | cons median medians =>
                            let ms := median :: medians
                            have hcert :
                                MedianGroupCertificates (fullGroupsOfFive xs) ms :=
                              fullGroupsOfFive_medianGroupCertificates hgroups
                            have hmedianSizeXs : 5 * ms.length ≤ xs.length := by
                              have hgroupsSize :=
                                fullGroupsOfFive_length_mul_five_le xs
                              simpa [hcert.1] using hgroupsSize
                            have hmedianSize : 5 * ms.length ≤ n := by
                              simpa [hlen] using hmedianSizeXs
                            have hmedianLtN : ms.length < n := by omega
                            have hmedianFuel : ms.length ≤ fuel := by omega
                            have hinner := ih ms.length hmedianLtN ms fuel ms.length
                              (ms.length / 2) rfl hmedianFuel (Nat.le_refl ms.length)
                            have hpivotCost :
                                recursiveMedianOfMediansPivotComparisonCostFuel
                                    (fuel + 1) xs ≤
                                  2 * n + 100 * ms.length := by
                              dsimp [ms] at hinner ⊢
                              simp only [recursiveMedianOfMediansPivotComparisonCostFuel,
                                hlen, hsmall, ↓reduceIte, hgroups]
                              simpa [selectCost] using
                                Nat.add_le_add_left hinner (2 * n)
                            by_cases hlo : k < ltCount pivot xs
                            · let low := xs.filter fun y => decide (y < pivot)
                              have hlowLt : low.length < xs.length :=
                                filter_length_lt_of_mem_false
                                  (fun y => decide (y < pivot)) hpivotMem (by simp)
                              have hlowLtN : low.length < n := by
                                simpa [hlen] using hlowLt
                              have hlowPivotFuel : low.length ≤ fuel + 1 := by omega
                              have hlowSelectorFuel : low.length ≤ selectorFuel := by omega
                              have hih := ih low.length hlowLtN low (fuel + 1)
                                selectorFuel k rfl hlowPivotFuel hlowSelectorFuel
                              have hclose :=
                                recursiveMedianOfMediansComparisonCost_large_step
                                  hnlarge hmedianSize
                                  (by simpa [hlen, low, ltCount] using hpivotBound.1)
                              simp only [selectCostFuel, hchoose, hlo, if_pos]
                              calc
                                xs.length +
                                      recursiveMedianOfMediansPivotComparisonCostFuel
                                        (fuel + 1) xs +
                                    selectCostFuel
                                      (recursiveMedianOfMediansPivotFuel? (fuel + 1))
                                      (fun ys => ys.length +
                                        recursiveMedianOfMediansPivotComparisonCostFuel
                                          (fuel + 1) ys)
                                      selectorFuel k
                                      (xs.filter fun y => decide (y < pivot))
                                    ≤ n + (2 * n + 100 * ms.length) +
                                        100 * low.length := by
                                          exact Nat.add_le_add
                                            (by simpa [hlen] using
                                              Nat.add_le_add_left hpivotCost n) hih
                                _ ≤ 100 * n := hclose
                                _ = 100 * xs.length := by rw [hlen]
                            · by_cases hmid : k < leCount pivot xs
                              · simp only [selectCostFuel, hchoose, hlo, hmid,
                                  if_false, if_pos]
                                have hclose :=
                                  recursiveMedianOfMediansComparisonCost_large_step
                                    hnlarge hmedianSize (strictBranch := 0) (by omega)
                                have hbase :
                                    xs.length +
                                        recursiveMedianOfMediansPivotComparisonCostFuel
                                          (fuel + 1) xs ≤
                                      n + (2 * n + 100 * ms.length) + 100 * 0 := by
                                  simpa [hlen] using
                                    Nat.add_le_add_left hpivotCost xs.length
                                exact le_trans hbase (by simpa [hlen] using hclose)
                              · let high := xs.filter fun y => decide (pivot < y)
                                have hhighLt : high.length < xs.length :=
                                  filter_length_lt_of_mem_false
                                    (fun y => decide (pivot < y)) hpivotMem (by simp)
                                have hhighLtN : high.length < n := by
                                  simpa [hlen] using hhighLt
                                have hhighPivotFuel : high.length ≤ fuel + 1 := by omega
                                have hhighSelectorFuel : high.length ≤ selectorFuel := by
                                  omega
                                have hih := ih high.length hhighLtN high (fuel + 1)
                                  selectorFuel (k - leCount pivot xs) rfl
                                  hhighPivotFuel hhighSelectorFuel
                                have hclose :=
                                  recursiveMedianOfMediansComparisonCost_large_step
                                    hnlarge hmedianSize
                                    (by simpa [hlen, high, gtCount] using hpivotBound.2)
                                simp only [selectCostFuel, hchoose, hlo, hmid]
                                calc
                                  xs.length +
                                        recursiveMedianOfMediansPivotComparisonCostFuel
                                          (fuel + 1) xs +
                                      selectCostFuel
                                        (recursiveMedianOfMediansPivotFuel? (fuel + 1))
                                        (fun ys => ys.length +
                                          recursiveMedianOfMediansPivotComparisonCostFuel
                                            (fuel + 1) ys)
                                        selectorFuel (k - leCount pivot xs)
                                        (xs.filter fun y => decide (pivot < y))
                                      ≤ n + (2 * n + 100 * ms.length) +
                                          100 * high.length := by
                                            exact Nat.add_le_add
                                              (by simpa [hlen] using
                                                Nat.add_le_add_left hpivotCost n) hih
                                  _ ≤ 100 * n := hclose
                                  _ = 100 * xs.length := by rw [hlen]

/-- Strengthened public-cost induction with arbitrary sufficient SELECT fuel. -/
private theorem recursiveMedianOfMediansComparisonCostFuel_linear_bound :
    ∀ n : Nat, ∀ (xs : List Nat) (selectorFuel k : Nat),
      xs.length = n → xs.length ≤ selectorFuel →
        selectCostFuel recursiveMedianOfMediansPivot?
          (fun ys => ys.length + recursiveMedianOfMediansPivotComparisonCost ys)
          selectorFuel k xs ≤ 100 * xs.length := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro xs selectorFuel k hlen hselectorFuel
      cases selectorFuel with
      | zero =>
          simp [selectCostFuel]
      | succ selectorFuel =>
          cases hchoose : recursiveMedianOfMediansPivot? xs with
          | none =>
              simp [selectCostFuel, hchoose]
          | some pivot =>
              have hpivotMem : pivot ∈ xs :=
                recursiveMedianOfMediansPivot?_mem hchoose
              have hpivotBound :=
                recursiveMedianOfMediansPivot?_partition_size_bound hchoose
              have hnpos : 0 < n := by
                have hxsne : xs ≠ [] := by
                  intro hnil
                  subst xs
                  simp at hpivotMem
                have : 0 < xs.length := by
                  rw [List.length_pos_iff_ne_nil]
                  exact hxsne
                simpa [hlen] using this
              have hselectorSucc : n ≤ selectorFuel + 1 := by
                simpa [hlen] using hselectorFuel
              by_cases hsmall : n < 50
              · have hpivotCost :
                    recursiveMedianOfMediansPivotComparisonCost xs = n * n := by
                  unfold recursiveMedianOfMediansPivotComparisonCost
                  rw [hlen]
                  cases n with
                  | zero => omega
                  | succ n =>
                      simp [recursiveMedianOfMediansPivotComparisonCostFuel,
                        hlen, hsmall]
                have hdet : deterministicPivot? xs = some pivot := by
                  unfold recursiveMedianOfMediansPivot? at hchoose
                  rw [hlen] at hchoose
                  cases n with
                  | zero => omega
                  | succ n =>
                      simpa [recursiveMedianOfMediansPivotFuel?, hlen, hsmall]
                        using hchoose
                have hhalf := deterministicPivot?_half_partition_size_bound hdet
                by_cases hlo : k < ltCount pivot xs
                · let low := xs.filter fun y => decide (y < pivot)
                  have hlowLt : low.length < xs.length :=
                    filter_length_lt_of_mem_false
                      (fun y => decide (y < pivot)) hpivotMem (by simp)
                  have hlowLtN : low.length < n := by simpa [hlen] using hlowLt
                  have hlowSelectorFuel : low.length ≤ selectorFuel := by omega
                  have hih := ih low.length hlowLtN low selectorFuel k rfl
                    hlowSelectorFuel
                  have hclose :
                      n + n * n + 100 * low.length ≤ 100 * n :=
                    recursiveMedianOfMediansComparisonCost_small_step hsmall
                      (by simpa [hlen, low, ltCount] using hhalf.1)
                  simp only [selectCostFuel, hchoose, hlo, if_pos, hpivotCost]
                  calc
                    xs.length + n * n +
                        selectCostFuel recursiveMedianOfMediansPivot?
                          (fun ys => ys.length +
                            recursiveMedianOfMediansPivotComparisonCost ys)
                          selectorFuel k
                          (xs.filter fun y => decide (y < pivot))
                        ≤ n + n * n + 100 * low.length := by
                            simpa [hlen, low] using
                              Nat.add_le_add_left hih (n + n * n)
                    _ ≤ 100 * n := hclose
                    _ = 100 * xs.length := by rw [hlen]
                · by_cases hmid : k < leCount pivot xs
                  · simp only [selectCostFuel, hchoose, hlo, hmid, if_false,
                      if_pos, hpivotCost]
                    have hclose : n + n * n ≤ 100 * n := by
                      have := recursiveMedianOfMediansComparisonCost_small_step
                        (strictBranch := 0) hsmall (by omega)
                      simpa using this
                    simpa [hlen] using hclose
                  · let high := xs.filter fun y => decide (pivot < y)
                    have hhighLt : high.length < xs.length :=
                      filter_length_lt_of_mem_false
                        (fun y => decide (pivot < y)) hpivotMem (by simp)
                    have hhighLtN : high.length < n := by
                      simpa [hlen] using hhighLt
                    have hhighSelectorFuel : high.length ≤ selectorFuel := by omega
                    have hih := ih high.length hhighLtN high selectorFuel
                      (k - leCount pivot xs) rfl hhighSelectorFuel
                    have hclose :
                        n + n * n + 100 * high.length ≤ 100 * n :=
                      recursiveMedianOfMediansComparisonCost_small_step hsmall
                        (by simpa [hlen, high, gtCount] using hhalf.2)
                    simp only [selectCostFuel, hchoose, hlo, hmid, if_false,
                      hpivotCost]
                    calc
                      xs.length + n * n +
                          selectCostFuel recursiveMedianOfMediansPivot?
                            (fun ys => ys.length +
                              recursiveMedianOfMediansPivotComparisonCost ys)
                            selectorFuel (k - leCount pivot xs)
                            (xs.filter fun y => decide (pivot < y))
                          ≤ n + n * n + 100 * high.length := by
                              simpa [hlen, high] using
                                Nat.add_le_add_left hih (n + n * n)
                      _ ≤ 100 * n := hclose
                      _ = 100 * xs.length := by rw [hlen]
              · have hnlarge : 50 ≤ n := Nat.le_of_not_gt hsmall
                cases n with
                | zero => omega
                | succ n =>
                    cases hgroups : medianOfFiveGroups? (fullGroupsOfFive xs) with
                    | none =>
                        rcases fullGroupsOfFive_medianOfFiveGroups?_isSome xs with
                          ⟨medians, hmedians⟩
                        rw [hgroups] at hmedians
                        contradiction
                    | some medians =>
                        cases medians with
                        | nil =>
                            have hcert :
                                MedianGroupCertificates (fullGroupsOfFive xs) [] :=
                              fullGroupsOfFive_medianGroupCertificates hgroups
                            have hgroupsLen : (fullGroupsOfFive xs).length = 0 := by
                              simpa using hcert.1
                            have hnear := fullGroupsOfFive_length_near xs
                            rw [hgroupsLen] at hnear
                            omega
                        | cons median medians =>
                            let ms := median :: medians
                            have hcert :
                                MedianGroupCertificates (fullGroupsOfFive xs) ms :=
                              fullGroupsOfFive_medianGroupCertificates hgroups
                            have hmedianSizeXs : 5 * ms.length ≤ xs.length := by
                              have hgroupsSize :=
                                fullGroupsOfFive_length_mul_five_le xs
                              simpa [hcert.1] using hgroupsSize
                            have hmedianSize : 5 * ms.length ≤ n + 1 := by
                              simpa [hlen] using hmedianSizeXs
                            have hmedianLtN : ms.length < n + 1 := by omega
                            have hmedianFuel : ms.length ≤ n := by omega
                            have hinner :=
                              recursiveMedianOfMediansFixedComparisonCostFuel_linear_bound
                                ms.length ms n ms.length (ms.length / 2) rfl
                                hmedianFuel (Nat.le_refl ms.length)
                            have hpivotCost :
                                recursiveMedianOfMediansPivotComparisonCost xs ≤
                                  2 * (n + 1) + 100 * ms.length := by
                              dsimp [ms] at hinner ⊢
                              unfold recursiveMedianOfMediansPivotComparisonCost
                              rw [hlen]
                              simp only [recursiveMedianOfMediansPivotComparisonCostFuel,
                                hlen, hsmall, ↓reduceIte, hgroups]
                              simpa [selectCost] using
                                Nat.add_le_add_left hinner (2 * (n + 1))
                            by_cases hlo : k < ltCount pivot xs
                            · let low := xs.filter fun y => decide (y < pivot)
                              have hlowLt : low.length < xs.length :=
                                filter_length_lt_of_mem_false
                                  (fun y => decide (y < pivot)) hpivotMem (by simp)
                              have hlowLtN : low.length < n + 1 := by
                                simpa [hlen] using hlowLt
                              have hlowSelectorFuel : low.length ≤ selectorFuel := by
                                omega
                              have hih := ih low.length hlowLtN low selectorFuel k
                                rfl hlowSelectorFuel
                              have hclose :=
                                recursiveMedianOfMediansComparisonCost_large_step
                                  hnlarge hmedianSize
                                  (by simpa [hlen, low, ltCount] using hpivotBound.1)
                              simp only [selectCostFuel, hchoose, hlo, if_pos]
                              calc
                                xs.length +
                                      recursiveMedianOfMediansPivotComparisonCost xs +
                                    selectCostFuel recursiveMedianOfMediansPivot?
                                      (fun ys => ys.length +
                                        recursiveMedianOfMediansPivotComparisonCost ys)
                                      selectorFuel k
                                      (xs.filter fun y => decide (y < pivot))
                                    ≤ (n + 1) +
                                        (2 * (n + 1) + 100 * ms.length) +
                                          100 * low.length := by
                                            exact Nat.add_le_add
                                              (by simpa [hlen] using
                                                Nat.add_le_add_left hpivotCost (n + 1)) hih
                                _ ≤ 100 * (n + 1) := hclose
                                _ = 100 * xs.length := by rw [hlen]
                            · by_cases hmid : k < leCount pivot xs
                              · simp only [selectCostFuel, hchoose, hlo, hmid,
                                  if_false, if_pos]
                                have hclose :=
                                  recursiveMedianOfMediansComparisonCost_large_step
                                    hnlarge hmedianSize (strictBranch := 0) (by omega)
                                have hbase :
                                    xs.length +
                                        recursiveMedianOfMediansPivotComparisonCost xs ≤
                                      (n + 1) +
                                        (2 * (n + 1) + 100 * ms.length) + 100 * 0 := by
                                  simpa [hlen] using
                                    Nat.add_le_add_left hpivotCost xs.length
                                exact le_trans hbase (by simpa [hlen] using hclose)
                              · let high := xs.filter fun y => decide (pivot < y)
                                have hhighLt : high.length < xs.length :=
                                  filter_length_lt_of_mem_false
                                    (fun y => decide (pivot < y)) hpivotMem (by simp)
                                have hhighLtN : high.length < n + 1 := by
                                  simpa [hlen] using hhighLt
                                have hhighSelectorFuel : high.length ≤ selectorFuel := by
                                  omega
                                have hih := ih high.length hhighLtN high selectorFuel
                                  (k - leCount pivot xs) rfl hhighSelectorFuel
                                have hclose :=
                                  recursiveMedianOfMediansComparisonCost_large_step
                                    hnlarge hmedianSize
                                    (by simpa [hlen, high, gtCount] using hpivotBound.2)
                                simp only [selectCostFuel, hchoose, hlo, hmid]
                                calc
                                  xs.length +
                                        recursiveMedianOfMediansPivotComparisonCost xs +
                                      selectCostFuel recursiveMedianOfMediansPivot?
                                        (fun ys => ys.length +
                                          recursiveMedianOfMediansPivotComparisonCost ys)
                                        selectorFuel (k - leCount pivot xs)
                                        (xs.filter fun y => decide (pivot < y))
                                      ≤ (n + 1) +
                                          (2 * (n + 1) + 100 * ms.length) +
                                            100 * high.length := by
                                              exact Nat.add_le_add
                                                (by simpa [hlen] using
                                                  Nat.add_le_add_left hpivotCost (n + 1)) hih
                                  _ ≤ 100 * (n + 1) := hclose
                                  _ = 100 * xs.length := by rw [hlen]

/--
The complete comparison charge of recursive median-of-medians SELECT is
linear, including every nested pivot-selection subproblem and every selected
outer partition branch.
-/
theorem recursiveMedianOfMediansComparisonCost_linear_bound
    (k : Nat) (xs : List Nat) :
    recursiveMedianOfMediansComparisonCost k xs ≤ 100 * xs.length := by
  unfold recursiveMedianOfMediansComparisonCost selectCost
  exact recursiveMedianOfMediansComparisonCostFuel_linear_bound xs.length xs
    xs.length k rfl (Nat.le_refl xs.length)

/--
Partition-path comparison cost of the executable median selector
{lit}`medianOfMediansSelect?`.

The local work at each recursion level is {lit}`xs.length`: one comparison per
element for the linear partition scan around the median-of-medians pivot.  This
is a genuine {lit}`Nat`-valued cost on list input, computed by the selector's
outer recursion.  It deliberately excludes the cost of constructing each
pivot.
-/
def medianOfMediansPartitionPathCost (k : Nat) (xs : List Nat) : Nat :=
  selectCost medianOfMediansPivot? (fun ys => ys.length) k xs

/--
**Linear bound for the outer partition path.**

The partition-comparison cost of {lit}`medianOfMediansSelect?` is linear with the
explicit constant {lit}`17`:

{lit}`medianOfMediansPartitionPathCost k xs ≤ 17 * xs.length`.

This is the concrete counterpart of the abstract recurrence closure
{lit}`medianOfMedians_linear_bound`: the CLRS branch bound
{lit}`medianOfMediansPivot?_partition_size_bound` supplies the
{lit}`10 * branch ≤ 7 * n + 12` hypothesis at every recursion level, and
{lit}`selectCost_linear_bound` sums the linear local work into the closed form
{lit}`≤ 17 n`.
-/
theorem medianOfMediansPartitionPathCost_linear_bound (k : Nat) (xs : List Nat) :
    medianOfMediansPartitionPathCost k xs ≤ 17 * xs.length := by
  have hbound : ∀ (ys : List Nat) (pivot : Nat),
      medianOfMediansPivot? ys = some pivot →
        10 * ltCount pivot ys ≤ 7 * ys.length + 12 ∧
        10 * gtCount pivot ys ≤ 7 * ys.length + 12 :=
    fun _ys _pivot hsel => medianOfMediansPivot?_partition_size_bound hsel
  have hstep : ∀ ys : List Nat, (fun zs => zs.length) ys ≤ 1 * ys.length :=
    fun ys => by simp
  have h := selectCost_linear_bound (a := 1) medianOfMediansPivot?
    (fun ys => ys.length) medianOfMediansPivot?_mem hbound hstep k xs
  simpa [medianOfMediansPartitionPathCost] using h

/-- Outer partition-path cost for the recursive median-of-medians selector. -/
def recursiveMedianOfMediansPartitionPathCost (k : Nat) (xs : List Nat) : Nat :=
  selectCost recursiveMedianOfMediansPivot? (fun ys => ys.length) k xs

/--
The outer partition path of the recursive selector is linear.  This diagnostic
bound intentionally omits nested pivot construction; the end-to-end theorem
{lit}`recursiveMedianOfMediansComparisonCost_linear_bound` includes it.
-/
theorem recursiveMedianOfMediansPartitionPathCost_linear_bound
    (k : Nat) (xs : List Nat) :
    recursiveMedianOfMediansPartitionPathCost k xs ≤ 17 * xs.length := by
  have hstep : ∀ ys : List Nat, (fun zs => zs.length) ys ≤ 1 * ys.length :=
    fun ys => by simp
  have h := selectCost_linear_bound (a := 1) recursiveMedianOfMediansPivot?
    (fun ys => ys.length) recursiveMedianOfMediansPivot?_mem
    (fun _ys _pivot hsel =>
      recursiveMedianOfMediansPivot?_partition_size_bound hsel)
    hstep k xs
  simpa [recursiveMedianOfMediansPartitionPathCost] using h

end Chapter09
end CLRS

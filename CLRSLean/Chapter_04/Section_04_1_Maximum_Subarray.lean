import Mathlib.Tactic
import CLRSLean.Chapter_04.Section_04_6_Master_Theorem_All_Input

/-!
# 4.1. The Maximum-Subarray Problem

This file gives the first Lean model for CLRS Section 4.1.  The textbook
problem asks for a nonempty contiguous subarray of maximum sum.  We model the
input as a list of integer daily changes, enumerate all nonempty contiguous
subarrays, and choose a candidate with maximum sum.

The first executable selector is an exhaustive finite search, which gives a
clean specification.  The file then builds the CLRS divide-and-conquer proof
layers on top of that specification: linear prefix, suffix, and crossing
scans; a structurally recursive selector over midpoint split trees with unit
leaves; and an execution-attached abstract control-step cost.

Main results:

- Theorem {lit}`mem_nonemptySubarrays_iff`: the candidate enumerator contains
  exactly the nonempty contiguous subarrays.
- Theorem {lit}`mem_crossingSubarrays_iff`: the crossing-candidate enumerator
  contains exactly the nonempty suffix/prefix candidates that cross a split.
- Theorem {lit}`bestCandidate_correct`: the generic finite argmax selector
  returns a member whose sum is at least every listed candidate.
- Theorem {lit}`maxCrossingSubarray_correct`: the crossing helper returns a
  maximum-sum candidate among all candidates crossing a split.
- Theorem {lit}`maxCrossingSubarray_isNonemptySubarray_append`: the crossing
  helper returns a valid nonempty subarray of the concatenated input.
- Theorems {lit}`maxPrefixLinear_result_correct`,
  {lit}`maxSuffixLinear_result_correct`, and
  {lit}`maxCrossingSubarrayLinear_result_correct`: the linear scans return
  optimal prefix, suffix, and crossing candidates.
- Theorem {lit}`subarray_append_left_or_right_or_crossing`: every nonempty
  subarray of {lit}`left ++ right` is left-only, right-only, or crossing.
- Theorem {lit}`subarray_append_optimal_of_cases`: a candidate that dominates
  the left-only, right-only, and crossing cases dominates every subarray of the
  concatenated input.
- Theorem {lit}`maxSubarrayDivideStep_correct`: an executable combine step for
  the CLRS divide-and-conquer proof returns a globally optimal candidate for
  {lit}`left ++ right`.
- Theorem {lit}`maxSubarrayDivideTree_correct`: a structurally recursive
  split-tree selector returns a globally optimal maximum subarray.
- Theorem {lit}`maxSubarrayDivideFuel_correct`: a fuelled midpoint splitter
  gives an executable divide-and-conquer selector with the same correctness
  contract.
- Theorems {lit}`maxSubarrayDivideCosted_result` and
  {lit}`maxSubarrayDivideCosted_correct`: erasing the measured cost recovers
  the midpoint execution, whose result is a maximum subarray.
- Theorems {lit}`maxPrefixLinearScoredWithCost_cost`,
  {lit}`maxSuffixLinearScoredWithCost_cost`, and
  {lit}`maxCrossingSubarrayLinearScoredWithCost_cost`: the attached scan
  counters equal their concrete linear transition counts.
- Theorems {lit}`maxSubarrayDivideCosted_cost_eq` and
  {lit}`maxSubarrayDivideCost_unfold`: the measured cost depends only on input
  length and follows the actual floor/ceiling midpoint recurrence.
- Theorem {lit}`maxSubarrayDivideCost_isBigTheta_nlogn`: that executable
  control-step cost is {lit}`Theta(n log n)` on all natural input lengths.
- Theorem {lit}`maxSubarray_exists_of_ne_nil`: nonempty inputs have a selected
  maximum-subarray candidate.
- Theorem {lit}`maxSubarray_correct`: the executable maximum-subarray selector
  returns a nonempty contiguous subarray whose sum is maximal among all
  nonempty contiguous subarrays.

Current gaps:

- The proved metric counts recursive frames, linear scan transitions, and
  constant-size candidate choices.  It does not charge explicit split-tree
  construction, integer-operation costs, Lean {lit}`List` allocation/copying,
  or garbage collection; a full imperative/RAM refinement remains open.
-/

namespace CLRS
namespace Chapter04

/-! ## Contiguous subarrays -/

/-- The sum of a candidate subarray. -/
def subarraySum (xs : List Int) : Int := xs.sum

/--
{lit}`pre` is a nonempty prefix of {lit}`xs`.

This is a specification predicate; the executable enumerator below is proved
equivalent to it.
-/
def IsNonemptyPrefix (pre xs : List Int) : Prop :=
  pre ≠ [] ∧ ∃ rest, xs = pre ++ rest

/--
{lit}`sub` is a nonempty contiguous subarray of {lit}`xs`.

The witnesses are the elements before and after the contiguous segment.
-/
def IsNonemptySubarray (sub xs : List Int) : Prop :=
  sub ≠ [] ∧ ∃ before after, xs = before ++ sub ++ after

/--
{lit}`suf` is a nonempty suffix of {lit}`xs`.

This is the right half of the CLRS crossing-subarray helper: a crossing subarray
uses a nonempty suffix of the left half and a nonempty prefix of the right half.
-/
def IsNonemptySuffix (suf xs : List Int) : Prop :=
  suf ≠ [] ∧ ∃ before, xs = before ++ suf

/--
{lit}`sub` crosses the split between {lit}`left` and {lit}`right` when it is a
nonempty suffix of the left side followed by a nonempty prefix of the right
side.
-/
def IsCrossingSubarray (sub left right : List Int) : Prop :=
  ∃ suf pre,
    IsNonemptySuffix suf left ∧ IsNonemptyPrefix pre right ∧ sub = suf ++ pre

/-- Enumerate all nonempty prefixes of a list. -/
def nonemptyPrefixes : List Int → List (List Int)
  | [] => []
  | x :: xs => [x] :: (nonemptyPrefixes xs).map (fun pre => x :: pre)

/-- Enumerate all nonempty suffixes of a list. -/
def nonemptySuffixes : List Int → List (List Int)
  | [] => []
  | x :: xs => (x :: xs) :: nonemptySuffixes xs

/-- Enumerate all subarrays crossing a fixed split. -/
def crossingSubarrays (left right : List Int) : List (List Int) :=
  (nonemptySuffixes left).flatMap
    (fun suf => (nonemptyPrefixes right).map (fun pre => suf ++ pre))

private theorem flatMap_nil {α β : Type} (xs : List α) :
    xs.flatMap (fun _ => ([] : List β)) = [] := by
  induction xs with
  | nil =>
      rfl
  | cons _ xs ih =>
      simp [List.flatMap]

/-- Enumerate all nonempty contiguous subarrays of a list. -/
def nonemptySubarrays : List Int → List (List Int)
  | [] => []
  | x :: xs => nonemptyPrefixes (x :: xs) ++ nonemptySubarrays xs

/-- The prefix enumerator is exact. -/
theorem mem_nonemptyPrefixes_iff {pre xs : List Int} :
    pre ∈ nonemptyPrefixes xs ↔ IsNonemptyPrefix pre xs := by
  induction xs generalizing pre with
  | nil =>
      simp [nonemptyPrefixes, IsNonemptyPrefix]
  | cons x xs ih =>
      constructor
      · intro h
        simp [nonemptyPrefixes] at h
        rcases h with hSingle | hMap
        · subst pre
          exact ⟨by simp, ⟨xs, rfl⟩⟩
        · rcases hMap with ⟨tail, htail, rfl⟩
          rcases ih.mp htail with ⟨_htailNonempty, rest, htailEq⟩
          exact ⟨by simp, ⟨rest, by simp [htailEq]⟩⟩
      · intro h
        rcases h with ⟨hpreNonempty, rest, hEq⟩
        cases pre with
        | nil =>
            exact False.elim (hpreNonempty rfl)
        | cons y ys =>
            simp [List.cons_append] at hEq
            rcases hEq with ⟨hxy, htail⟩
            subst y
            cases ys with
            | nil =>
                simp [nonemptyPrefixes]
            | cons z zs =>
                have htailMem : (z :: zs) ∈ nonemptyPrefixes xs := by
                  exact ih.mpr ⟨by simp, ⟨rest, htail⟩⟩
                simp [nonemptyPrefixes, htailMem]

/-- The suffix enumerator is exact. -/
theorem mem_nonemptySuffixes_iff {suf xs : List Int} :
    suf ∈ nonemptySuffixes xs ↔ IsNonemptySuffix suf xs := by
  induction xs generalizing suf with
  | nil =>
      simp [nonemptySuffixes, IsNonemptySuffix]
  | cons x xs ih =>
      constructor
      · intro h
        simp [nonemptySuffixes] at h
        rcases h with hAll | hTail
        · subst suf
          exact ⟨by simp, ⟨[], by simp⟩⟩
        · rcases ih.mp hTail with ⟨hsufNonempty, before, hEq⟩
          exact ⟨hsufNonempty, ⟨x :: before, by simp [hEq]⟩⟩
      · intro h
        rcases h with ⟨hsufNonempty, before, hEq⟩
        cases before with
        | nil =>
            have hEq' : suf = x :: xs := by
              simpa using hEq.symm
            subst suf
            simp [nonemptySuffixes]
        | cons y beforeTail =>
            simp [List.cons_append] at hEq
            rcases hEq with ⟨hxy, htail⟩
            subst y
            have htailMem : suf ∈ nonemptySuffixes xs :=
              ih.mpr ⟨hsufNonempty, ⟨beforeTail, htail⟩⟩
            simp [nonemptySuffixes, htailMem]

/-- The crossing-subarray enumerator is exact for a fixed split. -/
theorem mem_crossingSubarrays_iff {sub left right : List Int} :
    sub ∈ crossingSubarrays left right ↔
      IsCrossingSubarray sub left right := by
  constructor
  · intro h
    unfold crossingSubarrays at h
    rcases (List.mem_flatMap.mp h) with ⟨suf, hsufMem, hsubMem⟩
    rcases (List.mem_map.mp hsubMem) with ⟨pre, hpreMem, hsubEq⟩
    exact ⟨suf, pre,
      mem_nonemptySuffixes_iff.mp hsufMem,
      mem_nonemptyPrefixes_iff.mp hpreMem,
      hsubEq.symm⟩
  · intro h
    rcases h with ⟨suf, pre, hsuf, hpre, rfl⟩
    unfold crossingSubarrays
    exact (List.mem_flatMap.mpr
      ⟨suf, mem_nonemptySuffixes_iff.mpr hsuf,
        (List.mem_map.mpr ⟨pre, mem_nonemptyPrefixes_iff.mpr hpre, rfl⟩)⟩)

/--
Every crossing candidate is a nonempty contiguous subarray of the concatenated
input.
-/
theorem crossingSubarray_isNonemptySubarray_append {sub left right : List Int}
    (hcross : IsCrossingSubarray sub left right) :
    IsNonemptySubarray sub (left ++ right) := by
  rcases hcross with ⟨suf, pre, hsuf, hpre, rfl⟩
  rcases hsuf with ⟨hsufNonempty, before, hleft⟩
  rcases hpre with ⟨_hpreNonempty, after, hright⟩
  constructor
  · intro hnil
    cases suf with
    | nil =>
        exact hsufNonempty rfl
    | cons _ _ =>
        simp at hnil
  · exact ⟨before, after, by simp [hleft, hright, List.append_assoc]⟩

/-! ## Lifting subarrays across an append -/

/-- A left-half subarray is also a subarray after appending a right half. -/
theorem isNonemptySubarray_append_left {sub left right : List Int}
    (hsub : IsNonemptySubarray sub left) :
    IsNonemptySubarray sub (left ++ right) := by
  rcases hsub with ⟨hsubNonempty, before, after, hleft⟩
  exact ⟨hsubNonempty, before, after ++ right, by
    simp [hleft, List.append_assoc]⟩

/-- A right-half subarray is also a subarray after prepending a left half. -/
theorem isNonemptySubarray_append_right {sub left right : List Int}
    (hsub : IsNonemptySubarray sub right) :
    IsNonemptySubarray sub (left ++ right) := by
  rcases hsub with ⟨hsubNonempty, before, after, hright⟩
  exact ⟨hsubNonempty, left ++ before, after, by
    simp [hright, List.append_assoc]⟩

/-- The contiguous-subarray enumerator is exact. -/
theorem mem_nonemptySubarrays_iff {sub xs : List Int} :
    sub ∈ nonemptySubarrays xs ↔ IsNonemptySubarray sub xs := by
  induction xs generalizing sub with
  | nil =>
      simp [nonemptySubarrays, IsNonemptySubarray]
  | cons x xs ih =>
      constructor
      · intro h
        simp [nonemptySubarrays] at h
        rcases h with hPrefix | hTail
        · rcases mem_nonemptyPrefixes_iff.mp hPrefix with
            ⟨hsubNonempty, rest, hPrefixEq⟩
          exact ⟨hsubNonempty, ⟨[], rest, by simp [hPrefixEq]⟩⟩
        · rcases ih.mp hTail with ⟨hsubNonempty, before, after, hEq⟩
          exact ⟨hsubNonempty, ⟨x :: before, after, by simp [hEq]⟩⟩
      · intro h
        rcases h with ⟨hsubNonempty, before, after, hEq⟩
        simp [nonemptySubarrays]
        cases before with
        | nil =>
            left
            exact mem_nonemptyPrefixes_iff.mpr
              ⟨hsubNonempty, ⟨after, by simpa using hEq⟩⟩
        | cons y beforeTail =>
            right
            simp [List.cons_append] at hEq
            rcases hEq with ⟨_hy, htail⟩
            exact ih.mpr
              ⟨hsubNonempty, ⟨beforeTail, after, by
                simpa [List.append_assoc] using htail⟩⟩

/-! ## Split classification -/

/--
Every nonempty subarray of a concatenation is either fully in the left half,
fully in the right half, or crosses the split.

This is the structural lemma needed by the CLRS divide-and-conquer proof after
the recursive calls and the crossing helper have produced their local winners.
-/
theorem subarray_append_left_or_right_or_crossing {sub left right : List Int}
    (hsub : IsNonemptySubarray sub (left ++ right)) :
    IsNonemptySubarray sub left ∨
      IsNonemptySubarray sub right ∨ IsCrossingSubarray sub left right := by
  rcases hsub with ⟨hsubNonempty, before, after, hEq⟩
  have hEq' : left ++ right = before ++ (sub ++ after) := by
    simpa [List.append_assoc] using hEq
  rcases (List.append_eq_append_iff.mp hEq') with
    ⟨beforeRight, hbefore, hright⟩ | ⟨leftRest, hleft, htail⟩
  · right
    left
    exact ⟨hsubNonempty, ⟨beforeRight, after, by
      simpa [List.append_assoc] using hright⟩⟩
  · rcases (List.append_eq_append_iff.mp htail) with
      ⟨leftAfter, hleftRest, hafter⟩ | ⟨rightPrefix, hsubEq, hright⟩
    · left
      exact ⟨hsubNonempty, ⟨before, leftAfter, by
        simp [hleft, hleftRest, List.append_assoc]⟩⟩
    · cases leftRest with
      | nil =>
          simp at hsubEq
          subst sub
          right
          left
          exact ⟨hsubNonempty, ⟨[], after, by simpa using hright⟩⟩
      | cons x xs =>
          cases rightPrefix with
          | nil =>
              simp at hsubEq
              subst sub
              left
              exact ⟨hsubNonempty, ⟨before, [], by
                simpa [List.append_assoc] using hleft⟩⟩
          | cons y ys =>
              right
              right
              exact ⟨x :: xs, y :: ys,
                ⟨by simp, ⟨before, hleft⟩⟩,
                ⟨by simp, ⟨after, hright⟩⟩,
                hsubEq⟩

/--
If a candidate dominates every left-only, right-only, and crossing subarray,
then it dominates every nonempty subarray of the concatenated input.
-/
theorem subarray_append_optimal_of_cases {best left right : List Int}
    (hleft :
      ∀ cand, IsNonemptySubarray cand left →
        subarraySum cand ≤ subarraySum best)
    (hright :
      ∀ cand, IsNonemptySubarray cand right →
        subarraySum cand ≤ subarraySum best)
    (hcross :
      ∀ cand, IsCrossingSubarray cand left right →
        subarraySum cand ≤ subarraySum best) :
    ∀ cand, IsNonemptySubarray cand (left ++ right) →
      subarraySum cand ≤ subarraySum best := by
  intro cand hcand
  rcases subarray_append_left_or_right_or_crossing hcand with
    hleftCand | hrightCand | hcrossCand
  · exact hleft cand hleftCand
  · exact hright cand hrightCand
  · exact hcross cand hcrossCand

/-! ## Finite argmax -/

/-- Choose the candidate with greater sum, breaking ties toward the first one. -/
def betterCandidate (a b : List Int) : List Int :=
  if subarraySum a < subarraySum b then b else a

/-- A finite maximum-by-sum selector for a list of candidates. -/
def bestCandidate : List (List Int) → Option (List Int)
  | [] => none
  | cand :: rest =>
      match bestCandidate rest with
      | none => some cand
      | some best => some (betterCandidate cand best)

/--
The finite selector returns an element of the candidate list whose sum is at
least every candidate sum.
-/
theorem bestCandidate_correct {candidates : List (List Int)} {best : List Int}
    (hbest : bestCandidate candidates = some best) :
    best ∈ candidates ∧
      ∀ cand, cand ∈ candidates → subarraySum cand ≤ subarraySum best := by
  induction candidates generalizing best with
  | nil =>
      simp [bestCandidate] at hbest
  | cons cand rest ih =>
      simp [bestCandidate] at hbest
      cases hrest : bestCandidate rest with
      | none =>
          have hrestNil : rest = [] := by
            cases rest with
            | nil => rfl
            | cons restCand restTail =>
                cases htail : bestCandidate restTail <;>
                  simp [bestCandidate, htail] at hrest
          simp [hrest] at hbest
          subst best
          subst rest
          constructor
          · simp
          · intro other hother
            simp at hother
            subst other
            exact le_rfl
      | some restBest =>
          simp [hrest] at hbest
          have hrestCorrect := ih hrest
          by_cases hlt : subarraySum cand < subarraySum restBest
          · simp [betterCandidate, hlt] at hbest
            subst best
            constructor
            · simp [hrestCorrect.1]
            · intro other hother
              simp at hother
              rcases hother with hsame | hinRest
              · subst other
                exact le_of_lt hlt
              · exact hrestCorrect.2 other hinRest
          · simp [betterCandidate, hlt] at hbest
            subst best
            constructor
            · simp
            · intro other hother
              simp at hother
              rcases hother with hsame | hinRest
              · subst other
                exact le_rfl
              · exact le_trans (hrestCorrect.2 other hinRest) (le_of_not_gt hlt)

/-- Every nonempty candidate list has a selected best candidate. -/
theorem bestCandidate_exists_of_ne_nil {candidates : List (List Int)}
    (hcandidates : candidates ≠ []) :
    ∃ best, bestCandidate candidates = some best := by
  cases candidates with
  | nil =>
      exact False.elim (hcandidates rfl)
  | cons cand rest =>
      simp [bestCandidate]
      cases hrest : bestCandidate rest with
      | none =>
          exact ⟨cand, rfl⟩
      | some restBest =>
          exact ⟨betterCandidate cand restBest, rfl⟩

/-- If the finite argmax selector returns no candidate, the list was empty. -/
theorem bestCandidate_none_eq_nil {candidates : List (List Int)}
    (hbest : bestCandidate candidates = none) :
    candidates = [] := by
  by_contra hcandidates
  rcases bestCandidate_exists_of_ne_nil hcandidates with ⟨best, hsome⟩
  rw [hbest] at hsome
  contradiction

/-! ## Crossing-subarray helper -/

/--
Choose a maximum-sum subarray that crosses the split between {lit}`left` and
{lit}`right`.  If either side is empty there is no crossing candidate.
-/
def maxCrossingSubarray (left right : List Int) : Option (List Int) :=
  bestCandidate (crossingSubarrays left right)

/-- Empty left sides have no crossing candidate. -/
theorem maxCrossingSubarray_nil_left (right : List Int) :
    maxCrossingSubarray [] right = none := by
  rfl

/-- Empty right sides have no crossing candidate. -/
theorem maxCrossingSubarray_nil_right (left : List Int) :
    maxCrossingSubarray left [] = none := by
  simp [maxCrossingSubarray, crossingSubarrays, nonemptyPrefixes, flatMap_nil,
    bestCandidate]

/-- Nonempty left and right sides have at least one crossing candidate. -/
theorem maxCrossingSubarray_exists_of_ne_nil {left right : List Int}
    (hleft : left ≠ []) (hright : right ≠ []) :
    ∃ best, maxCrossingSubarray left right = some best := by
  unfold maxCrossingSubarray
  apply bestCandidate_exists_of_ne_nil
  cases left with
  | nil =>
      exact False.elim (hleft rfl)
  | cons x xs =>
      cases right with
      | nil =>
          exact False.elim (hright rfl)
      | cons y ys =>
          simp [crossingSubarrays, nonemptySuffixes, nonemptyPrefixes]

/--
Correctness of the CLRS crossing helper: whenever it returns a candidate, that
candidate crosses the split and has maximum sum among all crossing candidates.
-/
theorem maxCrossingSubarray_correct {left right best : List Int}
    (hbest : maxCrossingSubarray left right = some best) :
    IsCrossingSubarray best left right ∧
      ∀ cand, IsCrossingSubarray cand left right →
        subarraySum cand ≤ subarraySum best := by
  unfold maxCrossingSubarray at hbest
  rcases bestCandidate_correct hbest with ⟨hbestMem, hbestOptimal⟩
  constructor
  · exact mem_crossingSubarrays_iff.mp hbestMem
  · intro cand hcand
    exact hbestOptimal cand (mem_crossingSubarrays_iff.mpr hcand)

/-- If the crossing helper returns no candidate, no crossing candidate exists. -/
theorem maxCrossingSubarray_none_no_crossing {left right : List Int}
    (hbest : maxCrossingSubarray left right = none) :
    ∀ cand, ¬ IsCrossingSubarray cand left right := by
  intro cand hcand
  have hcandMem : cand ∈ crossingSubarrays left right :=
    mem_crossingSubarrays_iff.mpr hcand
  have hcandidates : crossingSubarrays left right ≠ [] := by
    intro hnil
    simp [hnil] at hcandMem
  rcases bestCandidate_exists_of_ne_nil hcandidates with ⟨best, hsome⟩
  unfold maxCrossingSubarray at hbest
  rw [hbest] at hsome
  contradiction

/--
The crossing helper returns an ordinary nonempty contiguous subarray of the
concatenated input.
-/
theorem maxCrossingSubarray_isNonemptySubarray_append {left right best : List Int}
    (hbest : maxCrossingSubarray left right = some best) :
    IsNonemptySubarray best (left ++ right) := by
  exact crossingSubarray_isNonemptySubarray_append
    (maxCrossingSubarray_correct hbest).1

/-! ## Linear crossing-subarray scan -/

/-- A running prefix sum paired with the length of the represented prefix. -/
abbrev PrefixScore := Int × Nat

/-- An executable subarray candidate paired with its cached sum. -/
abbrev ScoredSubarray := List Int × Int

/--
Build all running prefix sums in one traversal.  The accumulator stores the
sum and length of the input consumed before the current list.
-/
def prefixScoresAux : List Int → Int → Nat → List PrefixScore
  | [], _, _ => []
  | x :: xs, total, len =>
      let total' := total + x
      let len' := len + 1
      (total', len') :: prefixScoresAux xs total' len'

/-- Running sums and lengths of every nonempty prefix. -/
def prefixScores (xs : List Int) : List PrefixScore :=
  prefixScoresAux xs 0 0

/-- The accumulated score traversal represents exactly the nonempty prefixes. -/
theorem mem_prefixScoresAux_iff {score : Int} {len : Nat} {xs : List Int}
    {total : Int} {offset : Nat} :
    (score, len) ∈ prefixScoresAux xs total offset ↔
      ∃ pre rest,
        pre ≠ [] ∧ xs = pre ++ rest ∧
          score = total + subarraySum pre ∧
          len = offset + pre.length := by
  induction xs generalizing score len total offset with
  | nil =>
      simp [prefixScoresAux]
  | cons x xs ih =>
      constructor
      · intro h
        simp only [prefixScoresAux, List.mem_cons, Prod.mk.injEq] at h
        rcases h with ⟨hscore, hlen⟩ | htail
        · refine ⟨[x], xs, by simp, by simp, ?_, ?_⟩
          · simpa [subarraySum] using hscore
          · simpa using hlen
        · rcases (ih (total := total + x) (offset := offset + 1)).mp htail with
            ⟨pre, rest, hpre, hxs, hscore, hlen⟩
          refine ⟨x :: pre, rest, by simp, by simp [hxs], ?_, ?_⟩
          · simp only [subarraySum, List.sum_cons] at hscore ⊢
            omega
          · simp only [List.length_cons] at hlen ⊢
            omega
      · rintro ⟨pre, rest, hpre, hxs, hscore, hlen⟩
        cases pre with
        | nil =>
            exact False.elim (hpre rfl)
        | cons y ys =>
            simp only [List.cons_append] at hxs
            injection hxs with hxy htail
            subst y
            cases ys with
            | nil =>
                simp only [prefixScoresAux, List.mem_cons, Prod.mk.injEq]
                left
                constructor
                · simpa [subarraySum] using hscore
                · simpa using hlen
            | cons z zs =>
                simp only [prefixScoresAux, List.mem_cons, Prod.mk.injEq]
                right
                apply (ih (total := total + x) (offset := offset + 1)).mpr
                refine ⟨z :: zs, rest, by simp, htail, ?_, ?_⟩
                · simp only [subarraySum, List.sum_cons] at hscore ⊢
                  omega
                · simp only [List.length_cons] at hlen ⊢
                  omega

/-- The top-level running-score list is an exact scored prefix enumerator. -/
theorem mem_prefixScores_iff {score : Int} {len : Nat} {xs : List Int} :
    (score, len) ∈ prefixScores xs ↔
      ∃ pre,
        IsNonemptyPrefix pre xs ∧ score = subarraySum pre ∧ len = pre.length := by
  rw [prefixScores, mem_prefixScoresAux_iff]
  constructor
  · rintro ⟨pre, rest, hpre, hxs, hscore, hlen⟩
    exact ⟨pre, ⟨hpre, rest, hxs⟩, by simpa using hscore, by simpa using hlen⟩
  · rintro ⟨pre, ⟨hpre, rest, hxs⟩, hscore, hlen⟩
    exact ⟨pre, rest, hpre, hxs, by simpa using hscore, by simpa using hlen⟩

/-- Choose the larger recorded sum, breaking ties toward the first score. -/
def betterPrefixScore (a b : PrefixScore) : PrefixScore :=
  if a.1 < b.1 then b else a

/-- Select a maximum recorded prefix sum. -/
def bestPrefixScore : List PrefixScore → Option PrefixScore
  | [] => none
  | score :: rest =>
      match bestPrefixScore rest with
      | none => some score
      | some best => some (betterPrefixScore score best)

/-- The score selector returns a member whose recorded sum is maximal. -/
theorem bestPrefixScore_correct {scores : List PrefixScore} {best : PrefixScore}
    (hbest : bestPrefixScore scores = some best) :
    best ∈ scores ∧ ∀ score, score ∈ scores → score.1 ≤ best.1 := by
  induction scores generalizing best with
  | nil =>
      simp [bestPrefixScore] at hbest
  | cons score rest ih =>
      simp only [bestPrefixScore] at hbest
      cases hrest : bestPrefixScore rest with
      | none =>
          have hrestNil : rest = [] := by
            cases rest with
            | nil => rfl
            | cons next tail =>
                cases htail : bestPrefixScore tail <;>
                  simp [bestPrefixScore, htail] at hrest
          subst rest
          have heq : score = best := by
            exact Option.some.inj (by simpa [bestPrefixScore] using hbest)
          subst best
          simp
      | some restBest =>
          simp [hrest] at hbest
          have hrestCorrect := ih hrest
          by_cases hlt : score.1 < restBest.1
          · simp [betterPrefixScore, hlt] at hbest
            subst best
            constructor
            · simp [hrestCorrect.1]
            · intro other hother
              simp at hother
              rcases hother with rfl | hin
              · exact le_of_lt hlt
              · exact hrestCorrect.2 other hin
          · simp [betterPrefixScore, hlt] at hbest
            subst best
            constructor
            · simp
            · intro other hother
              simp at hother
              rcases hother with rfl | hin
              · exact le_rfl
              · exact le_trans (hrestCorrect.2 other hin) (le_of_not_gt hlt)

/-- If no best score is returned, the score list was empty. -/
theorem bestPrefixScore_none_eq_nil {scores : List PrefixScore}
    (hbest : bestPrefixScore scores = none) : scores = [] := by
  cases scores with
  | nil => rfl
  | cons score rest =>
      cases hrest : bestPrefixScore rest <;>
        simp [bestPrefixScore, hrest] at hbest

/--
Maximum-sum nonempty prefix computed from accumulated sums.  Only the selected
prefix is materialized after the two linear score traversals.
-/
def maxPrefixLinear (xs : List Int) : Option (List Int) :=
  match bestPrefixScore (prefixScores xs) with
  | none => none
  | some best => some (xs.take best.2)

/-- The accumulated-sum prefix scan returns an optimal nonempty prefix. -/
theorem maxPrefixLinear_result_correct (xs : List Int) :
    match maxPrefixLinear xs with
    | none => xs = []
    | some best =>
        IsNonemptyPrefix best xs ∧
          ∀ cand, IsNonemptyPrefix cand xs →
            subarraySum cand ≤ subarraySum best := by
  unfold maxPrefixLinear
  cases hscore : bestPrefixScore (prefixScores xs) with
  | none =>
      change xs = []
      have hscores := bestPrefixScore_none_eq_nil hscore
      cases xs with
      | nil => rfl
      | cons x tail =>
          simp [prefixScores, prefixScoresAux] at hscores
  | some bestScore =>
      rcases bestPrefixScore_correct hscore with ⟨hmem, hoptimal⟩
      rcases mem_prefixScores_iff.mp hmem with
        ⟨best, hbestPrefix, hbestSum, hbestLen⟩
      have htake : xs.take bestScore.2 = best := by
        rcases hbestPrefix with ⟨_, rest, hxs⟩
        rw [hbestLen, hxs]
        simp
      change
        IsNonemptyPrefix (xs.take bestScore.2) xs ∧
          ∀ cand, IsNonemptyPrefix cand xs →
            subarraySum cand ≤ subarraySum (xs.take bestScore.2)
      rw [htake]
      refine ⟨hbestPrefix, ?_⟩
      intro cand hcand
      have hcandMem : (subarraySum cand, cand.length) ∈ prefixScores xs :=
        mem_prefixScores_iff.mpr ⟨cand, hcand, rfl, rfl⟩
      have hle := hoptimal (subarraySum cand, cand.length) hcandMem
      simpa [hbestSum] using hle

/-- Reversing turns nonempty suffixes into nonempty prefixes, and conversely. -/
theorem isNonemptySuffix_iff_reverse_prefix {suf xs : List Int} :
    IsNonemptySuffix suf xs ↔ IsNonemptyPrefix suf.reverse xs.reverse := by
  constructor
  · rintro ⟨hsuf, before, hxs⟩
    constructor
    · simpa using hsuf
    · refine ⟨before.reverse, ?_⟩
      simp [hxs, List.reverse_append]
  · rintro ⟨hrev, rest, hxs⟩
    constructor
    · simpa using hrev
    · refine ⟨rest.reverse, ?_⟩
      have h := congrArg List.reverse hxs
      simpa [List.reverse_append] using h

/-- Reversal preserves the sum used by the maximum-subarray specification. -/
theorem subarraySum_reverse (xs : List Int) :
    subarraySum xs.reverse = subarraySum xs := by
  simp [subarraySum]

/-- Maximum-sum nonempty suffix obtained by one reverse-prefix traversal. -/
def maxSuffixLinear (xs : List Int) : Option (List Int) :=
  (maxPrefixLinear xs.reverse).map List.reverse

/-- The reverse-prefix suffix scan returns an optimal nonempty suffix. -/
theorem maxSuffixLinear_result_correct (xs : List Int) :
    match maxSuffixLinear xs with
    | none => xs = []
    | some best =>
        IsNonemptySuffix best xs ∧
          ∀ cand, IsNonemptySuffix cand xs →
            subarraySum cand ≤ subarraySum best := by
  have hp := maxPrefixLinear_result_correct xs.reverse
  cases hprefix : maxPrefixLinear xs.reverse with
  | none =>
      simp only [maxSuffixLinear, hprefix, Option.map_none]
      change xs = []
      rw [hprefix] at hp
      simpa using congrArg List.reverse hp
  | some bestPrefix =>
      simp only [maxSuffixLinear, hprefix, Option.map_some]
      rw [hprefix] at hp
      change
        IsNonemptySuffix bestPrefix.reverse xs ∧
          ∀ cand, IsNonemptySuffix cand xs →
            subarraySum cand ≤ subarraySum bestPrefix.reverse
      constructor
      · apply isNonemptySuffix_iff_reverse_prefix.mpr
        simpa using hp.1
      · intro cand hcand
        have hrev : IsNonemptyPrefix cand.reverse xs.reverse :=
          isNonemptySuffix_iff_reverse_prefix.mp hcand
        have hle := hp.2 cand.reverse hrev
        simpa [subarraySum_reverse] using hle

/--
Maximum-sum crossing subarray from one maximum-suffix scan on the left and one
maximum-prefix scan on the right.
-/
def maxCrossingSubarrayLinear (left right : List Int) : Option (List Int) :=
  match maxSuffixLinear left, maxPrefixLinear right with
  | some suf, some pre => some (suf ++ pre)
  | _, _ => none

/-- The linear crossing scan returns exactly the optimal crossing result. -/
theorem maxCrossingSubarrayLinear_result_correct (left right : List Int) :
    match maxCrossingSubarrayLinear left right with
    | none => ∀ cand, ¬ IsCrossingSubarray cand left right
    | some best =>
        IsCrossingSubarray best left right ∧
          ∀ cand, IsCrossingSubarray cand left right →
            subarraySum cand ≤ subarraySum best := by
  have hsuffix := maxSuffixLinear_result_correct left
  have hprefix := maxPrefixLinear_result_correct right
  cases hs : maxSuffixLinear left with
  | none =>
      simp only [maxCrossingSubarrayLinear, hs]
      rw [hs] at hsuffix
      change ∀ cand, ¬ IsCrossingSubarray cand left right
      intro cand hcross
      rcases hcross with ⟨suf, pre, hsuf, _hpre, _⟩
      subst left
      simpa [IsNonemptySuffix] using hsuf
  | some bestSuffix =>
      rw [hs] at hsuffix
      cases hp : maxPrefixLinear right with
      | none =>
          simp only [maxCrossingSubarrayLinear, hs, hp]
          rw [hp] at hprefix
          change ∀ cand, ¬ IsCrossingSubarray cand left right
          intro cand hcross
          rcases hcross with ⟨suf, pre, _hsuf, hpre, _⟩
          subst right
          simpa [IsNonemptyPrefix] using hpre
      | some bestPrefix =>
          simp only [maxCrossingSubarrayLinear, hs, hp]
          rw [hp] at hprefix
          change
            IsCrossingSubarray (bestSuffix ++ bestPrefix) left right ∧
              ∀ cand, IsCrossingSubarray cand left right →
                subarraySum cand ≤ subarraySum (bestSuffix ++ bestPrefix)
          constructor
          · exact ⟨bestSuffix, bestPrefix, hsuffix.1, hprefix.1, rfl⟩
          · intro cand hcross
            rcases hcross with ⟨suf, pre, hsuf, hpre, rfl⟩
            have hsufLe := hsuffix.2 suf hsuf
            have hpreLe := hprefix.2 pre hpre
            simp only [subarraySum, List.sum_append] at hsufLe hpreLe ⊢
            omega

/-! ### Cached-score execution interface -/

/-- The linear prefix scan together with the selected prefix's cached sum. -/
def maxPrefixLinearScored (xs : List Int) : Option ScoredSubarray :=
  match bestPrefixScore (prefixScores xs) with
  | none => none
  | some best => some (xs.take best.2, best.1)

/-- Erasing the cached sum recovers the public linear prefix selector. -/
theorem maxPrefixLinearScored_result (xs : List Int) :
    (maxPrefixLinearScored xs).map Prod.fst = maxPrefixLinear xs := by
  unfold maxPrefixLinearScored maxPrefixLinear
  cases bestPrefixScore (prefixScores xs) <;> rfl

/-- The cached prefix score equals the sum of the returned prefix. -/
theorem maxPrefixLinearScored_sum (xs : List Int) :
    match maxPrefixLinearScored xs with
    | none => True
    | some best => best.2 = subarraySum best.1 := by
  unfold maxPrefixLinearScored
  cases hscore : bestPrefixScore (prefixScores xs) with
  | none => trivial
  | some bestScore =>
      rcases bestPrefixScore_correct hscore with ⟨hmem, _⟩
      rcases mem_prefixScores_iff.mp hmem with
        ⟨best, hprefix, hsum, hlen⟩
      have htake : xs.take bestScore.2 = best := by
        rcases hprefix with ⟨_, rest, hxs⟩
        rw [hlen, hxs]
        simp
      change bestScore.1 = subarraySum (xs.take bestScore.2)
      rw [htake]
      exact hsum

/-- The linear suffix scan together with the selected suffix's cached sum. -/
def maxSuffixLinearScored (xs : List Int) : Option ScoredSubarray :=
  (maxPrefixLinearScored xs.reverse).map
    (fun best => (best.1.reverse, best.2))

/-- Erasing the cached sum recovers the public linear suffix selector. -/
theorem maxSuffixLinearScored_result (xs : List Int) :
    (maxSuffixLinearScored xs).map Prod.fst = maxSuffixLinear xs := by
  unfold maxSuffixLinearScored maxSuffixLinear
  rw [← maxPrefixLinearScored_result xs.reverse]
  cases maxPrefixLinearScored xs.reverse <;> rfl

/-- The cached suffix score equals the sum of the returned suffix. -/
theorem maxSuffixLinearScored_sum (xs : List Int) :
    match maxSuffixLinearScored xs with
    | none => True
    | some best => best.2 = subarraySum best.1 := by
  have hsum := maxPrefixLinearScored_sum xs.reverse
  cases hprefix : maxPrefixLinearScored xs.reverse with
  | none =>
      simp [maxSuffixLinearScored, hprefix]
  | some best =>
      rw [hprefix] at hsum
      simp only [maxSuffixLinearScored, hprefix, Option.map_some]
      change best.2 = subarraySum best.1.reverse
      simpa [subarraySum_reverse] using hsum

/-- The linear crossing scan together with its cached sum. -/
def maxCrossingSubarrayLinearScored
    (left right : List Int) : Option ScoredSubarray :=
  match maxSuffixLinearScored left, maxPrefixLinearScored right with
  | some suf, some pre => some (suf.1 ++ pre.1, suf.2 + pre.2)
  | _, _ => none

/-- Erasing the cached sum recovers the public linear crossing selector. -/
theorem maxCrossingSubarrayLinearScored_result (left right : List Int) :
    (maxCrossingSubarrayLinearScored left right).map Prod.fst =
      maxCrossingSubarrayLinear left right := by
  unfold maxCrossingSubarrayLinearScored maxCrossingSubarrayLinear
  rw [← maxSuffixLinearScored_result left,
    ← maxPrefixLinearScored_result right]
  cases maxSuffixLinearScored left <;>
    cases maxPrefixLinearScored right <;> rfl

/-- The cached crossing score equals the sum of the returned crossing subarray. -/
theorem maxCrossingSubarrayLinearScored_sum (left right : List Int) :
    match maxCrossingSubarrayLinearScored left right with
    | none => True
    | some best => best.2 = subarraySum best.1 := by
  have hsuffix := maxSuffixLinearScored_sum left
  have hprefix := maxPrefixLinearScored_sum right
  cases hs : maxSuffixLinearScored left <;>
    cases hp : maxPrefixLinearScored right <;>
      simp_all [maxCrossingSubarrayLinearScored, subarraySum, List.sum_append]

/-- Strong crossing contract for the cached-score execution. -/
theorem maxCrossingSubarrayLinearScored_result_correct
    (left right : List Int) :
    match maxCrossingSubarrayLinearScored left right with
    | none => ∀ cand, ¬ IsCrossingSubarray cand left right
    | some best =>
        IsCrossingSubarray best.1 left right ∧
          best.2 = subarraySum best.1 ∧
            ∀ cand, IsCrossingSubarray cand left right →
              subarraySum cand ≤ best.2 := by
  have hresult := maxCrossingSubarrayLinearScored_result left right
  have hsum := maxCrossingSubarrayLinearScored_sum left right
  cases hcross : maxCrossingSubarrayLinearScored left right with
  | none =>
      rw [hcross] at hresult hsum
      have hplain := maxCrossingSubarrayLinear_result_correct left right
      have hnone : maxCrossingSubarrayLinear left right = none := by
        simpa using hresult.symm
      rw [hnone] at hplain
      exact hplain
  | some best =>
      rw [hcross] at hresult hsum
      have hplain := maxCrossingSubarrayLinear_result_correct left right
      have hsome : maxCrossingSubarrayLinear left right = some best.1 := by
        simpa using hresult.symm
      rw [hsome] at hplain
      exact ⟨hplain.1, hsum, fun cand hcand =>
        le_trans (hplain.2 cand hcand) (le_of_eq hsum.symm)⟩

/-! ## Maximum-subarray selector -/

/--
Exhaustively choose a maximum-sum nonempty contiguous subarray.  Empty inputs
have no nonempty candidate and therefore return {lit}`none`.
-/
def maxSubarray (xs : List Int) : Option (List Int) :=
  bestCandidate (nonemptySubarrays xs)

/-- The selector returns {lit}`none` on the empty input. -/
theorem maxSubarray_nil :
    maxSubarray [] = none := by
  rfl

/-- Nonempty inputs have at least one nonempty contiguous-subarray candidate. -/
theorem maxSubarray_exists_of_ne_nil {xs : List Int} (hxs : xs ≠ []) :
    ∃ best, maxSubarray xs = some best := by
  cases xs with
  | nil =>
      exact False.elim (hxs rfl)
  | cons x xs =>
      unfold maxSubarray
      apply bestCandidate_exists_of_ne_nil
      simp [nonemptySubarrays, nonemptyPrefixes]

/--
Correctness of the maximum-subarray selector: whenever it returns a candidate,
that candidate is a nonempty contiguous subarray and has maximum sum among all
nonempty contiguous subarrays of the input.
-/
theorem maxSubarray_correct {xs best : List Int}
    (hbest : maxSubarray xs = some best) :
    IsNonemptySubarray best xs ∧
      ∀ cand, IsNonemptySubarray cand xs →
        subarraySum cand ≤ subarraySum best := by
  unfold maxSubarray at hbest
  rcases bestCandidate_correct hbest with ⟨hbestMem, hbestOptimal⟩
  constructor
  · exact mem_nonemptySubarrays_iff.mp hbestMem
  · intro cand hcand
    exact hbestOptimal cand (mem_nonemptySubarrays_iff.mpr hcand)

/-- If the exhaustive selector returns no candidate, no nonempty subarray exists. -/
theorem maxSubarray_none_no_subarray {xs : List Int}
    (hbest : maxSubarray xs = none) :
    ∀ cand, ¬ IsNonemptySubarray cand xs := by
  intro cand hcand
  have hcandMem : cand ∈ nonemptySubarrays xs :=
    mem_nonemptySubarrays_iff.mpr hcand
  have hcandidates : nonemptySubarrays xs ≠ [] := by
    intro hnil
    simp [hnil] at hcandMem
  rcases bestCandidate_exists_of_ne_nil hcandidates with ⟨best, hsome⟩
  unfold maxSubarray at hbest
  rw [hbest] at hsome
  contradiction

/--
Unified result specification for maximum-subarray selectors.

Returning {lit}`none` means that there is no nonempty contiguous subarray.
Returning {lit}`some best` means that {lit}`best` is a valid candidate whose
sum dominates every valid candidate.
-/
def IsMaxSubarrayResult (xs : List Int) : Option (List Int) → Prop
  | none => ∀ cand, ¬ IsNonemptySubarray cand xs
  | some best =>
      IsNonemptySubarray best xs ∧
        ∀ cand, IsNonemptySubarray cand xs →
          subarraySum cand ≤ subarraySum best

/-- The exhaustive selector satisfies the unified result specification. -/
theorem maxSubarray_result_correct (xs : List Int) :
    IsMaxSubarrayResult xs (maxSubarray xs) := by
  cases hbest : maxSubarray xs with
  | none =>
      exact maxSubarray_none_no_subarray hbest
  | some best =>
      exact maxSubarray_correct hbest

/-! ## Cached-score maximum-subarray results -/

/--
Maximum-subarray correctness with an additional invariant saying that the
cached score is exactly the returned list's sum.
-/
def IsScoredMaxSubarrayResult
    (xs : List Int) : Option ScoredSubarray → Prop
  | none => ∀ cand, ¬ IsNonemptySubarray cand xs
  | some best =>
      IsNonemptySubarray best.1 xs ∧
        best.2 = subarraySum best.1 ∧
          ∀ cand, IsNonemptySubarray cand xs → subarraySum cand ≤ best.2

/-- Erasing a valid cached score gives the ordinary maximum-subarray result. -/
theorem IsScoredMaxSubarrayResult.erase {xs : List Int}
    {result : Option ScoredSubarray}
    (hresult : IsScoredMaxSubarrayResult xs result) :
    IsMaxSubarrayResult xs (result.map Prod.fst) := by
  cases result with
  | none =>
      exact hresult
  | some best =>
      exact ⟨hresult.1, fun cand hcand => by
        rw [← hresult.2.1]
        exact hresult.2.2 cand hcand⟩

/-- Choose the candidate with larger cached score, breaking ties to the first. -/
def betterScoredCandidate (a b : ScoredSubarray) : ScoredSubarray :=
  if a.2 < b.2 then b else a

/-- Finite maximum selector using cached candidate sums. -/
def bestScoredCandidate : List ScoredSubarray → Option ScoredSubarray
  | [] => none
  | candidate :: rest =>
      match bestScoredCandidate rest with
      | none => some candidate
      | some best => some (betterScoredCandidate candidate best)

/-- The cached-score selector returns a member with maximal cached score. -/
theorem bestScoredCandidate_correct
    {candidates : List ScoredSubarray} {best : ScoredSubarray}
    (hbest : bestScoredCandidate candidates = some best) :
    best ∈ candidates ∧
      ∀ candidate, candidate ∈ candidates → candidate.2 ≤ best.2 := by
  induction candidates generalizing best with
  | nil =>
      simp [bestScoredCandidate] at hbest
  | cons candidate rest ih =>
      simp only [bestScoredCandidate] at hbest
      cases hrest : bestScoredCandidate rest with
      | none =>
          have hrestNil : rest = [] := by
            cases rest with
            | nil => rfl
            | cons next tail =>
                cases htail : bestScoredCandidate tail <;>
                  simp [bestScoredCandidate, htail] at hrest
          subst rest
          have heq : candidate = best := by
            exact Option.some.inj (by simpa [bestScoredCandidate] using hbest)
          subst best
          simp
      | some restBest =>
          simp [hrest] at hbest
          have hrestCorrect := ih hrest
          by_cases hlt : candidate.2 < restBest.2
          · simp [betterScoredCandidate, hlt] at hbest
            subst best
            constructor
            · simp [hrestCorrect.1]
            · intro other hother
              simp at hother
              rcases hother with rfl | hin
              · exact le_of_lt hlt
              · exact hrestCorrect.2 other hin
          · simp [betterScoredCandidate, hlt] at hbest
            subst best
            constructor
            · simp
            · intro other hother
              simp at hother
              rcases hother with rfl | hin
              · exact le_rfl
              · exact le_trans (hrestCorrect.2 other hin) (le_of_not_gt hlt)

/-- A missing cached-score winner implies an empty candidate list. -/
theorem bestScoredCandidate_none_eq_nil {candidates : List ScoredSubarray}
    (hbest : bestScoredCandidate candidates = none) : candidates = [] := by
  cases candidates with
  | nil => rfl
  | cons candidate rest =>
      cases hrest : bestScoredCandidate rest <;>
        simp [bestScoredCandidate, hrest] at hbest

/--
Combine the recursive left and right winners with the linear crossing winner,
using only their cached sums for the final constant-size choice.
-/
def maxSubarrayCombineLinearScored (left right : List Int)
    (leftBest rightBest : Option ScoredSubarray) : Option ScoredSubarray :=
  bestScoredCandidate
    (leftBest.toList ++ rightBest.toList ++
      (maxCrossingSubarrayLinearScored left right).toList)

/-- The cached-score linear combine step preserves the full result contract. -/
theorem maxSubarrayCombineLinearScored_result_correct
    {left right : List Int} {leftBest rightBest : Option ScoredSubarray}
    (hleft : IsScoredMaxSubarrayResult left leftBest)
    (hright : IsScoredMaxSubarrayResult right rightBest) :
    IsScoredMaxSubarrayResult (left ++ right)
      (maxSubarrayCombineLinearScored left right leftBest rightBest) := by
  cases hbest :
      maxSubarrayCombineLinearScored left right leftBest rightBest with
  | none =>
      unfold maxSubarrayCombineLinearScored at hbest
      have hnil := bestScoredCandidate_none_eq_nil hbest
      simp at hnil
      rcases hnil with ⟨hleftNone, hrightNone, hcrossNone⟩
      intro cand hcand
      rcases subarray_append_left_or_right_or_crossing hcand with
        hcandLeft | hcandRight | hcandCross
      · rw [hleftNone] at hleft
        exact hleft cand hcandLeft
      · rw [hrightNone] at hright
        exact hright cand hcandRight
      · have hcross :=
          maxCrossingSubarrayLinearScored_result_correct left right
        rw [hcrossNone] at hcross
        exact hcross cand hcandCross
  | some best =>
      unfold maxSubarrayCombineLinearScored at hbest
      rcases bestScoredCandidate_correct hbest with
        ⟨hbestMem, hbestOptimal⟩
      have hbestCases :
          (IsNonemptySubarray best.1 left ∧
              best.2 = subarraySum best.1) ∨
            (IsNonemptySubarray best.1 right ∧
              best.2 = subarraySum best.1) ∨
            (IsCrossingSubarray best.1 left right ∧
              best.2 = subarraySum best.1) := by
        simp at hbestMem
        rcases hbestMem with hleftMem | hrightMem | hcrossMem
        · rw [hleftMem] at hleft
          exact Or.inl ⟨hleft.1, hleft.2.1⟩
        · rw [hrightMem] at hright
          exact Or.inr (Or.inl ⟨hright.1, hright.2.1⟩)
        · have hcrossBest :
              maxCrossingSubarrayLinearScored left right = some best := by
            simpa using hcrossMem
          have hcross :=
            maxCrossingSubarrayLinearScored_result_correct left right
          rw [hcrossBest] at hcross
          exact Or.inr (Or.inr ⟨hcross.1, hcross.2.1⟩)
      have hvalid : IsNonemptySubarray best.1 (left ++ right) := by
        rcases hbestCases with hleftBest | hrightBest | hcrossBest
        · exact isNonemptySubarray_append_left hleftBest.1
        · exact isNonemptySubarray_append_right (left := left) hrightBest.1
        · exact crossingSubarray_isNonemptySubarray_append hcrossBest.1
      have hscore : best.2 = subarraySum best.1 := by
        rcases hbestCases with hleftBest | hrightBest | hcrossBest
        · exact hleftBest.2
        · exact hrightBest.2
        · exact hcrossBest.2
      refine ⟨hvalid, hscore, ?_⟩
      intro cand hcand
      rcases subarray_append_left_or_right_or_crossing hcand with
        hcandLeft | hcandRight | hcandCross
      · cases hleftBest : leftBest with
        | none =>
            rw [hleftBest] at hleft
            exact False.elim (hleft cand hcandLeft)
        | some leftWinner =>
            rw [hleftBest] at hleft
            have hwinnerMem :
                leftWinner ∈
                  leftBest.toList ++ rightBest.toList ++
                    (maxCrossingSubarrayLinearScored left right).toList := by
              simp [hleftBest]
            exact le_trans (hleft.2.2 cand hcandLeft)
              (hbestOptimal leftWinner hwinnerMem)
      · cases hrightBest : rightBest with
        | none =>
            rw [hrightBest] at hright
            exact False.elim (hright cand hcandRight)
        | some rightWinner =>
            rw [hrightBest] at hright
            have hwinnerMem :
                rightWinner ∈
                  leftBest.toList ++ rightBest.toList ++
                    (maxCrossingSubarrayLinearScored left right).toList := by
              simp [hrightBest]
            exact le_trans (hright.2.2 cand hcandRight)
              (hbestOptimal rightWinner hwinnerMem)
      · cases hcrossBest : maxCrossingSubarrayLinearScored left right with
        | none =>
            have hcross :=
              maxCrossingSubarrayLinearScored_result_correct left right
            rw [hcrossBest] at hcross
            exact False.elim (hcross cand hcandCross)
        | some crossWinner =>
            have hcross :=
              maxCrossingSubarrayLinearScored_result_correct left right
            rw [hcrossBest] at hcross
            have hwinnerMem :
                crossWinner ∈
                  leftBest.toList ++ rightBest.toList ++
                    (maxCrossingSubarrayLinearScored left right).toList := by
              simp [hcrossBest]
            exact le_trans (hcross.2.2 cand hcandCross)
              (hbestOptimal crossWinner hwinnerMem)

/-! ## Executable divide-and-conquer combine step -/

/--
Combine already-computed left and right winners with the crossing winner.

This is the local executable step used both by {lit}`maxSubarrayDivideStep` and
by the recursive split-tree selector below.
-/
def maxSubarrayCombineOptions (left right : List Int)
    (leftBest rightBest : Option (List Int)) : Option (List Int) :=
  bestCandidate
    (leftBest.toList ++ rightBest.toList ++
      (maxCrossingSubarray left right).toList)

/-- The local combine step preserves the maximum-subarray result contract. -/
theorem maxSubarrayCombineOptions_result_correct {left right : List Int}
    {leftBest rightBest : Option (List Int)}
    (hleft : IsMaxSubarrayResult left leftBest)
    (hright : IsMaxSubarrayResult right rightBest) :
    IsMaxSubarrayResult (left ++ right)
      (maxSubarrayCombineOptions left right leftBest rightBest) := by
  cases hbest :
      maxSubarrayCombineOptions left right leftBest rightBest with
  | none =>
      unfold maxSubarrayCombineOptions at hbest
      have hnil := bestCandidate_none_eq_nil hbest
      simp at hnil
      rcases hnil with ⟨hleftNone, hrightNone, hcrossNone⟩
      intro cand hcand
      rcases subarray_append_left_or_right_or_crossing hcand with
        hcandLeft | hcandRight | hcandCross
      · rw [hleftNone] at hleft
        exact hleft cand hcandLeft
      · rw [hrightNone] at hright
        exact hright cand hcandRight
      · exact maxCrossingSubarray_none_no_crossing hcrossNone cand hcandCross
  | some best =>
      unfold maxSubarrayCombineOptions at hbest
      rcases bestCandidate_correct hbest with ⟨hbestMem, hbestOptimal⟩
      have hbestCases :
          IsNonemptySubarray best left ∨
            IsNonemptySubarray best right ∨ IsCrossingSubarray best left right := by
        simp at hbestMem
        rcases hbestMem with hleftMem | hrightMem | hcrossMem
        · rw [hleftMem] at hleft
          exact Or.inl hleft.1
        · rw [hrightMem] at hright
          exact Or.inr (Or.inl hright.1)
        · have hcrossBest : maxCrossingSubarray left right = some best := by
            simpa using hcrossMem
          exact Or.inr (Or.inr (maxCrossingSubarray_correct hcrossBest).1)
      constructor
      · rcases hbestCases with hleftSub | hrightSub | hcrossSub
        · exact isNonemptySubarray_append_left hleftSub
        · exact isNonemptySubarray_append_right (left := left) hrightSub
        · exact crossingSubarray_isNonemptySubarray_append hcrossSub
      · apply subarray_append_optimal_of_cases
        · intro cand hcandLeft
          cases hleftBest : leftBest with
          | none =>
              rw [hleftBest] at hleft
              exact False.elim (hleft cand hcandLeft)
          | some leftWinner =>
              rw [hleftBest] at hleft
              have hcandLeLeftWinner := hleft.2 cand hcandLeft
              have hleftWinnerMem :
                  leftWinner ∈
                    leftBest.toList ++ rightBest.toList ++
                      (maxCrossingSubarray left right).toList := by
                simp [hleftBest]
              exact le_trans hcandLeLeftWinner
                (hbestOptimal leftWinner hleftWinnerMem)
        · intro cand hcandRight
          cases hrightBest : rightBest with
          | none =>
              rw [hrightBest] at hright
              exact False.elim (hright cand hcandRight)
          | some rightWinner =>
              rw [hrightBest] at hright
              have hcandLeRightWinner := hright.2 cand hcandRight
              have hrightWinnerMem :
                  rightWinner ∈
                    leftBest.toList ++ rightBest.toList ++
                      (maxCrossingSubarray left right).toList := by
                simp [hrightBest]
              exact le_trans hcandLeRightWinner
                (hbestOptimal rightWinner hrightWinnerMem)
        · intro cand hcandCross
          cases hcrossBest : maxCrossingSubarray left right with
          | none =>
              exact False.elim
                (maxCrossingSubarray_none_no_crossing hcrossBest cand hcandCross)
          | some crossWinner =>
              have hcrossCorrect := maxCrossingSubarray_correct hcrossBest
              have hcandLeCrossWinner := hcrossCorrect.2 cand hcandCross
              have hcrossWinnerMem :
                  crossWinner ∈
                    leftBest.toList ++ rightBest.toList ++
                      (maxCrossingSubarray left right).toList := by
                simp [hcrossBest]
              exact le_trans hcandLeCrossWinner
                (hbestOptimal crossWinner hcrossWinnerMem)

/--
One executable CLRS divide-and-conquer combine step.

The left and right subproblems are solved by the already-proved exact selector,
and the crossing case is solved by {lit}`maxCrossingSubarray`.  The step then
selects the best among the available local winners.
-/
def maxSubarrayDivideStep (left right : List Int) : Option (List Int) :=
  maxSubarrayCombineOptions left right (maxSubarray left) (maxSubarray right)

/--
Correctness of the executable divide-and-conquer combine step: whenever it
returns a candidate, that candidate is a nonempty subarray of the concatenated
input and dominates every nonempty subarray of that input.
-/
theorem maxSubarrayDivideStep_correct {left right best : List Int}
    (hbest : maxSubarrayDivideStep left right = some best) :
    IsNonemptySubarray best (left ++ right) ∧
      ∀ cand, IsNonemptySubarray cand (left ++ right) →
        subarraySum cand ≤ subarraySum best := by
  have hresult :=
    maxSubarrayCombineOptions_result_correct
      (left := left) (right := right)
      (leftBest := maxSubarray left) (rightBest := maxSubarray right)
      (maxSubarray_result_correct left) (maxSubarray_result_correct right)
  unfold maxSubarrayDivideStep at hbest
  rw [hbest] at hresult
  exact hresult

/-! ## Recursive divide-and-conquer selector -/

/--
An explicit split tree for divide-and-conquer maximum-subarray selection.

Leaves are solved directly by the exact selector.  Internal nodes combine the
recursive winners from the left and right children with the crossing helper.
-/
inductive SubarraySplitTree where
  | leaf (xs : List Int)
  | split (left right : SubarraySplitTree)

namespace SubarraySplitTree

/-- The input list represented by a split tree. -/
def input : SubarraySplitTree → List Int
  | leaf xs => xs
  | split left right => input left ++ input right

end SubarraySplitTree

/-- Recursive divide-and-conquer selector over an explicit split tree. -/
def maxSubarrayDivideTree : SubarraySplitTree → Option (List Int)
  | .leaf xs => maxSubarray xs
  | .split left right =>
      maxSubarrayCombineOptions left.input right.input
        (maxSubarrayDivideTree left) (maxSubarrayDivideTree right)

/-- The recursive split-tree selector satisfies the maximum-subarray contract. -/
theorem maxSubarrayDivideTree_result_correct (tree : SubarraySplitTree) :
    IsMaxSubarrayResult tree.input (maxSubarrayDivideTree tree) := by
  induction tree with
  | leaf xs =>
      exact maxSubarray_result_correct xs
  | split left right hleft hright =>
      exact maxSubarrayCombineOptions_result_correct hleft hright

/--
Correctness of the recursive split-tree selector: whenever it returns a
candidate, that candidate is globally optimal for the input represented by the
tree.
-/
theorem maxSubarrayDivideTree_correct {tree : SubarraySplitTree} {best : List Int}
    (hbest : maxSubarrayDivideTree tree = some best) :
    IsNonemptySubarray best tree.input ∧
      ∀ cand, IsNonemptySubarray cand tree.input →
        subarraySum cand ≤ subarraySum best := by
  have hresult := maxSubarrayDivideTree_result_correct tree
  rw [hbest] at hresult
  exact hresult

/--
Build a split tree by repeatedly splitting at the midpoint, for at most
{lit}`fuel` recursive levels.  When fuel runs out, the remaining chunk becomes a
leaf and is solved by the exact selector.
-/
def midpointSplitTree : Nat → List Int → SubarraySplitTree
  | 0, xs => .leaf xs
  | _fuel + 1, [] => .leaf []
  | _fuel + 1, [x] => .leaf [x]
  | fuel + 1, xs =>
      let mid := xs.length / 2
      .split (midpointSplitTree fuel (xs.take mid))
        (midpointSplitTree fuel (xs.drop mid))

/-- The fuelled midpoint split tree represents exactly the original input. -/
theorem midpointSplitTree_input (fuel : Nat) (xs : List Int) :
    (midpointSplitTree fuel xs).input = xs := by
  induction fuel generalizing xs with
  | zero =>
      rfl
  | succ fuel ih =>
      cases xs with
      | nil =>
          rfl
      | cons x xs =>
          cases xs with
          | nil =>
              rfl
          | cons y ys =>
              simp [midpointSplitTree, SubarraySplitTree.input, ih,
                List.take_append_drop]

/--
A fuelled executable divide-and-conquer selector.  Correctness holds for every
fuel value; larger fuel simply refines more leaves before falling back to the
exact selector.
-/
def maxSubarrayDivideFuel (fuel : Nat) (xs : List Int) : Option (List Int) :=
  maxSubarrayDivideTree (midpointSplitTree fuel xs)

/--
Correctness of the fuelled midpoint divide-and-conquer selector for the
original list input.
-/
theorem maxSubarrayDivideFuel_correct {fuel : Nat} {xs best : List Int}
    (hbest : maxSubarrayDivideFuel fuel xs = some best) :
    IsNonemptySubarray best xs ∧
      ∀ cand, IsNonemptySubarray cand xs →
        subarraySum cand ≤ subarraySum best := by
  have htree :=
    maxSubarrayDivideTree_correct
      (tree := midpointSplitTree fuel xs) (best := best) hbest
  simpa [maxSubarrayDivideFuel, midpointSplitTree_input] using htree

/-! ## Fully expanded linear divide-and-conquer execution -/

namespace SubarraySplitTree

/-- Every terminal problem in the tree has size at most one. -/
def UnitLeaves : SubarraySplitTree → Prop
  | .leaf xs => xs.length ≤ 1
  | .split left right => left.UnitLeaves ∧ right.UnitLeaves

end SubarraySplitTree

/-- Sufficient midpoint-splitting fuel leaves only empty or singleton inputs. -/
theorem midpointSplitTree_unitLeaves (fuel : Nat) (xs : List Int)
    (hfuel : xs.length ≤ fuel) :
    (midpointSplitTree fuel xs).UnitLeaves := by
  induction fuel generalizing xs with
  | zero =>
      have hnil : xs = [] := by
        apply List.eq_nil_of_length_eq_zero
        omega
      subst xs
      simp [midpointSplitTree, SubarraySplitTree.UnitLeaves]
  | succ fuel ih =>
      cases xs with
      | nil =>
          simp [midpointSplitTree, SubarraySplitTree.UnitLeaves]
      | cons x xs =>
          cases xs with
          | nil =>
              simp [midpointSplitTree, SubarraySplitTree.UnitLeaves]
          | cons y ys =>
              simp only [List.length_cons] at hfuel
              have hmidLt : (ys.length + 2) / 2 < ys.length + 2 :=
                Nat.div_lt_self (by omega) (by norm_num)
              have hmidPos : 0 < (ys.length + 2) / 2 :=
                Nat.div_pos (by omega) (by norm_num)
              have hdropLt :
                  (ys.length + 2) - (ys.length + 2) / 2 < ys.length + 2 :=
                Nat.sub_lt (by omega) hmidPos
              simp only [midpointSplitTree, SubarraySplitTree.UnitLeaves]
              constructor
              · apply ih
                simp only [List.length_take, List.length_cons]
                omega
              · apply ih
                simp only [List.length_drop, List.length_cons]
                omega

/-- Solve an empty or singleton leaf without invoking exhaustive enumeration. -/
def singletonMaxSubarrayScored : List Int → Option ScoredSubarray
  | [] => none
  | x :: _ => some ([x], x)

/-- Erase the cached score from the singleton leaf solver. -/
def singletonMaxSubarray (xs : List Int) : Option (List Int) :=
  (singletonMaxSubarrayScored xs).map Prod.fst

/-- The singleton leaf solver is correct whenever the leaf invariant holds. -/
theorem singletonMaxSubarrayScored_result_correct {xs : List Int}
    (hunit : xs.length ≤ 1) :
    IsScoredMaxSubarrayResult xs (singletonMaxSubarrayScored xs) := by
  cases xs with
  | nil =>
      change ∀ cand, ¬ IsNonemptySubarray cand []
      exact maxSubarray_none_no_subarray (by rfl)
  | cons x tail =>
      have htail : tail = [] := by
        apply List.eq_nil_of_length_eq_zero
        simp only [List.length_cons] at hunit
        omega
      subst tail
      have hplain := maxSubarray_result_correct [x]
      have hmax : maxSubarray [x] = some [x] := by rfl
      rw [hmax] at hplain
      exact ⟨hplain.1, by simp [subarraySum], fun cand hcand => by
        simpa [subarraySum] using hplain.2 cand hcand⟩

/-- Erased singleton execution satisfies the ordinary result specification. -/
theorem singletonMaxSubarray_result_correct {xs : List Int}
    (hunit : xs.length ≤ 1) :
    IsMaxSubarrayResult xs (singletonMaxSubarray xs) := by
  have hscored := singletonMaxSubarrayScored_result_correct hunit
  simpa [singletonMaxSubarray] using hscored.erase

/--
Recursive maximum-subarray execution over a split tree.  Cached sums flow from
children to the constant-size combine choice, and crossing candidates come
from the accumulated-sum linear scan.
-/
def maxSubarrayDivideTreeScored : SubarraySplitTree → Option ScoredSubarray
  | .leaf xs => singletonMaxSubarrayScored xs
  | .split left right =>
      maxSubarrayCombineLinearScored left.input right.input
        (maxSubarrayDivideTreeScored left)
        (maxSubarrayDivideTreeScored right)

/-- The cached-score split-tree execution satisfies the maximum contract. -/
theorem maxSubarrayDivideTreeScored_result_correct
    {tree : SubarraySplitTree} (hunit : tree.UnitLeaves) :
    IsScoredMaxSubarrayResult tree.input
      (maxSubarrayDivideTreeScored tree) := by
  induction tree with
  | leaf xs =>
      exact singletonMaxSubarrayScored_result_correct hunit
  | split left right hleft hright =>
      exact maxSubarrayCombineLinearScored_result_correct
        (hleft hunit.1) (hright hunit.2)

/--
Top-level executable divide-and-conquer maximum-subarray selector.  Splitting
continues until all terminal inputs have length at most one.
-/
def maxSubarrayDivide (xs : List Int) : Option (List Int) :=
  (maxSubarrayDivideTreeScored (midpointSplitTree xs.length xs)).map Prod.fst

/-- The fully expanded linear divide-and-conquer selector is correct. -/
theorem maxSubarrayDivide_result_correct (xs : List Int) :
    IsMaxSubarrayResult xs (maxSubarrayDivide xs) := by
  have hunit := midpointSplitTree_unitLeaves xs.length xs (le_refl xs.length)
  have hscored := maxSubarrayDivideTreeScored_result_correct hunit
  have herased := hscored.erase
  simpa [maxSubarrayDivide, midpointSplitTree_input] using herased

/-! ## Costed linear scans and recursive execution -/

/-- Running-prefix-score construction paired with visited input cells. -/
def prefixScoresAuxWithCost :
    List Int → Int → Nat → List PrefixScore × Nat
  | [], _, _ => ([], 0)
  | x :: xs, total, len =>
      let rest := prefixScoresAuxWithCost xs (total + x) (len + 1)
      ((total + x, len + 1) :: rest.1, rest.2 + 1)

/-- Erasing the transition count recovers running-prefix-score construction. -/
theorem prefixScoresAuxWithCost_result
    (xs : List Int) (total : Int) (len : Nat) :
    (prefixScoresAuxWithCost xs total len).1 =
      prefixScoresAux xs total len := by
  induction xs generalizing total len with
  | nil => rfl
  | cons x xs ih =>
      simp [prefixScoresAuxWithCost, prefixScoresAux, ih]

/-- Running-prefix-score construction visits each input cell exactly once. -/
theorem prefixScoresAuxWithCost_cost
    (xs : List Int) (total : Int) (len : Nat) :
    (prefixScoresAuxWithCost xs total len).2 = xs.length := by
  induction xs generalizing total len with
  | nil => rfl
  | cons x xs ih =>
      simp [prefixScoresAuxWithCost, ih]

/-- Top-level costed running-prefix-score construction. -/
def prefixScoresWithCost (xs : List Int) : List PrefixScore × Nat :=
  prefixScoresAuxWithCost xs 0 0

theorem prefixScoresWithCost_result (xs : List Int) :
    (prefixScoresWithCost xs).1 = prefixScores xs := by
  exact prefixScoresAuxWithCost_result xs 0 0

theorem prefixScoresWithCost_cost (xs : List Int) :
    (prefixScoresWithCost xs).2 = xs.length := by
  exact prefixScoresAuxWithCost_cost xs 0 0

/-- The running-prefix-score list contains one record per input element. -/
theorem prefixScoresAux_length
    (xs : List Int) (total : Int) (len : Nat) :
    (prefixScoresAux xs total len).length = xs.length := by
  induction xs generalizing total len with
  | nil => rfl
  | cons x xs ih =>
      simp [prefixScoresAux, ih]

theorem prefixScores_length (xs : List Int) :
    (prefixScores xs).length = xs.length := by
  exact prefixScoresAux_length xs 0 0

/-- Maximum-score selection paired with visited score records. -/
def bestPrefixScoreWithCost :
    List PrefixScore → Option PrefixScore × Nat
  | [] => (none, 0)
  | score :: rest =>
      let next := bestPrefixScoreWithCost rest
      match next.1 with
      | none => (some score, next.2 + 1)
      | some best => (some (betterPrefixScore score best), next.2 + 1)

/-- Erasing the transition count recovers maximum-score selection. -/
theorem bestPrefixScoreWithCost_result (scores : List PrefixScore) :
    (bestPrefixScoreWithCost scores).1 = bestPrefixScore scores := by
  induction scores with
  | nil => rfl
  | cons score rest ih =>
      simp only [bestPrefixScoreWithCost, bestPrefixScore]
      rw [ih]
      split <;> rfl

/-- Maximum-score selection visits each score record exactly once. -/
theorem bestPrefixScoreWithCost_cost (scores : List PrefixScore) :
    (bestPrefixScoreWithCost scores).2 = scores.length := by
  induction scores with
  | nil => rfl
  | cons score rest ih =>
      simp only [bestPrefixScoreWithCost]
      split <;> simp [ih]

/-- Linear prefix selection with an execution-attached control-step count. -/
def maxPrefixLinearScoredWithCost
    (xs : List Int) : Option ScoredSubarray × Nat :=
  let scores := prefixScoresWithCost xs
  let best := bestPrefixScoreWithCost scores.1
  let result := match best.1 with
    | none => none
    | some winner => some (xs.take winner.2, winner.1)
  (result, scores.2 + best.2 + 1)

/-- Erasing cost recovers cached-score linear prefix selection. -/
theorem maxPrefixLinearScoredWithCost_result (xs : List Int) :
    (maxPrefixLinearScoredWithCost xs).1 = maxPrefixLinearScored xs := by
  simp only [maxPrefixLinearScoredWithCost]
  unfold maxPrefixLinearScored
  rw [prefixScoresWithCost_result, bestPrefixScoreWithCost_result]

/-- Prefix selection performs two length-many scans and one wrapper step. -/
theorem maxPrefixLinearScoredWithCost_cost (xs : List Int) :
    (maxPrefixLinearScoredWithCost xs).2 = 2 * xs.length + 1 := by
  simp only [maxPrefixLinearScoredWithCost]
  rw [prefixScoresWithCost_cost, bestPrefixScoreWithCost_cost,
    prefixScoresWithCost_result, prefixScores_length]
  omega

/-- Reverse-prefix suffix selection with an execution-attached count. -/
def maxSuffixLinearScoredWithCost
    (xs : List Int) : Option ScoredSubarray × Nat :=
  let prefixRun := maxPrefixLinearScoredWithCost xs.reverse
  (prefixRun.1.map (fun best => (best.1.reverse, best.2)),
    prefixRun.2 + xs.length + 1)

/-- Erasing cost recovers cached-score linear suffix selection. -/
theorem maxSuffixLinearScoredWithCost_result (xs : List Int) :
    (maxSuffixLinearScoredWithCost xs).1 = maxSuffixLinearScored xs := by
  simp only [maxSuffixLinearScoredWithCost]
  unfold maxSuffixLinearScored
  rw [maxPrefixLinearScoredWithCost_result]

/-- Suffix selection charges the reverse traversal and the two prefix scans. -/
theorem maxSuffixLinearScoredWithCost_cost (xs : List Int) :
    (maxSuffixLinearScoredWithCost xs).2 = 3 * xs.length + 2 := by
  simp only [maxSuffixLinearScoredWithCost]
  rw [maxPrefixLinearScoredWithCost_cost, List.length_reverse]
  omega

/-- Linear crossing selection with execution-attached scan costs. -/
def maxCrossingSubarrayLinearScoredWithCost
    (left right : List Int) : Option ScoredSubarray × Nat :=
  let suffix := maxSuffixLinearScoredWithCost left
  let prefixRun := maxPrefixLinearScoredWithCost right
  let result := match suffix.1, prefixRun.1 with
    | some suf, some pre => some (suf.1 ++ pre.1, suf.2 + pre.2)
    | _, _ => none
  (result, suffix.2 + prefixRun.2 + 1)

/-- Erasing cost recovers cached-score linear crossing selection. -/
theorem maxCrossingSubarrayLinearScoredWithCost_result
    (left right : List Int) :
    (maxCrossingSubarrayLinearScoredWithCost left right).1 =
      maxCrossingSubarrayLinearScored left right := by
  simp only [maxCrossingSubarrayLinearScoredWithCost]
  unfold maxCrossingSubarrayLinearScored
  rw [maxSuffixLinearScoredWithCost_result,
    maxPrefixLinearScoredWithCost_result]

/-- The crossing execution has a concrete linear cost in both input lengths. -/
theorem maxCrossingSubarrayLinearScoredWithCost_cost
    (left right : List Int) :
    (maxCrossingSubarrayLinearScoredWithCost left right).2 =
      3 * left.length + 2 * right.length + 4 := by
  simp only [maxCrossingSubarrayLinearScoredWithCost]
  rw [maxSuffixLinearScoredWithCost_cost,
    maxPrefixLinearScoredWithCost_cost]
  omega

/-- Costed split-tree execution using the costed linear crossing scan. -/
def maxSubarrayDivideTreeCosted :
    SubarraySplitTree → Option ScoredSubarray × Nat
  | .leaf xs => (singletonMaxSubarrayScored xs, 1)
  | .split left right =>
      let leftRun := maxSubarrayDivideTreeCosted left
      let rightRun := maxSubarrayDivideTreeCosted right
      let crossing := maxCrossingSubarrayLinearScoredWithCost
        left.input right.input
      let result := bestScoredCandidate
        (leftRun.1.toList ++ rightRun.1.toList ++ crossing.1.toList)
      (result, leftRun.2 + rightRun.2 + crossing.2 + 1)

/-- Erasing tree-execution cost recovers the cached-score recursion. -/
theorem maxSubarrayDivideTreeCosted_result (tree : SubarraySplitTree) :
    (maxSubarrayDivideTreeCosted tree).1 =
      maxSubarrayDivideTreeScored tree := by
  induction tree with
  | leaf xs => rfl
  | split left right hleft hright =>
      simp only [maxSubarrayDivideTreeCosted,
        maxSubarrayDivideTreeScored]
      rw [hleft, hright,
        maxCrossingSubarrayLinearScoredWithCost_result]
      simp [maxSubarrayCombineLinearScored]

/-- Public costed execution, with cached sums erased from its result. -/
def maxSubarrayDivideCosted
    (xs : List Int) : Option (List Int) × Nat :=
  let run := maxSubarrayDivideTreeCosted
    (midpointSplitTree xs.length xs)
  (run.1.map Prod.fst, run.2)

/-- Erasing the public cost recovers the executable divide-and-conquer result. -/
theorem maxSubarrayDivideCosted_result (xs : List Int) :
    (maxSubarrayDivideCosted xs).1 = maxSubarrayDivide xs := by
  simp only [maxSubarrayDivideCosted]
  unfold maxSubarrayDivide
  rw [maxSubarrayDivideTreeCosted_result]

/-- The costed execution returns a correct maximum subarray. -/
theorem maxSubarrayDivideCosted_correct (xs : List Int) :
    IsMaxSubarrayResult xs (maxSubarrayDivideCosted xs).1 := by
  rw [maxSubarrayDivideCosted_result]
  exact maxSubarrayDivide_result_correct xs

/-- Structural control cost of a cached-score split-tree execution. -/
def maxSubarrayDivideTreeCost : SubarraySplitTree → Nat
  | .leaf _ => 1
  | .split left right =>
      maxSubarrayDivideTreeCost left + maxSubarrayDivideTreeCost right +
        3 * left.input.length + 2 * right.input.length + 5

/-- The cost component of tree execution is exactly its structural cost. -/
theorem maxSubarrayDivideTreeCosted_cost (tree : SubarraySplitTree) :
    (maxSubarrayDivideTreeCosted tree).2 =
      maxSubarrayDivideTreeCost tree := by
  induction tree with
  | leaf xs => rfl
  | split left right hleft hright =>
      simp only [maxSubarrayDivideTreeCosted,
        maxSubarrayDivideTreeCost]
      rw [hleft, hright,
        maxCrossingSubarrayLinearScoredWithCost_cost]
      omega

/--
Length-indexed cost of the fully expanded midpoint recursion.  For nontrivial
inputs the two recursive sizes are the actual floor and ceiling halves.
-/
def maxSubarrayDivideCost (n : Nat) : Nat :=
  if n ≤ 1 then
    1
  else
    maxSubarrayDivideCost (n / 2) +
      maxSubarrayDivideCost (n - n / 2) +
        3 * (n / 2) + 2 * (n - n / 2) + 5
termination_by n
decreasing_by
  · exact Nat.div_lt_self (by omega) (by norm_num)
  · exact Nat.sub_lt (by omega) (Nat.div_pos (by omega) (by norm_num))

/-- Base equation for empty and singleton inputs. -/
theorem maxSubarrayDivideCost_of_le_one {n : Nat} (hn : n ≤ 1) :
    maxSubarrayDivideCost n = 1 := by
  rw [maxSubarrayDivideCost]
  simp [hn]

/-- The exact mixed floor/ceiling recurrence on every nontrivial input. -/
theorem maxSubarrayDivideCost_unfold (n : Nat) (hn : 2 ≤ n) :
    maxSubarrayDivideCost n =
      maxSubarrayDivideCost (n / 2) +
        maxSubarrayDivideCost (n - n / 2) +
          3 * (n / 2) + 2 * (n - n / 2) + 5 := by
  rw [maxSubarrayDivideCost]
  simp [show ¬ n ≤ 1 by omega]

/--
Any sufficiently fuelled midpoint tree has the length-indexed structural cost.
-/
theorem maxSubarrayDivideTreeCost_midpoint
    (fuel : Nat) (xs : List Int) (hfuel : xs.length ≤ fuel) :
    maxSubarrayDivideTreeCost (midpointSplitTree fuel xs) =
      maxSubarrayDivideCost xs.length := by
  induction fuel generalizing xs with
  | zero =>
      have hnil : xs = [] := by
        apply List.eq_nil_of_length_eq_zero
        omega
      subst xs
      simp [midpointSplitTree, maxSubarrayDivideTreeCost,
        maxSubarrayDivideCost_of_le_one]
  | succ fuel ih =>
      cases xs with
      | nil =>
          simp [midpointSplitTree, maxSubarrayDivideTreeCost,
            maxSubarrayDivideCost_of_le_one]
      | cons x xs =>
          cases xs with
          | nil =>
              simp [midpointSplitTree, maxSubarrayDivideTreeCost,
                maxSubarrayDivideCost_of_le_one]
          | cons y ys =>
              simp only [List.length_cons] at hfuel
              have hlen : (x :: y :: ys).length = ys.length + 2 := by
                simp
              have hmidLt : (ys.length + 2) / 2 < ys.length + 2 :=
                Nat.div_lt_self (by omega) (by norm_num)
              have hmidPos : 0 < (ys.length + 2) / 2 :=
                Nat.div_pos (by omega) (by norm_num)
              have hdropLt :
                  (ys.length + 2) - (ys.length + 2) / 2 < ys.length + 2 :=
                Nat.sub_lt (by omega) hmidPos
              have htakeLen :
                  ((x :: y :: ys).take
                    ((x :: y :: ys).length / 2)).length =
                      (ys.length + 2) / 2 := by
                simp only [List.length_take, hlen]
                exact Nat.min_eq_left (Nat.le_of_lt hmidLt)
              have hdropLen :
                  ((x :: y :: ys).drop
                    ((x :: y :: ys).length / 2)).length =
                      (ys.length + 2) - (ys.length + 2) / 2 := by
                simp [List.length_drop, hlen]
              have htakeFuel :
                  ((x :: y :: ys).take
                    ((x :: y :: ys).length / 2)).length ≤ fuel := by
                simp only [List.length_take, List.length_cons]
                omega
              have hdropFuel :
                  ((x :: y :: ys).drop
                    ((x :: y :: ys).length / 2)).length ≤ fuel := by
                simp only [List.length_drop, List.length_cons]
                omega
              have htake := ih _ htakeFuel
              have hdrop := ih _ hdropFuel
              simp only [midpointSplitTree, maxSubarrayDivideTreeCost]
              rw [htake, hdrop]
              simp only [midpointSplitTree_input]
              rw [htakeLen, hdropLen, hlen]
              rw [maxSubarrayDivideCost_unfold (ys.length + 2) (by omega)]

/-- The public execution cost is exactly the real midpoint recurrence. -/
theorem maxSubarrayDivideCosted_cost (xs : List Int) :
    (maxSubarrayDivideCosted xs).2 = maxSubarrayDivideCost xs.length := by
  simp only [maxSubarrayDivideCosted]
  rw [maxSubarrayDivideTreeCosted_cost]
  exact maxSubarrayDivideTreeCost_midpoint xs.length xs (le_refl xs.length)

/-- Compatibility-facing name for the exact executable-cost equation. -/
theorem maxSubarrayDivideCosted_cost_eq (xs : List Int) :
    (maxSubarrayDivideCosted xs).2 = maxSubarrayDivideCost xs.length :=
  maxSubarrayDivideCosted_cost xs

/-! ## Runtime analysis

The measured execution makes recursive calls on the actual midpoint sizes
{lit}`⌊n/2⌋` and {lit}`⌈n/2⌉`.  Its per-node scan cost is linear.  Exact powers
of two therefore satisfy the usual case-2 bounds, and the all-input transfer
theorem yields {lit}`Θ(n log n)`.
-/

/-- The measured length cost is nondecreasing at each successor input. -/
theorem maxSubarrayDivideCost_le_succ :
    ∀ n, maxSubarrayDivideCost n ≤ maxSubarrayDivideCost (n + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hsmall : n ≤ 1
      · have hnCases : n = 0 ∨ n = 1 := by omega
        rcases hnCases with rfl | rfl
        · rw [maxSubarrayDivideCost_of_le_one (by norm_num),
            maxSubarrayDivideCost_of_le_one (by norm_num)]
        · rw [maxSubarrayDivideCost_of_le_one (by norm_num),
            maxSubarrayDivideCost_unfold 2 (by norm_num)]
          norm_num [maxSubarrayDivideCost_of_le_one]
      · have hn : 2 ≤ n := by omega
        have hfloorLt : n / 2 < n :=
          Nat.div_lt_self (by omega) (by norm_num)
        have hmidPos : 0 < n / 2 :=
          Nat.div_pos (by omega) (by norm_num)
        have hceilLt : n - n / 2 < n :=
          Nat.sub_lt (by omega) hmidPos
        have hfloorStep := ih (n / 2) hfloorLt
        have hceilStep := ih (n - n / 2) hceilLt
        rw [maxSubarrayDivideCost_unfold n hn,
          maxSubarrayDivideCost_unfold (n + 1) (by omega)]
        rcases (by omega :
            (n + 1) / 2 = n / 2 ∨ (n + 1) / 2 = n / 2 + 1) with
          hsame | hnext
        · rw [hsame]
          have hceilNext :
              (n + 1) - n / 2 = (n - n / 2) + 1 := by omega
          rw [hceilNext]
          omega
        · rw [hnext]
          have hceilSame :
              (n + 1) - (n / 2 + 1) = n - n / 2 := by omega
          rw [hceilSame]
          omega

/-- The measured length cost is monotone. -/
theorem maxSubarrayDivideCost_monotone : Monotone maxSubarrayDivideCost :=
  monotone_nat_of_le_succ maxSubarrayDivideCost_le_succ

/--
Every positive input cost is bounded by its two adjacent power-of-two costs.
-/
theorem maxSubarrayDivideCost_power_sandwich (n : Nat) (hn : 0 < n) :
    maxSubarrayDivideCost (2 ^ Nat.log 2 n) ≤ maxSubarrayDivideCost n ∧
      maxSubarrayDivideCost n ≤
        maxSubarrayDivideCost (2 ^ (Nat.log 2 n + 1)) := by
  rcases powerInterval_of_pos 2 n (by norm_num) hn.ne' with ⟨hlo, hhi⟩
  exact ⟨maxSubarrayDivideCost_monotone hlo,
    maxSubarrayDivideCost_monotone (Nat.le_of_lt hhi)⟩

/-- Real-valued view of the execution-attached natural control-step count. -/
def maxSubarrayDivideCostReal (n : Nat) : Real :=
  (maxSubarrayDivideCost n : Real)

/-- The real-valued execution cost satisfies the all-input monotonicity API. -/
theorem maxSubarrayDivideCostReal_monotoneAbs :
    MonotoneAbs maxSubarrayDivideCostReal := by
  intro m n hmn
  change |(maxSubarrayDivideCost m : Real)| ≤
    |(maxSubarrayDivideCost n : Real)|
  rw [abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast maxSubarrayDivideCost_monotone hmn

/-- Exact-power successor equation for the measured mixed recurrence. -/
theorem maxSubarrayDivideCost_pow_succ (k : Nat) :
    maxSubarrayDivideCost (2 ^ (k + 1)) =
      2 * maxSubarrayDivideCost (2 ^ k) + 5 * 2 ^ k + 5 := by
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by
    rw [pow_succ, Nat.mul_comm]
  have hpos : 2 ≤ 2 ^ (k + 1) := by
    rw [hpow]
    have : 0 < 2 ^ k := pow_pos (by norm_num) k
    omega
  rw [maxSubarrayDivideCost_unfold (2 ^ (k + 1)) hpos]
  rw [pow_succ_div_base (b := 2) (i := k) (by norm_num)]
  have hsub : 2 ^ (k + 1) - 2 ^ k = 2 ^ k := by
    rw [hpow]
    omega
  rw [hsub]
  omega

/-- Exact cost on powers of two, in a subtraction-free natural-number form. -/
theorem maxSubarrayDivideCost_pow_two (k : Nat) :
    2 * maxSubarrayDivideCost (2 ^ k) + 10 =
      (5 * k + 12) * 2 ^ k := by
  induction k with
  | zero =>
      rw [maxSubarrayDivideCost_of_le_one (by norm_num)]
      norm_num
  | succ k ih =>
      rw [maxSubarrayDivideCost_pow_succ, pow_succ]
      nlinarith

/-- Lower exact-power case-2 bound for the measured execution cost. -/
theorem maxSubarrayDivideCost_pow_lower (k : Nat) :
    (k + 1) * 2 ^ k ≤ maxSubarrayDivideCost (2 ^ k) := by
  induction k with
  | zero =>
      rw [maxSubarrayDivideCost_of_le_one (by norm_num)]
      norm_num
  | succ k ih =>
      rw [maxSubarrayDivideCost_pow_succ]
      rw [pow_succ]
      nlinarith [pow_pos (by norm_num : 0 < (2 : Nat)) k]

/-- Upper exact-power case-2 bound for the measured execution cost. -/
theorem maxSubarrayDivideCost_pow_upper (k : Nat) :
    maxSubarrayDivideCost (2 ^ k) ≤ 12 * (k + 1) * 2 ^ k := by
  induction k with
  | zero =>
      rw [maxSubarrayDivideCost_of_le_one (by norm_num)]
      norm_num
  | succ k ih =>
      rw [maxSubarrayDivideCost_pow_succ]
      rw [pow_succ]
      nlinarith [pow_pos (by norm_num : 0 < (2 : Nat)) k]

/-- Exact powers of the execution cost have the critical case-2 scale. -/
theorem maxSubarrayDivideCostReal_exactPowers_bigTheta :
    Chapter03.isBigTheta
      (fun k : Nat => maxSubarrayDivideCostReal (2 ^ k))
      (fun k : Nat => ((k : Real) + 1) * (2 : Real) ^ k) := by
  constructor
  · refine (Chapter03.isBigO_iff _ _).mpr
      ⟨12, by norm_num, 0, ?_⟩
    intro k _
    rw [abs_of_nonneg (Nat.cast_nonneg _),
      abs_of_nonneg (mul_nonneg (by positivity) (by positivity))]
    have h := maxSubarrayDivideCost_pow_upper k
    have hreal :
        (maxSubarrayDivideCost (2 ^ k) : Real) ≤
          (12 * (k + 1) * 2 ^ k : Nat) := by
      exact_mod_cast h
    simpa [maxSubarrayDivideCostReal, Nat.cast_mul, Nat.cast_add,
      Nat.cast_pow, mul_assoc] using hreal
  · change Chapter03.isBigO
      (fun k : Nat => ((k : Real) + 1) * (2 : Real) ^ k)
      (fun k : Nat => maxSubarrayDivideCostReal (2 ^ k))
    refine (Chapter03.isBigO_iff _ _).mpr
      ⟨1, by norm_num, 0, ?_⟩
    intro k _
    rw [abs_of_nonneg (mul_nonneg (by positivity) (by positivity)),
      abs_of_nonneg (Nat.cast_nonneg _)]
    have h := maxSubarrayDivideCost_pow_lower k
    have hreal :
        ((k + 1) * 2 ^ k : Nat) ≤
          (maxSubarrayDivideCost (2 ^ k) : Real) := by
      exact_mod_cast h
    simpa [maxSubarrayDivideCostReal, Nat.cast_mul, Nat.cast_add,
      Nat.cast_pow] using hreal

/--
**Runtime of the executable divide-and-conquer maximum-subarray algorithm.**
The abstract control-step count returned by {name}`maxSubarrayDivideCosted` is
{lit}`Θ(n log n)`.  This theorem does not claim RAM costs for Lean list
allocation or garbage collection.
-/
theorem maxSubarray_runtime_bigTheta :
    Chapter03.isBigTheta maxSubarrayDivideCostReal (realLogLogScale 2 2) := by
  have hcritical :
      Chapter03.isBigTheta maxSubarrayDivideCostReal
        (criticalPowerLogScale 2 2) :=
    allInput_bigTheta_of_criticalPowerLogScale 2 2
      maxSubarrayDivideCostReal (by norm_num) (by norm_num)
      maxSubarrayDivideCostReal_monotoneAbs
      maxSubarrayDivideCostReal_exactPowers_bigTheta
  exact Chapter03.isBigTheta_trans hcritical
    (criticalPowerLogScale_isBigTheta_realLogLogScale 2 2
      (by norm_num) (by norm_num))

/-- The execution-attached cost has the Chapter 4 real-log-log scale. -/
theorem maxSubarrayDivideCost_isBigTheta_realLogLogScale :
    Chapter03.isBigTheta maxSubarrayDivideCostReal
      (realLogLogScale 2 2) :=
  maxSubarray_runtime_bigTheta

/-- Textbook-facing name for the executable `Θ(n log n)` runtime theorem. -/
theorem maxSubarrayDivideCost_isBigTheta_nlogn :
    Chapter03.isBigTheta maxSubarrayDivideCostReal
      (realLogLogScale 2 2) :=
  maxSubarray_runtime_bigTheta

end Chapter04
end CLRS

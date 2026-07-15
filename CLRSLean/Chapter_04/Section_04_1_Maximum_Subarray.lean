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
layers on top of that specification: the crossing helper, the executable
combine step, and a structurally recursive selector over explicit split trees.

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
- Theorem {lit}`maxSubarray_exists_of_ne_nil`: nonempty inputs have a selected
  maximum-subarray candidate.
- Theorem {lit}`maxSubarray_correct`: the executable maximum-subarray selector
  returns a nonempty contiguous subarray whose sum is maximal among all
  nonempty contiguous subarrays.

Current gaps:

- The recursive divide-and-conquer correctness theorem is proved for an
  explicit/fuelled split model.  Runtime and RAM-cost analysis are future
  strengthening targets.
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

/-! ## Runtime analysis

The divide-and-conquer maximum-subarray algorithm makes two recursive calls on
halves and a linear crossing-subarray scan, giving the recurrence
{lit}`T(n) = 2 T(⌊n/2⌋) + Θ(n)`.  We prove {lit}`T(n) = Θ(n log n)` by
instantiating the Chapter 4 Master theorem (case 2) with {lit}`a = 2`,
{lit}`b = 2`.
-/

open Chapter04

/--
The work recurrence {lit}`T(n) = 2 T(⌊n/2⌋) + n` for the divide-and-conquer
maximum-subarray algorithm, matching the CLRS recurrence with one linear
crossing-subarray scan per level.
-/
noncomputable def maxSubarrayWork : ℕ → ℝ
  | 0 => 0
  | (n + 1) => 2 * maxSubarrayWork ((n + 1) / 2) + ((n + 1 : ℕ) : ℝ)
  decreasing_by exact Nat.div_lt_self (Nat.succ_pos n) (by norm_num)

/-- Base value of the work recurrence. -/
theorem maxSubarrayWork_zero : maxSubarrayWork 0 = 0 := by
  rw [maxSubarrayWork]

/-- One recursion step at a successor argument. -/
theorem maxSubarrayWork_succ (n : ℕ) :
    maxSubarrayWork (n + 1) = 2 * maxSubarrayWork ((n + 1) / 2) + ((n + 1 : ℕ) : ℝ) := by
  rw [maxSubarrayWork]

/-- One recursion step at any positive argument. -/
theorem maxSubarrayWork_pos_step (n : ℕ) (hn : 0 < n) :
    maxSubarrayWork n = 2 * maxSubarrayWork (n / 2) + ((n : ℕ) : ℝ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact maxSubarrayWork_succ m

/--
The forcing term {lit}`f(n) = T(n) - 2 T(⌊n/2⌋)` of the recurrence.
-/
noncomputable def maxSubarrayForcing (n : ℕ) : ℝ :=
  maxSubarrayWork n - 2 * maxSubarrayWork (n / 2)

/--
The work function satisfies the Chapter 4 floor-division Master recurrence with
{lit}`a = 2`, {lit}`b = 2`.
-/
theorem maxSubarrayWork_floorRec :
    FloorDivideRecurrence 2 2 maxSubarrayForcing maxSubarrayWork := by
  refine ⟨fun n => ?_⟩
  simp only [maxSubarrayForcing]
  push_cast
  ring

/-- The work function is nonnegative. -/
theorem maxSubarrayWork_nonneg : ∀ n, 0 ≤ maxSubarrayWork n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [maxSubarrayWork_zero]
    · rw [maxSubarrayWork_pos_step n hn]
      have hlt : n / 2 < n := Nat.div_lt_self hn (by norm_num)
      have hrec := ih (n / 2) hlt
      nlinarith

/-- The work function is nondecreasing across one step. -/
theorem maxSubarrayWork_le_succ : ∀ n, maxSubarrayWork n ≤ maxSubarrayWork (n + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; rw [maxSubarrayWork_zero]; exact maxSubarrayWork_nonneg _
    · rw [maxSubarrayWork_pos_step n hn, maxSubarrayWork_pos_step (n + 1) (Nat.succ_pos n)]
      have hcast : ((n : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
      rcases (by omega : (n + 1) / 2 = n / 2 ∨ (n + 1) / 2 = n / 2 + 1) with h | h
      · rw [h]; nlinarith
      · rw [h]
        have hj : n / 2 < n := Nat.div_lt_self hn (by norm_num)
        have hstep := ih (n / 2) hj
        nlinarith

/-- The work function is monotone. -/
theorem maxSubarrayWork_monotone : Monotone maxSubarrayWork :=
  monotone_nat_of_le_succ maxSubarrayWork_le_succ

/-- The work function satisfies the absolute-value monotonicity interface. -/
theorem maxSubarrayWork_monotoneAbs : MonotoneAbs maxSubarrayWork := by
  intro m n hmn
  rw [abs_of_nonneg (maxSubarrayWork_nonneg m), abs_of_nonneg (maxSubarrayWork_nonneg n)]
  exact maxSubarrayWork_monotone hmn

/-- Value of the work recurrence at the base input `1`. -/
theorem maxSubarrayWork_one : maxSubarrayWork 1 = 1 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, maxSubarrayWork_succ]
  norm_num [maxSubarrayWork_zero]

/-- The normalized base value is nonnegative, a case-2 hypothesis. -/
theorem maxSubarrayWork_base_nonneg : 0 ≤ normalizedValue 2 2 maxSubarrayWork 0 := by
  unfold normalizedValue
  norm_num [maxSubarrayWork_one]

/--
On exact powers {lit}`n = 2^(k+1)`, the forcing term is exactly {lit}`2^(k+1)`,
so the normalized forcing is identically {lit}`1`.  This places the recurrence
in Master case 2 where the forcing is proportional to the critical scale.

The closed form on exact powers is {lit}`T(2^k) = (k+1)·2^k` (proved by
induction), giving {lit}`f(2^(k+1)) = 2^(k+1)` and {lit}`f(2^(k+1))/2^(k+1) = 1`.
-/
theorem maxSubarray_normForcing (k : ℕ) : normalizedForcing 2 2 maxSubarrayForcing k = 1 := by
  -- Closed form: T(2^k) = (k+1) * 2^k  (in ℝ)
  have h_work_pow : ∀ (k : ℕ), maxSubarrayWork ((2 : ℕ) ^ k) = ((k : ℕ) + 1 : ℝ) * ((2 : ℕ) ^ k : ℝ) := by
    intro k
    induction k with
    | zero =>
        simp [maxSubarrayWork_one]
    | succ k ih =>
        have h_pow_succ : (2 : ℕ) ^ (k + 1) = 2 * (2 : ℕ) ^ k := by
          rw [pow_succ, mul_comm]
        rw [h_pow_succ]
        have hpos : 0 < 2 * (2 : ℕ) ^ k :=
          calc
            0 < (2 : ℕ) ^ (k + 1) := pow_pos (by norm_num) (k + 1)
            _ = 2 * (2 : ℕ) ^ k := by rw [pow_succ, mul_comm]
        rw [maxSubarrayWork_pos_step (2 * (2 : ℕ) ^ k) hpos]
        simp [ih]
        push_cast
        ring
  -- Prove the normalized forcing equals 1 by direct computation
  have hk := h_work_pow (k + 1)
  have hk' := h_work_pow k
  -- normalizedForcing 2 2 maxSubarrayForcing k
  -- = maxSubarrayForcing (2^(k+1)) / (2^(k+1))
  -- = (T(2^(k+1)) - 2*T(2^(k+1)/2)) / 2^(k+1)
  -- = (T(2^(k+1)) - 2*T(2^k)) / 2^(k+1)
  -- = ((k+2)*2^(k+1) - 2*(k+1)*2^k) / 2^(k+1)
  -- = 2^(k+1) / 2^(k+1) = 1
  dsimp [normalizedForcing, maxSubarrayForcing]
  -- Simplify 2^(k+1)/2 = 2^k
  have hdiv : (2 : ℕ) ^ (k + 1) / 2 = (2 : ℕ) ^ k := by
    rw [pow_succ, show (2 : ℕ) ^ k * 2 = 2 * (2 : ℕ) ^ k by ring, Nat.mul_div_right _ (by norm_num)]
  rw [hdiv, hk, hk']
  push_cast
  field_simp [show ((2 : ℝ) ^ (k + 1)) ≠ 0 from pow_ne_zero _ (by norm_num)]
  ring

/-- Lower bound for the normalized forcing: {lit}`0 < 1 ≤ normalizedForcing`. -/
theorem maxSubarray_term_lower (k : ℕ) :
    (1 : ℝ) ≤ normalizedForcing 2 2 maxSubarrayForcing k := by
  rw [maxSubarray_normForcing]

/-- Upper bound for the normalized forcing: {lit}`normalizedForcing ≤ 1`. -/
theorem maxSubarray_term_upper (k : ℕ) :
    normalizedForcing 2 2 maxSubarrayForcing k ≤ 1 := by
  rw [maxSubarray_normForcing]

/--
**Runtime of the divide-and-conquer maximum-subarray algorithm.**  The
recurrence {lit}`T(n) = 2 T(⌊n/2⌋) + Θ(n)` is {lit}`Θ(n log n)`.  This is
the CLRS {lit}`Θ(n log n)` bound for the divide-and-conquer maximum subarray,
obtained by discharging Master-theorem case 2 with {lit}`a = 2`, {lit}`b = 2`
through the Chapter 4 wrapper
{name}`CLRS.Chapter04.floorDivide_allInput_masterCase2_realLogLogScale`.
-/
theorem maxSubarray_runtime_bigTheta :
    Chapter03.isBigTheta maxSubarrayWork (realLogLogScale 2 2) :=
  floorDivide_allInput_masterCase2_realLogLogScale 2 2 maxSubarrayForcing maxSubarrayWork
    maxSubarrayWork_floorRec (by norm_num) (by norm_num) maxSubarrayWork_monotoneAbs
    maxSubarrayWork_base_nonneg (c := 1) (C := 1) (by norm_num) (by norm_num)
    maxSubarray_term_lower maxSubarray_term_upper

end Chapter04
end CLRS

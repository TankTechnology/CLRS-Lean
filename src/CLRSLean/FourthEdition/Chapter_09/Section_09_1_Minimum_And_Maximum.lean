import Mathlib

/-!
# CLRS Section 9.1 - Minimum and maximum

This section formalizes the pairwise algorithm for finding both extrema of a
nonempty list.  Each pair is compared internally, then only its smaller member
is compared with the running minimum and only its larger member with the
running maximum.

Main results:

* Theorem {lit}`minMax?_correct`: a successful run returns input members that
  bound every input element.
* Theorem {lit}`minMax?_comparisons_le`: the run performs at most
  {lit}`3 * floor(n / 2)` comparisons, the CLRS Section 9.1 bound.

Current gaps:

* None for the mathematical comparison-count model.  Machine-level instruction
  and memory costs are outside the Section 9.1 completion boundary.
-/

namespace CLRS
namespace Chapter09

/-! ## Executable pairwise algorithm -/

/-- The two extrema returned by the algorithm together with its comparison count. -/
structure MinMaxResult where
  minimum : Nat
  maximum : Nat
  comparisons : Nat
deriving Repr, DecidableEq

/--
Correctness certificate for a simultaneous minimum/maximum result: both
extrema occur in the input and every input value lies between them.
-/
def MinMaxCertificate (xs : List Nat) (result : MinMaxResult) : Prop :=
  result.minimum ∈ xs ∧
    result.maximum ∈ xs ∧
    ∀ x ∈ xs, result.minimum ≤ x ∧ x ≤ result.maximum

/-- Order two values with one comparison, returning the smaller one first. -/
def orderedPair (x y : Nat) : Nat × Nat :=
  if x ≤ y then (x, y) else (y, x)

/-- The one-comparison result for an input consisting of exactly one pair. -/
def pairMinMaxResult (x y : Nat) : MinMaxResult :=
  let ordered := orderedPair x y
  ⟨ordered.1, ordered.2, 1⟩

/--
Merge one ordered pair with the extrema of a nonempty recursive suffix.
The merge uses three comparisons: one inside the pair and one against each
suffix extremum.
-/
def combineMinMax (x y : Nat) (suffix : MinMaxResult) : MinMaxResult :=
  let ordered := orderedPair x y
  ⟨min ordered.1 suffix.minimum,
    max ordered.2 suffix.maximum,
    suffix.comparisons + 3⟩

/--
CLRS pairwise simultaneous minimum/maximum.

The empty input has no extrema, a singleton needs no comparison, an isolated
pair needs one comparison, and every pair merged with a nonempty suffix needs
three comparisons.
-/
def minMax? : List Nat → Option MinMaxResult
  | [] => none
  | [x] => some ⟨x, x, 0⟩
  | x :: y :: xs =>
      match minMax? xs with
      | none => some (pairMinMaxResult x y)
      | some suffix => some (combineMinMax x y suffix)

/-! ## Local correctness lemmas -/

/-- The ordered pair contains exactly its inputs and bounds both of them. -/
theorem orderedPair_spec (x y : Nat) :
    let ordered := orderedPair x y
    ordered.1 ∈ [x, y] ∧
      ordered.2 ∈ [x, y] ∧
      ordered.1 ≤ x ∧ ordered.1 ≤ y ∧
      x ≤ ordered.2 ∧ y ≤ ordered.2 := by
  simp only [orderedPair]
  split
  · simp_all
  · simp_all
    omega

/-- The base result for one pair has the full extrema certificate. -/
theorem pairMinMaxResult_correct (x y : Nat) :
    MinMaxCertificate [x, y] (pairMinMaxResult x y) := by
  rcases orderedPair_spec x y with
    ⟨hsmall_mem, hlarge_mem, hsmall_x, hsmall_y, hx_large, hy_large⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [pairMinMaxResult] using hsmall_mem
  · simpa [pairMinMaxResult] using hlarge_mem
  · intro z hz
    simp at hz
    rcases hz with rfl | rfl
    · simpa [pairMinMaxResult] using And.intro hsmall_x hx_large
    · simpa [pairMinMaxResult] using And.intro hsmall_y hy_large

/-- Merging a pair with certified suffix extrema preserves the certificate. -/
theorem combineMinMax_correct {xs : List Nat} {suffix : MinMaxResult}
    (hcert : MinMaxCertificate xs suffix) (x y : Nat) :
    MinMaxCertificate (x :: y :: xs) (combineMinMax x y suffix) := by
  rcases hcert with ⟨hsuffix_min_mem, hsuffix_max_mem, hsuffix_bounds⟩
  rcases orderedPair_spec x y with
    ⟨hsmall_mem, hlarge_mem, hsmall_x, hsmall_y, hx_large, hy_large⟩
  have hsmall_mem' : (orderedPair x y).1 = x ∨ (orderedPair x y).1 = y := by
    simpa using hsmall_mem
  have hlarge_mem' : (orderedPair x y).2 = x ∨ (orderedPair x y).2 = y := by
    simpa using hlarge_mem
  have hminimum_mem :
      min (orderedPair x y).1 suffix.minimum ∈ x :: y :: xs := by
    rcases Nat.le_total (orderedPair x y).1 suffix.minimum with hle | hle
    · rw [min_eq_left hle]
      rcases hsmall_mem' with heq | heq <;> simp [heq]
    · rw [min_eq_right hle]
      simp [hsuffix_min_mem]
  have hmaximum_mem :
      max (orderedPair x y).2 suffix.maximum ∈ x :: y :: xs := by
    rcases Nat.le_total (orderedPair x y).2 suffix.maximum with hle | hle
    · rw [max_eq_right hle]
      simp [hsuffix_max_mem]
    · rw [max_eq_left hle]
      rcases hlarge_mem' with heq | heq <;> simp [heq]
  refine ⟨?_, ?_, ?_⟩
  · simpa [combineMinMax] using hminimum_mem
  · simpa [combineMinMax] using hmaximum_mem
  · intro z hz
    simp only [List.mem_cons] at hz
    rcases hz with hzx | hzy | hz
    · subst z
      constructor
      ·
        simpa [combineMinMax] using
          Nat.le_trans (Nat.min_le_left (orderedPair x y).1 suffix.minimum) hsmall_x
      · simpa [combineMinMax] using
          Nat.le_trans hx_large
            (Nat.le_max_left (orderedPair x y).2 suffix.maximum)
    · subst z
      constructor
      ·
        simpa [combineMinMax] using
          Nat.le_trans (Nat.min_le_left (orderedPair x y).1 suffix.minimum) hsmall_y
      · simpa [combineMinMax] using
          Nat.le_trans hy_large
            (Nat.le_max_left (orderedPair x y).2 suffix.maximum)
    · rcases hsuffix_bounds z hz with ⟨hmin_z, hz_max⟩
      constructor
      · simpa [combineMinMax] using
          Nat.le_trans (Nat.min_le_right (orderedPair x y).1 suffix.minimum) hmin_z
      · simpa [combineMinMax] using
          Nat.le_trans hz_max
            (Nat.le_max_right (orderedPair x y).2 suffix.maximum)

/-! ## Public specification and comparison bound -/

/-- The pairwise algorithm fails exactly on the empty input. -/
theorem minMax?_eq_none_iff (xs : List Nat) :
    minMax? xs = none ↔ xs = [] := by
  cases xs with
  | nil => simp [minMax?]
  | cons x xs =>
      cases xs with
      | nil => simp [minMax?]
      | cons y xs =>
          cases hsuffix : minMax? xs <;> simp [minMax?, hsuffix]

/-- The pairwise algorithm succeeds exactly on nonempty inputs. -/
theorem minMax?_isSome_iff (xs : List Nat) :
    (minMax? xs).isSome ↔ xs ≠ [] := by
  rw [Option.isSome_iff_ne_none]
  simp [minMax?_eq_none_iff]

/-- A successful pairwise run returns the certified extrema of the input. -/
theorem minMax?_correct {xs : List Nat} {result : MinMaxResult}
    (hrun : minMax? xs = some result) :
    MinMaxCertificate xs result := by
  cases xs with
  | nil => simp [minMax?] at hrun
  | cons x xs =>
      cases xs with
      | nil =>
          simp [minMax?] at hrun
          subst result
          simp [MinMaxCertificate]
      | cons y xs =>
          cases hsuffix : minMax? xs with
          | none =>
              have hxs : xs = [] := (minMax?_eq_none_iff xs).mp hsuffix
              subst xs
              simp [minMax?] at hrun
              subst result
              exact pairMinMaxResult_correct x y
          | some suffix =>
              have hsuffix_cert : MinMaxCertificate xs suffix :=
                minMax?_correct hsuffix
              have hcombined := combineMinMax_correct hsuffix_cert x y
              simp [minMax?, hsuffix] at hrun
              subst result
              exact hcombined
termination_by xs.length
decreasing_by simp_all

/-- The returned minimum is an element of the input. -/
theorem minMax?_minimum_mem {xs : List Nat} {result : MinMaxResult}
    (hrun : minMax? xs = some result) :
    result.minimum ∈ xs :=
  (minMax?_correct hrun).1

/-- The returned maximum is an element of the input. -/
theorem minMax?_maximum_mem {xs : List Nat} {result : MinMaxResult}
    (hrun : minMax? xs = some result) :
    result.maximum ∈ xs :=
  (minMax?_correct hrun).2.1

/-- The returned minimum is at most every input element. -/
theorem minMax?_minimum_le {xs : List Nat} {result : MinMaxResult}
    (hrun : minMax? xs = some result) {x : Nat} (hx : x ∈ xs) :
    result.minimum ≤ x :=
  (minMax?_correct hrun).2.2 x hx |>.1

/-- Every input element is at most the returned maximum. -/
theorem minMax?_le_maximum {xs : List Nat} {result : MinMaxResult}
    (hrun : minMax? xs = some result) {x : Nat} (hx : x ∈ xs) :
    x ≤ result.maximum :=
  (minMax?_correct hrun).2.2 x hx |>.2

/--
The pairwise algorithm uses at most three comparisons per input pair:
{lit}`comparisons ≤ 3 * floor(xs.length / 2)`.
-/
theorem minMax?_comparisons_le {xs : List Nat} {result : MinMaxResult}
    (hrun : minMax? xs = some result) :
    result.comparisons ≤ 3 * (xs.length / 2) := by
  cases xs with
  | nil => simp [minMax?] at hrun
  | cons x xs =>
      cases xs with
      | nil =>
          simp [minMax?] at hrun
          subst result
          simp
      | cons y xs =>
          cases hsuffix : minMax? xs with
          | none =>
              have hxs : xs = [] := (minMax?_eq_none_iff xs).mp hsuffix
              subst xs
              simp [minMax?] at hrun
              subst result
              simp [pairMinMaxResult]
          | some suffix =>
              have ih : suffix.comparisons ≤ 3 * (xs.length / 2) :=
                minMax?_comparisons_le hsuffix
              simp [minMax?, hsuffix] at hrun
              subst result
              simp only [combineMinMax, List.length_cons]
              omega
termination_by xs.length
decreasing_by simp_all

end Chapter09
end CLRS

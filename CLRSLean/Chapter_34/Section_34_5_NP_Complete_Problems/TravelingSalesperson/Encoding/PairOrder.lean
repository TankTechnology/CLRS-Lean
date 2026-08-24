import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.Instance
import Mathlib.Tactic

/-!
# Canonical complete-matrix pair order for decision-TSP

The physical matrix lists every diagonal pair first.  It then lists both
orientations of every normalized pair, grouped by increasing upper endpoint.
Thus every in-range ordered pair occurs exactly once, while symmetric
instances can be generated directly from one undirected adjacency stream.
-/

namespace CLRS.Chapter34

/-- Every strict normalized pair `(lower, upper)` with `upper < n`. -/
def tspNormalizedPairs : Nat → List (Nat × Nat)
  | 0 => []
  | n + 1 =>
      tspNormalizedPairs n ++ (List.range n).map fun lower => (lower, n)

/-- Turn one undirected pair into its two directed orientations. -/
def tspPairOrientations (pair : Nat × Nat) : List (Nat × Nat) :=
  [pair, (pair.2, pair.1)]

/-- Canonical physical order of all `n²` directed matrix entries. -/
def tspPairOrder (n : Nat) : List (Nat × Nat) :=
  (List.range n).map (fun vertex => (vertex, vertex)) ++
    (tspNormalizedPairs n).flatMap tspPairOrientations

theorem mem_tspNormalizedPairs_iff {n u v : Nat} :
    (u, v) ∈ tspNormalizedPairs n ↔ u < v ∧ v < n := by
  induction n with
  | zero => simp [tspNormalizedPairs]
  | succ n ih =>
      simp only [tspNormalizedPairs, List.mem_append, ih,
        List.mem_map, List.mem_range, Prod.mk.injEq]
      constructor
      · rintro (⟨huv, hvn⟩ | ⟨lower, hlower, hlowerEq, hnEq⟩)
        · exact ⟨huv, Nat.lt_succ_of_lt hvn⟩
        · subst u
          subst v
          exact ⟨hlower, Nat.lt_succ_self n⟩
      · rintro ⟨huv, hvn⟩
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hvn) with hvn' | rfl
        · exact Or.inl ⟨huv, hvn'⟩
        · exact Or.inr ⟨u, huv, rfl, rfl⟩

private theorem mem_tspPairOrientations_iff {pair : Nat × Nat} {u v : Nat} :
    (u, v) ∈ tspPairOrientations pair ↔
      pair = (u, v) ∨ pair = (v, u) := by
  rcases pair with ⟨a, b⟩
  simp only [tspPairOrientations, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq]
  constructor
  · rintro (h | h)
    · exact Or.inl ⟨h.1.symm, h.2.symm⟩
    · exact Or.inr ⟨h.2.symm, h.1.symm⟩
  · rintro (h | h)
    · exact Or.inl ⟨h.1.symm, h.2.symm⟩
    · exact Or.inr ⟨h.2.symm, h.1.symm⟩

theorem mem_tspPairOrder_iff {n u v : Nat} :
    (u, v) ∈ tspPairOrder n ↔ u < n ∧ v < n := by
  rw [tspPairOrder, List.mem_append]
  constructor
  · rintro (hdiagonal | horientation)
    · rcases List.mem_map.mp hdiagonal with ⟨vertex, hvertex, heq⟩
      have hvertexLt := List.mem_range.mp hvertex
      cases heq
      exact ⟨hvertexLt, hvertexLt⟩
    · rcases List.mem_flatMap.mp horientation with ⟨pair, hpair, horientation⟩
      have hpairs := mem_tspNormalizedPairs_iff.mp hpair
      rcases mem_tspPairOrientations_iff.mp horientation with heq | heq
      · subst pair
        exact ⟨hpairs.1.trans hpairs.2, hpairs.2⟩
      · subst pair
        exact ⟨hpairs.2, hpairs.1.trans hpairs.2⟩
  · rintro ⟨hu, hv⟩
    rcases lt_trichotomy u v with huv | heq | hvu
    · exact Or.inr (List.mem_flatMap.mpr
        ⟨(u, v), mem_tspNormalizedPairs_iff.mpr ⟨huv, hv⟩,
          mem_tspPairOrientations_iff.mpr (Or.inl rfl)⟩)
    · subst v
      exact Or.inl (List.mem_map.mpr ⟨u, List.mem_range.mpr hu, rfl⟩)
    · exact Or.inr (List.mem_flatMap.mpr
        ⟨(v, u), mem_tspNormalizedPairs_iff.mpr ⟨hvu, hu⟩,
          mem_tspPairOrientations_iff.mpr (Or.inr rfl)⟩)

private theorem tspNormalizedPairs_length_recurrence (n : Nat) :
    (tspNormalizedPairs (n + 1)).length =
      (tspNormalizedPairs n).length + n := by
  simp [tspNormalizedPairs]

/-- The canonical pair family contains exactly one entry for every matrix
cell. -/
@[simp] theorem tspPairOrder_length (n : Nat) :
    (tspPairOrder n).length = n * n := by
  have invariant : n + 2 * (tspNormalizedPairs n).length = n * n := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [tspNormalizedPairs_length_recurrence]
        nlinarith
  simp only [tspPairOrder, List.length_append, List.length_map,
    List.length_range, List.length_flatMap]
  have horientations :
      ((tspNormalizedPairs n).map
        (fun pair => (tspPairOrientations pair).length)).sum =
        2 * (tspNormalizedPairs n).length := by
    simp [tspPairOrientations, Nat.mul_comm]
  rw [horientations]
  exact invariant

/-- Lookup in two aligned pair/weight streams, with zero fallback. -/
def lookupTSPWeight :
    List (Nat × Nat) → List Nat → Nat → Nat → Nat
  | pair :: pairs, weight :: weights, u, v =>
      if pair = (u, v) then weight
      else lookupTSPWeight pairs weights u v
  | _, _, _, _ => 0

/-- Looking up a mapped weight family recovers its generating function for
every pair present in the physical order. -/
theorem lookupTSPWeight_map_of_mem (pairs : List (Nat × Nat))
    (weight : (Nat × Nat) → Nat) {u v : Nat}
    (hmem : (u, v) ∈ pairs) :
    lookupTSPWeight pairs (pairs.map weight) u v = weight (u, v) := by
  induction pairs with
  | nil => simp at hmem
  | cons pair pairs ih =>
      simp only [List.map_cons, lookupTSPWeight, List.mem_cons] at hmem ⊢
      by_cases heq : pair = (u, v)
      · simp [heq]
      · simp [heq]
        exact ih (hmem.resolve_left (Ne.symm heq))

end CLRS.Chapter34

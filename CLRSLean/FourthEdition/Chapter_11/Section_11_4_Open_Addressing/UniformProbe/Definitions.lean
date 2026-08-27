import CLRSLean.FourthEdition.Chapter_11.Section_11_4_Open_Addressing
import CLRSLean.Probability.FiniteExpectation

/-!
# CLRS Section 11.4 - Uniform probe-space definitions

The sample space is the finite type of permutations of the table slots.  A
permutation sends probe positions to distinct table slots, exactly matching
the uniform-hashing assumption used in CLRS Theorems 11.6--11.8.
-/

namespace CLRS
namespace Chapter11

open Probability

/-- The first {lit}`i` positions of a probe permutation all hit occupied slots. -/
def firstProbesOccupied {m : Nat} (occupied : Finset (Fin m)) (i : Nat)
    (σ : Equiv.Perm (Fin m)) : Prop :=
  ∀ j : Fin m, j.val < i → σ j ∈ occupied

/-- Indicator of the occupied-prefix event with its classical decision procedure
fixed inside the definition. -/
noncomputable def firstProbesOccupiedIndicator {m : Nat}
    (occupied : Finset (Fin m)) (i : Nat) (σ : Equiv.Perm (Fin m)) : Real := by
  classical
  exact indicator (firstProbesOccupied occupied i σ)

/-- Uniform probability of an occupied prefix in the explicit permutation
sample space. -/
noncomputable def uniformProbeTailProbability {m : Nat}
    (occupied : Finset (Fin m)) (i : Nat) : Real := by
  classical
  exact fintypeExpect (firstProbesOccupiedIndicator occupied i)

/-- Number of probes made before an unsuccessful search reaches its first
empty slot, including that final empty-slot probe.  The definition is the
finite tail sum of the concrete permutation execution. -/
noncomputable def uniformUnsuccessfulProbeCount {m : Nat} (occupied : Finset (Fin m))
    (σ : Equiv.Perm (Fin m)) : Nat := by
  classical
  exact ∑ i ∈ Finset.range (m + 1),
    if firstProbesOccupied occupied i σ then 1 else 0

/-- The explicit unsuccessful-search probe count is bounded by the number of
its {lit}`m + 1` possible tails. -/
theorem uniformUnsuccessfulProbeCount_le {m : Nat} (occupied : Finset (Fin m))
    (σ : Equiv.Perm (Fin m)) :
    uniformUnsuccessfulProbeCount occupied σ ≤ m + 1 := by
  classical
  unfold uniformUnsuccessfulProbeCount
  calc
    (∑ i ∈ Finset.range (m + 1), if firstProbesOccupied occupied i σ then 1 else 0)
        ≤ ∑ _i ∈ Finset.range (m + 1), 1 := by
          apply Finset.sum_le_sum
          intro i hi
          split <;> omega
    _ = m + 1 := by simp

/-- Real-cast form of the concrete tail-count definition. -/
theorem uniformUnsuccessfulProbeCount_cast {m : Nat} (occupied : Finset (Fin m))
    (σ : Equiv.Perm (Fin m)) :
    (uniformUnsuccessfulProbeCount occupied σ : Real) =
      ∑ i ∈ Finset.range (m + 1),
        firstProbesOccupiedIndicator occupied i σ := by
  classical
  simp [uniformUnsuccessfulProbeCount, firstProbesOccupiedIndicator, indicator]

/-- Canonical set consisting of the first {lit}`n` slots, used only to package
the successful-search average over insertion times. -/
def canonicalOccupied (m n : Nat) : Finset (Fin m) :=
  Finset.univ.filter (fun x => x.val < n)

/-- The canonical occupied prefix has the requested cardinality when it fits
inside the table. -/
theorem canonicalOccupied_card (m n : Nat) (hn : n ≤ m) :
    (canonicalOccupied m n).card = n := by
  classical
  rw [canonicalOccupied]
  have heq : Finset.univ.filter (fun x : Fin m => x.val < n) =
      Finset.univ.map (Fin.castLEEmb hn) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · intro hx
      exact ⟨⟨x.val, hx⟩, by simp⟩
    · rintro ⟨y, _, rfl⟩
      exact y.isLt
  rw [heq, Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- Explicit successful-search expectation: average the concrete unsuccessful
probe count at the {lit}`n` insertion-time loads. -/
noncomputable def uniformSuccessfulExpectedProbes (m n : Nat) : Real :=
  (1 / (n : Real)) * ∑ j ∈ Finset.range n,
    fintypeExpect (fun σ : Equiv.Perm (Fin m) =>
      (uniformUnsuccessfulProbeCount (canonicalOccupied m j) σ : Real))

end Chapter11
end CLRS

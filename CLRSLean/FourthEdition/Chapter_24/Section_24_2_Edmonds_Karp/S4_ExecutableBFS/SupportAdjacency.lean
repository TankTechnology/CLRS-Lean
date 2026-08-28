import Mathlib

/-!
# Finite support adjacency buckets

This module builds adjacency buckets from a finite directed support.  The
builder records one RAM-model unit for each executed bucket insertion.  Its
membership, work, and total-storage specifications are independent of flow
semantics and are reused by the costed residual BFS.

This is an explicit unit-cost RAM abstraction for the textbook analysis; the
counter is not a claim about Lean kernel reduction or a particular compiled
`Finset` representation.
-/

namespace CLRS
namespace Chapter26

open Finset Classical

variable {V : Type*} [DecidableEq V]

/-- A finite directed support indexed by its source vertex. -/
structure SupportAdjacency (V : Type*) [DecidableEq V] where
  bucket : V → Finset V

namespace SupportAdjacency

/-- The empty support adjacency. -/
def empty : SupportAdjacency V where
  bucket := fun _ => ∅

/-- Insert one directed support arc into its source bucket. -/
def insertArc (A : SupportAdjacency V) (e : V × V) : SupportAdjacency V where
  bucket := Function.update A.bucket e.1 (insert e.2 (A.bucket e.1))

@[simp]
theorem empty_bucket (u : V) : (empty : SupportAdjacency V).bucket u = ∅ := rfl

@[simp]
theorem mem_insertArc_bucket {A : SupportAdjacency V} {e : V × V} {u v : V} :
    v ∈ (A.insertArc e).bucket u ↔ (u, v) = e ∨ v ∈ A.bucket u := by
  rcases e with ⟨a, b⟩
  by_cases h : u = a
  · subst u
    simp [insertArc]
  · simp [insertArc, Function.update, h]

/-- Total number of stored bucket entries. -/
noncomputable def storage [Fintype V] (A : SupportAdjacency V) : Nat :=
  ∑ u : V, (A.bucket u).card

theorem storage_insertArc_of_not_mem [Fintype V] (A : SupportAdjacency V)
    (e : V × V) (hnew : e.2 ∉ A.bucket e.1) :
    (A.insertArc e).storage = A.storage + 1 := by
  unfold storage
  change (∑ u, (Function.update A.bucket e.1
    (insert e.2 (A.bucket e.1)) u).card) = ∑ u, (A.bucket u).card + 1
  have hfun : (fun u => (Function.update A.bucket e.1
      (insert e.2 (A.bucket e.1)) u).card) =
      Function.update (fun u => (A.bucket u).card) e.1
        (insert e.2 (A.bucket e.1)).card := by
    funext u
    by_cases h : u = e.1 <;> simp [Function.update, h]
  rw [hfun]
  rw [Finset.sum_update_of_mem (Finset.mem_univ e.1)]
  rw [Finset.card_insert_of_notMem hnew]
  rw [Finset.sdiff_singleton_eq_erase]
  have hsum := Finset.sum_erase_add (Finset.univ : Finset V)
    (fun u => (A.bucket u).card) (Finset.mem_univ e.1)
  omega

end SupportAdjacency

/-- Result of building adjacency buckets, including the executed insert count. -/
structure SupportBuild (V : Type*) [DecidableEq V] where
  adjacency : SupportAdjacency V
  work : Nat

/-- Build buckets from a support list, charging one unit for each insertion. -/
def buildSupportAux : List (V × V) → SupportBuild V
  | [] => ⟨SupportAdjacency.empty, 0⟩
  | e :: rest =>
      let tail := buildSupportAux rest
      ⟨tail.adjacency.insertArc e, tail.work + 1⟩

@[simp]
theorem buildSupportAux_work (support : List (V × V)) :
    (buildSupportAux support).work = support.length := by
  induction support with
  | nil => rfl
  | cons e rest ih => simp [buildSupportAux, ih]

theorem mem_buildSupportAux {support : List (V × V)} {u v : V} :
    v ∈ (buildSupportAux support).adjacency.bucket u ↔ (u, v) ∈ support := by
  induction support with
  | nil => simp [buildSupportAux, SupportAdjacency.empty]
  | cons e rest ih =>
      simp [buildSupportAux, SupportAdjacency.mem_insertArc_bucket, ih]

theorem buildSupportAux_storage [Fintype V] {support : List (V × V)}
    (hnodup : support.Nodup) :
    (buildSupportAux support).adjacency.storage = support.length := by
  induction support with
  | nil => simp [buildSupportAux, SupportAdjacency.storage]
  | cons e rest ih =>
      rw [List.nodup_cons] at hnodup
      have hnew : e.2 ∉ (buildSupportAux rest).adjacency.bucket e.1 := by
        intro hmem
        exact hnodup.1 ((mem_buildSupportAux.mp hmem))
      rw [buildSupportAux]
      rw [SupportAdjacency.storage_insertArc_of_not_mem _ _ hnew]
      rw [ih hnodup.2]
      simp

/-- Build adjacency buckets from a duplicate-free finite support. -/
noncomputable def buildSupportAdjacency (support : Finset (V × V)) : SupportBuild V :=
  buildSupportAux support.toList

theorem mem_buildSupportAdjacency {support : Finset (V × V)} {u v : V} :
    v ∈ (buildSupportAdjacency support).adjacency.bucket u ↔ (u, v) ∈ support := by
  simp [buildSupportAdjacency, mem_buildSupportAux]

theorem buildSupportAdjacency_work (support : Finset (V × V)) :
    (buildSupportAdjacency support).work = support.card := by
  simp [buildSupportAdjacency]

theorem buildSupportAdjacency_storage [Fintype V] (support : Finset (V × V)) :
    (buildSupportAdjacency support).adjacency.storage = support.card := by
  rw [buildSupportAdjacency, buildSupportAux_storage support.nodup_toList]
  simp

theorem sum_bucket_card_le_storage [Fintype V] (A : SupportAdjacency V)
    (processed : Finset V) :
    ∑ u ∈ processed, (A.bucket u).card ≤ A.storage := by
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ processed)

end Chapter26
end CLRS

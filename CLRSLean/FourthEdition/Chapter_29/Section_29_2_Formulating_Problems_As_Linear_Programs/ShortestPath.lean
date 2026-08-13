import CLRSLean.FourthEdition.Chapter_22.Section_22_4_Difference_Constraints
import CLRSLean.FourthEdition.Chapter_29.Section_29_1_Standard_And_Slack_Forms.Normalization
import CLRSLean.FourthEdition.Chapter_29.Section_29_2_Formulating_Problems_As_Linear_Programs.NetworkFlow

/-!
# 29.2: Shortest paths as a linear program

For a source {lit}`s` and target {lit}`t`, CLRS maximizes {lit}`d t`, subject to
{lit}`d s = 0` and {lit}`d v ≤ d u + w u v` on every edge.  Thus every feasible
{lit}`d t` is a lower bound on every {lit}`s`-to-{lit}`t` walk; an attained
bound is optimal.

This module also records the finite standard-form encoding: the general-form
program is reindexed into a concrete {lit}`StandardLP` (one variable per
vertex), and feasibility and the objective value are proved to be preserved.
-/

namespace CLRS
namespace Chapter29
namespace ShortestPathLP

open Chapter24
open Matrix
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Feasibility constraints of the CLRS shortest-path LP. -/
def IsFeasible (G : WeightedGraph V) (s : V) (d : V → ℝ) : Prop :=
  d s = 0 ∧ ∀ u v, (u, v) ∈ G.edges → d v ≤ d u + G.w u v

/-- Optimality for the maximization objective {lit}`d t`. -/
def IsOptimal (G : WeightedGraph V) (s t : V) (d : V → ℝ) : Prop :=
  IsFeasible G s d ∧ ∀ e, IsFeasible G s e → e t ≤ d t

/-- Every feasible potential is a lower bound on the weight of every walk from
the source.  This is the core correctness property of the formulation. -/
theorem feasible_le_walkWeight {G : WeightedGraph V} {s t : V} {d : V → ℝ}
    (hd : IsFeasible G s d) (p : List V) (hp : G.IsWalkFrom s t p) :
    d t ≤ Chapter24.WeightedGraph.walkWeight G.w p := by
  have h := Chapter24.WeightedGraph.le_add_walkWeight_of_potential G d hd.2 s t p hp
  simpa [hd.1] using h

/-- If a feasible potential is attained by an actual source-to-target walk,
then it solves the shortest-path LP. -/
theorem optimal_of_attained_walk {G : WeightedGraph V} {s t : V} {d : V → ℝ}
    (hd : IsFeasible G s d) (p : List V) (hp : G.IsWalkFrom s t p)
    (hweight : Chapter24.WeightedGraph.walkWeight G.w p = d t) : IsOptimal G s t d := by
  refine ⟨hd, ?_⟩
  intro e he
  calc
    e t ≤ Chapter24.WeightedGraph.walkWeight G.w p := feasible_le_walkWeight he p hp
    _ = d t := hweight

/-! ## Finite standard-form encoding -/

/-- The type of directed edges that are actually present in the graph. -/
abbrev Edge (G : WeightedGraph V) := {e : V × V // e ∈ G.edges}

/-- The general-form program for the shortest-path LP: maximize {lit}`d t`
subject to {lit}`d s = 0` and {lit}`d v - d u ≤ w u v` on every edge.  All
vertices are free variables. -/
noncomputable def toGeneralLP (G : WeightedGraph V) (s t : V) : GeneralLP where
  n := Fintype.card V
  m := Fintype.card (Edge G) + 1
  maximize := true
  c := fun j => if (Fintype.equivFin V).symm j = t then 1 else 0
  rel := fun i =>
    Fin.cases
      (ConstraintRel.eq)
      (fun _ => ConstraintRel.le)
      i
  A := fun i =>
    Fin.cases
      (fun j => if (Fintype.equivFin V).symm j = s then 1 else 0)
      (fun e j =>
        let uv := (Fintype.equivFin (Edge G)).symm e
        (if (Fintype.equivFin V).symm j = uv.1.2 then 1 else 0) -
          (if (Fintype.equivFin V).symm j = uv.1.1 then 1 else 0))
      i
  b := fun i =>
    Fin.cases
      (0 : ℝ)
      (fun e =>
        let uv := (Fintype.equivFin (Edge G)).symm e
        G.w uv.1.1 uv.1.2)
      i
  free := fun _ => true

/-- The index of the source-equality constraint. -/
abbrev sourceIndex (G : WeightedGraph V) : Fin (Fintype.card (Edge G) + 1) := 0

/-- The index of the constraint attached to a present edge. -/
abbrev edgeIndex (G : WeightedGraph V) (e : Fin (Fintype.card (Edge G))) :
    Fin (Fintype.card (Edge G) + 1) :=
  e.succ

lemma A_source (G : WeightedGraph V) (s t : V) (j : Fin (Fintype.card V)) :
    (toGeneralLP G s t).A (sourceIndex G) j =
      if (Fintype.equivFin V).symm j = s then 1 else 0 := by
  simp [toGeneralLP, sourceIndex]

lemma b_source (G : WeightedGraph V) (s t : V) :
    (toGeneralLP G s t).b (sourceIndex G) = 0 := by
  simp [toGeneralLP, sourceIndex]

lemma rel_source (G : WeightedGraph V) (s t : V) :
    (toGeneralLP G s t).rel (sourceIndex G) = ConstraintRel.eq := by
  simp [toGeneralLP, sourceIndex]

lemma A_edge (G : WeightedGraph V) (s t : V) (e : Fin (Fintype.card (Edge G)))
    (j : Fin (Fintype.card V)) :
    (toGeneralLP G s t).A (edgeIndex G e) j =
      (if (Fintype.equivFin V).symm j = ((Fintype.equivFin (Edge G)).symm e).1.2 then 1 else 0) -
        (if (Fintype.equivFin V).symm j = ((Fintype.equivFin (Edge G)).symm e).1.1 then 1 else 0) := by
  simp [toGeneralLP, edgeIndex]

lemma b_edge (G : WeightedGraph V) (s t : V) (e : Fin (Fintype.card (Edge G))) :
    (toGeneralLP G s t).b (edgeIndex G e) =
      G.w ((Fintype.equivFin (Edge G)).symm e).1.1 ((Fintype.equivFin (Edge G)).symm e).1.2 := by
  simp [toGeneralLP, edgeIndex]

lemma rel_edge (G : WeightedGraph V) (s t : V) (e : Fin (Fintype.card (Edge G))) :
    (toGeneralLP G s t).rel (edgeIndex G e) = ConstraintRel.le := by
  simp [toGeneralLP, edgeIndex]

/-- The source row of the encoded constraint matrix reads out {lit}`d s`. -/
lemma mulVec_source (G : WeightedGraph V) (s t : V) (d : V → ℝ) :
    ((toGeneralLP G s t).A *ᵥ FinEncoding.lift d) (sourceIndex G) = d s := by
  calc
    ((toGeneralLP G s t).A *ᵥ FinEncoding.lift d) (sourceIndex G)
        = ∑ j : Fin (Fintype.card V), (toGeneralLP G s t).A (sourceIndex G) j * FinEncoding.lift d j := by rfl
    _ = ∑ j : Fin (Fintype.card V),
          (if (Fintype.equivFin V).symm j = s then 1 else 0) * FinEncoding.lift d j := by
          simp only [A_source]
    _ = d s := FinEncoding.sum_indicator s d

/-- An edge row of the encoded constraint matrix reads out {lit}`d v - d u`. -/
lemma mulVec_edge (G : WeightedGraph V) (s t : V) (e : Fin (Fintype.card (Edge G)))
    (d : V → ℝ) :
    ((toGeneralLP G s t).A *ᵥ FinEncoding.lift d) (edgeIndex G e) =
      d ((Fintype.equivFin (Edge G)).symm e).1.2 - d ((Fintype.equivFin (Edge G)).symm e).1.1 := by
  calc
    ((toGeneralLP G s t).A *ᵥ FinEncoding.lift d) (edgeIndex G e)
        = ∑ j : Fin (Fintype.card V), (toGeneralLP G s t).A (edgeIndex G e) j * FinEncoding.lift d j := by rfl
    _ = ∑ j : Fin (Fintype.card V),
          ((if (Fintype.equivFin V).symm j = ((Fintype.equivFin (Edge G)).symm e).1.2 then 1 else 0) -
             (if (Fintype.equivFin V).symm j = ((Fintype.equivFin (Edge G)).symm e).1.1 then 1 else 0)) *
            FinEncoding.lift d j := by
          simp only [A_edge]
    _ = (∑ j : Fin (Fintype.card V),
          (if (Fintype.equivFin V).symm j = ((Fintype.equivFin (Edge G)).symm e).1.2 then 1 else 0) * FinEncoding.lift d j) -
          (∑ j : Fin (Fintype.card V),
          (if (Fintype.equivFin V).symm j = ((Fintype.equivFin (Edge G)).symm e).1.1 then 1 else 0) * FinEncoding.lift d j) := by
          simp only [sub_mul, Finset.sum_sub_distrib]
    _ = d ((Fintype.equivFin (Edge G)).symm e).1.2 - d ((Fintype.equivFin (Edge G)).symm e).1.1 := by
          rw [FinEncoding.sum_indicator, FinEncoding.sum_indicator]

/-- Semantic feasibility is exactly encoded general-form feasibility. -/
theorem feasible_iff_generalLP (G : WeightedGraph V) (s t : V) (d : V → ℝ) :
    IsFeasible G s d ↔ (toGeneralLP G s t).IsFeasible (FinEncoding.lift d) := by
  unfold IsFeasible GeneralLP.IsFeasible
  constructor
  · intro hd
    refine ⟨?_, ?_⟩
    · intro j hfree
      exfalso
      simpa [toGeneralLP] using hfree
    · intro i
      exact Fin.cases (motive := fun i => match (toGeneralLP G s t).rel i with
          | ConstraintRel.le => ((toGeneralLP G s t).A *ᵥ FinEncoding.lift d) i ≤ (toGeneralLP G s t).b i
          | ConstraintRel.eq => ((toGeneralLP G s t).A *ᵥ FinEncoding.lift d) i = (toGeneralLP G s t).b i
          | ConstraintRel.ge => (toGeneralLP G s t).b i ≤ ((toGeneralLP G s t).A *ᵥ FinEncoding.lift d) i)
        (by
          rw [rel_source, mulVec_source, b_source]
          exact hd.1)
        (fun e => by
          rw [rel_edge, mulVec_edge, b_edge]
          have h := hd.2 ((Fintype.equivFin (Edge G)).symm e).1.1 ((Fintype.equivFin (Edge G)).symm e).1.2 ((Fintype.equivFin (Edge G)).symm e).2
          linarith)
        i
  · intro h
    refine ⟨?_, ?_⟩
    · have hsource := h.2 (sourceIndex G)
      rw [rel_source] at hsource
      rw [mulVec_source, b_source] at hsource
      exact hsource
    · intro u v huv
      let e : Edge G := ⟨(u, v), huv⟩
      have hedge := h.2 (edgeIndex G (Fintype.equivFin (Edge G) e))
      rw [rel_edge] at hedge
      rw [mulVec_edge, b_edge] at hedge
      have hedge' : d v - d u ≤ G.w u v := by simpa [e] using hedge
      linarith

/-- The general-form objective reads out {lit}`d t`. -/
lemma objective_generalLP (G : WeightedGraph V) (s t : V) (d : V → ℝ) :
    (toGeneralLP G s t).objective (FinEncoding.lift d) = d t := by
  dsimp [GeneralLP.objective, toGeneralLP]
  simp only [dotProduct]
  rw [FinEncoding.sum_reindex]
  simp only [FinEncoding.lift]
  rw [Finset.sum_eq_single t]
  · simp
  · intro v _ hv; simp [hv]
  · intro h; exact False.elim (h (Finset.mem_univ t))

/-- The finite standard-form program obtained by normalizing the shortest-path
general program. -/
noncomputable def toStandardLP (G : WeightedGraph V) (s t : V) :=
  (toGeneralLP G s t).toStandardLP

/-- The expansion of a potential to the normalized standard-form variable
vector. -/
noncomputable def fullLift (G : WeightedGraph V) (s t : V) (d : V → ℝ) :
    Fin (Fintype.card V + Fintype.card V) → ℝ :=
  (toGeneralLP G s t).lift (FinEncoding.lift d)

/-- The normalized standard-form objective is exactly the shortest-path
objective {lit}`d t`. -/
theorem objective_toStandardLP (G : WeightedGraph V) (s t : V) (d : V → ℝ) :
    (toStandardLP G s t).objective (fullLift G s t d) = d t := by
  unfold toStandardLP fullLift
  rw [GeneralLP.objective_lift]
  rw [objective_generalLP]
  simp [toGeneralLP, GeneralLP.objectiveSign]

/-- Feasibility is exactly preserved under the finite standard-form encoding. -/
theorem feasible_iff_toStandardLP (G : WeightedGraph V) (s t : V) (d : V → ℝ) :
    IsFeasible G s d ↔ (toStandardLP G s t).IsFeasible (fullLift G s t d) := by
  unfold toStandardLP fullLift
  rw [← GeneralLP.feasible_iff_lift]
  exact feasible_iff_generalLP G s t d

end ShortestPathLP
end Chapter29
end CLRS

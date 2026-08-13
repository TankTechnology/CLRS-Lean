import CLRSLean.FourthEdition.Chapter_29.Section_29_1_Standard_And_Slack_Forms.Normalization
import CLRSLean.FourthEdition.Chapter_29.Section_29_2_Formulating_Problems_As_Linear_Programs.NetworkFlow

/-!
# 29.2: Maximum flow as a linear program

The variables are the gross directed flows {lit}`f u v`.  The constraints are
nonnegativity, capacity, and conservation at every vertex other than
{lit}`s,t`; the objective is the net flow leaving {lit}`s`, exactly as in CLRS
§29.2.

This module also records the finite standard-form encoding: one nonnegative
variable per ordered pair, a capacity inequality per ordered pair, and a
conservation equality per internal vertex, reindexed into a concrete
{lit}`StandardLP`.
-/

namespace CLRS
namespace Chapter29
namespace MaximumFlowLP

open Finset
open Matrix
open scoped BigOperators

variable {V : Type*} [Fintype V] (N : FlowNetwork V)

/-- The constraints of the maximum-flow LP. -/
def IsFeasible (f : V → V → ℝ) : Prop :=
  (∀ u v, 0 ≤ f u v) ∧
  (∀ u v, f u v ≤ N.capacity u v) ∧
  ∀ u, u ≠ N.source → u ≠ N.sink → FlowNetwork.ConservesAt f u

/-- The textbook maximum-flow objective: source outflow minus source inflow. -/
def objective (f : V → V → ℝ) : ℝ := FlowNetwork.netOutflow f N.source

/-- A feasible flow maximizing the source outflow. -/
def IsOptimal (f : V → V → ℝ) : Prop :=
  IsFeasible N f ∧ ∀ g, IsFeasible N g → objective N g ≤ objective N f

/-- The displayed LP constraints are precisely the usual finite-network flow
constraints. -/
theorem isFeasible_iff (f : V → V → ℝ) : IsFeasible N f ↔ N.IsFlow f := by
  simp only [IsFeasible, FlowNetwork.IsFlow, FlowNetwork.IsCapacityFeasible]
  tauto

/-- The LP optimum is precisely a maximum flow under the same objective. -/
theorem isOptimal_iff (f : V → V → ℝ) :
    IsOptimal N f ↔
      N.IsFlow f ∧ ∀ g, N.IsFlow g →
        FlowNetwork.netOutflow g N.source ≤ FlowNetwork.netOutflow f N.source := by
  simp only [IsOptimal, objective, isFeasible_iff]

/-! ## Finite standard-form encoding -/

section Encoding

variable [DecidableEq V]

/-- The internal vertices at which flow is conserved. -/
abbrev Internal (N : FlowNetwork V) := {u : V // u ≠ N.source ∧ u ≠ N.sink}

/-- The general-form program for the maximum-flow LP: one nonnegative variable
per ordered pair, a capacity inequality per ordered pair, and a conservation
equality per internal vertex. -/
noncomputable def toGeneralLP (N : FlowNetwork V) : GeneralLP where
  n := Fintype.card (V × V)
  m := Fintype.card (V × V) + Fintype.card (Internal N)
  maximize := true
  c := fun j =>
    (if ((Fintype.equivFin (V × V)).symm j).1 = N.source then 1 else 0) -
      (if ((Fintype.equivFin (V × V)).symm j).2 = N.source then 1 else 0)
  rel := fun i =>
    Fin.addCases (motive := fun _ => ConstraintRel)
      (fun _ => ConstraintRel.le)
      (fun _ => ConstraintRel.eq)
      i
  A := fun i =>
    Fin.addCases (motive := fun _ => Fin (Fintype.card (V × V)) → ℝ)
      (fun e j => if j = e then 1 else 0)
      (fun u j =>
        let v := ((Fintype.equivFin (Internal N)).symm u).1
        (if ((Fintype.equivFin (V × V)).symm j).1 = v then 1 else 0) -
          (if ((Fintype.equivFin (V × V)).symm j).2 = v then 1 else 0))
      i
  b := fun i =>
    Fin.addCases (motive := fun _ => ℝ)
      (fun e => N.capacity ((Fintype.equivFin (V × V)).symm e).1 ((Fintype.equivFin (V × V)).symm e).2)
      (fun _ => 0)
      i
  free := fun _ => false

/-- The index of the capacity constraint for a directed pair. -/
abbrev capIndex (N : FlowNetwork V) (e : Fin (Fintype.card (V × V))) :
    Fin (Fintype.card (V × V) + Fintype.card (Internal N)) :=
  Fin.castAdd (Fintype.card (Internal N)) e

/-- The index of the conservation constraint for an internal vertex. -/
abbrev consIndex (N : FlowNetwork V) (u : Fin (Fintype.card (Internal N))) :
    Fin (Fintype.card (V × V) + Fintype.card (Internal N)) :=
  Fin.natAdd (Fintype.card (V × V)) u

lemma A_cap (N : FlowNetwork V) (e : Fin (Fintype.card (V × V))) (j : Fin (Fintype.card (V × V))) :
    (toGeneralLP N).A (capIndex N e) j = if j = e then 1 else 0 := by
  dsimp [toGeneralLP, capIndex]
  rw [FinEncoding.addCases_castAdd]

lemma b_cap (N : FlowNetwork V) (e : Fin (Fintype.card (V × V))) :
    (toGeneralLP N).b (capIndex N e) =
      N.capacity ((Fintype.equivFin (V × V)).symm e).1 ((Fintype.equivFin (V × V)).symm e).2 := by
  dsimp [toGeneralLP, capIndex]
  rw [FinEncoding.addCases_castAdd]

lemma rel_cap (N : FlowNetwork V) (e : Fin (Fintype.card (V × V))) :
    (toGeneralLP N).rel (capIndex N e) = ConstraintRel.le := by
  dsimp [toGeneralLP, capIndex]
  rw [FinEncoding.addCases_castAdd]

lemma A_cons (N : FlowNetwork V) (u : Fin (Fintype.card (Internal N))) (j : Fin (Fintype.card (V × V))) :
    (toGeneralLP N).A (consIndex N u) j =
      (if ((Fintype.equivFin (V × V)).symm j).1 = ((Fintype.equivFin (Internal N)).symm u).1 then 1 else 0) -
        (if ((Fintype.equivFin (V × V)).symm j).2 = ((Fintype.equivFin (Internal N)).symm u).1 then 1 else 0) := by
  dsimp [toGeneralLP, consIndex]
  rw [FinEncoding.addCases_natAdd]

lemma b_cons (N : FlowNetwork V) (u : Fin (Fintype.card (Internal N))) :
    (toGeneralLP N).b (consIndex N u) = 0 := by
  dsimp [toGeneralLP, consIndex]
  rw [FinEncoding.addCases_natAdd]

lemma rel_cons (N : FlowNetwork V) (u : Fin (Fintype.card (Internal N))) :
    (toGeneralLP N).rel (consIndex N u) = ConstraintRel.eq := by
  dsimp [toGeneralLP, consIndex]
  rw [FinEncoding.addCases_natAdd]

/-- A capacity row reads out the gross flow on its directed pair. -/
lemma mulVec_cap (N : FlowNetwork V) (e : Fin (Fintype.card (V × V))) (f : V → V → ℝ) :
    ((toGeneralLP N).A *ᵥ FinEncoding.lift₂ f) (capIndex N e) = FinEncoding.lift₂ f e := by
  calc
    ((toGeneralLP N).A *ᵥ FinEncoding.lift₂ f) (capIndex N e)
        = ∑ j : Fin (Fintype.card (V × V)), (toGeneralLP N).A (capIndex N e) j * FinEncoding.lift₂ f j := by rfl
    _ = ∑ j : Fin (Fintype.card (V × V)), (if j = e then 1 else 0) * FinEncoding.lift₂ f j := by
          simp only [A_cap]
    _ = FinEncoding.lift₂ f e := FinEncoding.sum_indicator_fin e (FinEncoding.lift₂ f)

/-- A conservation row reads out the net outflow at its vertex. -/
lemma mulVec_cons (N : FlowNetwork V) (u : Fin (Fintype.card (Internal N))) (f : V → V → ℝ) :
    ((toGeneralLP N).A *ᵥ FinEncoding.lift₂ f) (consIndex N u) =
      FlowNetwork.outflow f ((Fintype.equivFin (Internal N)).symm u).1 -
        FlowNetwork.inflow f ((Fintype.equivFin (Internal N)).symm u).1 := by
  calc
    ((toGeneralLP N).A *ᵥ FinEncoding.lift₂ f) (consIndex N u)
        = ∑ j : Fin (Fintype.card (V × V)), (toGeneralLP N).A (consIndex N u) j * FinEncoding.lift₂ f j := by rfl
    _ = ∑ j : Fin (Fintype.card (V × V)),
          ((if ((Fintype.equivFin (V × V)).symm j).1 = ((Fintype.equivFin (Internal N)).symm u).1 then 1 else 0) -
             (if ((Fintype.equivFin (V × V)).symm j).2 = ((Fintype.equivFin (Internal N)).symm u).1 then 1 else 0)) *
            FinEncoding.lift₂ f j := by
          simp only [A_cons]
    _ = (∑ j : Fin (Fintype.card (V × V)),
          (if ((Fintype.equivFin (V × V)).symm j).1 = ((Fintype.equivFin (Internal N)).symm u).1 then 1 else 0) * FinEncoding.lift₂ f j) -
          (∑ j : Fin (Fintype.card (V × V)),
          (if ((Fintype.equivFin (V × V)).symm j).2 = ((Fintype.equivFin (Internal N)).symm u).1 then 1 else 0) * FinEncoding.lift₂ f j) := by
          simp only [sub_mul, Finset.sum_sub_distrib]
    _ = (∑ b : V, f ((Fintype.equivFin (Internal N)).symm u).1 b) -
          (∑ b : V, f b ((Fintype.equivFin (Internal N)).symm u).1) := by
          rw [FinEncoding.sum_indicator_fst, FinEncoding.sum_indicator_snd]
    _ = FlowNetwork.outflow f ((Fintype.equivFin (Internal N)).symm u).1 -
          FlowNetwork.inflow f ((Fintype.equivFin (Internal N)).symm u).1 := rfl

/-- Semantic feasibility is exactly encoded general-form feasibility. -/
theorem feasible_iff_generalLP (N : FlowNetwork V) (f : V → V → ℝ) :
    IsFeasible N f ↔ (toGeneralLP N).IsFeasible (FinEncoding.lift₂ f) := by
  unfold IsFeasible GeneralLP.IsFeasible
  constructor
  · intro hd
    refine ⟨?_, ?_⟩
    · intro j hfree
      simpa [FinEncoding.lift₂, FinEncoding.lift, Function.uncurry] using
        (hd.1 ((Fintype.equivFin (V × V)).symm j).1 ((Fintype.equivFin (V × V)).symm j).2)
    · intro i
      exact Fin.addCases (motive := fun i => match (toGeneralLP N).rel i with
          | ConstraintRel.le => ((toGeneralLP N).A *ᵥ FinEncoding.lift₂ f) i ≤ (toGeneralLP N).b i
          | ConstraintRel.eq => ((toGeneralLP N).A *ᵥ FinEncoding.lift₂ f) i = (toGeneralLP N).b i
          | ConstraintRel.ge => (toGeneralLP N).b i ≤ ((toGeneralLP N).A *ᵥ FinEncoding.lift₂ f) i)
        (fun e => by
          rw [rel_cap, mulVec_cap, b_cap]
          simpa [FinEncoding.lift₂, FinEncoding.lift, Function.uncurry] using
            (hd.2.1 ((Fintype.equivFin (V × V)).symm e).1 ((Fintype.equivFin (V × V)).symm e).2))
        (fun u => by
          rw [rel_cons, mulVec_cons, b_cons]
          have hc := hd.2.2 ((Fintype.equivFin (Internal N)).symm u).1
            ((Fintype.equivFin (Internal N)).symm u).2.1
            ((Fintype.equivFin (Internal N)).symm u).2.2
          unfold FlowNetwork.ConservesAt at hc
          linarith)
        i
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro u v
      have hn := h.1 (Fintype.equivFin (V × V) (u, v))
      simpa [FinEncoding.lift₂, FinEncoding.lift, Function.uncurry] using (hn (by simp [toGeneralLP]))
    · intro u v
      have hc := h.2 (capIndex N (Fintype.equivFin (V × V) (u, v)))
      rw [rel_cap] at hc
      rw [mulVec_cap, b_cap] at hc
      simpa [FinEncoding.lift₂, FinEncoding.lift, Function.uncurry] using hc
    · intro u hu hw
      let e : Internal N := ⟨u, ⟨hu, hw⟩⟩
      have hcons := h.2 (consIndex N (Fintype.equivFin (Internal N) e))
      rw [rel_cons] at hcons
      rw [mulVec_cons, b_cons] at hcons
      have hcons' : FlowNetwork.outflow f u - FlowNetwork.inflow f u = 0 := by
        simpa [e] using hcons
      unfold FlowNetwork.ConservesAt
      linarith

/-- The general-form objective is the textbook maximum-flow objective. -/
lemma objective_generalLP (N : FlowNetwork V) (f : V → V → ℝ) :
    (toGeneralLP N).objective (FinEncoding.lift₂ f) = objective N f := by
  dsimp [GeneralLP.objective, toGeneralLP, objective, FlowNetwork.netOutflow, FlowNetwork.outflow, FlowNetwork.inflow]
  simp only [dotProduct, sub_mul, Finset.sum_sub_distrib]
  rw [FinEncoding.sum_indicator_fst, FinEncoding.sum_indicator_snd]

/-- The finite standard-form program obtained by normalizing the maximum-flow
general program. -/
noncomputable def toStandardLP (N : FlowNetwork V) :=
  (toGeneralLP N).toStandardLP

/-- The expansion of a gross-flow vector to the normalized standard-form
variable vector. -/
noncomputable def fullLift (N : FlowNetwork V) (f : V → V → ℝ) :
    Fin (Fintype.card (V × V) + Fintype.card (V × V)) → ℝ :=
  (toGeneralLP N).lift (FinEncoding.lift₂ f)

/-- The normalized standard-form objective is the maximum-flow objective. -/
theorem objective_toStandardLP (N : FlowNetwork V) (f : V → V → ℝ) :
    (toStandardLP N).objective (fullLift N f) = objective N f := by
  unfold toStandardLP fullLift
  rw [GeneralLP.objective_lift]
  rw [objective_generalLP]
  simp [toGeneralLP, GeneralLP.objectiveSign]

/-- Feasibility is exactly preserved under the finite standard-form encoding. -/
theorem feasible_iff_toStandardLP (N : FlowNetwork V) (f : V → V → ℝ) :
    IsFeasible N f ↔ (toStandardLP N).IsFeasible (fullLift N f) := by
  unfold toStandardLP fullLift
  rw [← GeneralLP.feasible_iff_lift]
  exact feasible_iff_generalLP N f

end Encoding

end MaximumFlowLP
end Chapter29
end CLRS

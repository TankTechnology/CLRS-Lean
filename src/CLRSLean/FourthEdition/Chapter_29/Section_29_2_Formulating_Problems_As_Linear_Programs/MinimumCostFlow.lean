import CLRSLean.FourthEdition.Chapter_29.Section_29_1_Standard_And_Slack_Forms.Normalization
import CLRSLean.FourthEdition.Chapter_29.Section_29_2_Formulating_Problems_As_Linear_Programs.NetworkFlow

/-!
# 29.2: Minimum-cost flow as a linear program

In addition to capacities, a network assigns a unit cost to every directed
pair.  A demand-{lit}`d` flow has net source outflow {lit}`d`; minimizing the
sum of unit cost times flow gives the CLRS minimum-cost-flow formulation.

This module also records the finite standard-form encoding: one nonnegative
variable per ordered pair, a capacity inequality per ordered pair, a
conservation equality per internal vertex, and one source-demand equality,
reindexed into a concrete {lit}`StandardLP`.
-/

namespace CLRS
namespace Chapter29

open Finset
open Matrix
open scoped BigOperators

/-- A capacitated network with a real unit cost on each directed pair. -/
structure CostedFlowNetwork (V : Type*) [Fintype V] extends FlowNetwork V where
  cost : V → V → ℝ

namespace MinimumCostFlowLP

variable {V : Type*} [Fintype V] (N : CostedFlowNetwork V) (demand : ℝ)

/-- The capacity, conservation, and exact-demand constraints. -/
def IsFeasible (f : V → V → ℝ) : Prop :=
  N.toFlowNetwork.IsFlow f ∧
    FlowNetwork.netOutflow f N.source = demand

/-- Total cost {lit}`Σ_u Σ_v a_uv f_uv`. -/
def objective (f : V → V → ℝ) : ℝ :=
  ∑ u, ∑ v, N.cost u v * f u v

/-- A demand flow of minimum total cost. -/
def IsOptimal (f : V → V → ℝ) : Prop :=
  IsFeasible N demand f ∧
    ∀ g, IsFeasible N demand g → objective N f ≤ objective N g

/-- The LP constraints are exactly capacity-feasible flow plus the prescribed
source demand. -/
theorem isFeasible_iff (f : V → V → ℝ) :
    IsFeasible N demand f ↔
      N.toFlowNetwork.IsFlow f ∧
        FlowNetwork.netOutflow f N.source = demand := by
  rfl

/-- The minimization specification agrees exactly with minimum-cost demand
flow. -/
theorem isOptimal_iff (f : V → V → ℝ) :
    IsOptimal N demand f ↔
      (N.toFlowNetwork.IsFlow f ∧
        FlowNetwork.netOutflow f N.source = demand) ∧
      ∀ g, (N.toFlowNetwork.IsFlow g ∧
        FlowNetwork.netOutflow g N.source = demand) →
        (∑ u, ∑ v, N.cost u v * f u v) ≤
          ∑ u, ∑ v, N.cost u v * g u v := by
  rfl

/-! ## Finite standard-form encoding -/

section Encoding

variable [DecidableEq V]

/-- The internal vertices at which flow is conserved. -/
abbrev Internal (N : CostedFlowNetwork V) := {u : V // u ≠ N.source ∧ u ≠ N.sink}

/-- The general-form program for the minimum-cost-flow LP: one nonnegative
variable per ordered pair, a capacity inequality per ordered pair, a
conservation equality per internal vertex, and a source-demand equality.  The
objective is minimized (cost is the sum of unit cost times flow). -/
noncomputable def toGeneralLP (N : CostedFlowNetwork V) (demand : ℝ) : GeneralLP where
  n := Fintype.card (V × V)
  m := Fintype.card (V × V) + Fintype.card (Internal N) + 1
  maximize := false
  c := fun j => N.cost ((Fintype.equivFin (V × V)).symm j).1 ((Fintype.equivFin (V × V)).symm j).2
  rel := fun i =>
    Fin.cases
      (ConstraintRel.eq)
      (fun i => Fin.addCases (motive := fun _ => ConstraintRel)
        (fun _ => ConstraintRel.le)
        (fun _ => ConstraintRel.eq)
        i)
      i
  A := fun i =>
    Fin.cases
      (fun j =>
        (if ((Fintype.equivFin (V × V)).symm j).1 = N.source then 1 else 0) -
          (if ((Fintype.equivFin (V × V)).symm j).2 = N.source then 1 else 0))
      (fun i j => Fin.addCases (motive := fun _ => ℝ)
        (fun e => if j = e then 1 else 0)
        (fun u =>
          let v := ((Fintype.equivFin (Internal N)).symm u).1
          (if ((Fintype.equivFin (V × V)).symm j).1 = v then 1 else 0) -
            (if ((Fintype.equivFin (V × V)).symm j).2 = v then 1 else 0))
        i)
      i
  b := fun i =>
    Fin.cases
      (demand)
      (fun i => Fin.addCases (motive := fun _ => ℝ)
        (fun e => N.capacity ((Fintype.equivFin (V × V)).symm e).1 ((Fintype.equivFin (V × V)).symm e).2)
        (fun _ => 0)
        i)
      i
  free := fun _ => false

/-- The index of the source-demand equality constraint. -/
abbrev demandIndex (N : CostedFlowNetwork V) :
    Fin (Fintype.card (V × V) + Fintype.card (Internal N) + 1) := 0

/-- The index of the capacity constraint for a directed pair. -/
abbrev capIndex (N : CostedFlowNetwork V) (e : Fin (Fintype.card (V × V))) :
    Fin (Fintype.card (V × V) + Fintype.card (Internal N) + 1) :=
  (Fin.castAdd (Fintype.card (Internal N)) e).succ

/-- The index of the conservation constraint for an internal vertex. -/
abbrev consIndex (N : CostedFlowNetwork V) (u : Fin (Fintype.card (Internal N))) :
    Fin (Fintype.card (V × V) + Fintype.card (Internal N) + 1) :=
  (Fin.natAdd (Fintype.card (V × V)) u).succ

lemma A_demand (N : CostedFlowNetwork V) (demand : ℝ) (j : Fin (Fintype.card (V × V))) :
    (toGeneralLP N demand).A (demandIndex N) j =
      (if ((Fintype.equivFin (V × V)).symm j).1 = N.source then 1 else 0) -
        (if ((Fintype.equivFin (V × V)).symm j).2 = N.source then 1 else 0) := by
  simp [toGeneralLP, demandIndex]

lemma b_demand (N : CostedFlowNetwork V) (demand : ℝ) :
    (toGeneralLP N demand).b (demandIndex N) = demand := by
  simp [toGeneralLP, demandIndex]

lemma rel_demand (N : CostedFlowNetwork V) (demand : ℝ) :
    (toGeneralLP N demand).rel (demandIndex N) = ConstraintRel.eq := by
  simp [toGeneralLP, demandIndex]

lemma A_cap (N : CostedFlowNetwork V) (demand : ℝ) (e : Fin (Fintype.card (V × V))) (j : Fin (Fintype.card (V × V))) :
    (toGeneralLP N demand).A (capIndex N e) j = if j = e then 1 else 0 := by
  dsimp [toGeneralLP, capIndex]
  rw [FinEncoding.addCases_castAdd]

lemma b_cap (N : CostedFlowNetwork V) (demand : ℝ) (e : Fin (Fintype.card (V × V))) :
    (toGeneralLP N demand).b (capIndex N e) =
      N.capacity ((Fintype.equivFin (V × V)).symm e).1 ((Fintype.equivFin (V × V)).symm e).2 := by
  dsimp [toGeneralLP, capIndex]
  rw [FinEncoding.addCases_castAdd]

lemma rel_cap (N : CostedFlowNetwork V) (demand : ℝ) (e : Fin (Fintype.card (V × V))) :
    (toGeneralLP N demand).rel (capIndex N e) = ConstraintRel.le := by
  dsimp [toGeneralLP, capIndex]
  rw [FinEncoding.addCases_castAdd]

lemma A_cons (N : CostedFlowNetwork V) (demand : ℝ) (u : Fin (Fintype.card (Internal N))) (j : Fin (Fintype.card (V × V))) :
    (toGeneralLP N demand).A (consIndex N u) j =
      (if ((Fintype.equivFin (V × V)).symm j).1 = ((Fintype.equivFin (Internal N)).symm u).1 then 1 else 0) -
        (if ((Fintype.equivFin (V × V)).symm j).2 = ((Fintype.equivFin (Internal N)).symm u).1 then 1 else 0) := by
  dsimp [toGeneralLP, consIndex]
  rw [FinEncoding.addCases_natAdd]

lemma b_cons (N : CostedFlowNetwork V) (demand : ℝ) (u : Fin (Fintype.card (Internal N))) :
    (toGeneralLP N demand).b (consIndex N u) = 0 := by
  dsimp [toGeneralLP, consIndex]
  rw [FinEncoding.addCases_natAdd]

lemma rel_cons (N : CostedFlowNetwork V) (demand : ℝ) (u : Fin (Fintype.card (Internal N))) :
    (toGeneralLP N demand).rel (consIndex N u) = ConstraintRel.eq := by
  dsimp [toGeneralLP, consIndex]
  rw [FinEncoding.addCases_natAdd]

/-- The demand row reads out the source net outflow. -/
lemma mulVec_demand (N : CostedFlowNetwork V) (demand : ℝ) (f : V → V → ℝ) :
    ((toGeneralLP N demand).A *ᵥ FinEncoding.lift₂ f) (demandIndex N) =
      FlowNetwork.netOutflow f N.source := by
  calc
    ((toGeneralLP N demand).A *ᵥ FinEncoding.lift₂ f) (demandIndex N)
        = ∑ j : Fin (Fintype.card (V × V)), (toGeneralLP N demand).A (demandIndex N) j * FinEncoding.lift₂ f j := by rfl
    _ = ∑ j : Fin (Fintype.card (V × V)),
          ((if ((Fintype.equivFin (V × V)).symm j).1 = N.source then 1 else 0) -
             (if ((Fintype.equivFin (V × V)).symm j).2 = N.source then 1 else 0)) *
            FinEncoding.lift₂ f j := by
          simp only [A_demand]
    _ = (∑ j : Fin (Fintype.card (V × V)),
          (if ((Fintype.equivFin (V × V)).symm j).1 = N.source then 1 else 0) * FinEncoding.lift₂ f j) -
          (∑ j : Fin (Fintype.card (V × V)),
          (if ((Fintype.equivFin (V × V)).symm j).2 = N.source then 1 else 0) * FinEncoding.lift₂ f j) := by
          simp only [sub_mul, Finset.sum_sub_distrib]
    _ = (∑ b : V, f N.source b) - (∑ b : V, f b N.source) := by
          rw [FinEncoding.sum_indicator_fst, FinEncoding.sum_indicator_snd]
    _ = FlowNetwork.netOutflow f N.source := rfl

/-- A capacity row reads out the gross flow on its directed pair. -/
lemma mulVec_cap (N : CostedFlowNetwork V) (demand : ℝ) (e : Fin (Fintype.card (V × V))) (f : V → V → ℝ) :
    ((toGeneralLP N demand).A *ᵥ FinEncoding.lift₂ f) (capIndex N e) = FinEncoding.lift₂ f e := by
  calc
    ((toGeneralLP N demand).A *ᵥ FinEncoding.lift₂ f) (capIndex N e)
        = ∑ j : Fin (Fintype.card (V × V)), (toGeneralLP N demand).A (capIndex N e) j * FinEncoding.lift₂ f j := by rfl
    _ = ∑ j : Fin (Fintype.card (V × V)), (if j = e then 1 else 0) * FinEncoding.lift₂ f j := by
          simp only [A_cap]
    _ = FinEncoding.lift₂ f e := FinEncoding.sum_indicator_fin e (FinEncoding.lift₂ f)

/-- A conservation row reads out the net outflow at its vertex. -/
lemma mulVec_cons (N : CostedFlowNetwork V) (demand : ℝ) (u : Fin (Fintype.card (Internal N))) (f : V → V → ℝ) :
    ((toGeneralLP N demand).A *ᵥ FinEncoding.lift₂ f) (consIndex N u) =
      FlowNetwork.outflow f ((Fintype.equivFin (Internal N)).symm u).1 -
        FlowNetwork.inflow f ((Fintype.equivFin (Internal N)).symm u).1 := by
  calc
    ((toGeneralLP N demand).A *ᵥ FinEncoding.lift₂ f) (consIndex N u)
        = ∑ j : Fin (Fintype.card (V × V)), (toGeneralLP N demand).A (consIndex N u) j * FinEncoding.lift₂ f j := by rfl
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
theorem feasible_iff_generalLP (N : CostedFlowNetwork V) (demand : ℝ) (f : V → V → ℝ) :
    IsFeasible N demand f ↔ (toGeneralLP N demand).IsFeasible (FinEncoding.lift₂ f) := by
  unfold IsFeasible GeneralLP.IsFeasible FlowNetwork.IsFlow FlowNetwork.IsCapacityFeasible
  constructor
  · intro hd
    refine ⟨?_, ?_⟩
    · intro j hfree
      simpa [FinEncoding.lift₂, FinEncoding.lift, Function.uncurry] using
        (hd.1.1.1 ((Fintype.equivFin (V × V)).symm j).1 ((Fintype.equivFin (V × V)).symm j).2)
    · intro i
      exact Fin.cases (motive := fun i => match (toGeneralLP N demand).rel i with
          | ConstraintRel.le => ((toGeneralLP N demand).A *ᵥ FinEncoding.lift₂ f) i ≤ (toGeneralLP N demand).b i
          | ConstraintRel.eq => ((toGeneralLP N demand).A *ᵥ FinEncoding.lift₂ f) i = (toGeneralLP N demand).b i
          | ConstraintRel.ge => (toGeneralLP N demand).b i ≤ ((toGeneralLP N demand).A *ᵥ FinEncoding.lift₂ f) i)
        (by
          rw [rel_demand, mulVec_demand, b_demand]
          exact hd.2)
        (fun i => by
          exact Fin.addCases (motive := fun i => match (toGeneralLP N demand).rel i.succ with
              | ConstraintRel.le => ((toGeneralLP N demand).A *ᵥ FinEncoding.lift₂ f) i.succ ≤ (toGeneralLP N demand).b i.succ
              | ConstraintRel.eq => ((toGeneralLP N demand).A *ᵥ FinEncoding.lift₂ f) i.succ = (toGeneralLP N demand).b i.succ
              | ConstraintRel.ge => (toGeneralLP N demand).b i.succ ≤ ((toGeneralLP N demand).A *ᵥ FinEncoding.lift₂ f) i.succ)
            (fun e => by
              rw [rel_cap, mulVec_cap, b_cap]
              simpa [FinEncoding.lift₂, FinEncoding.lift, Function.uncurry] using
                (hd.1.1.2 ((Fintype.equivFin (V × V)).symm e).1 ((Fintype.equivFin (V × V)).symm e).2))
            (fun u => by
              rw [rel_cons, mulVec_cons, b_cons]
              have hc := hd.1.2 ((Fintype.equivFin (Internal N)).symm u).1
                ((Fintype.equivFin (Internal N)).symm u).2.1
                ((Fintype.equivFin (Internal N)).symm u).2.2
              unfold FlowNetwork.ConservesAt at hc
              linarith)
            i)
        i
  · intro h
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
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
    · have hdemand := h.2 (demandIndex N)
      rw [rel_demand] at hdemand
      rw [mulVec_demand, b_demand] at hdemand
      exact hdemand

/-- The general-form objective is the total cost (minimized). -/
lemma objective_generalLP (N : CostedFlowNetwork V) (demand : ℝ) (f : V → V → ℝ) :
    (toGeneralLP N demand).objective (FinEncoding.lift₂ f) = objective N f := by
  dsimp [GeneralLP.objective, toGeneralLP, objective]
  simp only [dotProduct]
  rw [FinEncoding.sum_reindex]
  simp [FinEncoding.lift₂, FinEncoding.lift, Function.uncurry]
  rw [Fintype.sum_prod_type]

/-- The finite standard-form program obtained by normalizing the minimum-cost
general program. -/
noncomputable def toStandardLP (N : CostedFlowNetwork V) (demand : ℝ) :=
  (toGeneralLP N demand).toStandardLP

/-- The expansion of a gross-flow vector to the normalized standard-form
variable vector. -/
noncomputable def fullLift (N : CostedFlowNetwork V) (demand : ℝ) (f : V → V → ℝ) :
    Fin (Fintype.card (V × V) + Fintype.card (V × V)) → ℝ :=
  (toGeneralLP N demand).lift (FinEncoding.lift₂ f)

/-- The normalized standard-form objective equals the signed total cost. -/
theorem objective_toStandardLP (N : CostedFlowNetwork V) (demand : ℝ) (f : V → V → ℝ) :
    (toStandardLP N demand).objective (fullLift N demand f) = -objective N f := by
  unfold toStandardLP fullLift
  rw [GeneralLP.objective_lift]
  rw [objective_generalLP]
  simp [toGeneralLP, GeneralLP.objectiveSign]

/-- Feasibility is exactly preserved under the finite standard-form encoding. -/
theorem feasible_iff_toStandardLP (N : CostedFlowNetwork V) (demand : ℝ) (f : V → V → ℝ) :
    IsFeasible N demand f ↔ (toStandardLP N demand).IsFeasible (fullLift N demand f) := by
  unfold toStandardLP fullLift
  rw [← GeneralLP.feasible_iff_lift]
  exact feasible_iff_generalLP N demand f

end Encoding

end MinimumCostFlowLP
end Chapter29
end CLRS

import CLRSLean.FourthEdition.Chapter_29.Section_29_1_Standard_And_Slack_Forms.Normalization
import CLRSLean.FourthEdition.Chapter_29.Section_29_2_Formulating_Problems_As_Linear_Programs.NetworkFlow

/-!
# 29.2: Multicommodity flow as a linear program

Each commodity has its own source, sink, demand, and nonnegative gross flow.
All commodities share the edge capacities.  The optional cost objective also
records Exercise 29.2-7's minimum-cost multicommodity formulation.

This module also records the finite standard-form encoding: one nonnegative
variable per commodity/ordered-pair, a shared capacity inequality per ordered
pair, a conservation equality per internal commodity/vertex, and a demand
equality per commodity, reindexed into a concrete {lit}`StandardLP`.
-/

namespace CLRS
namespace Chapter29

open Finset
open Matrix
open scoped BigOperators

/-- Source, sink, and nonnegative demand of one commodity. -/
structure Commodity (V : Type*) where
  source : V
  sink : V
  source_ne_sink : source ≠ sink
  demand : ℝ
  demand_nonnegative : 0 ≤ demand

namespace MulticommodityFlowLP

variable {V K : Type*} [Fintype V] [Fintype K]

/-- Total flow of all commodities on one directed pair. -/
def aggregate (f : K → V → V → ℝ) (u v : V) : ℝ := ∑ i, f i u v

/-- The CLRS multicommodity feasibility constraints. -/
def IsFeasible (N : FlowNetwork V) (commodity : K → Commodity V)
    (f : K → V → V → ℝ) : Prop :=
  (∀ i u v, 0 ≤ f i u v) ∧
  (∀ u v, aggregate f u v ≤ N.capacity u v) ∧
  (∀ i u, u ≠ (commodity i).source → u ≠ (commodity i).sink →
    FlowNetwork.ConservesAt (f i) u) ∧
  ∀ i, FlowNetwork.netOutflow (f i) (commodity i).source = (commodity i).demand

/-- An expanded statement of the displayed multicommodity LP. -/
theorem isFeasible_iff (N : FlowNetwork V) (commodity : K → Commodity V)
    (f : K → V → V → ℝ) :
    IsFeasible N commodity f ↔
      (∀ i u v, 0 ≤ f i u v) ∧
      (∀ u v, (∑ i, f i u v) ≤ N.capacity u v) ∧
      (∀ i u, u ≠ (commodity i).source → u ≠ (commodity i).sink →
        FlowNetwork.inflow (f i) u = FlowNetwork.outflow (f i) u) ∧
      ∀ i, FlowNetwork.outflow (f i) (commodity i).source -
          FlowNetwork.inflow (f i) (commodity i).source = (commodity i).demand := by
  rfl

/-- Total cost of the aggregate multicommodity flow. -/
def cost (unitCost : V → V → ℝ) (f : K → V → V → ℝ) : ℝ :=
  ∑ u, ∑ v, unitCost u v * aggregate f u v

/-- Minimum-cost feasible multicommodity routing. -/
def IsMinimumCost (N : FlowNetwork V) (commodity : K → Commodity V)
    (unitCost : V → V → ℝ) (f : K → V → V → ℝ) : Prop :=
  IsFeasible N commodity f ∧
    ∀ g, IsFeasible N commodity g → cost unitCost f ≤ cost unitCost g

/-- Expanded optimality statement for minimum-cost multicommodity flow. -/
theorem isMinimumCost_iff (N : FlowNetwork V) (commodity : K → Commodity V)
    (unitCost : V → V → ℝ) (f : K → V → V → ℝ) :
    IsMinimumCost N commodity unitCost f ↔
      IsFeasible N commodity f ∧
      ∀ g, IsFeasible N commodity g →
        (∑ u, ∑ v, unitCost u v * (∑ i, f i u v)) ≤
          ∑ u, ∑ v, unitCost u v * (∑ i, g i u v) := by
  rfl

/-! ## Finite standard-form encoding -/

section Encoding

variable [DecidableEq V] [DecidableEq K]

/-- Lift a commodity-indexed flow to the `Fin`-indexed vector over
{lit}`K × (V × V)`. -/
noncomputable def lift₃ (f : K → V → V → ℝ) : Fin (Fintype.card (K × (V × V))) → ℝ :=
  FinEncoding.lift (fun p : K × (V × V) => f p.1 p.2.1 p.2.2)

/-- The internal commodity/vertex pairs at which flow is conserved. -/
abbrev Internal (N : FlowNetwork V) (commodity : K → Commodity V) :=
  {p : K × V // p.2 ≠ (commodity p.1).source ∧ p.2 ≠ (commodity p.1).sink}

/-- Sum of an indicator on the commodity and the source coordinate (outflow). -/
lemma sum_indicator_fst_fst (i : K) (u : V) (f : K → V → V → ℝ) :
    (∑ j : Fin (Fintype.card (K × (V × V))),
      (if ((Fintype.equivFin (K × (V × V))).symm j).1 = i ∧
           ((Fintype.equivFin (K × (V × V))).symm j).2.1 = u then 1 else 0) * lift₃ f j) =
      ∑ b : V, f i u b := by
  rw [FinEncoding.sum_reindex]
  simp [lift₃, FinEncoding.lift]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single u]
    · simp
    · intro a _ ha; simp [ha]
    · intro h; exact False.elim (h (Finset.mem_univ u))
  · intro k _ hk; simp [hk]
  · intro h; exact False.elim (h (Finset.mem_univ i))

/-- Sum of an indicator on the commodity and the target coordinate (inflow). -/
lemma sum_indicator_fst_snd (i : K) (u : V) (f : K → V → V → ℝ) :
    (∑ j : Fin (Fintype.card (K × (V × V))),
      (if ((Fintype.equivFin (K × (V × V))).symm j).1 = i ∧
           ((Fintype.equivFin (K × (V × V))).symm j).2.2 = u then 1 else 0) * lift₃ f j) =
      ∑ a : V, f i a u := by
  rw [FinEncoding.sum_reindex]
  simp [lift₃, FinEncoding.lift]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single u]
    · simp
    · intro a _ ha; simp [ha]
    · intro h; exact False.elim (h (Finset.mem_univ u))
  · intro k _ hk; simp [hk]
  · intro h; exact False.elim (h (Finset.mem_univ i))

/-- Sum of an indicator on the directed pair (shared capacity). -/
lemma sum_indicator_pair (u v : V) (f : K → V → V → ℝ) :
    (∑ j : Fin (Fintype.card (K × (V × V))),
      (if ((Fintype.equivFin (K × (V × V))).symm j).2 = (u, v) then 1 else 0) * lift₃ f j) =
      ∑ i : K, f i u v := by
  rw [FinEncoding.sum_reindex]
  simp [lift₃, FinEncoding.lift]
  rw [Fintype.sum_prod_type]
  simp [Finset.sum_ite_eq']

/-- The general-form program for the multicommodity-flow LP. -/
noncomputable def toGeneralLP (N : FlowNetwork V) (commodity : K → Commodity V)
    (unitCost : V → V → ℝ) : GeneralLP where
  n := Fintype.card (K × (V × V))
  m := Fintype.card (V × V) + Fintype.card (Internal N commodity) + Fintype.card K
  maximize := false
  c := fun j => unitCost ((Fintype.equivFin (K × (V × V))).symm j).2.1 ((Fintype.equivFin (K × (V × V))).symm j).2.2
  rel := fun i =>
    Fin.addCases (motive := fun _ => ConstraintRel)
      (fun ij => Fin.addCases (motive := fun _ => ConstraintRel)
        (fun _ => ConstraintRel.le)
        (fun _ => ConstraintRel.eq)
        ij)
      (fun _ => ConstraintRel.eq)
      i
  A := fun i =>
    Fin.addCases (motive := fun _ => Fin (Fintype.card (K × (V × V))) → ℝ)
      (fun ij => Fin.addCases (motive := fun _ => Fin (Fintype.card (K × (V × V))) → ℝ)
        (fun e j => if ((Fintype.equivFin (K × (V × V))).symm j).2 = (Fintype.equivFin (V × V)).symm e then 1 else 0)
        (fun p j =>
          let iu := (Fintype.equivFin (Internal N commodity)).symm p
          (if ((Fintype.equivFin (K × (V × V))).symm j).1 = iu.1.1 ∧
               ((Fintype.equivFin (K × (V × V))).symm j).2.1 = iu.1.2 then 1 else 0) -
            (if ((Fintype.equivFin (K × (V × V))).symm j).1 = iu.1.1 ∧
                 ((Fintype.equivFin (K × (V × V))).symm j).2.2 = iu.1.2 then 1 else 0))
        ij)
      (fun i j =>
        let ci := (Fintype.equivFin K).symm i
        (if ((Fintype.equivFin (K × (V × V))).symm j).1 = ci ∧
             ((Fintype.equivFin (K × (V × V))).symm j).2.1 = (commodity ci).source then 1 else 0) -
          (if ((Fintype.equivFin (K × (V × V))).symm j).1 = ci ∧
               ((Fintype.equivFin (K × (V × V))).symm j).2.2 = (commodity ci).source then 1 else 0))
      i
  b := fun i =>
    Fin.addCases (motive := fun _ => ℝ)
      (fun ij => Fin.addCases (motive := fun _ => ℝ)
        (fun e => N.capacity ((Fintype.equivFin (V × V)).symm e).1 ((Fintype.equivFin (V × V)).symm e).2)
        (fun _ => 0)
        ij)
      (fun i => (commodity ((Fintype.equivFin K).symm i)).demand)
      i
  free := fun _ => false

/-- The index of the shared-capacity constraint for a directed pair. -/
abbrev capIndex (N : FlowNetwork V) (commodity : K → Commodity V) (e : Fin (Fintype.card (V × V))) :
    Fin (Fintype.card (V × V) + Fintype.card (Internal N commodity) + Fintype.card K) :=
  Fin.castAdd (Fintype.card K) (Fin.castAdd (Fintype.card (Internal N commodity)) e)

/-- The index of the conservation constraint for an internal commodity/vertex. -/
abbrev consIndex (N : FlowNetwork V) (commodity : K → Commodity V) (p : Fin (Fintype.card (Internal N commodity))) :
    Fin (Fintype.card (V × V) + Fintype.card (Internal N commodity) + Fintype.card K) :=
  Fin.castAdd (Fintype.card K) (Fin.natAdd (Fintype.card (V × V)) p)

/-- The index of the demand constraint for a commodity. -/
abbrev demandIndex (N : FlowNetwork V) (commodity : K → Commodity V) (i : Fin (Fintype.card K)) :
    Fin (Fintype.card (V × V) + Fintype.card (Internal N commodity) + Fintype.card K) :=
  Fin.natAdd (Fintype.card (V × V) + Fintype.card (Internal N commodity)) i

lemma rel_cap (N : FlowNetwork V) (commodity : K → Commodity V) (e : Fin (Fintype.card (V × V))) :
    (toGeneralLP N commodity (fun _ _ => 0)).rel (capIndex N commodity e) = ConstraintRel.le := by
  dsimp [toGeneralLP, capIndex]
  rw [FinEncoding.addCases_castAdd]
  rw [FinEncoding.addCases_castAdd]

lemma b_cap (N : FlowNetwork V) (commodity : K → Commodity V) (e : Fin (Fintype.card (V × V))) :
    (toGeneralLP N commodity (fun _ _ => 0)).b (capIndex N commodity e) =
      N.capacity ((Fintype.equivFin (V × V)).symm e).1 ((Fintype.equivFin (V × V)).symm e).2 := by
  dsimp [toGeneralLP, capIndex]
  rw [FinEncoding.addCases_castAdd]
  rw [FinEncoding.addCases_castAdd]

lemma A_cap (N : FlowNetwork V) (commodity : K → Commodity V) (e : Fin (Fintype.card (V × V)))
    (j : Fin (Fintype.card (K × (V × V)))) :
    (toGeneralLP N commodity (fun _ _ => 0)).A (capIndex N commodity e) j =
      if ((Fintype.equivFin (K × (V × V))).symm j).2 = (Fintype.equivFin (V × V)).symm e then 1 else 0 := by
  dsimp [toGeneralLP, capIndex]
  rw [FinEncoding.addCases_castAdd]
  rw [FinEncoding.addCases_castAdd]

lemma rel_cons (N : FlowNetwork V) (commodity : K → Commodity V) (p : Fin (Fintype.card (Internal N commodity))) :
    (toGeneralLP N commodity (fun _ _ => 0)).rel (consIndex N commodity p) = ConstraintRel.eq := by
  dsimp [toGeneralLP, consIndex]
  rw [FinEncoding.addCases_castAdd]
  rw [FinEncoding.addCases_natAdd]

lemma b_cons (N : FlowNetwork V) (commodity : K → Commodity V) (p : Fin (Fintype.card (Internal N commodity))) :
    (toGeneralLP N commodity (fun _ _ => 0)).b (consIndex N commodity p) = 0 := by
  dsimp [toGeneralLP, consIndex]
  rw [FinEncoding.addCases_castAdd]
  rw [FinEncoding.addCases_natAdd]

lemma A_cons (N : FlowNetwork V) (commodity : K → Commodity V) (p : Fin (Fintype.card (Internal N commodity)))
    (j : Fin (Fintype.card (K × (V × V)))) :
    (toGeneralLP N commodity (fun _ _ => 0)).A (consIndex N commodity p) j =
      (if ((Fintype.equivFin (K × (V × V))).symm j).1 = ((Fintype.equivFin (Internal N commodity)).symm p).1.1 ∧
           ((Fintype.equivFin (K × (V × V))).symm j).2.1 = ((Fintype.equivFin (Internal N commodity)).symm p).1.2 then 1 else 0) -
        (if ((Fintype.equivFin (K × (V × V))).symm j).1 = ((Fintype.equivFin (Internal N commodity)).symm p).1.1 ∧
             ((Fintype.equivFin (K × (V × V))).symm j).2.2 = ((Fintype.equivFin (Internal N commodity)).symm p).1.2 then 1 else 0) := by
  dsimp [toGeneralLP, consIndex]
  rw [FinEncoding.addCases_castAdd]
  rw [FinEncoding.addCases_natAdd]

lemma rel_demand (N : FlowNetwork V) (commodity : K → Commodity V) (i : Fin (Fintype.card K)) :
    (toGeneralLP N commodity (fun _ _ => 0)).rel (demandIndex N commodity i) = ConstraintRel.eq := by
  dsimp [toGeneralLP, demandIndex]
  rw [FinEncoding.addCases_natAdd]

lemma b_demand (N : FlowNetwork V) (commodity : K → Commodity V) (i : Fin (Fintype.card K)) :
    (toGeneralLP N commodity (fun _ _ => 0)).b (demandIndex N commodity i) =
      (commodity ((Fintype.equivFin K).symm i)).demand := by
  dsimp [toGeneralLP, demandIndex]
  rw [FinEncoding.addCases_natAdd]

lemma A_demand (N : FlowNetwork V) (commodity : K → Commodity V) (i : Fin (Fintype.card K))
    (j : Fin (Fintype.card (K × (V × V)))) :
    (toGeneralLP N commodity (fun _ _ => 0)).A (demandIndex N commodity i) j =
      (if ((Fintype.equivFin (K × (V × V))).symm j).1 = (Fintype.equivFin K).symm i ∧
           ((Fintype.equivFin (K × (V × V))).symm j).2.1 = (commodity ((Fintype.equivFin K).symm i)).source then 1 else 0) -
        (if ((Fintype.equivFin (K × (V × V))).symm j).1 = (Fintype.equivFin K).symm i ∧
             ((Fintype.equivFin (K × (V × V))).symm j).2.2 = (commodity ((Fintype.equivFin K).symm i)).source then 1 else 0) := by
  dsimp [toGeneralLP, demandIndex]
  rw [FinEncoding.addCases_natAdd]

/-- A capacity row reads out the aggregate flow on its directed pair. -/
lemma mulVec_cap (N : FlowNetwork V) (commodity : K → Commodity V) (e : Fin (Fintype.card (V × V)))
    (f : K → V → V → ℝ) :
    ((toGeneralLP N commodity (fun _ _ => 0)).A *ᵥ lift₃ f) (capIndex N commodity e) =
      aggregate f ((Fintype.equivFin (V × V)).symm e).1 ((Fintype.equivFin (V × V)).symm e).2 := by
  calc
    ((toGeneralLP N commodity (fun _ _ => 0)).A *ᵥ lift₃ f) (capIndex N commodity e)
        = ∑ j : Fin (Fintype.card (K × (V × V))), (toGeneralLP N commodity (fun _ _ => 0)).A (capIndex N commodity e) j * lift₃ f j := by rfl
    _ = ∑ j : Fin (Fintype.card (K × (V × V))),
          (if ((Fintype.equivFin (K × (V × V))).symm j).2 = (Fintype.equivFin (V × V)).symm e then 1 else 0) * lift₃ f j := by
          simp only [A_cap]
    _ = ∑ i : K, f i ((Fintype.equivFin (V × V)).symm e).1 ((Fintype.equivFin (V × V)).symm e).2 := by
          simpa using (sum_indicator_pair ((Fintype.equivFin (V × V)).symm e).1 ((Fintype.equivFin (V × V)).symm e).2 f)
    _ = aggregate f ((Fintype.equivFin (V × V)).symm e).1 ((Fintype.equivFin (V × V)).symm e).2 := rfl

/-- A conservation row reads out the net outflow of one commodity at its
internal vertex. -/
lemma mulVec_cons (N : FlowNetwork V) (commodity : K → Commodity V) (p : Fin (Fintype.card (Internal N commodity)))
    (f : K → V → V → ℝ) :
    ((toGeneralLP N commodity (fun _ _ => 0)).A *ᵥ lift₃ f) (consIndex N commodity p) =
      FlowNetwork.outflow (f ((Fintype.equivFin (Internal N commodity)).symm p).1.1) ((Fintype.equivFin (Internal N commodity)).symm p).1.2 -
        FlowNetwork.inflow (f ((Fintype.equivFin (Internal N commodity)).symm p).1.1) ((Fintype.equivFin (Internal N commodity)).symm p).1.2 := by
  calc
    ((toGeneralLP N commodity (fun _ _ => 0)).A *ᵥ lift₃ f) (consIndex N commodity p)
        = ∑ j : Fin (Fintype.card (K × (V × V))), (toGeneralLP N commodity (fun _ _ => 0)).A (consIndex N commodity p) j * lift₃ f j := by rfl
    _ = ∑ j : Fin (Fintype.card (K × (V × V))),
          ((if ((Fintype.equivFin (K × (V × V))).symm j).1 = ((Fintype.equivFin (Internal N commodity)).symm p).1.1 ∧
                ((Fintype.equivFin (K × (V × V))).symm j).2.1 = ((Fintype.equivFin (Internal N commodity)).symm p).1.2 then 1 else 0) -
             (if ((Fintype.equivFin (K × (V × V))).symm j).1 = ((Fintype.equivFin (Internal N commodity)).symm p).1.1 ∧
                  ((Fintype.equivFin (K × (V × V))).symm j).2.2 = ((Fintype.equivFin (Internal N commodity)).symm p).1.2 then 1 else 0)) *
            lift₃ f j := by
          simp only [A_cons]
    _ = (∑ j : Fin (Fintype.card (K × (V × V))),
          (if ((Fintype.equivFin (K × (V × V))).symm j).1 = ((Fintype.equivFin (Internal N commodity)).symm p).1.1 ∧
               ((Fintype.equivFin (K × (V × V))).symm j).2.1 = ((Fintype.equivFin (Internal N commodity)).symm p).1.2 then 1 else 0) * lift₃ f j) -
          (∑ j : Fin (Fintype.card (K × (V × V))),
          (if ((Fintype.equivFin (K × (V × V))).symm j).1 = ((Fintype.equivFin (Internal N commodity)).symm p).1.1 ∧
               ((Fintype.equivFin (K × (V × V))).symm j).2.2 = ((Fintype.equivFin (Internal N commodity)).symm p).1.2 then 1 else 0) * lift₃ f j) := by
          simp only [sub_mul, Finset.sum_sub_distrib]
    _ = (∑ b : V, f ((Fintype.equivFin (Internal N commodity)).symm p).1.1 ((Fintype.equivFin (Internal N commodity)).symm p).1.2 b) -
          (∑ a : V, f ((Fintype.equivFin (Internal N commodity)).symm p).1.1 a ((Fintype.equivFin (Internal N commodity)).symm p).1.2) := by
          rw [sum_indicator_fst_fst, sum_indicator_fst_snd]
    _ = FlowNetwork.outflow (f ((Fintype.equivFin (Internal N commodity)).symm p).1.1) ((Fintype.equivFin (Internal N commodity)).symm p).1.2 -
          FlowNetwork.inflow (f ((Fintype.equivFin (Internal N commodity)).symm p).1.1) ((Fintype.equivFin (Internal N commodity)).symm p).1.2 := rfl

/-- A demand row reads out the net outflow of one commodity at its source. -/
lemma mulVec_demand (N : FlowNetwork V) (commodity : K → Commodity V) (i : Fin (Fintype.card K))
    (f : K → V → V → ℝ) :
    ((toGeneralLP N commodity (fun _ _ => 0)).A *ᵥ lift₃ f) (demandIndex N commodity i) =
      FlowNetwork.netOutflow (f ((Fintype.equivFin K).symm i)) (commodity ((Fintype.equivFin K).symm i)).source := by
  calc
    ((toGeneralLP N commodity (fun _ _ => 0)).A *ᵥ lift₃ f) (demandIndex N commodity i)
        = ∑ j : Fin (Fintype.card (K × (V × V))), (toGeneralLP N commodity (fun _ _ => 0)).A (demandIndex N commodity i) j * lift₃ f j := by rfl
    _ = ∑ j : Fin (Fintype.card (K × (V × V))),
          ((if ((Fintype.equivFin (K × (V × V))).symm j).1 = (Fintype.equivFin K).symm i ∧
                ((Fintype.equivFin (K × (V × V))).symm j).2.1 = (commodity ((Fintype.equivFin K).symm i)).source then 1 else 0) -
             (if ((Fintype.equivFin (K × (V × V))).symm j).1 = (Fintype.equivFin K).symm i ∧
                  ((Fintype.equivFin (K × (V × V))).symm j).2.2 = (commodity ((Fintype.equivFin K).symm i)).source then 1 else 0)) *
            lift₃ f j := by
          simp only [A_demand]
    _ = (∑ j : Fin (Fintype.card (K × (V × V))),
          (if ((Fintype.equivFin (K × (V × V))).symm j).1 = (Fintype.equivFin K).symm i ∧
               ((Fintype.equivFin (K × (V × V))).symm j).2.1 = (commodity ((Fintype.equivFin K).symm i)).source then 1 else 0) * lift₃ f j) -
          (∑ j : Fin (Fintype.card (K × (V × V))),
          (if ((Fintype.equivFin (K × (V × V))).symm j).1 = (Fintype.equivFin K).symm i ∧
               ((Fintype.equivFin (K × (V × V))).symm j).2.2 = (commodity ((Fintype.equivFin K).symm i)).source then 1 else 0) * lift₃ f j) := by
          simp only [sub_mul, Finset.sum_sub_distrib]
    _ = (∑ b : V, f ((Fintype.equivFin K).symm i) (commodity ((Fintype.equivFin K).symm i)).source b) -
          (∑ a : V, f ((Fintype.equivFin K).symm i) a (commodity ((Fintype.equivFin K).symm i)).source) := by
          rw [sum_indicator_fst_fst, sum_indicator_fst_snd]
    _ = FlowNetwork.netOutflow (f ((Fintype.equivFin K).symm i)) (commodity ((Fintype.equivFin K).symm i)).source := rfl

/-- Semantic feasibility is exactly encoded general-form feasibility. -/
theorem feasible_iff_generalLP (N : FlowNetwork V) (commodity : K → Commodity V)
    (f : K → V → V → ℝ) :
    IsFeasible N commodity f ↔ (toGeneralLP N commodity (fun _ _ => 0)).IsFeasible (lift₃ f) := by
  unfold IsFeasible GeneralLP.IsFeasible
  constructor
  · intro hd
    refine ⟨?_, ?_⟩
    · intro j hfree
      simpa [lift₃, FinEncoding.lift] using
        (hd.1 ((Fintype.equivFin (K × (V × V))).symm j).1
          ((Fintype.equivFin (K × (V × V))).symm j).2.1
          ((Fintype.equivFin (K × (V × V))).symm j).2.2)
    · intro i
      exact Fin.addCases (motive := fun i => match (toGeneralLP N commodity (fun _ _ => 0)).rel i with
          | ConstraintRel.le => ((toGeneralLP N commodity (fun _ _ => 0)).A *ᵥ lift₃ f) i ≤ (toGeneralLP N commodity (fun _ _ => 0)).b i
          | ConstraintRel.eq => ((toGeneralLP N commodity (fun _ _ => 0)).A *ᵥ lift₃ f) i = (toGeneralLP N commodity (fun _ _ => 0)).b i
          | ConstraintRel.ge => (toGeneralLP N commodity (fun _ _ => 0)).b i ≤ ((toGeneralLP N commodity (fun _ _ => 0)).A *ᵥ lift₃ f) i)
        (fun ij =>
          Fin.addCases (motive := fun ij => match (toGeneralLP N commodity (fun _ _ => 0)).rel (Fin.castAdd (Fintype.card K) ij) with
              | ConstraintRel.le => ((toGeneralLP N commodity (fun _ _ => 0)).A *ᵥ lift₃ f) (Fin.castAdd (Fintype.card K) ij) ≤ (toGeneralLP N commodity (fun _ _ => 0)).b (Fin.castAdd (Fintype.card K) ij)
              | ConstraintRel.eq => ((toGeneralLP N commodity (fun _ _ => 0)).A *ᵥ lift₃ f) (Fin.castAdd (Fintype.card K) ij) = (toGeneralLP N commodity (fun _ _ => 0)).b (Fin.castAdd (Fintype.card K) ij)
              | ConstraintRel.ge => (toGeneralLP N commodity (fun _ _ => 0)).b (Fin.castAdd (Fintype.card K) ij) ≤ ((toGeneralLP N commodity (fun _ _ => 0)).A *ᵥ lift₃ f) (Fin.castAdd (Fintype.card K) ij))
            (fun e => by
              rw [rel_cap, mulVec_cap, b_cap]
              simpa [aggregate] using
                (hd.2.1 ((Fintype.equivFin (V × V)).symm e).1 ((Fintype.equivFin (V × V)).symm e).2))
            (fun p => by
              rw [rel_cons, mulVec_cons, b_cons]
              have hc := hd.2.2.1 ((Fintype.equivFin (Internal N commodity)).symm p).1.1
                ((Fintype.equivFin (Internal N commodity)).symm p).1.2
                ((Fintype.equivFin (Internal N commodity)).symm p).2.1
                ((Fintype.equivFin (Internal N commodity)).symm p).2.2
              unfold FlowNetwork.ConservesAt at hc
              linarith)
            ij)
        (fun i => by
          rw [rel_demand, mulVec_demand, b_demand]
          exact hd.2.2.2 ((Fintype.equivFin K).symm i))
        i
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i u v
      have hn := h.1 (Fintype.equivFin (K × (V × V)) (i, (u, v)))
      simpa [lift₃, FinEncoding.lift] using (hn (by simp [toGeneralLP]))
    · intro u v
      have hc := h.2 (capIndex N commodity (Fintype.equivFin (V × V) (u, v)))
      rw [rel_cap] at hc
      rw [mulVec_cap, b_cap] at hc
      simpa [aggregate] using hc
    · intro i u hu hw
      let e : Internal N commodity := ⟨(i, u), ⟨hu, hw⟩⟩
      have hcons := h.2 (consIndex N commodity (Fintype.equivFin (Internal N commodity) e))
      rw [rel_cons] at hcons
      rw [mulVec_cons, b_cons] at hcons
      have hcons' : FlowNetwork.outflow (f i) u - FlowNetwork.inflow (f i) u = 0 := by
        simpa [e] using hcons
      unfold FlowNetwork.ConservesAt
      linarith
    · intro i
      have hdemand := h.2 (demandIndex N commodity (Fintype.equivFin K i))
      rw [rel_demand] at hdemand
      rw [mulVec_demand, b_demand] at hdemand
      simpa using hdemand

/-- The general-form objective is the aggregate minimum cost. -/
lemma objective_generalLP (N : FlowNetwork V) (commodity : K → Commodity V)
    (unitCost : V → V → ℝ) (f : K → V → V → ℝ) :
    (toGeneralLP N commodity unitCost).objective (lift₃ f) = cost unitCost f := by
  dsimp [GeneralLP.objective, toGeneralLP, cost, aggregate]
  simp only [dotProduct]
  rw [FinEncoding.sum_reindex]
  simp [lift₃, FinEncoding.lift]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  rw [Fintype.sum_prod_type]
  simp [Finset.mul_sum]

/-- The finite standard-form program obtained by normalizing the
multicommodity general program. -/
noncomputable def toStandardLP (N : FlowNetwork V) (commodity : K → Commodity V)
    (unitCost : V → V → ℝ) :=
  (toGeneralLP N commodity unitCost).toStandardLP

/-- The expansion of a commodity flow to the normalized standard-form variable
vector. -/
noncomputable def fullLift (N : FlowNetwork V) (commodity : K → Commodity V)
    (unitCost : V → V → ℝ) (f : K → V → V → ℝ) :
    Fin (Fintype.card (K × (V × V)) + Fintype.card (K × (V × V))) → ℝ :=
  (toGeneralLP N commodity unitCost).lift (lift₃ f)

/-- The normalized standard-form objective equals the signed aggregate cost. -/
theorem objective_toStandardLP (N : FlowNetwork V) (commodity : K → Commodity V)
    (unitCost : V → V → ℝ) (f : K → V → V → ℝ) :
    (toStandardLP N commodity unitCost).objective (fullLift N commodity unitCost f) = -cost unitCost f := by
  unfold toStandardLP fullLift
  rw [GeneralLP.objective_lift]
  rw [objective_generalLP]
  simp [toGeneralLP, GeneralLP.objectiveSign]

/-- Feasibility is exactly preserved under the finite standard-form encoding. -/
theorem feasible_iff_toStandardLP (N : FlowNetwork V) (commodity : K → Commodity V)
    (f : K → V → V → ℝ) :
    IsFeasible N commodity f ↔ (toStandardLP N commodity (fun _ _ => 0)).IsFeasible (fullLift N commodity (fun _ _ => 0) f) := by
  unfold toStandardLP fullLift
  rw [← GeneralLP.feasible_iff_lift]
  exact feasible_iff_generalLP N commodity f

end Encoding

end MulticommodityFlowLP
end Chapter29
end CLRS

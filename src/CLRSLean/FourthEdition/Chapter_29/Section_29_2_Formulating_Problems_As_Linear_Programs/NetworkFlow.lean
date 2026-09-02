import Mathlib

/-!
# 29.2: Common finite-network definitions

CLRS writes its flow linear programs with one nonnegative variable {lit}`f u v`
for every ordered pair of vertices.  A missing edge is represented by capacity
zero.  This file records that shared finite-network vocabulary, together with
the finite-standard-form encoding helpers used by every §29.2 formulation.
-/

namespace CLRS
namespace Chapter29

open Finset
open scoped BigOperators

/-- A finite directed capacitated network.  Capacities are total; assigning
capacity zero to nonedges gives exactly the convention used in CLRS §29.2. -/
structure FlowNetwork (V : Type*) [Fintype V] where
  source : V
  sink : V
  source_ne_sink : source ≠ sink
  capacity : V → V → ℝ
  capacity_nonnegative : ∀ u v, 0 ≤ capacity u v

namespace FlowNetwork

variable {V : Type*} [Fintype V] (N : FlowNetwork V)

/-- Total flow leaving a vertex. -/
def outflow (f : V → V → ℝ) (u : V) : ℝ := ∑ v, f u v

/-- Total flow entering a vertex. -/
def inflow (f : V → V → ℝ) (u : V) : ℝ := ∑ v, f v u

/-- Net flow leaving a vertex. -/
def netOutflow (f : V → V → ℝ) (u : V) : ℝ := outflow f u - inflow f u

/-- Flow conservation at one vertex. -/
def ConservesAt (f : V → V → ℝ) (u : V) : Prop := inflow f u = outflow f u

/-- The nonnegativity and capacity inequalities shared by the flow LPs. -/
def IsCapacityFeasible (f : V → V → ℝ) : Prop :=
  (∀ u v, 0 ≤ f u v) ∧ ∀ u v, f u v ≤ N.capacity u v

/-- A feasible single-commodity flow: capacity constraints everywhere and
conservation away from the source and sink. -/
def IsFlow (f : V → V → ℝ) : Prop :=
  N.IsCapacityFeasible f ∧
    ∀ u, u ≠ N.source → u ≠ N.sink → ConservesAt f u

end FlowNetwork

/-! ## Finite standard-form encoding helpers

These helpers reindex semantic vectors over a finite type into the `Fin`-indexed
vectors used by {lit}`StandardLP`, and prove the sum identities that the
assignment bridges rely on. -/

namespace FinEncoding

variable {ι : Type*} [Fintype ι]

/-- Lift a semantic vector over a finite type to the `Fin`-indexed vector of the
same coordinates. -/
noncomputable def lift (x : ι → ℝ) : Fin (Fintype.card ι) → ℝ :=
  x ∘ (Fintype.equivFin ι).symm

/-- Project a `Fin`-indexed vector back to a semantic vector. -/
noncomputable def proj (x : Fin (Fintype.card ι) → ℝ) : ι → ℝ :=
  x ∘ (Fintype.equivFin ι)

/-- Lifting then projecting recovers the original vector. -/
theorem proj_lift (x : ι → ℝ) (a : ι) : proj (lift x) a = x a := by
  simp [proj, lift]

/-- A finite sum over `Fin (card ι)` reindexes to a sum over `ι`. -/
theorem sum_reindex {M : Type*} [AddCommMonoid M] (f : Fin (Fintype.card ι) → M) :
    (∑ i : Fin (Fintype.card ι), f i) = ∑ a : ι, f (Fintype.equivFin ι a) := by
  exact (Equiv.sum_comp (Fintype.equivFin ι) f).symm

/-- The indicator sum that collapses an `ι`-indicator to its selected coordinate. -/
theorem sum_indicator [DecidableEq ι] (a : ι) (x : ι → ℝ) :
    (∑ j : Fin (Fintype.card ι),
        (if (Fintype.equivFin ι).symm j = a then 1 else 0) * lift x j) = x a := by
  calc
    (∑ j : Fin (Fintype.card ι),
        (if (Fintype.equivFin ι).symm j = a then 1 else 0) * lift x j)
        = ∑ b : ι, (if b = a then 1 else 0) * x b := by
            rw [sum_reindex]
            simp [lift]
    _ = x a := by
            rw [Finset.sum_eq_single a]
            · simp
            · intro b _ hb; simp [hb]
            · intro h; exact False.elim (h (Finset.mem_univ a))

/-- A direct `Fin`-indicator sum (no reindexing): the coefficient is nonzero
exactly at the selected coordinate. -/
theorem sum_indicator_fin {n : ℕ} (e : Fin n) (x : Fin n → ℝ) :
    (∑ j : Fin n, (if j = e then 1 else 0) * x j) = x e := by
  rw [Finset.sum_eq_single e]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact False.elim (h (Finset.mem_univ e))

/-- {lit}`Fin.addCases` reduces on a left ({lit}`castAdd`) index. -/
theorem addCases_castAdd {m n : ℕ} {C : Type u} (left : Fin m → C) (right : Fin n → C) (e : Fin m) :
    Fin.addCases left right (Fin.castAdd n e) = left e := by
  simp [Fin.addCases]

/-- {lit}`Fin.addCases` reduces on a right ({lit}`natAdd`) index. -/
theorem addCases_natAdd {m n : ℕ} {C : Type u} (left : Fin m → C) (right : Fin n → C) (v : Fin n) :
    Fin.addCases left right (Fin.natAdd m v) = right v := by
  simp [Fin.addCases]

/-- Lift a binary vector to the `Fin`-indexed vector over ordered pairs. -/
noncomputable def lift₂ {α β : Type*} [Fintype α] [Fintype β] (x : α → β → ℝ) :
    Fin (Fintype.card (α × β)) → ℝ :=
  lift (Function.uncurry x)

/-- Project a `Fin`-indexed vector over ordered pairs back to a binary vector. -/
noncomputable def proj₂ {α β : Type*} [Fintype α] [Fintype β]
    (x : Fin (Fintype.card (α × β)) → ℝ) : α → β → ℝ :=
  Function.curry (proj x)

/-- Sum of an indicator on the first coordinate over all ordered pairs. -/
theorem sum_indicator_fst {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (a : α) (x : α → β → ℝ) :
    (∑ j : Fin (Fintype.card (α × β)),
        (if ((Fintype.equivFin (α × β)).symm j).1 = a then 1 else 0) * lift₂ x j) =
      ∑ b : β, x a b := by
  calc
    (∑ j : Fin (Fintype.card (α × β)),
        (if ((Fintype.equivFin (α × β)).symm j).1 = a then 1 else 0) * lift₂ x j)
        = ∑ p : α × β, (if p.1 = a then 1 else 0) * x p.1 p.2 := by
            rw [sum_reindex]
            simp [lift₂, lift, Function.uncurry]
    _ = ∑ b : β, x a b := by
            rw [Fintype.sum_prod_type]
            rw [Finset.sum_eq_single a]
            · simp
            · intro c _ hc; simp [hc]
            · intro h; exact False.elim (h (Finset.mem_univ a))

/-- Sum of an indicator on the second coordinate over all ordered pairs. -/
theorem sum_indicator_snd {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (a : β) (x : α → β → ℝ) :
    (∑ j : Fin (Fintype.card (α × β)),
        (if ((Fintype.equivFin (α × β)).symm j).2 = a then 1 else 0) * lift₂ x j) =
      ∑ b : α, x b a := by
  calc
    (∑ j : Fin (Fintype.card (α × β)),
        (if ((Fintype.equivFin (α × β)).symm j).2 = a then 1 else 0) * lift₂ x j)
        = ∑ p : α × β, (if p.2 = a then 1 else 0) * x p.1 p.2 := by
            rw [sum_reindex]
            simp [lift₂, lift, Function.uncurry]
    _ = ∑ b : α, x b a := by
            rw [Fintype.sum_prod_type]
            rw [Finset.sum_comm]
            rw [Finset.sum_eq_single a]
            · simp
            · intro c _ hc; simp [hc]
            · intro h; exact False.elim (h (Finset.mem_univ a))

end FinEncoding

end Chapter29
end CLRS

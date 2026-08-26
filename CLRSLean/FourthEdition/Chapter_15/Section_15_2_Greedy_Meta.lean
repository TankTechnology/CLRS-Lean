import Mathlib

/-!
# Section 15.2 - Greedy-choice property and optimal substructure (meta-theorems)

This section formalizes the two structural properties that CLRS §15.2 identifies
as the reusable core of every greedy algorithm:

1. **Greedy-choice property**: making a locally optimal
   (greedy) choice never prevents a globally optimal solution.
2. **Optimal substructure**: an optimal solution to a
   problem contains within it optimal solutions to its subproblems.

We define an abstract `GreedyProblem` structure that bundles the data and axioms
needed to prove greedy optimality, and prove the meta-theorem `gsolve_optimal`:
if a problem satisfies both properties (with a well-founded size measure), then
the recursive greedy algorithm returns an optimal solution for every instance.

The instantiation with the activity-selection problem from §15.1 is provided
in a separate companion file and recovers the existing
`greedySelect_maxCardinality` theorem as a corollary of the generic
meta-theorem.

Main results:

- Structure `GreedyProblem` : bundles the greedy-choice property and optimal
  substructure.
- Definition `gsolve` : the generic recursive greedy solver.
- Theorem `gsolve_optimal` : `gsolve` returns optimal solutions for every
  instance of a `GreedyProblem`.
- Predicate `GreedyChoiceProperty` : the abstract greedy-choice property.
- Predicate `OptimalSubstructure` : the abstract, solver-independent
  optimal-substructure property.

Notation conventions:

- `P` : problem type
- `Sol` : solution type
- `Elem` : type of individual elements
- `optimal p s` : `s` is an optimal solution for `p`
- `greedyElt p` : the greedy element for `p`
- `sub p` : the subproblem after making the greedy choice
- `combine e s` : assemble a solution from the greedy element and tail solution
- `size p` : a `Nat` well-founded measure
-/

namespace CLRS
namespace GreedyMeta

/-! ## The abstract `GreedyProblem` structure -/

/--
A `GreedyProblem` formalizes the CLRS §15.2 pattern.  It bundles:

**Data**:
- `optimal p s` : `s` is an optimal solution for `p`
- `greedyElt p` : the locally optimal (greedy) element
- `sub p` : the residual subproblem after removing the greedy choice and
  incompatible elements
- `combine e s` : construct a solution from the greedy element and a
  subproblem solution
- `base` : the base (empty) solution
- `size p` : a `Nat` measure for termination and induction

**Axioms**:
1. `greedy_choice`: a non-base problem has an optimal solution beginning with
   the greedy choice.
2. `optimal_substructure`: the tail of such an optimal solution is optimal for
   the residual subproblem.
3. `replace_optimal_tail`: any other optimal residual solution can replace that
   tail.  This is the small compositional bridge needed by the generic solver.
4. `sub_lt` and `base_opt`: well-foundedness and base-case optimality.
-/
structure GreedyProblem (Elem Sol P : Type) where
  optimal : P → Sol → Prop
  greedyElt : P → Elem
  sub : P → P
  combine : Elem → Sol → Sol
  base : Sol
  size : P → ℕ

  -- The greedy choice occurs in some optimal solution.
  greedy_choice : ∀ (p : P), size p > 0 →
    ∃ tail, optimal p (combine (greedyElt p) tail)

  -- The tail of an optimal greedy-shaped solution is optimal for the subproblem.
  optimal_substructure : ∀ (p : P) (tail : Sol), size p > 0 →
    optimal p (combine (greedyElt p) tail) → optimal (sub p) tail

  -- Optimal tails are interchangeable under the fixed greedy choice.
  replace_optimal_tail : ∀ (p : P) (oldTail newTail : Sol), size p > 0 →
    optimal (sub p) oldTail → optimal (sub p) newTail →
    optimal p (combine (greedyElt p) oldTail) →
    optimal p (combine (greedyElt p) newTail)

  -- The subproblem is strictly smaller (well-foundedness)
  sub_lt : ∀ (p : P), size p > 0 → size (sub p) < size p

  -- Base-case optimality
  base_opt : ∀ (p : P), size p = 0 → optimal p base

/-! ## Generic recursive greedy solver -/

/--
The recursive greedy solver for a `GreedyProblem`.  Defined by well-founded
recursion on the `size` measure.
-/
noncomputable def gsolve (gp : GreedyProblem Elem Sol P) : P → Sol :=
  fun p =>
    if h : gp.size p > 0 then
      gp.combine (gp.greedyElt p) (gsolve gp (gp.sub p))
    else
      gp.base
termination_by p => gp.size p
decreasing_by
  exact gp.sub_lt _ h

/--
Recursion equation for non-base problems: `gsolve` makes the greedy choice
and recurses on the subproblem.
-/
theorem gsolve_eq (gp : GreedyProblem Elem Sol P) {p : P} (h : gp.size p > 0) :
    gsolve gp p = gp.combine (gp.greedyElt p) (gsolve gp (gp.sub p)) := by
  rw [gsolve.eq_def]
  simp [h]

/--
Base-case equation: when `size p = 0`, `gsolve` returns `base`.
-/
theorem gsolve_base (gp : GreedyProblem Elem Sol P) {p : P} (h : gp.size p = 0) :
    gsolve gp p = gp.base := by
  rw [gsolve.eq_def]
  simp [h]

/-! ## Meta-theorem (CLRS §15.2) -/

/--
**Meta-theorem.**  If a problem class satisfies the greedy-choice property
and optimal substructure (formalized as a `GreedyProblem`), then the
recursive greedy algorithm `gsolve` returns an optimal solution for every
problem instance.

Proof by strong induction on the `size` measure.
-/
theorem gsolve_optimal (gp : GreedyProblem Elem Sol P) (p : P) :
    gp.optimal p (gsolve gp p) := by
  induction hsize : gp.size p using Nat.strong_induction_on generalizing p with
  | h n ih =>
    by_cases hzero : gp.size p = 0
    · rw [gsolve_base gp hzero]
      exact gp.base_opt p hzero
    · have hpos : gp.size p > 0 := Nat.pos_of_ne_zero hzero
      rw [gsolve_eq gp hpos]
      have hsub_lt : gp.size (gp.sub p) < gp.size p := gp.sub_lt p hpos
      have h_eq : gp.size (gp.sub p) < n := by
        rw [← hsize]
        exact hsub_lt
      have h_ih : gp.optimal (gp.sub p) (gsolve gp (gp.sub p)) :=
        ih (gp.size (gp.sub p)) h_eq (gp.sub p) rfl
      rcases gp.greedy_choice p hpos with ⟨oldTail, hwhole⟩
      have hold_opt : gp.optimal (gp.sub p) oldTail :=
        gp.optimal_substructure p oldTail hpos hwhole
      exact gp.replace_optimal_tail p oldTail (gsolve gp (gp.sub p)) hpos
        hold_opt h_ih hwhole

/-! ## Predicate form of the greedy properties -/

/--
`GreedyChoiceProperty` says that every active problem has an optimal solution
that begins with its locally greedy element.  It is an existence property and
does not mention a particular solver.
-/
def GreedyChoiceProperty (P Elem Sol : Type) (optimal : P → Sol → Prop)
    (active : P → Prop) (greedyElt : P → Elem)
    (combine : Elem → Sol → Sol) : Prop :=
  ∀ p, active p → ∃ tail, optimal p (combine (greedyElt p) tail)

/--
`OptimalSubstructure` says that whenever an optimal solution is decomposed into
the greedy choice and a tail, that tail is optimal for the residual subproblem.
Unlike the former formulation, this is a property of the problem decomposition
and is independent of any solver.
-/
def OptimalSubstructure (P Elem Sol : Type) (optimal : P → Sol → Prop)
    (active : P → Prop) (greedyElt : P → Elem) (subproblem : P → P)
    (combine : Elem → Sol → Sol) : Prop :=
  ∀ p tail, active p →
    optimal p (combine (greedyElt p) tail) → optimal (subproblem p) tail

theorem GreedyProblem.greedyChoiceProperty (gp : GreedyProblem Elem Sol P) :
    GreedyChoiceProperty P Elem Sol gp.optimal (fun p => gp.size p > 0)
      gp.greedyElt gp.combine :=
  gp.greedy_choice

theorem GreedyProblem.hasOptimalSubstructure (gp : GreedyProblem Elem Sol P) :
    OptimalSubstructure P Elem Sol gp.optimal (fun p => gp.size p > 0)
      gp.greedyElt gp.sub gp.combine :=
  gp.optimal_substructure

end GreedyMeta
end CLRS

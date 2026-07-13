import Mathlib

/-!
# Section 16.2 - Greedy-choice property and optimal substructure (meta-theorems)

This section formalizes the two structural properties that CLRS §16.2 identifies
as the reusable core of every greedy algorithm:

1. **Greedy-choice property** (CLRS Lemma 16.1): making a locally optimal
   (greedy) choice never prevents a globally optimal solution.
2. **Optimal substructure** (CLRS Lemma 16.2): an optimal solution to a
   problem contains within it optimal solutions to its subproblems.

We define an abstract `GreedyProblem` structure that bundles the data and axioms
needed to prove greedy optimality, and prove the meta-theorem `gsolve_optimal`:
if a problem satisfies both properties (with a well-founded size measure), then
the recursive greedy algorithm returns an optimal solution for every instance.

The instantiation with the activity-selection problem from §16.1 is provided
in a separate companion file and recovers the existing
`greedySelect_maxCardinality` theorem as a corollary of the generic
meta-theorem.

Main results:

- Structure `GreedyProblem` : bundles the greedy-choice property and optimal
  substructure.
- Definition `gsolve` : the generic recursive greedy solver.
- Theorem `gsolve_optimal` : `gsolve` returns optimal solutions for every
  instance of a `GreedyProblem`.
- Predicate `GreedyChoiceProperty` : the abstract greedy-choice property
  (CLRS Lemma 16.1).
- Predicate `OptimalSubstructure` : the abstract optimal-substructure property
  (CLRS Lemma 16.2).

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
A `GreedyProblem` formalizes the CLRS §16.2 pattern.  It bundles:

**Data**:
- `optimal p s` : `s` is an optimal solution for `p`
- `greedyElt p` : the locally optimal (greedy) element
- `sub p` : the residual subproblem after removing the greedy choice and
  incompatible elements
- `combine e s` : construct a solution from the greedy element and a
  subproblem solution
- `base` : the base (empty) solution
- `size p` : a `Nat` measure for termination and induction

**Axioms** (the two CLRS §16.2 properties plus well-foundedness):
1. `gcp` (greedy-choice property, Lemma 16.1): for a non-base problem, any
   optimal solution for the subproblem extends to an optimal solution for the
   original via the greedy choice.
2. `sub_lt` (size decreases): the subproblem is strictly smaller.
3. `base_opt` (base-case optimality): the base solution is optimal when the
   problem size is zero.
-/
structure GreedyProblem (Elem Sol P : Type) where
  optimal : P → Sol → Prop
  greedyElt : P → Elem
  sub : P → P
  combine : Elem → Sol → Sol
  base : Sol
  size : P → ℕ

  -- Greedy-choice property (Lemma 16.1): only required for nonempty problems
  gcp : ∀ (p : P) (s : Sol), size p > 0 → optimal (sub p) s → optimal p (combine (greedyElt p) s)

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

/-! ## Meta-theorem (CLRS §16.2) -/

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
      apply gp.gcp p (gsolve gp (gp.sub p)) hpos
      have hsub_lt : gp.size (gp.sub p) < gp.size p := gp.sub_lt p hpos
      have h_eq : gp.size (gp.sub p) < n := by
        rw [← hsize]
        exact hsub_lt
      have h_ih : gp.optimal (gp.sub p) (gsolve gp (gp.sub p)) :=
        ih (gp.size (gp.sub p)) h_eq (gp.sub p) rfl
      exact h_ih

/-! ## Predicate form of the greedy properties -/

/--
`GreedyChoiceProperty` is a predicate on a problem class: for every problem `p`
and optimal subproblem solution `s`, the combined solution `combine s` is
optimal for `p`.  This is the abstract version of CLRS Lemma 16.1.
-/
def GreedyChoiceProperty (P Sol : Type) (optimal : P → Sol → Prop)
    (subproblem : outParam (P → P)) (combine : outParam (Sol → Sol)) : Prop :=
  ∀ (p : P) (s : Sol), optimal (subproblem p) s → optimal p (combine s)

/--
`OptimalSubstructure` is a predicate on a problem class: the greedy solver
`solve` returns an optimal solution for every subproblem.  This is the abstract
version of CLRS Lemma 16.2.
-/
def OptimalSubstructure (P Sol : Type) (optimal : P → Sol → Prop)
    (subproblem : outParam (P → P)) (solve : outParam (P → Sol)) : Prop :=
  ∀ (p : P), optimal (subproblem p) (solve (subproblem p))

end GreedyMeta
end CLRS

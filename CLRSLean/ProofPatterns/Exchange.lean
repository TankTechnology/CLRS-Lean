import Mathlib

/-!
# Exchange-certificate proof pattern

This module records the common greedy-exchange shape: transform any feasible
competitor into one that contains the greedy local choice while becoming no
worse under the problem's comparison relation.
-/

namespace CLRS
namespace ProofPatterns

/--
A generic exchange certificate.

{lit}`target` is the structural property gained after the exchange, such as
"starts with the greedy activity", "contains the light edge", or "has the two
least-frequency symbols as sibling leaves".  {lit}`noWorse new old` is supplied by
the concrete problem: for maximization it can mean {lit}`score old <= score new`,
and for minimization it can mean {lit}`cost new <= cost old`.
-/
structure ExchangeCertificate
    (Solution : Type u) (feasible target : Solution -> Prop)
    (noWorse : Solution -> Solution -> Prop) where
  exchange : Solution -> Solution
  feasible_exchange : forall s, feasible s -> feasible (exchange s)
  target_exchange : forall s, feasible s -> target (exchange s)
  noWorse_exchange : forall s, feasible s -> noWorse (exchange s) s

namespace ExchangeCertificate

/-- Consume an exchange certificate for a single feasible competitor. -/
theorem exists_target_for
    {Solution : Type u} {feasible target : Solution -> Prop}
    {noWorse : Solution -> Solution -> Prop}
    (cert : ExchangeCertificate Solution feasible target noWorse)
    {s : Solution} (hs : feasible s) :
    exists s', feasible s' ∧ target s' ∧ noWorse s' s := by
  exact ⟨cert.exchange s, cert.feasible_exchange s hs,
    cert.target_exchange s hs, cert.noWorse_exchange s hs⟩

/-- Maximization-oriented exchange relation induced by a score. -/
def NoLessScore (score : Solution -> Nat) (new old : Solution) : Prop :=
  score old <= score new

/-- Minimization-oriented exchange relation induced by a cost. -/
def NoGreaterCost (cost : Solution -> Nat) (new old : Solution) : Prop :=
  cost new <= cost old

end ExchangeCertificate

end ProofPatterns
end CLRS

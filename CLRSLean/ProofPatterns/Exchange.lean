import Mathlib

/-!
# Exchange optimality and certificate proof pattern

This module separates two common greedy-exchange layers.  {lit}`Optimal` and its
transport theorems combine feasibility with a problem-specific no-worse
relation.  {lit}`ExchangeCertificate` records the stronger case where witness
construction is a total exchange function.
-/

namespace CLRS
namespace ProofPatterns

/-- A feasible solution that is no worse than every feasible competitor. -/
structure Optimal
    (feasible : Solution → Prop)
    (noWorse : Solution → Solution → Prop)
    (chosen : Solution) : Prop where
  feasible_chosen : feasible chosen
  noWorse_than : ∀ other, feasible other → noWorse chosen other

namespace Optimal

/-- Replacing an optimum by a feasible no-worse solution preserves optimality. -/
theorem of_noWorse
    {Solution : Type u} {feasible : Solution → Prop}
    {noWorse : Solution → Solution → Prop} {old new : Solution}
    (hold : Optimal feasible noWorse old)
    (hnew : feasible new) (hnewOld : noWorse new old)
    (htrans : ∀ {a b c}, noWorse a b → noWorse b c → noWorse a c) :
    Optimal feasible noWorse new := by
  refine ⟨hnew, ?_⟩
  intro other hother
  exact htrans hnewOld (hold.noWorse_than other hother)

end Optimal

/-- A chosen feasible solution is optimal when every competitor exchanges to a
target that lies between the chosen solution and that competitor. -/
theorem optimal_of_exchange
    {Solution : Type u} {feasible target : Solution → Prop}
    {noWorse : Solution → Solution → Prop} {chosen : Solution}
    (hchosen : feasible chosen)
    (hexchange : ∀ other, feasible other →
      ∃ exchanged, target exchanged ∧ noWorse exchanged other)
    (htarget : ∀ exchanged, target exchanged → noWorse chosen exchanged)
    (htrans : ∀ {a b c}, noWorse a b → noWorse b c → noWorse a c) :
    Optimal feasible noWorse chosen := by
  refine ⟨hchosen, ?_⟩
  intro other hother
  rcases hexchange other hother with ⟨exchanged, hexchanged, hbetter⟩
  exact htrans (htarget exchanged hexchanged) hbetter

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

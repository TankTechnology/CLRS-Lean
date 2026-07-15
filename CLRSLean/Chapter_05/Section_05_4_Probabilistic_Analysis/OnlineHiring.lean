import CLRSLean.Probability.FiniteExpectation
import Mathlib

/-!
# CLRS §5.4.4 — The On-line Hiring Problem

We model the on-line hiring problem (CLRS §5.4.4).  {lit}`n` candidates arrive
in random order (uniform over all {lit}`n!` permutations).  After each interview
the algorithm must decide immediately whether to hire the current candidate and
stop, or to continue.  The goal is to maximize the probability of hiring the
**best** candidate.

The optimal strategy (CLRS p. 139): interview the first {lit}`k` applicants
without hiring (the *observation phase*), then hire the first applicant who is
better than every applicant seen so far.  For {lit}`k = n/e` the probability of
hiring the best candidate approaches {lit}`1/e`.

**Status:** Definitions are in place; the probability formula
{lit}`Pr[hire best] = (k/n)·(H_{n-1} - H_{k-1})` and the asymptotic
{lit}`1/e` bound are **deferred** to a future refinement.
-/

namespace CLRS
namespace Chapter05

open CLRS.Probability

/-! ## Model

The sample space is the uniform distribution over {lit}`Equiv.Perm (Fin n)`.
Candidate {lit}`i` has **score** {lit}`π i` ({lit}`0` = best, {lit}`n-1` =
worst).  The absolute best candidate is the one with score {lit}`0`.
-/

/--
The absolute best candidate: the one mapped to {lit}`0` (smallest score) by
the permutation.
-/
def isAbsoluteBest {n : ℕ} (π : Equiv.Perm (Fin n)) (i : Fin n) : Prop :=
  π i = 0

/--
The {lit}`k`-threshold hiring strategy (specification).  Interview the first
{lit}`k` candidates without hiring, then hire the first candidate whose score
is smaller than all previous scores (i.e., the first best-so-far after
position {lit}`k`).

The implementation as a computable function over {lit}`Fin n` positions is
deferred; the probability analysis is deferred.
-/
def hiringStrategy {n : ℕ} (k : Fin n) (π : Equiv.Perm (Fin n)) : Option (Fin n) :=
  -- Deferred: return the first position j ≥ k such that π j = min_{i ≤ j} π i
  none

/--
Probability that the threshold-{lit}`k` strategy hires the absolute best
candidate, over the uniform random permutation of {lit}`Fin n`.
-/
noncomputable def probHireBest (n : ℕ) (k : Fin n) : ℝ :=
  fintypeExpect (fun π : Equiv.Perm (Fin n) =>
    indicator (match hiringStrategy k π with
    | some i => isAbsoluteBest π i
    | none => False))

end Chapter05
end CLRS

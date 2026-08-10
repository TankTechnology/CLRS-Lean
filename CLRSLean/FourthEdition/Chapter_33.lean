import CLRSLean.FourthEdition.Chapter_33.Section_33_1_Clustering
import CLRSLean.FourthEdition.Chapter_33.Section_33_2_Multiplicative_Weights
import CLRSLean.FourthEdition.Chapter_33.Section_33_3_Gradient_Descent

/-!
# Chapter 33 — Machine-Learning Algorithms

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

Section 33.1 (Clustering) is formalized natively in
`CLRSLean.FourthEdition.Chapter_33.Section_33_1_Clustering`: the k-means
clustering problem, Lloyd's algorithm, and the two monotonicity theorems of
the cost under the assignment and update steps.  Section 33.2
(Multiplicative-weights algorithms) is formalized natively in
`CLRSLean.FourthEdition.Chapter_33.Section_33_2_Multiplicative_Weights`: the
potential-based analysis of the multiplicative-weights update method and its
regret bound against the best expert.  Section 33.3 (Gradient descent) is
formalized natively in
`CLRSLean.FourthEdition.Chapter_33.Section_33_3_Gradient_Descent`: the
gradient-descent method for minimizing a convex differentiable function and
the convergence bound on the average iterate (Theorem 33.8).  No legacy source
is promoted into this chapter.

- [Clustering section](CLRSLean/FourthEdition/Chapter_33/Section_33_1_Clustering/)
- [Multiplicative-weights section](CLRSLean/FourthEdition/Chapter_33/Section_33_2_Multiplicative_Weights/)
- [Gradient-descent section](CLRSLean/FourthEdition/Chapter_33/Section_33_3_Gradient_Descent/)

## Coverage boundary

Status: `complete`.  Represented sections: 33.1 (Clustering) — the k-means
cost, its variance decomposition, Lemma 33.1 (the mean minimizes the
within-cluster sum of squared distances), and Theorem 33.2 (a Lloyd iteration
never increases the cost).  33.2 (Multiplicative-weights algorithms) — the
multiplicative-weights update rule, the potential and expected-loss accounting,
the exponential potential chain, and Theorem 33.3 (the total expected loss is
within an additive `ln n / η` and a multiplicative `(1 + η)` factor of the best
expert's loss).  33.3 (Gradient descent) — the gradient-descent lemma, the
per-step and telescoping potential inequalities, and Theorem 33.8 (the average
iterate converges with bound `‖x₀ - x*‖²/(2·η·K) + η·G²/2`).

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/

import CLRSLean.FourthEdition.Chapter_33.Section_33_1_Clustering

/-!
# Chapter 33 — Machine-Learning Algorithms

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

Section 33.1 (Clustering) is formalized natively in
`CLRSLean.FourthEdition.Chapter_33.Section_33_1_Clustering`: the k-means
clustering problem, Lloyd's algorithm, and the two monotonicity theorems of
the cost under the assignment and update steps.  No legacy source is promoted
into this chapter.

- [Clustering section](CLRSLean/FourthEdition/Chapter_33/Section_33_1_Clustering/)

## Coverage boundary

Status: `partial`.  Represented sections: 33.1 (Clustering) — the k-means cost,
its variance decomposition, Lemma 33.1 (the mean minimizes the within-cluster
sum of squared distances), and Theorem 33.2 (a Lloyd iteration never increases
the cost).  Sections 33.2 (Multiplicative-weights algorithms) and 33.3
(Gradient descent) are not started.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/

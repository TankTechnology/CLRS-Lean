import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# 33.1 Clustering

This section formalizes the **k-means clustering** problem and Lloyd's
algorithm from CLRS §33.1.  A *clustering* of a finite set of points
partitions them into `k` clusters, each with a centroid, and its cost is the
sum over all points of the squared Euclidean distance to the centroid of the
point's own cluster.

Main results:

- Definition `sumSqDist`: the within-cluster sum of squared distances to a
  candidate center.
- Definition `mean`: the centroid (average) of a finite point family over an
  index set.
- Definition `Clustering`: an assignment of each point to a cluster together
  with one centroid per cluster.
- Definition `kMeansCost`: the cost of a clustering.
- Theorem `mean_minimizes_sumSqDist` (Lemma 33.1): the mean of a cluster
  minimizes the within-cluster sum of squared distances.
- Theorem `assignStep_cost_le`: reassigning every point to a *nearest*
  centroid never increases the cost.
- Theorem `updateStep_cost_le`: replacing every centroid by the mean of its
  cluster never increases the cost.
- Theorem `lloyd_iteration_cost_le` (Theorem 33.2): one Lloyd iteration
  (assignment, then update) never increases the cost.

The ambient point space is a real inner product space `E` (CLRS works with
`ℝᵈ`, which is `EuclideanSpace ℝ (Fin d)` in Mathlib).  Points are given by a
finite family `P : Fin n → E`, and a cluster is an index set; the mean of a
cluster counts each of its indices, so two distinct indices with coincident
coordinates are both included.  The development is deliberately abstract:
only the monotonicity of the cost under Lloyd's two steps is proved; the
termination guarantee and convergence rate are not addressed.

Notation conventions used in this section:

- `E` : the ambient real inner product space containing the points
- `n` : the number of points
- `k` : the number of clusters
- `P` : a finite family of points (`Fin n → E`)
- `C` : a clustering of the points
-/
noncomputable section

open scoped BigOperators
open scoped RealInnerProductSpace

namespace CLRS

namespace KMeans

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/--
The **sum of squared distances** from the points `P i` (for `i ∈ S`) to a
candidate center `c`.  This is the within-cluster cost of a cluster whose
points are indexed by `S` and whose center is `c` (CLRS §33.1).
-/
def sumSqDist {α : Type*} (P : α → E) (S : Finset α) (c : E) : ℝ :=
  ∑ i ∈ S, ‖P i - c‖ ^ 2

/--
The **mean** (centroid) of the point family `P` over the index set `S`: the
average of the points `P i` for `i ∈ S`.  For the empty set it returns the
zero vector.
-/
def mean {α : Type*} (P : α → E) (S : Finset α) : E :=
  (S.card : ℝ)⁻¹ • (∑ i ∈ S, P i)

/--
The sum of the displacements of the points of `S` from their mean vanishes:
the mean is the center of mass of the point family `P` over `S`.
-/
lemma sum_sub_mean_eq_zero {α : Type*} (P : α → E) (S : Finset α) :
    ∑ i ∈ S, (P i - mean P S) = 0 := by
  by_cases h0 : S.card = 0
  · rw [Finset.card_eq_zero.mp h0]
    simp [mean]
  · have hn : (S.card : ℝ) ≠ 0 := by exact_mod_cast h0
    calc
      (∑ i ∈ S, (P i - mean P S)) = (∑ i ∈ S, P i) - (∑ i ∈ S, mean P S) := by
        rw [Finset.sum_sub_distrib]
      _ = (∑ i ∈ S, P i) - S.card • mean P S := by
        rw [Finset.sum_const]
      _ = (∑ i ∈ S, P i) - (S.card : ℝ) • ((S.card : ℝ)⁻¹ • (∑ i ∈ S, P i)) := by
        rw [← Nat.cast_smul_eq_nsmul, mean]
      _ = (∑ i ∈ S, P i) - (∑ i ∈ S, P i) := by
        rw [smul_inv_smul₀ hn]
      _ = 0 := by abel

/--
**Variance decomposition** (parallel-axis theorem).  For any index set `S`,
point family `P` with mean `m`, and any center `c`, the sum of squared
distances to `c` exceeds the sum of squared distances to `m` by
`|S| · ‖c - m‖²`:
`∑ i ∈ S ‖P i - c‖² = ∑ i ∈ S ‖P i - m‖² + |S| · ‖c - m‖²`.
-/
theorem sumSqDist_eq_add_card_mul {α : Type*} (P : α → E) (S : Finset α) (c : E) :
    sumSqDist P S c =
      sumSqDist P S (mean P S) + (S.card : ℝ) * ‖c - mean P S‖ ^ 2 := by
  unfold sumSqDist
  calc
    (∑ i ∈ S, ‖P i - c‖ ^ 2)
        = (∑ i ∈ S,
            (‖P i - mean P S‖ ^ 2 + 2 * ⟪P i - mean P S, mean P S - c⟫ +
              ‖mean P S - c‖ ^ 2)) := by
            apply Finset.sum_congr rfl
            intro i hi
            have hpc : P i - c = (P i - mean P S) + (mean P S - c) := by abel
            rw [hpc, norm_add_sq_real]
            rfl
    _ = (∑ i ∈ S, ‖P i - mean P S‖ ^ 2) +
          2 * (∑ i ∈ S, ⟪P i - mean P S, mean P S - c⟫) +
          (S.card : ℝ) * ‖mean P S - c‖ ^ 2 := by
            rw [Finset.sum_add_distrib]
            rw [Finset.sum_add_distrib]
            rw [Finset.mul_sum]
            rw [Finset.sum_const]
            simp
    _ = (∑ i ∈ S, ‖P i - mean P S‖ ^ 2) +
          2 * ⟪∑ i ∈ S, (P i - mean P S), mean P S - c⟫ +
          (S.card : ℝ) * ‖mean P S - c‖ ^ 2 := by
            rw [← sum_inner S (fun i => P i - mean P S) (mean P S - c)]
    _ = (∑ i ∈ S, ‖P i - mean P S‖ ^ 2) + (S.card : ℝ) * ‖mean P S - c‖ ^ 2 := by
            rw [sum_sub_mean_eq_zero P S]
            simp
    _ = sumSqDist P S (mean P S) + (S.card : ℝ) * ‖c - mean P S‖ ^ 2 := by
            rw [← norm_sub_rev (mean P S) c]
            simp [sumSqDist]

/--
**Lemma 33.1.**  The mean of a cluster minimizes the sum of squared distances
to its points: for any index set `S`, point family `P`, and candidate center
`c`, `∑ i ∈ S ‖P i - c‖² ≥ ∑ i ∈ S ‖P i - mean P S‖²`.  The variance
decomposition `sumSqDist_eq_add_card_mul` shows the difference is exactly
`|S| · ‖c - mean P S‖² ≥ 0`.
-/
theorem mean_minimizes_sumSqDist {α : Type*} (P : α → E) (S : Finset α) (c : E) :
    sumSqDist P S (mean P S) ≤ sumSqDist P S c := by
  rw [sumSqDist_eq_add_card_mul P S c]
  have h : 0 ≤ (S.card : ℝ) * ‖c - mean P S‖ ^ 2 := by positivity
  linarith

/--
A **clustering** of `n` points into `k` clusters consists of an assignment of
every point to a cluster together with a centroid for every cluster (CLRS
§33.1).  The ambient point space `E` is a real inner product space.
-/
structure Clustering (n k : ℕ) (E : Type*) where
  /-- The cluster to which each point is assigned. -/
  assign : Fin n → Fin k
  /-- The centroid of each cluster. -/
  centroid : Fin k → E

/--
The points of `P` assigned to cluster `j` by `C`, as a `Finset` of indices.
-/
def cluster (C : Clustering n k E) (j : Fin k) : Finset (Fin n) :=
  Finset.univ.filter fun i => C.assign i = j

/--
The **k-means cost** of a clustering `C` of the points `P`: the sum over all
points of the squared distance to the centroid of the point's assigned
cluster.  This equals the sum over clusters of the within-cluster squared
distances (see `kMeansCost_eq_sum_cluster`).
-/
def kMeansCost (P : Fin n → E) (C : Clustering n k E) : ℝ :=
  ∑ i : Fin n, ‖P i - C.centroid (C.assign i)‖ ^ 2

/--
Sum over the fibers of a function on a finite type: the sum over `β` of the
sum of `f` on the preimage of each element equals the total sum of `f`.
-/
lemma sum_fiberwise {α β : Type*} [Fintype β] [DecidableEq β] {γ : Type*} [AddCommMonoid γ]
    (s : Finset α) (g : α → β) (f : α → γ) :
    (∑ b : β, ∑ a ∈ s.filter (fun a => g a = b), f a) = ∑ a ∈ s, f a := by
  calc
    (∑ b : β, ∑ a ∈ s.filter (fun a => g a = b), f a)
        = (∑ b : β, ∑ a ∈ s, if g a = b then f a else 0) := by
            simp_rw [Finset.sum_filter]
    _ = (∑ a ∈ s, ∑ b : β, if g a = b then f a else 0) := by
            rw [Finset.sum_comm]
    _ = ∑ a ∈ s, f a := by
            apply Finset.sum_congr rfl
            intro a ha
            simp

/--
The k-means cost of a clustering is the sum, over clusters, of the sum of
squared distances from each cluster's points to its own centroid.
-/
theorem kMeansCost_eq_sum_cluster (P : Fin n → E) (C : Clustering n k E) :
    kMeansCost P C =
      ∑ j : Fin k, ∑ i ∈ cluster C j, ‖P i - C.centroid j‖ ^ 2 := by
  unfold kMeansCost
  have hfw :
      (∑ j : Fin k, ∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => C.assign i = j),
          ‖P i - C.centroid (C.assign i)‖ ^ 2) =
        ∑ i : Fin n, ‖P i - C.centroid (C.assign i)‖ ^ 2 := by
    exact sum_fiberwise (s := (Finset.univ : Finset (Fin n))) (g := C.assign)
      (f := fun i => ‖P i - C.centroid (C.assign i)‖ ^ 2)
  calc
    (∑ i : Fin n, ‖P i - C.centroid (C.assign i)‖ ^ 2)
        = (∑ j : Fin k, ∑ i ∈ cluster C j, ‖P i - C.centroid (C.assign i)‖ ^ 2) := by
            rw [cluster, hfw]
    _ = (∑ j : Fin k, ∑ i ∈ cluster C j, ‖P i - C.centroid j‖ ^ 2) := by
            apply Finset.sum_congr rfl
            intro j hj
            apply Finset.sum_congr rfl
            intro i hi
            rw [(Finset.mem_filter.mp hi).2]

/--
There is a cluster whose centroid is a *nearest* centroid to `p`: among the
`k` candidates some one minimizes the squared distance to `p`.
-/
lemma exists_nearest (centroids : Fin k → E) (p : E) (hk : 0 < k) :
    ∃ j : Fin k, ∀ j' : Fin k, ‖p - centroids j‖ ^ 2 ≤ ‖p - centroids j'‖ ^ 2 := by
  let vals : Finset ℝ := Finset.univ.image fun j : Fin k => ‖p - centroids j‖ ^ 2
  have hne : vals.Nonempty := by
    haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩, trivial⟩
    obtain ⟨j⟩ := (Finset.univ_nonempty : (Finset.univ : Finset (Fin k)).Nonempty)
    exact ⟨‖p - centroids j‖ ^ 2, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩
  let m : ℝ := vals.min' hne
  have hm_le : ∀ y ∈ vals, m ≤ y := by
    intro y hy
    simpa [m] using vals.min'_le y hy
  have hm_mem : m ∈ vals := Finset.min'_mem vals hne
  rcases Finset.mem_image.mp hm_mem with ⟨j, hj, hjm⟩
  refine ⟨j, ?_⟩
  intro j'
  exact (hjm.symm ▸ hm_le (‖p - centroids j'‖ ^ 2)
    (Finset.mem_image.mpr ⟨j', Finset.mem_univ j', rfl⟩))

/--
The index of a **nearest centroid** to `p` (CLRS §33.1, assignment step).
Ties are broken by the choice made in `exists_nearest`.
-/
noncomputable def nearestIndex (centroids : Fin k → E) (p : E) (hk : 0 < k) : Fin k :=
  Classical.choose (exists_nearest centroids p hk)

/--
The nearest centroid is no farther from `p` than any other centroid.
-/
lemma nearestIndex_sq_le (centroids : Fin k → E) (p : E) (hk : 0 < k) (j : Fin k) :
    ‖p - centroids (nearestIndex centroids p hk)‖ ^ 2 ≤ ‖p - centroids j‖ ^ 2 := by
  exact Classical.choose_spec (exists_nearest centroids p hk) j

/--
The **assignment step** of Lloyd's algorithm: keep the centroids fixed and
move every point to a nearest centroid.
-/
def assignStep (P : Fin n → E) (C : Clustering n k E) (hk : 0 < k) : Clustering n k E where
  assign := fun i => nearestIndex C.centroid (P i) hk
  centroid := C.centroid

/--
The **assignment step never increases the cost**: moving every point to a
nearest centroid can only bring each point closer to its centroid.
-/
theorem assignStep_cost_le (P : Fin n → E) (C : Clustering n k E) (hk : 0 < k) :
    kMeansCost P (assignStep P C hk) ≤ kMeansCost P C := by
  unfold kMeansCost
  apply Finset.sum_le_sum
  intro i hi
  simpa [assignStep] using (nearestIndex_sq_le C.centroid (P i) hk (C.assign i))

/--
The **mean of cluster** `j` in the clustering `C`: the average of the points
assigned to `j`.
-/
def clusterMean (P : Fin n → E) (C : Clustering n k E) (j : Fin k) : E :=
  mean P (cluster C j)

/--
The **update step** of Lloyd's algorithm: keep the assignment fixed and
replace every centroid by the mean of its cluster's points.
-/
def updateStep (P : Fin n → E) (C : Clustering n k E) : Clustering n k E where
  assign := C.assign
  centroid := fun j => clusterMean P C j

/--
The **update step never increases the cost**: by `mean_minimizes_sumSqDist`
(Lemma 33.1) each cluster's within-cluster cost is minimized when its
centroid is the mean of its points.
-/
theorem updateStep_cost_le (P : Fin n → E) (C : Clustering n k E) :
    kMeansCost P (updateStep P C) ≤ kMeansCost P C := by
  rw [kMeansCost_eq_sum_cluster P (updateStep P C)]
  rw [kMeansCost_eq_sum_cluster P C]
  calc
    (∑ j : Fin k, ∑ i ∈ cluster (updateStep P C) j, ‖P i - (updateStep P C).centroid j‖ ^ 2)
        = (∑ j : Fin k, ∑ i ∈ cluster C j, ‖P i - mean P (cluster C j)‖ ^ 2) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hcl : cluster (updateStep P C) j = cluster C j := by
              simp [cluster, updateStep]
            rw [hcl]
            apply Finset.sum_congr rfl
            intro i hi
            simp [updateStep, clusterMean]
    _ ≤ (∑ j : Fin k, ∑ i ∈ cluster C j, ‖P i - C.centroid j‖ ^ 2) := by
            apply Finset.sum_le_sum
            intro j hj
            simpa [clusterMean, sumSqDist] using
              mean_minimizes_sumSqDist P (cluster C j) (C.centroid j)

/--
**Theorem 33.2.**  Lloyd's algorithm never increases the cost: one full
iteration (assign every point to a nearest centroid, then replace each
centroid by the mean of its cluster) does not increase the k-means cost.
-/
theorem lloyd_iteration_cost_le (P : Fin n → E) (C : Clustering n k E) (hk : 0 < k) :
    kMeansCost P (updateStep P (assignStep P C hk)) ≤ kMeansCost P C := by
  exact le_trans (updateStep_cost_le P (assignStep P C hk)) (assignStep_cost_le P C hk)

end KMeans

end CLRS

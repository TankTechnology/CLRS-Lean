import CLRSLean.Chapter_21.Section_21_4_Analysis.CostedExecution

/-!
# CLRS Section 21.4 - Inverse-Ackermann amortization

This module instantiates the Chapter 21 potential framework for the costed
{lit}`Batteries.UnionFind` execution.  It follows the CLRS/Alstrup analysis:
each non-root receives an Ackermann level and an iteration index derived from
the ranks of the node and its parent.  Path compression either crosses one of
the few Ackermann levels or increases an index, releasing one unit of
potential.
-/

namespace CLRS
namespace Chapter21
namespace Analysis
namespace Ackermann

open Batteries
open Finset

/-! ## Ackermann iteration facts -/

/-- Mathlib's Ackermann successor row is an explicit iterate of the previous row. -/
theorem ack_succ_eq_iterate (k n : Nat) :
    ack (k + 1) n = (ack k)^[n + 1] 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        ack (k + 1) (n + 1) = ack k (ack (k + 1) n) := by
          rw [ack_succ_succ]
        _ = ack k ((ack k)^[n + 1] 1) := by rw [ih]
        _ = (ack k)^[(n + 1) + 1] 1 := by
          symm
          simpa only [Nat.succ_eq_add_one] using
            Function.iterate_succ_apply' (ack k) (n + 1) 1

/-- Iterating a monotone function is monotone in the starting value. -/
theorem iterate_mono_start {f : Nat → Nat} (hf : Monotone f)
    {x y i : Nat} (hxy : x ≤ y) :
    f^[i] x ≤ f^[i] y := by
  induction i with
  | zero => simpa using hxy
  | succ i ih =>
      simpa only [Function.iterate_succ_apply'] using hf ih

/-- Ackermann iteration advances by at least one on every application. -/
theorem add_le_iterate_ack (k i x : Nat) :
    x + i ≤ (ack k)^[i] x := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [Function.iterate_succ_apply']
      have hstep : (ack k)^[i] x + 1 ≤ ack k ((ack k)^[i] x) :=
        Nat.succ_le_of_lt (lt_ack_right k ((ack k)^[i] x))
      omega

/-- Ackermann iteration is monotone in the number of iterations. -/
theorem iterate_ack_mono_count (k x : Nat) :
    Monotone (fun i => (ack k)^[i] x) := by
  intro i j hij
  induction hij with
  | refl => exact Nat.le_refl _
  | @step j _ ih =>
      exact ih.trans <| by
        change (ack k)^[j] x ≤ (ack k)^[j.succ] x
        rw [Function.iterate_succ_apply']
        exact (lt_ack_right k ((ack k)^[j] x)).le

/-- The selected Ackermann row in {lit}`inverseAckermannAt` already exceeds its input. -/
theorem inverseAckermannAt_strict_spec (r n : Nat) :
    n < ack (inverseAckermannAt r n - 1) r :=
  inverseAckermannAt_pred_spec r n

/-! ## Rank offsets, levels, and indices -/

/-- Positive rank used by the Ackermann potential. -/
def rankr (r : Nat) (s : UnionFind) (x : Nat) : Nat :=
  s.rank x + r

/-- Zero-based greatest Ackermann level fitting between a node and its parent. -/
def preLevel (r : Nat) (s : UnionFind) (x : Nat) : Nat :=
  Nat.findGreatest
    (fun k => ack k (rankr r s x) ≤ rankr r s (s.parent x))
    (rankr r s (s.parent x))

/-- Positive level of a non-root node. -/
def level (r : Nat) (s : UnionFind) (x : Nat) : Nat :=
  preLevel r s x + 1

/-- Iteration count inside the node's current Ackermann level. -/
def index (r : Nat) (s : UnionFind) (x : Nat) : Nat :=
  Nat.findGreatest
    (fun i =>
      (ack (preLevel r s x))^[i] (rankr r s x) ≤
        rankr r s (s.parent x))
    (rankr r s (s.parent x))

/-- The rank offset is at least its positive parameter. -/
theorem le_rankr (r : Nat) (s : UnionFind) (x : Nat) :
    r ≤ rankr r s x := by
  simp [rankr]

/-- The rank offset strictly increases across every nontrivial parent edge. -/
theorem rankr_lt_parent {r : Nat} {s : UnionFind} {x : Nat}
    (hx : s.parent x ≠ x) :
    rankr r s x < rankr r s (s.parent x) := by
  simpa [rankr] using s.rank_lt hx

/-- Ackermann row zero fits below the parent rank of every non-root. -/
theorem level_zero_fits {r : Nat} {s : UnionFind} {x : Nat}
    (hx : s.parent x ≠ x) :
    ack 0 (rankr r s x) ≤ rankr r s (s.parent x) := by
  simpa using rankr_lt_parent (r := r) hx

/-- The greatest selected pre-level satisfies its defining inequality. -/
theorem preLevel_spec {r : Nat} {s : UnionFind} {x : Nat}
    (hx : s.parent x ≠ x) :
    ack (preLevel r s x) (rankr r s x) ≤
      rankr r s (s.parent x) := by
  unfold preLevel
  exact Nat.findGreatest_spec (P := fun k =>
      ack k (rankr r s x) ≤ rankr r s (s.parent x))
    (Nat.zero_le _) (level_zero_fits hx)

/-- The next Ackermann level no longer fits below the parent rank. -/
theorem parent_rankr_lt_next_level {r : Nat} {s : UnionFind} {x : Nat}
    (_hx : s.parent x ≠ x) :
    rankr r s (s.parent x) <
      ack (preLevel r s x + 1) (rankr r s x) := by
  by_cases hnext : preLevel r s x + 1 ≤ rankr r s (s.parent x)
  · exact Nat.lt_of_not_ge
      (Nat.findGreatest_is_greatest
        (P := fun k => ack k (rankr r s x) ≤ rankr r s (s.parent x))
        (by simp [preLevel]) hnext)
  · have hbound : rankr r s (s.parent x) < preLevel r s x + 1 :=
      Nat.lt_of_not_ge hnext
    exact hbound.trans (lt_ack_left _ _)

/-- Every non-root has a positive level. -/
theorem level_pos (r : Nat) (s : UnionFind) (x : Nat) :
    0 < level r s x := by
  simp [level]

/-- A level is below the inverse-Ackermann height of the parent rank. -/
theorem level_lt_inverse_parent {r : Nat}
    {s : UnionFind} {x : Nat} (hx : s.parent x ≠ x) :
    level r s x < inverseAckermannAt r (rankr r s (s.parent x)) := by
  let a := inverseAckermannAt r (rankr r s (s.parent x)) - 1
  have ha : rankr r s (s.parent x) < ack a r := by
    exact inverseAckermannAt_pred_spec r _
  have hmono : ack a r ≤ ack a (rankr r s x) :=
    ack_mono_right a (le_rankr r s x)
  have hnot : ¬ack a (rankr r s x) ≤ rankr r s (s.parent x) := by
    omega
  have hpre : preLevel r s x < a := by
    apply Nat.lt_of_not_ge
    intro hale
    have hrow :
        ack a (rankr r s x) ≤ ack (preLevel r s x) (rankr r s x) :=
      ack_mono_left _ hale
    exact hnot (hrow.trans (preLevel_spec hx))
  have hapos : 0 < inverseAckermannAt r (rankr r s (s.parent x)) :=
    inverseAckermannAt_pos _ _
  dsimp [level, a]
  omega

/-- Zero iterations fit below every non-root parent rank. -/
theorem index_zero_fits {r : Nat} {s : UnionFind} {x : Nat}
    (hx : s.parent x ≠ x) :
    (ack (preLevel r s x))^[0] (rankr r s x) ≤
      rankr r s (s.parent x) := by
  simpa using (rankr_lt_parent (r := r) hx).le

/-- The selected index satisfies its defining iteration inequality. -/
theorem index_spec {r : Nat} {s : UnionFind} {x : Nat}
    (hx : s.parent x ≠ x) :
    (ack (preLevel r s x))^[index r s x] (rankr r s x) ≤
      rankr r s (s.parent x) := by
  unfold index
  exact Nat.findGreatest_spec (P := fun i =>
      (ack (preLevel r s x))^[i] (rankr r s x) ≤
        rankr r s (s.parent x))
    (Nat.zero_le _) (index_zero_fits hx)

/-- The index of every non-root is at least one. -/
theorem one_le_index {r : Nat} {s : UnionFind} {x : Nat}
    (hx : s.parent x ≠ x) :
    1 ≤ index r s x := by
  unfold index
  apply Nat.le_findGreatest
  · exact Nat.succ_le_of_lt (Nat.zero_lt_of_lt (rankr_lt_parent (r := r) hx))
  · simpa only [Function.iterate_one] using preLevel_spec (r := r) hx

/-- The iteration index never exceeds the positive rank offset of its node. -/
theorem index_le_rankr {r : Nat} (hr : 1 ≤ r) {s : UnionFind} {x : Nat}
    (hx : s.parent x ≠ x) :
    index r s x ≤ rankr r s x := by
  let q := preLevel r s x
  let rx := rankr r s x
  let rp := rankr r s (s.parent x)
  have hnext : rp < ack (q + 1) rx := by
    exact parent_rankr_lt_next_level (r := r) hx
  have hack_iter : ack (q + 1) rx = (ack q)^[rx + 1] 1 :=
    ack_succ_eq_iterate q rx
  have hone : 1 ≤ rx := le_trans hr (le_rankr r s x)
  have hstart : (ack q)^[rx + 1] 1 ≤ (ack q)^[rx + 1] rx :=
    iterate_mono_start (ack_mono_right q) hone
  have hfail : ¬(ack q)^[rx + 1] rx ≤ rp := by
    rw [← hack_iter] at hstart
    omega
  apply Nat.le_of_not_gt
  intro hindex
  have hmono :
      (ack q)^[rx + 1] rx ≤ (ack q)^[index r s x] rx :=
    iterate_ack_mono_count q rx hindex
  exact hfail (hmono.trans (index_spec (r := r) hx))

/-! ## Node and forest potentials -/

/-- Positive inverse-Ackermann height at a rank offset. -/
noncomputable abbrev alpha (r n : Nat) : Nat :=
  inverseAckermannAt r n

/-- CLRS/Alstrup potential of one union-find node. -/
noncomputable def nodePotential (r : Nat) (s : UnionFind) (x : Nat) : Nat :=
  if s.parent x = x then
    alpha r (rankr r s x) * (rankr r s x + 1)
  else if alpha r (rankr r s x) = alpha r (rankr r s (s.parent x)) then
    (alpha r (rankr r s x) - level r s x) * rankr r s x -
        index r s x + 1
  else
    0

/-- Total potential over the allocated forest. -/
noncomputable def potential (r : Nat) (s : UnionFind) : Nat :=
  ∑ x ∈ range s.size, nodePotential r s x

@[simp]
theorem nodePotential_root {r : Nat} {s : UnionFind} {x : Nat}
    (hx : s.parent x = x) :
    nodePotential r s x =
      alpha r (rankr r s x) * (rankr r s x + 1) := by
  simp [nodePotential, hx]

theorem nodePotential_nonroot_same {r : Nat} {s : UnionFind} {x : Nat}
    (hx : s.parent x ≠ x)
    (ha : alpha r (rankr r s x) = alpha r (rankr r s (s.parent x))) :
    nodePotential r s x =
      (alpha r (rankr r s x) - level r s x) * rankr r s x -
        index r s x + 1 := by
  simp [nodePotential, hx, ha]

theorem nodePotential_nonroot_ne {r : Nat} {s : UnionFind} {x : Nat}
    (hx : s.parent x ≠ x)
    (ha : alpha r (rankr r s x) ≠ alpha r (rankr r s (s.parent x))) :
    nodePotential r s x = 0 := by
  simp [nodePotential, hx, ha]

/-- In the non-root same-height case, the level leaves at least one coefficient. -/
theorem level_lt_alpha_self {r : Nat} {s : UnionFind} {x : Nat}
    (hx : s.parent x ≠ x)
    (ha : alpha r (rankr r s x) = alpha r (rankr r s (s.parent x))) :
    level r s x < alpha r (rankr r s x) := by
  rw [ha]
  exact level_lt_inverse_parent hx

/-- The index subtraction in the node potential is safe. -/
theorem index_le_level_mass {r : Nat} (hr : 1 ≤ r)
    {s : UnionFind} {x : Nat} (hx : s.parent x ≠ x)
    (ha : alpha r (rankr r s x) = alpha r (rankr r s (s.parent x))) :
    index r s x ≤
      (alpha r (rankr r s x) - level r s x) * rankr r s x := by
  have hcoef : 1 ≤ alpha r (rankr r s x) - level r s x := by
    have hlevel := level_lt_alpha_self hx ha
    omega
  exact (index_le_rankr hr hx).trans <| by
    simpa only [one_mul] using
      Nat.mul_le_mul_right (rankr r s x) hcoef

/-- Every same-height non-root owns at least one unit of potential. -/
theorem one_le_nodePotential {r : Nat} (hr : 1 ≤ r)
    {s : UnionFind} {x : Nat} (hx : s.parent x ≠ x)
    (ha : alpha r (rankr r s x) = alpha r (rankr r s (s.parent x))) :
    1 ≤ nodePotential r s x := by
  rw [nodePotential_nonroot_same hx ha]
  have := index_le_level_mass hr hx ha
  omega

/-- Every node potential is bounded by the corresponding root-form expression. -/
theorem nodePotential_le_rootForm {r : Nat}
    (s : UnionFind) (x : Nat) :
    nodePotential r s x ≤
      alpha r (rankr r s x) * (rankr r s x + 1) := by
  by_cases hx : s.parent x = x
  · simp [nodePotential, hx]
  by_cases ha : alpha r (rankr r s x) = alpha r (rankr r s (s.parent x))
  · rw [nodePotential_nonroot_same hx ha]
    have hlevel : level r s x ≤ alpha r (rankr r s x) :=
      (level_lt_alpha_self hx ha).le
    have hmul :
        (alpha r (rankr r s x) - level r s x) * rankr r s x ≤
          alpha r (rankr r s x) * rankr r s x := by
      exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    have halpha : 1 ≤ alpha r (rankr r s x) :=
      inverseAckermannAt_pos _ _
    rw [Nat.mul_add]
    simp only [Nat.mul_one]
    omega
  · simp [nodePotential, hx, ha]

/-- Auxiliary arithmetic for lexicographically increasing level/index pairs. -/
theorem lexPotential_mono {a rank k₁ k₂ i₁ i₂ : Nat}
    (hk : k₁ ≤ k₂) (hk₂ : k₂ < a)
    (hi₁ : i₁ ≤ rank) (hi₂ : 1 ≤ i₂)
    (hindex : k₁ = k₂ → i₁ ≤ i₂) :
    (a - k₂) * rank - i₂ + 1 ≤
      (a - k₁) * rank - i₁ + 1 := by
  rcases hk.eq_or_lt with h | h
  · subst k₂
    exact Nat.add_le_add_right (Nat.sub_le_sub_left (hindex rfl) _) 1
  · have hcoef : a - k₂ + 1 ≤ a - k₁ := by omega
    have hmul : (a - k₂) * rank + rank ≤ (a - k₁) * rank := by
      simpa [Nat.add_mul] using Nat.mul_le_mul_right rank hcoef
    omega

/-! ## Monotone parent evolution -/

/-- The pre-level can only grow when the node rank is fixed and the parent rank grows. -/
theorem preLevel_mono_parent {r : Nat} {s t : UnionFind} {x : Nat}
    (hrank : rankr r s x = rankr r t x)
    (hparent : rankr r s (s.parent x) ≤ rankr r t (t.parent x)) :
    preLevel r s x ≤ preLevel r t x := by
  unfold preLevel
  apply Nat.findGreatest_mono
  · intro k hk
    rw [← hrank]
    exact hk.trans hparent
  · exact hparent

/-- At a fixed level, the iteration index can only grow with the parent rank. -/
theorem index_mono_parent {r : Nat} {s t : UnionFind} {x : Nat}
    (hrank : rankr r s x = rankr r t x)
    (hparent : rankr r s (s.parent x) ≤ rankr r t (t.parent x))
    (hlevel : preLevel r s x = preLevel r t x) :
    index r s x ≤ index r t x := by
  unfold index
  apply Nat.findGreatest_mono
  · intro i hi
    rw [← hrank, ← hlevel]
    exact hi.trans hparent
  · exact hparent

/--
If a non-root keeps its rank, stays a non-root, and its parent rank grows, its
potential cannot increase.
-/
theorem nodePotential_mono_parent {r : Nat} (hr : 1 ≤ r)
    {s t : UnionFind} {x : Nat}
    (hsroot : s.parent x ≠ x) (htroot : t.parent x ≠ x)
    (hrank : rankr r s x = rankr r t x)
    (hparent : rankr r s (s.parent x) ≤ rankr r t (t.parent x)) :
    nodePotential r t x ≤ nodePotential r s x := by
  have halpha_x : alpha r (rankr r s x) = alpha r (rankr r t x) :=
    congrArg (alpha r) hrank
  have halpha_parent :
      alpha r (rankr r s (s.parent x)) ≤
        alpha r (rankr r t (t.parent x)) :=
    inverseAckermannAt_mono r hparent
  by_cases hsheight :
      alpha r (rankr r s x) = alpha r (rankr r s (s.parent x))
  · rw [nodePotential_nonroot_same hsroot hsheight]
    by_cases htheight :
        alpha r (rankr r t x) = alpha r (rankr r t (t.parent x))
    · rw [nodePotential_nonroot_same htroot htheight]
      have hk := preLevel_mono_parent hrank hparent
      have hklt := level_lt_alpha_self htroot htheight
      have hi_old := index_le_rankr hr hsroot
      have hi_new := one_le_index (r := r) htroot
      rw [hrank]
      apply lexPotential_mono (Nat.add_le_add_right hk 1)
      · exact hklt
      · simpa [hrank] using hi_old
      · exact hi_new
      · intro heq
        apply index_mono_parent hrank hparent
        simpa [level] using heq
    · rw [nodePotential_nonroot_ne htroot htheight]
      exact Nat.zero_le _
  · rw [nodePotential_nonroot_ne hsroot hsheight]
    have hslt : alpha r (rankr r s x) <
        alpha r (rankr r s (s.parent x)) := by
      have hmono := inverseAckermannAt_mono r
        (rankr_lt_parent (r := r) hsroot).le
      exact lt_of_le_of_ne hmono hsheight
    have htlt : alpha r (rankr r t x) <
        alpha r (rankr r t (t.parent x)) := by
      rw [← halpha_x]
      exact hslt.trans_le halpha_parent
    rw [nodePotential_nonroot_ne htroot (ne_of_lt htlt)]

/-! ## Path compression never raises the total potential -/

@[simp]
theorem find_rankr (r : Nat) (s : UnionFind) (q : Fin s.size) (x : Nat) :
    rankr r (s.find q).1 x = rankr r s x := by
  simp [rankr, Costed.find_rank]

/-- A path-compressing find preserves exactly the set of roots. -/
theorem find_isRoot_iff (s : UnionFind) (q : Fin s.size) (x : Nat) :
    (s.find q).1.parent x = x ↔ s.parent x = x := by
  rw [← UnionFind.rootD_eq_self, UnionFind.find_root_1,
    UnionFind.rootD_eq_self]

/-- Under path compression, the rank of every node's parent can only grow. -/
theorem find_parent_rankr_mono (r : Nat) (s : UnionFind) (q : Fin s.size)
    (x : Nat) :
    rankr r s (s.parent x) ≤
      rankr r (s.find q).1 ((s.find q).1.parent x) := by
  rcases UnionFind.find_parent_or s q x with hchanged | hsame
  · have hroot : s.rootD (s.parent x) = s.rootD x :=
      UnionFind.rootD_parent s x
    have hrank : s.rank (s.parent x) ≤ s.rank (s.rootD x) := by
      rw [← hroot]
      exact UnionFind.le_rank_root
    rw [hchanged.1]
    simpa [rankr, Costed.find_rank] using Nat.add_le_add_right hrank r
  · rw [hsame]
    simp [rankr, Costed.find_rank]

/-- Each individual node's potential cannot increase during a find. -/
theorem nodePotential_find_le {r : Nat} (hr : 1 ≤ r)
    (s : UnionFind) (q : Fin s.size) (x : Nat) :
    nodePotential r (s.find q).1 x ≤ nodePotential r s x := by
  by_cases hroot : s.parent x = x
  · have hroot' : (s.find q).1.parent x = x := (find_isRoot_iff s q x).2 hroot
    rw [nodePotential_root hroot', nodePotential_root hroot, find_rankr]
  · have hroot' : (s.find q).1.parent x ≠ x := by
      exact fun h => hroot ((find_isRoot_iff s q x).1 h)
    exact nodePotential_mono_parent hr hroot hroot'
      (find_rankr r s q x).symm (find_parent_rankr_mono r s q x)

/-- Total Ackermann potential cannot increase during path compression. -/
theorem potential_find_le {r : Nat} (hr : 1 ≤ r)
    (s : UnionFind) (q : Fin s.size) :
    potential r (s.find q).1 ≤ potential r s := by
  unfold potential
  rw [UnionFind.find_size]
  exact sum_le_sum fun x _ => nodePotential_find_le hr s q x

/-! ## Initial potential -/

@[simp]
theorem singletonForest_parent (n x : Nat) :
    (Forest.singletonForest n).parent x = x := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [Forest.singletonForest] using ih

/-- Every initialized singleton owns exactly {lit}`r + 1` potential units. -/
theorem nodePotential_singleton (r n x : Nat) :
    nodePotential r (Forest.singletonForest n) x = r + 1 := by
  rw [nodePotential_root (singletonForest_parent n x)]
  simp [rankr, inverseAckermannAt_self, Costed.singletonForest_rank]

/-- Initialization has linear potential, which accounts for MAKE-SET operations. -/
theorem potential_singleton (r n : Nat) :
    potential r (Forest.singletonForest n) = n * (r + 1) := by
  unfold potential
  rw [Forest.singletonForest_size]
  calc
    ∑ x ∈ range n, nodePotential r (Forest.singletonForest n) x =
        ∑ _x ∈ range n, (r + 1) := by
      apply sum_congr rfl
      intro x _
      exact nodePotential_singleton r n x
    _ = n * (r + 1) := by simp

/-! ## Exact adjacent-rank level and index -/

/-- Iterating Ackermann row zero simply adds the iteration count. -/
theorem iterate_ack_zero (i x : Nat) :
    (ack 0)^[i] x = x + i := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [Function.iterate_succ_apply', ih]
      simp [Nat.add_assoc]

/-- A node whose parent rank is exactly one greater has pre-level zero. -/
theorem preLevel_eq_zero_of_parent_succ {r : Nat} {s : UnionFind} {x : Nat}
    (hparent : rankr r s (s.parent x) = rankr r s x + 1) :
    preLevel r s x = 0 := by
  unfold preLevel
  apply Nat.findGreatest_eq_zero_iff.2
  intro k hkpos _hkbound hfit
  have hrow : ack 1 (rankr r s x) ≤ ack k (rankr r s x) :=
    ack_mono_left _ hkpos
  simp only [ack_one] at hrow
  omega

/-- At adjacent ranks, the positive level is one. -/
theorem level_eq_one_of_parent_succ {r : Nat} {s : UnionFind} {x : Nat}
    (hparent : rankr r s (s.parent x) = rankr r s x + 1) :
    level r s x = 1 := by
  simp [level, preLevel_eq_zero_of_parent_succ hparent]

/-- At adjacent ranks, exactly one row-zero iteration fits. -/
theorem index_eq_one_of_parent_succ {r : Nat} {s : UnionFind} {x : Nat}
    (hparent : rankr r s (s.parent x) = rankr r s x + 1) :
    index r s x = 1 := by
  unfold index
  rw [preLevel_eq_zero_of_parent_succ hparent]
  apply Nat.findGreatest_eq_iff.2
  refine ⟨?_, ?_, ?_⟩
  · rw [hparent]
    exact Nat.le_add_left 1 _
  · intro _
    simp [hparent]
  · intro i hi _hibound hfit
    rw [iterate_ack_zero, hparent] at hfit
    omega

/-! ## Link evolution -/

/-- Rank-preserving parent growth cannot increase a node potential, including roots. -/
theorem nodePotential_mono_evolution {r : Nat} (hr : 1 ≤ r)
    {s t : UnionFind} {x : Nat}
    (hrank : rankr r s x = rankr r t x)
    (hparent : rankr r s (s.parent x) ≤ rankr r t (t.parent x))
    (hnonroot : s.parent x ≠ x → t.parent x ≠ x) :
    nodePotential r t x ≤ nodePotential r s x := by
  by_cases hroot : s.parent x = x
  · rw [nodePotential_root hroot]
    rw [hrank]
    exact nodePotential_le_rootForm t x
  · exact nodePotential_mono_parent hr hroot (hnonroot hroot) hrank hparent

/-- Isolate two distinguished points when comparing finite sums. -/
theorem sum_le_sum_pair {f g : Nat → Nat} {s : Finset Nat} {x y slack : Nat}
    (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y)
    (hother : ∀ z ∈ s, z ≠ x → z ≠ y → f z ≤ g z)
    (hpair : f x + f y ≤ g x + g y + slack) :
    ∑ z ∈ s, f z ≤ ∑ z ∈ s, g z + slack := by
  classical
  have hy' : y ∈ s.erase x := by simp [hy, hxy.symm]
  have hrest :
      ∑ z ∈ (s.erase x).erase y, f z ≤
        ∑ z ∈ (s.erase x).erase y, g z := by
    apply sum_le_sum
    intro z hz
    apply hother z
    · exact mem_of_mem_erase (mem_of_mem_erase hz)
    · exact fun h => by subst z; simp at hz
    · exact fun h => by subst z; simp at hz
  calc
    ∑ z ∈ s, f z = f x + (f y + ∑ z ∈ (s.erase x).erase y, f z) := by
      rw [← s.add_sum_erase f hx]
      rw [← (s.erase x).add_sum_erase f hy']
    _ ≤ (f x + f y) + ∑ z ∈ (s.erase x).erase y, g z := by
      omega
    _ ≤ (g x + g y + slack) + ∑ z ∈ (s.erase x).erase y, g z := by
      exact Nat.add_le_add_right hpair _
    _ = ∑ z ∈ s, g z + slack := by
      rw [← s.add_sum_erase g hx]
      rw [← (s.erase x).add_sum_erase g hy']
      omega

/-- Linking roots never turns an existing non-root back into a root. -/
theorem link_preserves_nonroot {s : UnionFind} {x y : Fin s.size}
    (_xroot : s.parent x = x) (yroot : s.parent y = y) {i : Nat}
    (hi : s.parent i ≠ i) :
    (s.link x y yroot).parent i ≠ i := by
  rw [UnionFind.parent_link (self := s) (x := x) (y := y) yroot]
  split <;> rename_i hxy
  · exact hi
  split <;> rename_i hrank
  · split <;> rename_i hiy
    · subst i
      exact fun h => hxy (by simpa [yroot] using h)
    · exact hi
  · split <;> rename_i hix
    · subst i
      exact fun h => hxy (by simpa [_xroot] using h.symm)
    · exact hi

/-- Linking a lower-rank {lit}`y` below {lit}`x` changes no ranks. -/
theorem link_rankr_of_y_lt_x {r : Nat} {s : UnionFind} {x y : Fin s.size}
    (yroot : s.parent y = y) (hrank : s.rank y < s.rank x) (i : Nat) :
    rankr r (s.link x y yroot) i = rankr r s i := by
  have hxy : x.1 ≠ y.1 := by
    intro h
    have : x = y := Fin.ext h
    subst y
    omega
  simp [rankr, Costed.link_rank, hxy, hrank]

/-- Linking a lower-rank {lit}`x` below {lit}`y` changes no ranks. -/
theorem link_rankr_of_x_lt_y {r : Nat} {s : UnionFind} {x y : Fin s.size}
    (yroot : s.parent y = y) (hrank : s.rank x < s.rank y) (i : Nat) :
    rankr r (s.link x y yroot) i = rankr r s i := by
  have hxy : x.1 ≠ y.1 := by
    intro h
    have : x = y := Fin.ext h
    subst y
    omega
  have hnot : ¬s.rank y < s.rank x := Nat.not_lt_of_ge hrank.le
  have hne : s.rank x ≠ s.rank y := ne_of_lt hrank
  simp [rankr, Costed.link_rank, hxy, hnot, hne]

/-- Parent ranks grow when a lower-rank {lit}`y` is linked below {lit}`x`. -/
theorem link_parent_rankr_mono_of_y_lt_x {r : Nat} {s : UnionFind}
    {x y : Fin s.size} (yroot : s.parent y = y)
    (hrank : s.rank y < s.rank x) (i : Nat) :
    rankr r s (s.parent i) ≤
      rankr r (s.link x y yroot) ((s.link x y yroot).parent i) := by
  have hxy : x.1 ≠ y.1 := by
    intro h
    have : x = y := Fin.ext h
    subst y
    omega
  rw [UnionFind.parent_link (self := s) (x := x) (y := y) yroot]
  simp only [if_neg hxy, if_pos hrank]
  split <;> rename_i hiy
  · subst i
    rw [yroot, link_rankr_of_y_lt_x yroot hrank]
    simp [rankr]
    omega
  · rw [link_rankr_of_y_lt_x yroot hrank]

/-- Parent ranks grow when a lower-rank {lit}`x` is linked below {lit}`y`. -/
theorem link_parent_rankr_mono_of_x_lt_y {r : Nat} {s : UnionFind}
    {x y : Fin s.size} (xroot : s.parent x = x) (yroot : s.parent y = y)
    (hrank : s.rank x < s.rank y) (i : Nat) :
    rankr r s (s.parent i) ≤
      rankr r (s.link x y yroot) ((s.link x y yroot).parent i) := by
  have hxy : x.1 ≠ y.1 := by
    intro h
    have : x = y := Fin.ext h
    subst y
    omega
  have hnot : ¬s.rank y < s.rank x := Nat.not_lt_of_ge hrank.le
  rw [UnionFind.parent_link (self := s) (x := x) (y := y) yroot]
  simp only [if_neg hxy, if_neg hnot]
  split <;> rename_i hix
  · subst i
    rw [link_rankr_of_x_lt_y yroot hrank]
    rw [xroot]
    simp [rankr]
    omega
  · rw [link_rankr_of_x_lt_y yroot hrank]

/-- A strict-rank link cannot increase total potential. -/
theorem potential_link_le_of_ne_rank {r : Nat} (hr : 1 ≤ r)
    {s : UnionFind} {x y : Fin s.size}
    (xroot : s.parent x = x) (yroot : s.parent y = y)
    (hne : s.rank x ≠ s.rank y) :
    potential r (s.link x y yroot) ≤ potential r s := by
  unfold potential
  have hsize : (s.link x y yroot).size = s.size := by
    simp [UnionFind.link, UnionFind.size]
  rw [hsize]
  apply sum_le_sum
  intro i _hi
  rcases lt_or_gt_of_ne hne with hxy | hyx
  · exact nodePotential_mono_evolution hr
      (link_rankr_of_x_lt_y yroot hxy i).symm
      (link_parent_rankr_mono_of_x_lt_y xroot yroot hxy i)
      (link_preserves_nonroot xroot yroot)
  · exact nodePotential_mono_evolution hr
      (link_rankr_of_y_lt_x yroot hyx i).symm
      (link_parent_rankr_mono_of_y_lt_x yroot hyx i)
      (link_preserves_nonroot xroot yroot)

/-! ## Equal-rank link -/

/-- In an equal-rank link, only the winning root {lit}`y` gains one rank. -/
theorem link_rankr_of_eq_rank {r : Nat} {s : UnionFind}
    {x y : Fin s.size} (yroot : s.parent y = y)
    (hxy : x.1 ≠ y.1) (heq : s.rank x = s.rank y) (i : Nat) :
    rankr r (s.link x y yroot) i =
      if i = y.1 then rankr r s y + 1 else rankr r s i := by
  by_cases hi : i = y.1
  · simp [rankr, Costed.link_rank, hxy, heq, hi]
    omega
  · simp [rankr, Costed.link_rank, hxy, heq, hi]

/-- The losing root becomes a child of the winning root. -/
theorem link_parent_x_of_eq_rank {s : UnionFind} {x y : Fin s.size}
    (yroot : s.parent y = y) (hxy : x.1 ≠ y.1)
    (heq : s.rank x = s.rank y) :
    (s.link x y yroot).parent x = y := by
  have hnot : ¬s.rank y < s.rank x := by omega
  simpa [hxy, hnot] using
    UnionFind.parent_link (self := s) (x := x) (y := y) yroot (i := (x : Nat))

/-- The winning root remains a root after an equal-rank link. -/
theorem link_parent_y_of_eq_rank {s : UnionFind} {x y : Fin s.size}
    (yroot : s.parent y = y) (hxy : x.1 ≠ y.1)
    (heq : s.rank x = s.rank y) :
    (s.link x y yroot).parent y = y := by
  have hnot : ¬s.rank y < s.rank x := by omega
  simpa [hxy, hnot, yroot] using
    UnionFind.parent_link (self := s) (x := x) (y := y) yroot (i := (y : Nat))

/-- Equal old ranks give equal positive rank offsets. -/
theorem rankr_eq_of_rank_eq {r : Nat} {s : UnionFind}
    {x y : Nat} (heq : s.rank x = s.rank y) :
    rankr r s x = rankr r s y := by
  simp [rankr, heq]

/-- The losing root keeps its rank in an equal-rank link. -/
theorem link_rankr_x_of_eq_rank {r : Nat} {s : UnionFind}
    {x y : Fin s.size} (yroot : s.parent y = y)
    (hxy : x.1 ≠ y.1) (heq : s.rank x = s.rank y) :
    rankr r (s.link x y yroot) x = rankr r s x := by
  rw [link_rankr_of_eq_rank yroot hxy heq]
  simp [hxy]

/-- The winning root's positive rank offset increases by exactly one. -/
theorem link_rankr_y_of_eq_rank {r : Nat} {s : UnionFind}
    {x y : Fin s.size} (yroot : s.parent y = y)
    (hxy : x.1 ≠ y.1) (heq : s.rank x = s.rank y) :
    rankr r (s.link x y yroot) y = rankr r s y + 1 := by
  rw [link_rankr_of_eq_rank yroot hxy heq]
  simp

/-- The new parent rank of the losing root is exactly adjacent to its rank. -/
theorem link_parent_rankr_x_succ {r : Nat} {s : UnionFind}
    {x y : Fin s.size} (yroot : s.parent y = y)
    (hxy : x.1 ≠ y.1) (heq : s.rank x = s.rank y) :
    rankr r (s.link x y yroot) ((s.link x y yroot).parent x) =
      rankr r (s.link x y yroot) x + 1 := by
  rw [link_parent_x_of_eq_rank yroot hxy heq,
    link_rankr_y_of_eq_rank yroot hxy heq,
    link_rankr_x_of_eq_rank yroot hxy heq]
  rw [rankr_eq_of_rank_eq heq]

/-- Exact potential of the losing root when an equal-rank link stays in one alpha row. -/
theorem nodePotential_link_x_same_alpha {r : Nat} (hr : 1 ≤ r) {s : UnionFind}
    {x y : Fin s.size} (yroot : s.parent y = y)
    (hxy : x.1 ≠ y.1) (heq : s.rank x = s.rank y)
    (ha : alpha r (rankr r s x) = alpha r (rankr r s x + 1)) :
    nodePotential r (s.link x y yroot) x =
      (alpha r (rankr r s x) - 1) * rankr r s x := by
  let t := s.link x y yroot
  have hparent := link_parent_x_of_eq_rank yroot hxy heq
  have hrx := link_rankr_x_of_eq_rank (r := r) yroot hxy heq
  have hparentRank := link_parent_rankr_x_succ (r := r) yroot hxy heq
  have hsame :
      alpha r (rankr r t x) = alpha r (rankr r t (t.parent x)) := by
    rw [hrx, hparentRank, hrx]
    exact ha
  have hnonroot : t.parent x ≠ x := by
    rw [show t.parent x = y by exact hparent]
    exact hxy.symm
  rw [nodePotential_nonroot_same hnonroot hsame]
  have hlevel : level r t x = 1 :=
    level_eq_one_of_parent_succ hparentRank
  have hindex : index r t x = 1 :=
    index_eq_one_of_parent_succ hparentRank
  have hmass := index_le_level_mass hr hnonroot hsame
  rw [hlevel, hindex, hrx] at hmass ⊢
  omega

/-- Exact potential of the losing root when the winning rank crosses an alpha row. -/
theorem nodePotential_link_x_ne_alpha {r : Nat} {s : UnionFind}
    {x y : Fin s.size} (yroot : s.parent y = y)
    (hxy : x.1 ≠ y.1) (heq : s.rank x = s.rank y)
    (ha : alpha r (rankr r s x) ≠ alpha r (rankr r s x + 1)) :
    nodePotential r (s.link x y yroot) x = 0 := by
  let t := s.link x y yroot
  have hparent := link_parent_x_of_eq_rank yroot hxy heq
  have hrx := link_rankr_x_of_eq_rank (r := r) yroot hxy heq
  have hparentRank := link_parent_rankr_x_succ (r := r) yroot hxy heq
  apply nodePotential_nonroot_ne
  · rw [show t.parent x = y by exact hparent]
    exact hxy.symm
  · rw [hrx, hparentRank, hrx]
    exact ha

/-- The two roots involved in an equal-rank link gain at most two potential units. -/
theorem nodePotential_link_pair_le_add_two {r : Nat} (hr : 1 ≤ r)
    {s : UnionFind} {x y : Fin s.size}
    (xroot : s.parent x = x) (yroot : s.parent y = y)
    (hxy : x.1 ≠ y.1) (heq : s.rank x = s.rank y) :
    nodePotential r (s.link x y yroot) x +
        nodePotential r (s.link x y yroot) y ≤
      nodePotential r s x + nodePotential r s y + 2 := by
  let rx := rankr r s x
  let a := alpha r rx
  have hry : rankr r s y = rx := (rankr_eq_of_rank_eq heq).symm
  have hnewy : rankr r (s.link x y yroot) y = rx + 1 := by
    rw [link_rankr_y_of_eq_rank yroot hxy heq, hry]
  have hnewroot : (s.link x y yroot).parent y = y :=
    link_parent_y_of_eq_rank yroot hxy heq
  rw [nodePotential_root xroot, nodePotential_root yroot,
    nodePotential_root hnewroot, hnewy, hry]
  by_cases ha : a = alpha r (rx + 1)
  · have ha' :
        alpha r (rankr r s x) = alpha r (rankr r s x + 1) := by
      simpa [a, rx] using ha
    rw [nodePotential_link_x_same_alpha hr yroot hxy heq ha']
    change (a - 1) * rx + alpha r (rx + 1) * (rx + 1 + 1) ≤
      a * (rx + 1) + a * (rx + 1) + 2
    rw [← ha]
    have haPos : 1 ≤ a := inverseAckermannAt_pos _ _
    have hasub : a - 1 + 1 = a := Nat.sub_add_cancel haPos
    nlinarith
  · have ha' :
        alpha r (rankr r s x) ≠ alpha r (rankr r s x + 1) := by
      simpa [a, rx] using ha
    rw [nodePotential_link_x_ne_alpha yroot hxy heq ha']
    change 0 + alpha r (rx + 1) * (rx + 1 + 1) ≤
      a * (rx + 1) + a * (rx + 1) + 2
    have haPos : 1 ≤ a := inverseAckermannAt_pos _ _
    have hsucc : alpha r (rx + 1) ≤ a + 1 :=
      inverseAckermannAt_succ_le r rx
    nlinarith

/-- Away from the winning root, an equal-rank link preserves node ranks. -/
theorem link_rankr_of_eq_rank_of_ne_y {r : Nat} {s : UnionFind}
    {x y : Fin s.size} (yroot : s.parent y = y)
    (hxy : x.1 ≠ y.1) (heq : s.rank x = s.rank y)
    {i : Nat} (hiy : i ≠ y.1) :
    rankr r (s.link x y yroot) i = rankr r s i := by
  rw [link_rankr_of_eq_rank yroot hxy heq]
  simp [hiy]

/-- Away from the losing root, an equal-rank link can only grow the parent rank. -/
theorem link_parent_rankr_mono_of_eq_rank {r : Nat} {s : UnionFind}
    {x y : Fin s.size} (yroot : s.parent y = y)
    (hxy : x.1 ≠ y.1) (heq : s.rank x = s.rank y)
    {i : Nat} (hix : i ≠ x.1) :
    rankr r s (s.parent i) ≤
      rankr r (s.link x y yroot) ((s.link x y yroot).parent i) := by
  have hnot : ¬s.rank y < s.rank x := by omega
  rw [UnionFind.parent_link (self := s) (x := x) (y := y) yroot]
  simp only [if_neg hxy, if_neg hnot,
    if_neg (show ¬x.1 = i by exact fun h => hix h.symm)]
  rw [link_rankr_of_eq_rank yroot hxy heq]
  split <;> rename_i hp
  · rw [hp]
    omega
  · exact Nat.le_refl _

/-- An equal-rank link raises the whole forest potential by at most two. -/
theorem potential_link_le_add_two_of_eq_rank {r : Nat} (hr : 1 ≤ r)
    {s : UnionFind} {x y : Fin s.size}
    (xroot : s.parent x = x) (yroot : s.parent y = y)
    (hxy : x.1 ≠ y.1) (heq : s.rank x = s.rank y) :
    potential r (s.link x y yroot) ≤ potential r s + 2 := by
  unfold potential
  have hsize : (s.link x y yroot).size = s.size := by
    simp [UnionFind.link, UnionFind.size]
  rw [hsize]
  apply sum_le_sum_pair (x := x.1) (y := y.1)
  · simp [x.2]
  · simp [y.2]
  · exact hxy
  · intro i _hi hix hiy
    exact nodePotential_mono_evolution hr
      (link_rankr_of_eq_rank_of_ne_y yroot hxy heq hiy).symm
      (link_parent_rankr_mono_of_eq_rank yroot hxy heq hix)
      (link_preserves_nonroot xroot yroot)
  · exact nodePotential_link_pair_le_add_two hr xroot yroot hxy heq

/-- Every union-by-rank link raises Ackermann potential by at most two. -/
theorem potential_link_le_add_two {r : Nat} (hr : 1 ≤ r)
    {s : UnionFind} {x y : Fin s.size}
    (xroot : s.parent x = x) (yroot : s.parent y = y) :
    potential r (s.link x y yroot) ≤ potential r s + 2 := by
  by_cases hxy : x.1 = y.1
  · have hfin : x = y := Fin.ext hxy
    subst y
    simp [UnionFind.link, UnionFind.linkAux]
  · by_cases heq : s.rank x = s.rank y
    · exact potential_link_le_add_two_of_eq_rank hr xroot yroot hxy heq
    · exact (potential_link_le_of_ne_rank hr xroot yroot heq).trans
        (Nat.le_add_right _ _)

/-! ## Union potential -/

/-- A complete Batteries union raises Ackermann potential by at most two. -/
theorem potential_union_le_add_two {r : Nat} (hr : 1 ≤ r)
    (s : UnionFind) (x y : Fin s.size) :
    potential r (s.union x y) ≤ potential r s + 2 := by
  unfold UnionFind.union
  generalize hfindx : s.find x = fx
  rcases fx with ⟨s₁, rx, ex⟩
  dsimp only
  have hy : (y : Nat) < s₁.size := by
    rw [ex]
    exact y.2
  let y₁ : Fin s₁.size := ⟨y, hy⟩
  let fy := s₁.find y₁
  let s₂ := fy.1
  let ry : Fin s₂.size := fy.2.1
  have ey : s₂.size = s₁.size := fy.2.2
  let rx₂ : Fin s₂.size := ⟨rx, by rw [ey]; exact rx.2⟩
  have rxroot₁ : s₁.parent rx = rx := by
    have hreturned : (rx : Nat) = s.rootD x := by
      have h := UnionFind.find_root_2 s x
      rw [hfindx] at h
      exact h
    have hroot_old : s.parent rx = rx := by
      simpa [hreturned] using UnionFind.parent_rootD s x
    have h := Costed.find_preserves_root s x hroot_old
    rw [hfindx] at h
    exact h
  have rxroot₂ : s₂.parent rx₂ = rx₂ := by
    simpa [s₂, fy, rx₂] using
      Costed.find_preserves_root s₁ y₁ rxroot₁
  have ryroot₂ : s₂.parent ry = ry := by
    have hreturned : (ry : Nat) = s₁.rootD y₁ := by
      have h := UnionFind.find_root_2 s₁ y₁
      change (ry : Nat) = s₁.rootD y₁ at h
      exact h
    subst ry
    simpa [s₂, fy] using
      Costed.find_preserves_root s₁ y₁ (UnionFind.parent_rootD s₁ y₁)
  have hfind₁ : potential r s₁ ≤ potential r s := by
    simpa [hfindx] using potential_find_le hr s x
  have hfind₂ : potential r s₂ ≤ potential r s₁ := by
    simpa [s₂, fy] using potential_find_le hr s₁ y₁
  have hlink : potential r (s₂.link rx₂ ry ryroot₂) ≤ potential r s₂ + 2 :=
    potential_link_le_add_two hr rxroot₂ ryroot₂
  have htotal : potential r (s₂.link rx₂ ry ryroot₂) ≤ potential r s + 2 := by
    omega
  simpa [s₂, fy, ry, rx₂, y₁] using htotal

/-! ## Parent-chain bookkeeping for path compression -/

/-- The non-root vertices traversed by Batteries find, in traversal order. -/
def findNodes (s : UnionFind) (x : Fin s.size) : List Nat :=
  let y := s.arr[x.1].parent
  if h : y = x then
    []
  else
    have := Nat.sub_lt_sub_left (s.lt_rankMax x) (s.rank'_lt _ _ h)
    x.1 :: findNodes s ⟨y, s.parent'_lt _ x.2⟩
termination_by s.rankMax - s.rank x

/-- The explicit node list has exactly the concrete traversal-counter length. -/
@[simp]
theorem findNodes_length (s : UnionFind) (x : Fin s.size) :
    (findNodes s x).length = Costed.findEdges s x := by
  rw [findNodes, Costed.findEdges]
  split
  · rfl
  · simp only [List.length_cons, Nat.add_right_cancel_iff]
    exact findNodes_length s ⟨s.arr[x.1].parent, s.parent'_lt _ x.2⟩
termination_by s.rankMax - s.rank x
decreasing_by
  exact Nat.sub_lt_sub_left (s.lt_rankMax x) (s.rank'_lt _ _ ‹_›)

/-- Every listed find node is allocated. -/
theorem findNodes_mem_lt {s : UnionFind} {x : Fin s.size} {v : Nat}
    (hv : v ∈ findNodes s x) : v < s.size := by
  rw [findNodes] at hv
  split at hv
  · simp at hv
  · simp only [List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact x.2
    · exact findNodes_mem_lt hv
termination_by s.rankMax - s.rank x
decreasing_by
  exact Nat.sub_lt_sub_left (s.lt_rankMax x) (s.rank'_lt _ _ ‹_›)

/-- Every listed find node is a non-root in the original forest. -/
theorem findNodes_mem_nonroot {s : UnionFind} {x : Fin s.size} {v : Nat}
    (hv : v ∈ findNodes s x) : s.parent v ≠ v := by
  rw [findNodes] at hv
  split at hv
  · simp at hv
  · rename_i h
    simp only [List.mem_cons] at hv
    rcases hv with rfl | hv
    · simpa [UnionFind.parent, UnionFind.parentD_eq x.2] using h
    · exact findNodes_mem_nonroot hv
termination_by s.rankMax - s.rank x
decreasing_by
  exact Nat.sub_lt_sub_left (s.lt_rankMax x) (s.rank'_lt _ _ ‹_›)

/-- Ranks are monotone from the current find node to every listed node. -/
theorem findNodes_rank_le {s : UnionFind} {x : Fin s.size} {v : Nat}
    (hv : v ∈ findNodes s x) : s.rank x ≤ s.rank v := by
  rw [findNodes] at hv
  split at hv
  · simp at hv
  · rename_i h
    simp only [List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact Nat.le_refl _
    · have hstep : s.rank x < s.rank s.arr[x.1].parent :=
        s.rank'_lt _ _ h
      exact hstep.le.trans (findNodes_rank_le hv)
termination_by s.rankMax - s.rank x
decreasing_by
  exact Nat.sub_lt_sub_left (s.lt_rankMax x) (s.rank'_lt _ _ ‹_›)

/-- Every tail node has larger rank than the current find node. -/
theorem findNodes_tail_rank_lt {s : UnionFind} {x : Fin s.size} {v : Nat}
    (hv : v ∈ (findNodes s
      ⟨s.arr[x.1].parent, s.parent'_lt _ x.2⟩)) :
    s.rank x < s.rank v := by
  have hnonroot : s.arr[x.1].parent ≠ x := by
    intro h
    rw [findNodes] at hv
    simp [h] at hv
  exact (s.rank'_lt _ _ hnonroot).trans_le (findNodes_rank_le hv)

/-- Every listed node is connected to the find start by an exact parent path. -/
theorem findNodes_path_to_mem {s : UnionFind} {x : Fin s.size} {v : Nat}
    (hv : v ∈ findNodes s x) :
    ∃ k, ParentPath s x v k := by
  rw [findNodes] at hv
  split at hv
  · simp at hv
  · rename_i h
    simp only [List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact ⟨0, ParentPath.refl x⟩
    · rcases findNodes_path_to_mem hv with ⟨k, hk⟩
      have hparent : s.parent x = s.arr[x.1].parent :=
        UnionFind.parentD_eq x.2
      exact ⟨k + 1, ParentPath.step hparent (fun h' => h h'.symm) hk⟩
termination_by s.rankMax - s.rank x
decreasing_by
  exact Nat.sub_lt_sub_left (s.lt_rankMax x) (s.rank'_lt _ _ ‹_›)

/-- Two listed nodes with equal rank are the same node. -/
theorem findNodes_rank_injective {s : UnionFind} {x : Fin s.size} {u v : Nat}
    (hu : u ∈ findNodes s x) (hv : v ∈ findNodes s x)
    (hrank : s.rank u = s.rank v) : u = v := by
  rw [findNodes] at hu
  split at hu
  · simp at hu
  · rename_i h
    have hxlist : findNodes s x =
        x.1 :: findNodes s ⟨s.arr[x.1].parent, s.parent'_lt _ x.2⟩ := by
      rw [findNodes]
      simp [h]
    rw [hxlist] at hv
    simp only [List.mem_cons] at hu hv
    rcases hu with rfl | hu <;> rcases hv with rfl | hv
    · rfl
    · exact (Nat.ne_of_lt (findNodes_tail_rank_lt hv) hrank).elim
    · exact (Nat.ne_of_gt (findNodes_tail_rank_lt hu) hrank).elim
    · exact findNodes_rank_injective hu hv hrank
termination_by s.rankMax - s.rank x
decreasing_by
  exact Nat.sub_lt_sub_left (s.lt_rankMax x) (s.rank'_lt _ _ ‹_›)

/-- The executable parent-chain list contains no duplicate vertices. -/
theorem findNodes_nodup (s : UnionFind) (x : Fin s.size) :
    (findNodes s x).Nodup := by
  rw [findNodes]
  split
  · exact List.nodup_nil
  · apply List.nodup_cons.2
    constructor
    · intro hx
      exact (Nat.lt_irrefl _ (findNodes_tail_rank_lt hx))
    · exact findNodes_nodup s
        ⟨s.arr[x.1].parent, s.parent'_lt _ x.2⟩
termination_by s.rankMax - s.rank x
decreasing_by
  exact Nat.sub_lt_sub_left (s.lt_rankMax x) (s.rank'_lt _ _ ‹_›)

/-- On one find chain, a lower-rank listed node has the higher-rank node as an ancestor. -/
theorem findNodes_ancestor_of_rank_lt {s : UnionFind} {q : Fin s.size}
    {u v : Nat} (hu : u ∈ findNodes s q) (hv : v ∈ findNodes s q)
    (hrank : s.rank u < s.rank v) :
    ∃ k, ParentPath s (s.parent u) v k := by
  rw [findNodes] at hu
  split at hu
  · simp at hu
  · rename_i h
    have hqlist : findNodes s q =
        q.1 :: findNodes s ⟨s.arr[q.1].parent, s.parent'_lt _ q.2⟩ := by
      rw [findNodes]
      simp [h]
    rw [hqlist] at hv
    simp only [List.mem_cons] at hu hv
    rcases hu with rfl | hu
    · rcases hv with rfl | hv
      · exact (Nat.lt_irrefl _ hrank).elim
      · simpa [UnionFind.parent, UnionFind.parentD_eq q.2] using
          findNodes_path_to_mem hv
    · rcases hv with rfl | hv
      · have htail := findNodes_tail_rank_lt hu
        omega
      · exact findNodes_ancestor_of_rank_lt hu hv hrank
termination_by s.rankMax - s.rank q
decreasing_by
  exact Nat.sub_lt_sub_left (s.lt_rankMax q) (s.rank'_lt _ _ ‹_›)

namespace ParentPath

/-- Endpoints of a parent path have the same canonical root. -/
theorem rootD_eq {s : UnionFind} {x z k : Nat}
    (path : ParentPath s x z k) : s.rootD x = s.rootD z := by
  induction path with
  | refl => rfl
  | @step x y z k hparent _ rest ih =>
      calc
        s.rootD x = s.rootD (s.parent x) :=
          (UnionFind.rootD_parent (self := s) (x := x)).symm
        _ = s.rootD y := by rw [hparent]
        _ = s.rootD z := ih

/-- Positive rank offsets are monotone along a parent path. -/
theorem rankr_le_endpoint {r : Nat} {s : UnionFind} {x z k : Nat}
    (path : ParentPath s x z k) :
    rankr r s x ≤ rankr r s z := by
  have h := parentPath_rank_bound path
  simp only [rankr]
  omega

/-- Ackermann heights are monotone along a parent path. -/
theorem alpha_le_endpoint {r : Nat} {s : UnionFind} {x z k : Nat}
    (path : ParentPath s x z k) :
    alpha r (rankr r s x) ≤ alpha r (rankr r s z) :=
  inverseAckermannAt_mono r (rankr_le_endpoint path)

end ParentPath

/-- A non-head parent updated by {lit}`find x` is updated exactly as by the recursive find. -/
theorem find_parent_tail {s : UnionFind} {x y v : Nat}
    (hx : x < s.size) (hparent : s.parent x = y)
    (hvx : v ≠ x) :
    (s.find ⟨x, hx⟩).1.parent v =
      (s.find ⟨y, by rw [← hparent]; exact (s.parent_lt x).2 hx⟩).1.parent v := by
  have hparent' : s.arr[x].parent = y := by
    simpa [UnionFind.parent, UnionFind.parentD_eq hx] using hparent
  change
    UnionFind.parentD (UnionFind.findAux s ⟨x, hx⟩).s v =
      UnionFind.parentD
        (UnionFind.findAux s
          ⟨y, by rw [← hparent]; exact (s.parent_lt x).2 hx⟩).s v
  rw [UnionFind.parentD_findAux]
  simp [hvx, hparent']

/-- Batteries find points every traversed non-root directly at the returned root. -/
theorem find_parent_eq_root_of_mem {s : UnionFind} {x : Fin s.size} {v : Nat}
    (hv : v ∈ findNodes s x) :
    (s.find x).1.parent v = s.rootD x := by
  rw [findNodes] at hv
  split at hv
  · simp at hv
  · rename_i h
    simp only [List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact UnionFind.find_parent_1 s x
    · have hparent : s.parent x = s.arr[x.1].parent :=
        UnionFind.parentD_eq x.2
      have hvx : v ≠ x := by
        intro hvx
        subst v
        exact Nat.lt_irrefl _ (findNodes_tail_rank_lt hv)
      rw [find_parent_tail x.2 hparent hvx]
      calc
        (s.find ⟨s.arr[x.1].parent, s.parent'_lt _ x.2⟩).1.parent v =
            s.rootD s.arr[x.1].parent := find_parent_eq_root_of_mem hv
        _ = s.rootD (s.parent x) := by rw [hparent]
        _ = s.rootD x := UnionFind.rootD_parent s x
termination_by s.rankMax - s.rank x
decreasing_by
  exact Nat.sub_lt_sub_left (s.lt_rankMax x) (s.rank'_lt _ _ ‹_›)

/-! ## Potential released by pleasant path nodes -/

/-- Strict lexicographic progress in level/index releases a potential unit. -/
theorem lexPotential_lt {a rank k₁ k₂ i₁ i₂ : Nat}
    (hk₂ : k₂ < a)
    (hi₁ : i₁ ≤ rank) (hi₂ : 1 ≤ i₂)
    (hi₂mass : i₂ ≤ (a - k₂) * rank)
    (hlex : k₁ < k₂ ∨ k₁ = k₂ ∧ i₁ < i₂) :
    (a - k₂) * rank - i₂ + 1 <
      (a - k₁) * rank - i₁ + 1 := by
  rcases hlex with hk | ⟨rfl, hi⟩
  · have hcoef : a - k₂ + 1 ≤ a - k₁ := by omega
    have hmul : (a - k₂) * rank + rank ≤ (a - k₁) * rank := by
      simpa [Nat.add_mul] using Nat.mul_le_mul_right rank hcoef
    omega
  · omega

/-- A parent path whose start is allocated also has an allocated endpoint. -/
theorem ParentPath.endpoint_lt {s : UnionFind} {x z k : Nat}
    (path : ParentPath s x z k) (hx : x < s.size) : z < s.size := by
  induction path with
  | refl => exact hx
  | @step x y z k hparent _ rest ih =>
      apply ih
      rw [← hparent]
      exact (s.parent_lt x).2 hx

/-- A listed node has the same canonical root as the find query. -/
theorem findNodes_rootD_eq {s : UnionFind} {q : Fin s.size} {x : Nat}
    (hx : x ∈ findNodes s q) : s.rootD x = s.rootD q := by
  rcases findNodes_path_to_mem hx with ⟨k, path⟩
  exact (ParentPath.rootD_eq path).symm

/-- A same-level non-root ancestor forces the compressed index to advance. -/
theorem index_succ_le_find_of_same_level_ancestor {r : Nat}
    {s : UnionFind} {q : Fin s.size} {x y : Nat}
    (hxmem : x ∈ findNodes s q)
    (hy : s.parent y ≠ y)
    {k : Nat} (path : ParentPath s (s.parent x) y k)
    (hlevel : level r s x = level r s y)
    (hlevelFind : level r s x = level r (s.find q).1 x) :
    index r s x + 1 ≤ index r (s.find q).1 x := by
  have hx : s.parent x ≠ x := findNodes_mem_nonroot hxmem
  have hpre : preLevel r s x = preLevel r s y := by
    simp only [level] at hlevel
    omega
  have hpreFind : preLevel r s x = preLevel r (s.find q).1 x := by
    simp only [level] at hlevelFind
    omega
  have hpathRank : rankr r s (s.parent x) ≤ rankr r s y :=
    ParentPath.rankr_le_endpoint path
  have hiterParent :
      (ack (preLevel r s x))^[index r s x + 1] (rankr r s x) ≤
        rankr r s (s.parent y) := by
    rw [Function.iterate_succ_apply']
    have hbase := (index_spec (r := r) hx).trans hpathRank
    exact (ack_mono_right _ hbase).trans <| by
      rw [hpre]
      exact preLevel_spec hy
  have hrootY : s.rootD (s.parent y) = s.rootD q := by
    rw [UnionFind.rootD_parent]
    have hpathRoot := ParentPath.rootD_eq path
    rw [UnionFind.rootD_parent] at hpathRoot
    exact hpathRoot.symm.trans (findNodes_rootD_eq hxmem)
  have hparentRootRank :
      rankr r s (s.parent y) ≤ rankr r s (s.rootD q) := by
    have h := UnionFind.le_rank_root (self := s) (x := s.parent y)
    simp only [rankr]
    rw [hrootY] at h
    omega
  have hiterRoot := hiterParent.trans hparentRootRank
  have hnewParent : (s.find q).1.parent x = s.rootD q :=
    find_parent_eq_root_of_mem hxmem
  have hbound :
      index r s x + 1 ≤ rankr r (s.find q).1 ((s.find q).1.parent x) := by
    have hadd := add_le_iterate_ack (preLevel r s x) (index r s x + 1)
      (rankr r s x)
    rw [hnewParent]
    simp only [find_rankr]
    omega
  unfold index
  apply Nat.le_findGreatest hbound
  rw [← hpreFind]
  simp only [find_rankr, hnewParent]
  exact hiterRoot

/-- A top-path node with a later non-root ancestor at the same level releases potential. -/
theorem nodePotential_find_lt_of_same_level_ancestor {r : Nat} (hr : 1 ≤ r)
    {s : UnionFind} {q : Fin s.size} {x y : Nat}
    (hxmem : x ∈ findNodes s q)
    (htop : alpha r (rankr r s x) = alpha r (rankr r s (s.rootD q)))
    (hy : s.parent y ≠ y) {k : Nat}
    (path : ParentPath s (s.parent x) y k)
    (hlevel : level r s x = level r s y) :
    nodePotential r (s.find q).1 x < nodePotential r s x := by
  let t := (s.find q).1
  have hx : s.parent x ≠ x := findNodes_mem_nonroot hxmem
  have htx : t.parent x ≠ x := by
    exact fun h => hx ((find_isRoot_iff s q x).1 h)
  have hnewParent : t.parent x = s.rootD q :=
    find_parent_eq_root_of_mem hxmem
  have hparentAlphaLe :
      alpha r (rankr r s (s.parent x)) ≤
        alpha r (rankr r s (s.rootD q)) := by
    have h := UnionFind.le_rank_root (self := s) (x := s.parent x)
    have hroot : s.rootD (s.parent x) = s.rootD q := by
      rw [UnionFind.rootD_parent]
      exact findNodes_rootD_eq hxmem
    rw [hroot] at h
    exact inverseAckermannAt_mono r (by simpa [rankr] using h)
  have holdSame :
      alpha r (rankr r s x) = alpha r (rankr r s (s.parent x)) := by
    have hmono := inverseAckermannAt_mono r (rankr_lt_parent (r := r) hx).le
    exact Nat.le_antisymm hmono (hparentAlphaLe.trans_eq htop.symm)
  have hnewSame :
      alpha r (rankr r t x) = alpha r (rankr r t (t.parent x)) := by
    dsimp [t]
    rw [find_rankr, hnewParent, find_rankr]
    exact htop
  rw [nodePotential_nonroot_same hx holdSame,
    nodePotential_nonroot_same htx hnewSame]
  have hk : level r s x ≤ level r t x := by
    have hpre := preLevel_mono_parent (find_rankr r s q x).symm
      (find_parent_rankr_mono r s q x)
    simpa [level] using Nat.add_le_add_right hpre 1
  have hklt : level r t x < alpha r (rankr r t x) :=
    level_lt_alpha_self htx hnewSame
  have hiOld : index r s x ≤ rankr r s x := index_le_rankr hr hx
  have hiNew : 1 ≤ index r t x := one_le_index htx
  have hiNewMass := index_le_level_mass hr htx hnewSame
  have hrankEq : rankr r t x = rankr r s x := by
    simp [t]
  rw [hrankEq] at hklt hiNewMass ⊢
  by_cases hkeq : level r s x = level r t x
  · have hiAdvance := index_succ_le_find_of_same_level_ancestor
      hxmem hy path hlevel hkeq
    apply lexPotential_lt
    · simpa only [find_rankr] using hklt
    · exact hiOld
    · exact hiNew
    · simpa only [find_rankr] using hiNewMass
    · have hiAdvanceT : index r s x + 1 ≤ index r t x := by
        simpa [t] using hiAdvance
      exact Or.inr ⟨hkeq, by omega⟩
  · apply lexPotential_lt
    · simpa only [find_rankr] using hklt
    · exact hiOld
    · exact hiNew
    · simpa only [find_rankr] using hiNewMass
    · exact Or.inl (lt_of_le_of_ne hk hkeq)

/-! ## The two exceptional classes on a compressed path -/

/-- Ackermann height of a node's positive rank offset. -/
noncomputable abbrev height (r : Nat) (s : UnionFind) (x : Nat) : Nat :=
  alpha r (rankr r s x)

/-- A path edge that strictly crosses an Ackermann height boundary. -/
def IsBoundary (r : Nat) (s : UnionFind) (x : Nat) : Prop :=
  height r s x ≠ height r s (s.parent x)

/-- A top-path node with no proper non-root ancestor at the same level. -/
def IsTopUnpleasant (r : Nat) (s : UnionFind) (x : Nat) : Prop :=
  height r s x = height r s (s.rootD x) ∧
    ∀ y k, ParentPath s (s.parent x) y k →
      s.parent y ≠ y → level r s x ≠ level r s y

noncomputable instance isBoundaryDecidable (r : Nat) (s : UnionFind) :
    DecidablePred (IsBoundary r s) :=
  Classical.decPred _

noncomputable instance isTopUnpleasantDecidable (r : Nat) (s : UnionFind) :
    DecidablePred (IsTopUnpleasant r s) :=
  Classical.decPred _

/-- Heights are monotone across every parent edge. -/
theorem height_le_parent {r : Nat} {s : UnionFind} {x : Nat}
    (hx : s.parent x ≠ x) :
    height r s x ≤ height r s (s.parent x) :=
  inverseAckermannAt_mono r (rankr_lt_parent (r := r) hx).le

/-- Boundary edges strictly raise Ackermann height. -/
theorem height_lt_parent_of_boundary {r : Nat} {s : UnionFind} {x : Nat}
    (hx : s.parent x ≠ x) (hboundary : IsBoundary r s x) :
    height r s x < height r s (s.parent x) :=
  lt_of_le_of_ne (height_le_parent hx) hboundary

/-- Every traversed node either releases potential or belongs to one exceptional class. -/
theorem findNode_releases_or_exceptional {r : Nat} (hr : 1 ≤ r)
    {s : UnionFind} {q : Fin s.size} {x : Nat}
    (hxmem : x ∈ findNodes s q) :
    nodePotential r (s.find q).1 x < nodePotential r s x ∨
      IsBoundary r s x ∨ IsTopUnpleasant r s x := by
  classical
  have hx : s.parent x ≠ x := findNodes_mem_nonroot hxmem
  by_cases hboundary : IsBoundary r s x
  · exact Or.inr (Or.inl hboundary)
  have holdSame : height r s x = height r s (s.parent x) :=
    not_ne_iff.mp hboundary
  have hrootEq : s.rootD x = s.rootD q := findNodes_rootD_eq hxmem
  have htopLe : height r s x ≤ height r s (s.rootD q) := by
    have h := UnionFind.le_rank_root (self := s) (x := x)
    rw [hrootEq] at h
    exact inverseAckermannAt_mono r (by simpa [rankr] using h)
  by_cases htop : height r s x = height r s (s.rootD q)
  · by_cases hunpleasant : IsTopUnpleasant r s x
    · exact Or.inr (Or.inr hunpleasant)
    · have hnotall :
          ¬∀ y k, ParentPath s (s.parent x) y k →
            s.parent y ≠ y → level r s x ≠ level r s y := by
        intro hall
        exact hunpleasant ⟨by simpa [hrootEq] using htop, hall⟩
      push Not at hnotall
      rcases hnotall with ⟨y, k, path, hy, hlevel⟩
      exact Or.inl <| nodePotential_find_lt_of_same_level_ancestor hr
        hxmem htop hy path hlevel
  · have htopLt : height r s x < height r s (s.rootD q) :=
      lt_of_le_of_ne htopLe htop
    have htx : (s.find q).1.parent x ≠ x := by
      exact fun h => hx ((find_isRoot_iff s q x).1 h)
    have hnewParent : (s.find q).1.parent x = s.rootD q :=
      find_parent_eq_root_of_mem hxmem
    have hnewNe :
        height r (s.find q).1 x ≠
          height r (s.find q).1 ((s.find q).1.parent x) := by
      intro heq
      apply htop
      change
        alpha r (rankr r (s.find q).1 x) =
          alpha r (rankr r (s.find q).1 ((s.find q).1.parent x)) at heq
      rw [find_rankr, hnewParent, find_rankr] at heq
      exact heq
    have holdPositive : 1 ≤ nodePotential r s x :=
      one_le_nodePotential hr hx holdSame
    rw [nodePotential_nonroot_ne htx hnewNe]
    exact Or.inl holdPositive

/-! ## Counting exceptional vertices -/

/-- An injective map into {lit}`range bound` bounds a finite set's cardinality. -/
theorem card_le_of_injOn_lt {t : Finset Nat} {f : Nat → Nat} {bound : Nat}
    (hinj : Set.InjOn f (t : Set Nat))
    (hbound : ∀ x ∈ t, f x < bound) :
    t.card ≤ bound := by
  classical
  have himage : t.image f ⊆ range bound := by
    intro y hy
    simp only [mem_image] at hy
    rcases hy with ⟨x, hx, rfl⟩
    simpa using hbound x hx
  calc
    t.card = (t.image f).card := (card_image_iff.mpr hinj).symm
    _ ≤ (range bound).card := card_le_card himage
    _ = bound := by simp

/-- A parent of a listed node has height at most the query root's height. -/
theorem parent_height_le_find_root {r : Nat} {s : UnionFind}
    {q : Fin s.size} {x : Nat} (hxmem : x ∈ findNodes s q) :
    height r s (s.parent x) ≤ height r s (s.rootD q) := by
  have h := UnionFind.le_rank_root (self := s) (x := s.parent x)
  have hroot : s.rootD (s.parent x) = s.rootD q := by
    rw [UnionFind.rootD_parent]
    exact findNodes_rootD_eq hxmem
  rw [hroot] at h
  exact inverseAckermannAt_mono r (by simpa [rankr] using h)

/-- Boundary-node heights are injective along one find chain. -/
theorem boundary_height_injOn {r : Nat} {s : UnionFind} (q : Fin s.size) :
    Set.InjOn (height r s)
      (((findNodes s q).toFinset.filter (IsBoundary r s) : Finset Nat) : Set Nat) := by
  intro u hu v hv heq
  simp only [coe_filter, List.mem_toFinset, Set.mem_setOf_eq] at hu hv
  rcases hu with ⟨huPath, huBoundary⟩
  rcases hv with ⟨hvPath, hvBoundary⟩
  apply findNodes_rank_injective huPath hvPath
  by_contra hrank
  rcases lt_or_gt_of_ne hrank with huv | hvu
  · rcases findNodes_ancestor_of_rank_lt huPath hvPath huv with ⟨k, path⟩
    have huNonroot := findNodes_mem_nonroot huPath
    have hstrict := height_lt_parent_of_boundary huNonroot huBoundary
    have htail : height r s (s.parent u) ≤ height r s v :=
      ParentPath.alpha_le_endpoint (r := r) path
    exact (Nat.ne_of_lt (hstrict.trans_le htail)) heq
  · rcases findNodes_ancestor_of_rank_lt hvPath huPath hvu with ⟨k, path⟩
    have hvNonroot := findNodes_mem_nonroot hvPath
    have hstrict := height_lt_parent_of_boundary hvNonroot hvBoundary
    have htail : height r s (s.parent v) ≤ height r s u :=
      ParentPath.alpha_le_endpoint (r := r) path
    exact (Nat.ne_of_lt (hstrict.trans_le htail)) heq.symm

/-- At most {lit}`alpha(root)` path nodes cross a height boundary. -/
theorem boundary_card_le_root_height {r : Nat} {s : UnionFind} (q : Fin s.size) :
    ((findNodes s q).toFinset.filter (IsBoundary r s)).card ≤
      height r s (s.rootD q) := by
  apply card_le_of_injOn_lt (boundary_height_injOn q)
  intro x hx
  simp only [mem_filter, List.mem_toFinset] at hx
  exact (height_lt_parent_of_boundary (findNodes_mem_nonroot hx.1) hx.2).trans_le
    (parent_height_le_find_root hx.1)

/-- Levels are injective among top-unpleasant nodes on one find chain. -/
theorem unpleasant_level_injOn {r : Nat} {s : UnionFind} (q : Fin s.size) :
    Set.InjOn (level r s)
      (((findNodes s q).toFinset.filter (IsTopUnpleasant r s) : Finset Nat) : Set Nat) := by
  intro u hu v hv heq
  simp only [coe_filter, List.mem_toFinset, Set.mem_setOf_eq] at hu hv
  rcases hu with ⟨huPath, huBad⟩
  rcases hv with ⟨hvPath, hvBad⟩
  apply findNodes_rank_injective huPath hvPath
  by_contra hrank
  rcases lt_or_gt_of_ne hrank with huv | hvu
  · rcases findNodes_ancestor_of_rank_lt huPath hvPath huv with ⟨k, path⟩
    exact (huBad.2 v k path (findNodes_mem_nonroot hvPath)) heq
  · rcases findNodes_ancestor_of_rank_lt hvPath huPath hvu with ⟨k, path⟩
    exact (hvBad.2 u k path (findNodes_mem_nonroot huPath)) heq.symm

/-- At most {lit}`alpha(root)` top-path nodes can be unpleasant. -/
theorem unpleasant_card_le_root_height {r : Nat} {s : UnionFind} (q : Fin s.size) :
    ((findNodes s q).toFinset.filter (IsTopUnpleasant r s)).card ≤
      height r s (s.rootD q) := by
  apply card_le_of_injOn_lt (unpleasant_level_injOn q)
  intro x hx
  simp only [mem_filter, List.mem_toFinset] at hx
  have hxNonroot := findNodes_mem_nonroot hx.1
  exact (level_lt_inverse_parent hxNonroot).trans_le
    (parent_height_le_find_root hx.1)

/-! ## Local amortized find bound -/

/-- The finite set of non-root vertices visited by a concrete find. -/
def pathSet (s : UnionFind) (q : Fin s.size) : Finset Nat :=
  (findNodes s q).toFinset

/-- Visited vertices whose potential strictly decreases. -/
noncomputable def releaseSet (r : Nat) (s : UnionFind) (q : Fin s.size) : Finset Nat :=
  (pathSet s q).filter
    (fun x => nodePotential r (s.find q).1 x < nodePotential r s x)

/-- Visited vertices that cross an Ackermann height boundary. -/
noncomputable def boundarySet (r : Nat) (s : UnionFind) (q : Fin s.size) : Finset Nat :=
  (pathSet s q).filter (IsBoundary r s)

/-- Visited top-path vertices that are unpleasant. -/
noncomputable def unpleasantSet (r : Nat) (s : UnionFind) (q : Fin s.size) : Finset Nat :=
  (pathSet s q).filter (IsTopUnpleasant r s)

/-- The visited set is covered by released, boundary, and unpleasant vertices. -/
theorem pathSet_subset_three_classes {r : Nat} (hr : 1 ≤ r)
    (s : UnionFind) (q : Fin s.size) :
    pathSet s q ⊆
      (releaseSet r s q ∪ boundarySet r s q) ∪ unpleasantSet r s q := by
  classical
  intro x hx
  have hxmem : x ∈ findNodes s q := by simpa [pathSet] using hx
  rcases findNode_releases_or_exceptional hr hxmem with hrelease | hboundary | hunpleasant
  · simp [releaseSet, boundarySet, unpleasantSet, pathSet, hxmem, hrelease]
  · simp [releaseSet, boundarySet, unpleasantSet, pathSet, hxmem, hboundary]
  · simp [releaseSet, boundarySet, unpleasantSet, pathSet, hxmem, hunpleasant]

/-- The path length is bounded by released vertices plus two root-height charges. -/
theorem findEdges_le_release_add_two_height {r : Nat} (hr : 1 ≤ r)
    (s : UnionFind) (q : Fin s.size) :
    Costed.findEdges s q ≤
      (releaseSet r s q).card + 2 * height r s (s.rootD q) := by
  classical
  have hcover := card_le_card (pathSet_subset_three_classes hr s q)
  have hunion₁ := card_union_le (releaseSet r s q) (boundarySet r s q)
  have hunion₂ := card_union_le
    (releaseSet r s q ∪ boundarySet r s q) (unpleasantSet r s q)
  have hboundary : (boundarySet r s q).card ≤ height r s (s.rootD q) := by
    simpa [boundarySet, pathSet] using boundary_card_le_root_height (r := r) q
  have hunpleasant : (unpleasantSet r s q).card ≤ height r s (s.rootD q) := by
    simpa [unpleasantSet, pathSet] using unpleasant_card_le_root_height (r := r) q
  have hpathCard : (pathSet s q).card = Costed.findEdges s q := by
    rw [pathSet, List.toFinset_card_of_nodup (findNodes_nodup s q)]
    exact findNodes_length s q
  omega

/-- Every released vertex pays one unit from the total potential drop. -/
theorem potential_find_add_release_card_le {r : Nat} (hr : 1 ≤ r)
    (s : UnionFind) (q : Fin s.size) :
    potential r (s.find q).1 + (releaseSet r s q).card ≤ potential r s := by
  classical
  let released := releaseSet r s q
  have hreleasedSubset : released ⊆ range s.size := by
    intro x hx
    have hxBoth : x ∈ pathSet s q ∧
        nodePotential r (s.find q).1 x < nodePotential r s x := by
      simpa [released, releaseSet] using hx
    have hxPath : x ∈ findNodes s q := by
      simpa [pathSet] using hxBoth.1
    simpa using findNodes_mem_lt hxPath
  have hfilter :
      (range s.size).filter (fun x => x ∈ released) = released := by
    ext x
    simp only [mem_filter, mem_range]
    constructor
    · exact fun h => h.2
    · intro hx
      exact ⟨by simpa using hreleasedSubset hx, hx⟩
  have hpoint : ∀ x ∈ range s.size,
      nodePotential r (s.find q).1 x + (if x ∈ released then 1 else 0) ≤
        nodePotential r s x := by
    intro x _hx
    by_cases hrelease : x ∈ released
    · have hlt : nodePotential r (s.find q).1 x < nodePotential r s x := by
        have hboth : x ∈ pathSet s q ∧
            nodePotential r (s.find q).1 x < nodePotential r s x := by
          simpa [released, releaseSet] using hrelease
        exact hboth.2
      simp only [if_pos hrelease]
      omega
    · simp only [if_neg hrelease, Nat.add_zero]
      exact nodePotential_find_le hr s q x
  have hsum := sum_le_sum hpoint
  simp only [sum_add_distrib, sum_boole, hfilter] at hsum
  unfold potential
  rw [UnionFind.find_size]
  exact hsum

/-- A concrete find has amortized cost below twice the root Ackermann height. -/
theorem find_amortized_le_root_height {r : Nat} (hr : 1 ≤ r)
    (s : UnionFind) (q : Fin s.size) :
    potential r (s.find q).1 + Costed.findEdges s q + 1 ≤
      potential r s + 2 * height r s (s.rootD q) + 1 := by
  have hcost := findEdges_le_release_add_two_height hr s q
  have hdrop := potential_find_add_release_card_le hr s q
  omega

/-- Reachable rank mass bounds the root's positive rank by the universe size. -/
theorem root_rankr_one_le_size {s : UnionFind} (budget : Costed.RankBudget s)
    (q : Fin s.size) : rankr 1 s (s.rootD q) ≤ s.size := by
  have hrootLt : s.rootD q < s.size := UnionFind.rootD_lt.2 q.2
  have hrank := rank_le_log2 budget.toRankMassCertificate hrootLt
  have hsize : s.size ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt q.2)
  have hlog : Nat.log2 s.size < s.size := by
    exact (Nat.log2_lt hsize).2 Nat.lt_two_pow_self
  simp only [rankr]
  omega

/-- The root Ackermann height is at most the universe inverse-Ackermann value. -/
theorem root_height_le_inverseAckermann {s : UnionFind}
    (budget : Costed.RankBudget s) (q : Fin s.size) :
    height 1 s (s.rootD q) ≤ inverseAckermann s.size := by
  exact inverseAckermannAt_mono 1 (root_rankr_one_le_size budget q)

/-- The concrete Batteries find satisfies the CLRS inverse-Ackermann amortized bound. -/
theorem costedFind_amortized_le {s : UnionFind}
    (budget : Costed.RankBudget s) (q : Fin s.size) :
    potential 1 (s.find q).1 + (Costed.costedFind s q).cost ≤
      potential 1 s + 2 * inverseAckermann s.size + 1 := by
  rw [Costed.costedFind_cost]
  have hlocal := find_amortized_le_root_height (r := 1) (by omega) s q
  have hroot := root_height_le_inverseAckermann budget q
  omega

/-! ## Amortized union and complete executions -/

/-- A concrete Batteries union has amortized charge at most {lit}`4 alpha(n) + 5`. -/
theorem costedUnion_amortized_le {s : UnionFind}
    (budget : Costed.RankBudget s) (x y : Fin s.size) :
    potential 1 (s.union x y) + (Costed.costedUnion s x y).cost ≤
      potential 1 s + 4 * inverseAckermann s.size + 5 := by
  unfold UnionFind.union
  generalize hfindx : s.find x = fx
  rcases fx with ⟨s₁, rx, ex⟩
  dsimp only
  have hy : (y : Nat) < s₁.size := by
    rw [ex]
    exact y.2
  let y₁ : Fin s₁.size := ⟨y, hy⟩
  let fy := s₁.find y₁
  let s₂ := fy.1
  let ry : Fin s₂.size := fy.2.1
  have ey : s₂.size = s₁.size := fy.2.2
  let rx₂ : Fin s₂.size := ⟨rx, by rw [ey]; exact rx.2⟩
  have b₁ : Costed.RankBudget s₁ := by
    simpa [hfindx] using budget.afterFind x
  have rxroot₁ : s₁.parent rx = rx := by
    have hreturned : (rx : Nat) = s.rootD x := by
      have h := UnionFind.find_root_2 s x
      rw [hfindx] at h
      exact h
    have hrootOld : s.parent rx = rx := by
      simpa [hreturned] using UnionFind.parent_rootD s x
    have h := Costed.find_preserves_root s x hrootOld
    rw [hfindx] at h
    exact h
  have rxroot₂ : s₂.parent rx₂ = rx₂ := by
    simpa [s₂, fy, rx₂] using Costed.find_preserves_root s₁ y₁ rxroot₁
  have ryroot₂ : s₂.parent ry = ry := by
    have hreturned : (ry : Nat) = s₁.rootD y₁ := by
      have h := UnionFind.find_root_2 s₁ y₁
      change (ry : Nat) = s₁.rootD y₁ at h
      exact h
    subst ry
    simpa [s₂, fy] using
      Costed.find_preserves_root s₁ y₁ (UnionFind.parent_rootD s₁ y₁)
  have hfind₁ :
      potential 1 s₁ + Costed.findEdges s x + 1 ≤
        potential 1 s + 2 * inverseAckermann s.size + 1 := by
    have h := costedFind_amortized_le budget x
    rw [Costed.costedFind_cost, hfindx] at h
    omega
  have hfind₂ :
      potential 1 s₂ + Costed.findEdges s₁ y₁ + 1 ≤
        potential 1 s₁ + 2 * inverseAckermann s.size + 1 := by
    have h := costedFind_amortized_le b₁ y₁
    rw [Costed.costedFind_cost] at h
    have halphaEq : inverseAckermann s₁.size = inverseAckermann s.size :=
      congrArg inverseAckermann ex
    rw [halphaEq] at h
    dsimp [s₂, fy]
    omega
  have hlink :
      potential 1 (s₂.link rx₂ ry ryroot₂) ≤ potential 1 s₂ + 2 :=
    potential_link_le_add_two (r := 1) (by omega) rxroot₂ ryroot₂
  have htotal :
      potential 1 (s₂.link rx₂ ry ryroot₂) +
          (Costed.findEdges s x + Costed.findEdges s₁ y₁ + 3) ≤
        potential 1 s + 4 * inverseAckermann s.size + 5 := by
    omega
  let secondFindCost :
      (fx : (s₁ : UnionFind) × { _root : Fin s₁.size // s₁.size = s.size }) → Nat :=
    fun fx => Costed.findEdges fx.1
      ⟨y, by rw [fx.2.2]; exact y.2⟩
  have hactual :
      Costed.findEdges (s.find x).1 (Costed.secondNodeAfterFind s x y) =
        secondFindCost (s.find x) := by
    dsimp [secondFindCost]
    apply congrArg (Costed.findEdges (s.find x).1)
    apply Fin.ext
    rfl
  have hrewrite :
      secondFindCost (s.find x) = secondFindCost ⟨s₁, ⟨rx, ex⟩⟩ :=
    congrArg secondFindCost hfindx
  have hcost : (Costed.costedUnion s x y).cost =
      Costed.findEdges s x + Costed.findEdges s₁ y₁ + 3 := by
    rw [Costed.costedUnion_cost, Costed.unionCost, hactual, hrewrite]
  rw [hcost]
  simpa [s₂, fy, ry, rx₂, y₁] using htotal

/-- Every costed machine step has a uniform {lit}`9 alpha(n)` amortized charge. -/
theorem step_amortized_le {n : Nat} (m : Costed.Machine n)
    (op : Costed.Operation n) :
    potential 1 (Costed.step m op).state.forest + (Costed.step m op).cost ≤
      potential 1 m.forest + 9 * inverseAckermann n := by
  cases op with
  | find x =>
      let xi := m.node x
      have h := costedFind_amortized_le m.budget xi
      have halpha : 1 ≤ inverseAckermann n := inverseAckermann_pos n
      have halphaEq : inverseAckermann m.forest.size = inverseAckermann n :=
        congrArg inverseAckermann m.size_eq
      rw [halphaEq, Costed.costedFind_cost] at h
      change potential 1 (m.forest.find xi).1 +
        (Costed.findEdges m.forest xi + 1) ≤
          potential 1 m.forest + 9 * inverseAckermann n
      omega
  | union x y =>
      let xi := m.node x
      let yi := m.node y
      have h := costedUnion_amortized_le m.budget xi yi
      have halpha : 1 ≤ inverseAckermann n := inverseAckermann_pos n
      have halphaEq : inverseAckermann m.forest.size = inverseAckermann n :=
        congrArg inverseAckermann m.size_eq
      rw [halphaEq, Costed.costedUnion_cost] at h
      change potential 1 (m.forest.union xi yi) + Costed.unionCost m.forest xi yi ≤
        potential 1 m.forest + 9 * inverseAckermann n
      omega

/-- Ackermann potential telescopes over every finite concrete execution. -/
theorem run_amortized_le {n : Nat} (m : Costed.Machine n)
    (ops : List (Costed.Operation n)) :
    potential 1 (Costed.run m ops).state.forest + (Costed.run m ops).cost ≤
      potential 1 m.forest + ops.length * (9 * inverseAckermann n) := by
  induction ops generalizing m with
  | nil => simp [Costed.run]
  | cons op ops ih =>
      let one := Costed.step m op
      have hone := step_amortized_le m op
      have hrest := ih one.state
      simp only [Costed.run, one] at hrest ⊢
      rw [List.length_cons, Nat.succ_mul]
      omega

/--
The final CLRS Chapter 21 bound for the real Batteries implementation:
initialization plus {lit}`m` finds/unions costs {lit}`O((m+n) alpha(n))`.
-/
theorem run_cost_le_inverseAckermann (n : Nat)
    (ops : List (Costed.Operation n)) :
    (Costed.run (Costed.Machine.initial n) ops).cost ≤
      9 * (ops.length + n) * inverseAckermann n := by
  have hamortized := run_amortized_le (Costed.Machine.initial n) ops
  have hinitial :
      potential 1 (Costed.Machine.initial n).forest = 2 * n := by
    simpa [Costed.Machine.initial, Nat.mul_comm] using potential_singleton 1 n
  rw [hinitial] at hamortized
  have halpha : 1 ≤ inverseAckermann n := inverseAckermann_pos n
  nlinarith

/-- With the standard {lit}`n <= m` assumption, the bound is {lit}`O(m alpha(n))`. -/
theorem run_cost_le_inverseAckermann_of_universe_le_ops (n : Nat)
    (ops : List (Costed.Operation n)) (hnm : n ≤ ops.length) :
    (Costed.run (Costed.Machine.initial n) ops).cost ≤
      18 * ops.length * inverseAckermann n := by
  exact (run_cost_le_inverseAckermann n ops).trans <| by
    have halpha : 1 ≤ inverseAckermann n := inverseAckermann_pos n
    nlinarith

end Ackermann
end Analysis
end Chapter21
end CLRS

import Mathlib.Computability.Ackermann
import CLRSLean.Chapter_17.Section_17_1_Amortized_Framework
import CLRSLean.Chapter_21.Section_21_3_Disjoint_Set_Forests

/-!
# CLRS Section 21.4 - Analysis of union by rank with path compression

This section isolates the quantitative certificates used by the CLRS analysis.
The executable forest already enforces strictly increasing ranks along every
nontrivial parent edge.  A rank-mass certificate supplies the complementary
fact that a node of rank {lit}`r` accounts for at least {lit}`2^r` elements.
Together they give the logarithmic rank and uncompressed-path bounds.

The final part defines an inverse-Ackermann function from Mathlib's Ackermann
function and packages the potential-method endpoint used by the path-
compression analysis.  The theorem is deliberately certificate based: a
low-level cost semantics can establish the per-operation amortized charge and
then reuse the total bound without repeating the telescoping argument.

Main results:

- Theorem {lit}`Analysis.parentPath_rank_bound`: a parent path has length at
  most the rank increase along it.
- Theorems {lit}`Analysis.rank_le_log2` and
  {lit}`Analysis.parentPath_length_le_log2`: rank and uncompressed depth are
  logarithmic under the CLRS rank-mass invariant.
- Theorems {lit}`Analysis.inverseAckermann_spec` and
  {lit}`Analysis.inverseAckermann_minimal`: the formal inverse-Ackermann
  threshold and its minimality property.
- Theorem {lit}`Analysis.total_cost_le_of_inverseAckermann_certificate`:
  per-operation inverse-Ackermann potential charges imply the aggregate bound.
-/

namespace CLRS
namespace Chapter21
namespace Analysis

open Batteries

/-! ## Rank and parent-path bounds -/

/-- A parent path carrying its exact number of nontrivial parent edges. -/
inductive ParentPath (s : UnionFind) : Nat → Nat → Nat → Prop where
  | refl (x : Nat) : ParentPath s x x 0
  | step {x y z k : Nat}
      (hparent : s.parent x = y) (hne : x ≠ y)
      (rest : ParentPath s y z k) :
      ParentPath s x z (k + 1)

/-- Ranks increase by at least the path length along every parent path. -/
theorem parentPath_rank_bound {s : UnionFind} {x z k : Nat}
    (hpath : ParentPath s x z k) :
    s.rank x + k ≤ s.rank z := by
  induction hpath with
  | refl x => simp
  | @step x y z k hparent hne rest ih =>
      have hxy : s.rank x < s.rank y := by
        have hparent_ne : s.parent x ≠ x := by
          rw [hparent]
          exact Ne.symm hne
        simpa [hparent] using s.rank_lt hparent_ne
      omega

/-- In particular, path length is bounded by the rank of its endpoint. -/
theorem parentPath_length_le_rank {s : UnionFind} {x z k : Nat}
    (hpath : ParentPath s x z k) :
    k ≤ s.rank z := by
  exact Nat.le_trans (Nat.le_add_left k (s.rank x))
    (by simpa [Nat.add_comm] using parentPath_rank_bound hpath)

/--
The CLRS rank-mass invariant: every allocated node of rank {lit}`r` is assigned
a mass of at least {lit}`2^r`, and no mass exceeds the forest size.
-/
structure RankMassCertificate (s : UnionFind) where
  mass : Nat → Nat
  pow_rank_le : ∀ {x}, x < s.size → 2 ^ s.rank x ≤ mass x
  mass_le_size : ∀ {x}, x < s.size → mass x ≤ s.size

/-- A rank-mass certificate implies the standard logarithmic rank bound. -/
theorem rank_le_log2 {s : UnionFind} (cert : RankMassCertificate s)
    {x : Nat} (hx : x < s.size) :
    s.rank x ≤ Nat.log2 s.size := by
  have hsize : s.size ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt hx)
  apply (Nat.le_log2 hsize).2
  exact Nat.le_trans (cert.pow_rank_le hx) (cert.mass_le_size hx)

/-- Parent paths ending at an allocated node have logarithmic length. -/
theorem parentPath_length_le_log2 {s : UnionFind}
    (cert : RankMassCertificate s) {x z k : Nat}
    (hpath : ParentPath s x z k) (hz : z < s.size) :
    k ≤ Nat.log2 s.size :=
  Nat.le_trans (parentPath_length_le_rank hpath) (rank_le_log2 cert hz)

/-! ## Inverse Ackermann threshold -/

private theorem exists_ackermann_above (n : Nat) :
    ∃ k, n < ack k 1 := by
  refine ⟨n + 1, ?_⟩
  exact Nat.lt_trans (Nat.lt_succ_self n) (lt_ack_left (n + 1) 1)

/-- A one-argument inverse-Ackermann threshold suitable for asymptotic charges. -/
noncomputable def inverseAckermann (n : Nat) : Nat :=
  Nat.find (exists_ackermann_above n)

/-- Ackermann at the selected level exceeds the input. -/
theorem inverseAckermann_spec (n : Nat) :
    n < ack (inverseAckermann n) 1 :=
  Nat.find_spec (exists_ackermann_above n)

/-- The selected inverse-Ackermann level is the least sufficient level. -/
theorem inverseAckermann_minimal {n k : Nat} (h : n < ack k 1) :
    inverseAckermann n ≤ k :=
  Nat.find_min' (exists_ackermann_above n) h

/-- A simple explicit upper bound, useful when only finiteness is needed. -/
theorem inverseAckermann_le_succ (n : Nat) :
    inverseAckermann n ≤ n + 1 :=
  inverseAckermann_minimal
    (Nat.lt_trans (Nat.lt_succ_self n) (lt_ack_left (n + 1) 1))

/-! ## Potential-method aggregate endpoint -/

/-- A finite integer-valued prefix bounded termwise by a constant is bounded by its length times it. -/
theorem prefixCostR_le_const (cost : Nat → Int) (steps : Nat) (bound : Int)
    (hbound : ∀ i, i < steps → cost i ≤ bound) :
    Chapter17.prefixCostR cost steps ≤ Int.ofNat steps * bound := by
  induction steps with
  | zero => simp [Chapter17.prefixCostR]
  | succ steps ih =>
      have ih' := ih (fun i hi => hbound i (Nat.lt_trans hi (Nat.lt_succ_self steps)))
      have hlast := hbound steps (Nat.lt_succ_self steps)
      calc
        Chapter17.prefixCostR cost (steps + 1) =
            Chapter17.prefixCostR cost steps + cost steps := by
              simp [Chapter17.prefixCostR]
        _ ≤ Int.ofNat steps * bound + bound := add_le_add ih' hlast
        _ = Int.ofNat (steps + 1) * bound := by
          change (steps : Int) * bound + bound =
            ((steps + 1 : Nat) : Int) * bound
          rw [Int.natCast_add_one]
          ring

/--
Potential-method certificate for the inverse-Ackermann analysis.  The missing
implementation-specific obligation is exactly {lit}`amortized_le`: each
concrete operation must expose an actual traversal cost and prove its
amortized charge is at most a constant multiple of α.
-/
structure InverseAckermannCertificate
    (tr : Chapter17.PotentialTrace)
    (steps universeSize constantFactor : Nat) : Prop where
  potential_endpoint : tr.potential 0 ≤ tr.potential steps
  amortized_le :
    ∀ i, i < steps →
      Chapter17.amortizedCost tr i ≤
        Int.ofNat (constantFactor * inverseAckermann universeSize)

/-- Certified inverse-Ackermann charges give the aggregate CLRS cost bound. -/
theorem total_cost_le_of_inverseAckermann_certificate
    (tr : Chapter17.PotentialTrace)
    (steps universeSize constantFactor : Nat)
    (cert : InverseAckermannCertificate tr steps universeSize constantFactor) :
    Chapter17.prefixCostR tr.actual steps ≤
      Int.ofNat (steps * (constantFactor * inverseAckermann universeSize)) := by
  calc
    Chapter17.prefixCostR tr.actual steps ≤
        Chapter17.prefixCostR (Chapter17.amortizedCost tr) steps :=
      Chapter17.potential_totalCost_le_totalAmortized tr steps
        cert.potential_endpoint
    _ ≤ Int.ofNat steps *
        Int.ofNat (constantFactor * inverseAckermann universeSize) :=
      prefixCostR_le_const _ _ _ cert.amortized_le
    _ = Int.ofNat (steps * (constantFactor * inverseAckermann universeSize)) := by
      simp

end Analysis
end Chapter21
end CLRS

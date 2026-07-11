import CLRSLean.Chapter_21.Section_21_4_Analysis

/-!
# CLRS Section 21.4 - Costed union-find execution

This module instruments the actual {lit}`Batteries.UnionFind` operations rather
than introducing a second union-find implementation.  A call to
{lit}`findEdges` follows the same parent recursion as Batteries
{lit}`findAux` and counts its nontrivial parent-edge traversals.  The costed
operations retain the exact Batteries result while exposing those traversals.

The proof-only rank budget assigns mass to roots.  Initialization assigns one
unit to every singleton, path compression leaves the budget unchanged, and a
link transfers the losing root's mass to the winning root.  Conservation of
total mass is the finite resource argument behind the logarithmic rank bound.

Main results:

- Theorem {lit}`findEdges_parentPath`: the counter is the exact parent-path
  length followed by the real find recursion.
- Definition {lit}`RankBudget.afterUnion`: every reachable Batteries union
  preserves enough conserved mass to justify its ranks.
- Theorem {lit}`run_refines_spec`: erasing a complete costed execution gives
  the abstract Section 21.1 operation semantics.
- Theorem {lit}`run_cost_le`: {lit}`m` operations cost at most
  {lit}`m * (2 * log2 n + 3)` in this traversal-and-link model.
-/

namespace CLRS
namespace Chapter21
namespace Analysis
namespace Costed

open Batteries
open Finset

/-! ## Traversal cost of the real Batteries find -/

/-- Number of nontrivial parent edges traversed by Batteries {lit}`findAux`. -/
def findEdges (s : UnionFind) (x : Fin s.size) : Nat :=
  let y := s.arr[x.1].parent
  if h : y = x then
    0
  else
    have := Nat.sub_lt_sub_left (s.lt_rankMax x) (s.rank'_lt _ _ h)
    findEdges s ⟨y, s.parent'_lt _ x.2⟩ + 1
termination_by s.rankMax - s.rank x

/-- A costed call retains exactly the state and representative returned by Batteries. -/
structure FindResultAt (s : UnionFind) (x : Fin s.size) where
  state : UnionFind
  root : Nat
  cost : Nat
  state_eq : state = (s.find x).1
  root_eq : root = (s.find x).2.1.1

/-- Instrument the real Batteries {lit}`find`; one unit also pays for the root inspection. -/
def costedFind (s : UnionFind) (x : Fin s.size) : FindResultAt s x where
  state := (s.find x).1
  root := (s.find x).2.1.1
  cost := findEdges s x + 1
  state_eq := rfl
  root_eq := rfl

@[simp]
theorem costedFind_state (s : UnionFind) (x : Fin s.size) :
    (costedFind s x).state = (s.find x).1 :=
  rfl

@[simp]
theorem costedFind_root (s : UnionFind) (x : Fin s.size) :
    (costedFind s x).root = s.rootD x := by
  exact UnionFind.find_root_2 s x

@[simp]
theorem costedFind_cost (s : UnionFind) (x : Fin s.size) :
    (costedFind s x).cost = findEdges s x + 1 :=
  rfl

/-- The traversal counter produces an exact parent path to the canonical root. -/
theorem findEdges_parentPath (s : UnionFind) (x : Fin s.size) :
    ParentPath s x (s.rootD x) (findEdges s x) := by
  rw [findEdges]
  split
  · rename_i h
    have hparent : s.parent x = x := by
      simpa [UnionFind.parent, UnionFind.parentD_eq x.2] using h
    rw [UnionFind.rootD_eq_self.2 hparent]
    exact ParentPath.refl x
  · rename_i h
    have hparent : s.parent x = s.arr[x.1].parent :=
      UnionFind.parentD_eq x.2
    have hne : (x : Nat) ≠ s.arr[x.1].parent := by
      exact fun h' => h h'.symm
    have hmeasure := Nat.sub_lt_sub_left (s.lt_rankMax x) (s.rank'_lt _ _ h)
    have hrest := findEdges_parentPath s ⟨s.arr[x.1].parent, s.parent'_lt _ x.2⟩
    rw [← UnionFind.rootD_parent s x]
    rw [hparent]
    exact ParentPath.step hparent hne hrest
termination_by s.rankMax - s.rank x

/-! ## A conserved rank-mass budget -/

/--
A proof-only mass assignment.  Every root has enough mass to pay for its rank,
and the total assigned mass never exceeds the number of allocated nodes.
-/
structure RankBudget (s : UnionFind) where
  mass : Nat → Nat
  root_pow_rank_le :
    ∀ {x}, x < s.size → s.parent x = x → 2 ^ s.rank x ≤ mass x
  total_mass_le : ∑ x ∈ range s.size, mass x ≤ s.size

/-- Any conserved root budget supplies the rank-mass certificate used by 21.4. -/
def RankBudget.toRankMassCertificate {s : UnionFind} (budget : RankBudget s) :
    RankMassCertificate s where
  mass x := budget.mass (s.rootD x)
  pow_rank_le := by
    intro x hx
    have hroot_lt : s.rootD x < s.size := UnionFind.rootD_lt.2 hx
    have hrank : s.rank x ≤ s.rank (s.rootD x) := UnionFind.le_rank_root
    exact (Nat.pow_le_pow_right Nat.zero_lt_two hrank).trans
      (budget.root_pow_rank_le hroot_lt (UnionFind.parent_rootD s x))
  mass_le_size := by
    intro x hx
    have hroot_mem : s.rootD x ∈ range s.size := by
      simp [UnionFind.rootD_lt.2 hx]
    calc
      budget.mass (s.rootD x) ≤ ∑ i ∈ range s.size, budget.mass i := by
        exact single_le_sum (fun _ _ => Nat.zero_le _) hroot_mem
      _ ≤ s.size := budget.total_mass_le

/-- Every node in a singleton forest has rank zero. -/
@[simp]
theorem singletonForest_rank (n i : Nat) :
    (Forest.singletonForest n).rank i = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [Forest.singletonForest] using ih

/-- Singleton initialization owns exactly one mass unit per node. -/
def singletonRankBudget (n : Nat) : RankBudget (Forest.singletonForest n) where
  mass := fun _ => 1
  root_pow_rank_le := by simp
  total_mass_le := by simp

/-- Path compression changes no rank. -/
@[simp]
theorem find_rank (s : UnionFind) (x : Fin s.size) (i : Nat) :
    (s.find x).1.rank i = s.rank i := by
  exact UnionFind.rankD_findAux

/-- Path compression preserves every conserved rank budget. -/
def RankBudget.afterFind {s : UnionFind} (budget : RankBudget s)
    (x : Fin s.size) : RankBudget (s.find x).1 where
  mass := budget.mass
  root_pow_rank_le := by
    intro i hi hroot
    have hold_rootD : s.rootD i = i := by
      rw [← UnionFind.find_root_1 s x i]
      exact UnionFind.rootD_eq_self.2 hroot
    have hold_root : s.parent i = i := UnionFind.rootD_eq_self.1 hold_rootD
    simpa using budget.root_pow_rank_le (by simpa using hi) hold_root
  total_mass_le := by
    simpa using budget.total_mass_le

/-- A costed find from a budgeted state has logarithmic concrete cost. -/
theorem costedFind_cost_le_log2 {s : UnionFind} (budget : RankBudget s)
    (x : Fin s.size) :
    (costedFind s x).cost ≤ Nat.log2 s.size + 1 := by
  rw [costedFind_cost]
  exact Nat.add_le_add_right
    (parentPath_length_le_log2 budget.toRankMassCertificate
      (findEdges_parentPath s x) (UnionFind.rootD_lt.2 x.2)) 1

/-! ## Mass transfer for union-by-rank links -/

/-- Move the losing root's proof mass to the winning root. -/
def transferMass (mass : Nat → Nat) (winner loser : Nat) : Nat → Nat :=
  fun i => if i = winner then mass winner + mass loser
    else if i = loser then 0 else mass i

@[simp]
theorem transferMass_winner {mass : Nat → Nat} {winner loser : Nat} :
    transferMass mass winner loser winner = mass winner + mass loser := by
  simp [transferMass]

@[simp]
theorem transferMass_loser {mass : Nat → Nat} {winner loser : Nat}
    (hne : loser ≠ winner) :
    transferMass mass winner loser loser = 0 := by
  simp [transferMass, hne]

/-- Transferring mass between two distinct in-range nodes preserves the total. -/
theorem sum_transferMass_range {mass : Nat → Nat} {n winner loser : Nat}
    (hwinner : winner < n) (hloser : loser < n) (hne : winner ≠ loser) :
    ∑ i ∈ range n, transferMass mass winner loser i =
      ∑ i ∈ range n, mass i := by
  classical
  let s := range n
  let rest := (s.erase winner).erase loser
  have hw : winner ∈ range n := by simpa using hwinner
  have hl : loser ∈ (range n).erase winner := by
    simp [hloser, hne.symm]
  have hrest :
      ∑ i ∈ rest, transferMass mass winner loser i =
        ∑ i ∈ rest, mass i := by
    apply sum_congr rfl
    intro i hi
    have hiw : i ≠ winner := by
      exact fun h => by subst i; simp [rest, s] at hi
    have hil : i ≠ loser := by
      exact fun h => by subst i; simp [rest, s] at hi
    simp [transferMass, hiw, hil]
  have hleft :
      ∑ i ∈ range n, transferMass mass winner loser i =
        transferMass mass winner loser winner +
          (transferMass mass winner loser loser +
            ∑ i ∈ rest, transferMass mass winner loser i) := by
    calc
      ∑ i ∈ range n, transferMass mass winner loser i =
          transferMass mass winner loser winner +
            ∑ i ∈ (range n).erase winner,
              transferMass mass winner loser i :=
        ((range n).add_sum_erase _ hw).symm
      _ = transferMass mass winner loser winner +
          (transferMass mass winner loser loser +
            ∑ i ∈ rest, transferMass mass winner loser i) := by
        rw [show rest = ((range n).erase winner).erase loser by rfl]
        rw [((range n).erase winner).add_sum_erase _ hl]
  have hright :
      ∑ i ∈ range n, mass i =
        mass winner + (mass loser + ∑ i ∈ rest, mass i) := by
    calc
      ∑ i ∈ range n, mass i =
          mass winner + ∑ i ∈ (range n).erase winner, mass i :=
        ((range n).add_sum_erase _ hw).symm
      _ = mass winner + (mass loser + ∑ i ∈ rest, mass i) := by
        rw [show rest = ((range n).erase winner).erase loser by rfl]
        rw [((range n).erase winner).add_sum_erase _ hl]
  rw [hleft, hright, transferMass_winner,
    transferMass_loser hne.symm, zero_add, hrest, Nat.add_assoc]

/-- Exact rank effect of the Batteries link primitive. -/
theorem link_rank (s : UnionFind) (x y : Fin s.size)
    (yroot : s.parent y = y) (i : Nat) :
    (s.link x y yroot).rank i =
      if x.1 = y.1 then s.rank i
      else if s.rank y < s.rank x then s.rank i
      else if i = y.1 ∧ s.rank x = s.rank y then s.rank y + 1
      else s.rank i := by
  simp only [UnionFind.link, UnionFind.rank, UnionFind.linkAux]
  split <;> rename_i hxy
  · rfl
  · split <;> rename_i hrank
    · rw [if_pos (by simpa [UnionFind.rankD_eq] using hrank)]
      simp only [UnionFind.rankD_set]
      split <;> rename_i hi
      · subst i
        simp [UnionFind.rankD_eq]
      · rfl
    · have hrankD :
          ¬UnionFind.rankD s.arr y < UnionFind.rankD s.arr x := by
        simpa [UnionFind.rankD_eq] using hrank
      simp only [if_neg hrankD]
      split <;> rename_i heq
      · by_cases hi : i = y.1
        · subst i
          simp [UnionFind.rankD_eq, heq]
        · split <;> rename_i hxi
          · exact (hi hxi.1).elim
          · rw [UnionFind.rankD_set]
            rw [if_neg (fun h : y.1 = i => hi h.symm)]
            rw [UnionFind.rankD_set]
            split <;> rename_i hxi'
            · subst i
              rw [UnionFind.rankD_eq x.2]
            · rfl
      · have hcond :
            ¬(i = y.1 ∧
              UnionFind.rankD s.arr x = UnionFind.rankD s.arr y) := by
          intro h
          exact heq (by simpa [UnionFind.rankD_eq] using h.2)
        simp only [if_neg hcond]
        simp only [UnionFind.rankD_set]
        split <;> rename_i hxi
        · subst i
          rw [UnionFind.rankD_eq x.2]
        · rfl

/-- Linking two roots preserves the conserved budget. -/
def RankBudget.afterLink {s : UnionFind} (budget : RankBudget s)
    (x y : Fin s.size) (xroot : s.parent x = x)
    (yroot : s.parent y = y) : RankBudget (s.link x y yroot) := by
  classical
  by_cases hxy : x.1 = y.1
  · have hfin : x = y := Fin.ext hxy
    subst y
    refine
      { mass := budget.mass
        root_pow_rank_le := ?_
        total_mass_le := ?_ }
    · intro i hi hroot
      simpa [UnionFind.link, UnionFind.linkAux] using
        budget.root_pow_rank_le (by simpa [UnionFind.link, UnionFind.linkAux] using hi)
          (by simpa [UnionFind.link, UnionFind.linkAux] using hroot)
    · simpa [UnionFind.link, UnionFind.linkAux] using budget.total_mass_le
  · by_cases hrank : s.rank y < s.rank x
    · refine
        { mass := transferMass budget.mass x y
          root_pow_rank_le := ?_
          total_mass_le := ?_ }
      · intro i hi hroot
        have hi_old : i < s.size := by
          simpa [UnionFind.link, UnionFind.size] using hi
        by_cases hiy : i = y.1
        · subst i
          have hparent := UnionFind.parent_link (self := s) (x := x) (y := y) yroot
            (i := (y : Nat))
          rw [hparent] at hroot
          simp only [if_neg hxy, if_pos hrank] at hroot
          exact (hxy hroot).elim
        · have hroot_old : s.parent i = i := by
            have hparent := UnionFind.parent_link (self := s) (x := x) (y := y) yroot
              (i := i)
            rw [hparent] at hroot
            simp only [if_neg hxy, if_pos hrank,
              if_neg (fun h : y.1 = i => hiy h.symm)] at hroot
            exact hroot
          by_cases hix : i = x.1
          · subst i
            have hpow := budget.root_pow_rank_le x.2 xroot
            rw [link_rank s x y yroot]
            simp [hxy, hrank, transferMass]
            exact Nat.le_add_right_of_le hpow
          · rw [link_rank s x y yroot]
            simp only [if_neg hxy, if_pos hrank]
            simpa [transferMass, hix, hiy] using
              budget.root_pow_rank_le hi_old hroot_old
      · have hsize : (s.link x y yroot).size = s.size := by
          simp [UnionFind.link, UnionFind.size]
        rw [hsize]
        rw [sum_transferMass_range x.2 y.2 hxy]
        exact budget.total_mass_le
    · refine
        { mass := transferMass budget.mass y x
          root_pow_rank_le := ?_
          total_mass_le := ?_ }
      · intro i hi hroot
        have hi_old : i < s.size := by
          simpa [UnionFind.link, UnionFind.size] using hi
        by_cases hix : i = x.1
        · subst i
          have hparent := UnionFind.parent_link (self := s) (x := x) (y := y) yroot
            (i := (x : Nat))
          rw [hparent] at hroot
          simp only [if_neg hxy, if_neg hrank] at hroot
          exact (hxy hroot.symm).elim
        · have hroot_old : s.parent i = i := by
            have hparent := UnionFind.parent_link (self := s) (x := x) (y := y) yroot
              (i := i)
            rw [hparent] at hroot
            simp only [if_neg hxy, if_neg hrank,
              if_neg (fun h : x.1 = i => hix h.symm)] at hroot
            exact hroot
          by_cases hiy : i = y.1
          · subst i
            have hxpow := budget.root_pow_rank_le x.2 xroot
            have hypow := budget.root_pow_rank_le y.2 yroot
            by_cases heq : s.rank x = s.rank y
            · rw [link_rank s x y yroot]
              simp only [if_neg hxy, if_neg hrank]
              simp only [transferMass_winner]
              simpa [heq, pow_succ, Nat.mul_two] using
                Nat.add_le_add hypow hxpow
            · rw [link_rank s x y yroot]
              simp only [if_neg hxy, if_neg hrank]
              simp only [transferMass_winner]
              simp only [heq, and_false, ↓reduceIte]
              exact Nat.le_add_right_of_le hypow
          · rw [link_rank s x y yroot]
            simp only [if_neg hxy, if_neg hrank,
              if_neg (show ¬(i = y.1 ∧ s.rank x = s.rank y) by simp [hiy])]
            simpa [transferMass, hix, hiy] using
              budget.root_pow_rank_le hi_old hroot_old
      · have hsize : (s.link x y yroot).size = s.size := by
          simp [UnionFind.link, UnionFind.size]
        rw [hsize]
        rw [sum_transferMass_range y.2 x.2 (Ne.symm hxy)]
        exact budget.total_mass_le

/-- A root remains a root when another path is compressed. -/
theorem find_preserves_root (s : UnionFind) (x : Fin s.size) {r : Nat}
    (hroot : s.parent r = r) :
    (s.find x).1.parent r = r := by
  apply UnionFind.rootD_eq_self.1
  rw [UnionFind.find_root_1]
  exact UnionFind.rootD_eq_self.2 hroot

/-- The two finds and final link used by Batteries {lit}`union` preserve the budget. -/
def RankBudget.afterUnion {s : UnionFind} (budget : RankBudget s)
    (x y : Fin s.size) : RankBudget (s.union x y) := by
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
  have b₁ : RankBudget s₁ := by
    simpa [hfindx] using budget.afterFind x
  have b₂ : RankBudget s₂ := by
    simpa [s₂, fy] using b₁.afterFind y₁
  have rxroot₁ : s₁.parent rx = rx := by
    have hreturned : (rx : Nat) = s.rootD x := by
      have h := UnionFind.find_root_2 s x
      rw [hfindx] at h
      exact h
    have hroot_old : s.parent rx = rx := by
      simpa [hreturned] using UnionFind.parent_rootD s x
    have h := find_preserves_root s x hroot_old
    rw [hfindx] at h
    exact h
  have rxroot₂ : s₂.parent rx₂ = rx₂ := by
    simpa [s₂, fy, rx₂] using find_preserves_root s₁ y₁ rxroot₁
  have ryroot₂ : s₂.parent ry = ry := by
    have hreturned : (ry : Nat) = s₁.rootD y₁ := by
      have h := UnionFind.find_root_2 s₁ y₁
      change (ry : Nat) = s₁.rootD y₁ at h
      exact h
    subst ry
    simpa [s₂, fy] using
      find_preserves_root s₁ y₁ (UnionFind.parent_rootD s₁ y₁)
  simpa [s₂, fy, ry, rx₂, y₁] using
    b₂.afterLink rx₂ ry rxroot₂ ryroot₂

/-! ## Costed union and fixed-universe executions -/

/-- Cast the second union argument across the first find's size equality. -/
def secondNodeAfterFind (s : UnionFind) (x y : Fin s.size) :
    Fin (s.find x).1.size :=
  ⟨y, by simp⟩

/-- Concrete cost of the two Batteries finds plus the final constant-time link. -/
def unionCost (s : UnionFind) (x y : Fin s.size) : Nat :=
  findEdges s x + findEdges (s.find x).1 (secondNodeAfterFind s x y) + 3

/-- A costed union retains exactly the state returned by Batteries. -/
structure UnionResult (s : UnionFind) (x y : Fin s.size) where
  state : UnionFind
  cost : Nat
  state_eq : state = s.union x y

/-- Instrument the real Batteries {lit}`union`. -/
def costedUnion (s : UnionFind) (x y : Fin s.size) : UnionResult s x y where
  state := s.union x y
  cost := unionCost s x y
  state_eq := rfl

@[simp]
theorem costedUnion_state (s : UnionFind) (x y : Fin s.size) :
    (costedUnion s x y).state = s.union x y :=
  rfl

@[simp]
theorem costedUnion_cost (s : UnionFind) (x y : Fin s.size) :
    (costedUnion s x y).cost = unionCost s x y :=
  rfl

/-- A concrete Batteries union costs at most two logarithmic finds and one link. -/
theorem costedUnion_cost_le_log2 {s : UnionFind} (budget : RankBudget s)
    (x y : Fin s.size) :
    (costedUnion s x y).cost ≤ 2 * Nat.log2 s.size + 3 := by
  have hfirst : findEdges s x ≤ Nat.log2 s.size :=
    parentPath_length_le_log2 budget.toRankMassCertificate
      (findEdges_parentPath s x) (UnionFind.rootD_lt.2 x.2)
  have hsecond :
      findEdges (s.find x).1 (secondNodeAfterFind s x y) ≤
        Nat.log2 (s.find x).1.size :=
    parentPath_length_le_log2 (budget.afterFind x).toRankMassCertificate
      (findEdges_parentPath (s.find x).1 (secondNodeAfterFind s x y))
      (UnionFind.rootD_lt.2 (secondNodeAfterFind s x y).2)
  rw [costedUnion_cost, unionCost]
  have hsize : (s.find x).1.size = s.size := UnionFind.find_size s x
  rw [hsize] at hsecond
  omega

/-- A forest whose executable size is fixed by the operation universe. -/
structure SizedForest (n : Nat) where
  forest : UnionFind
  size_eq : forest.size = n

namespace SizedForest

/-- Cast a universe index to the current executable forest. -/
def node {n : Nat} (s : SizedForest n) (x : Fin n) : Fin s.forest.size :=
  Fin.cast s.size_eq.symm x

@[simp]
theorem node_val {n : Nat} (s : SizedForest n) (x : Fin n) :
    (s.node x : Nat) = x := by
  simp [node]

/-- Forget proof-only budgets while retaining the executable state. -/
def find {n : Nat} (s : SizedForest n) (x : Fin n) : SizedForest n where
  forest := (s.forest.find (s.node x)).1
  size_eq := by simp [s.size_eq]

/-- Plain execution of the real Batteries union. -/
def union {n : Nat} (s : SizedForest n) (x y : Fin n) : SizedForest n where
  forest := s.forest.union (s.node x) (s.node y)
  size_eq := by simp [Forest.union_size, s.size_eq]

end SizedForest

/-- A reachable executable state together with its conserved rank budget. -/
structure Machine (n : Nat) where
  forest : UnionFind
  size_eq : forest.size = n
  budget : RankBudget forest

namespace Machine

/-- The initialized costed machine. -/
def initial (n : Nat) : Machine n where
  forest := Forest.singletonForest n
  size_eq := Forest.singletonForest_size n
  budget := singletonRankBudget n

/-- Forget proof-only state. -/
def erase {n : Nat} (m : Machine n) : SizedForest n where
  forest := m.forest
  size_eq := m.size_eq

/-- Cast a universe index to the current executable forest. -/
def node {n : Nat} (m : Machine n) (x : Fin n) : Fin m.forest.size :=
  Fin.cast m.size_eq.symm x

end Machine

/-- Fixed-universe operations used by the costed execution. -/
inductive Operation (n : Nat) where
  | find (x : Fin n)
  | union (x y : Fin n)
deriving Repr

/-- Forget cost-level indexing and interpret an operation in the abstract 21.1 specification. -/
def Operation.toSpec {n : Nat} : Operation n → Chapter21.Operation Nat
  | .find x => .find x
  | .union x y => .union x y

/-- One costed operation and its next certified state. -/
structure StepResult (n : Nat) where
  state : Machine n
  cost : Nat

/-- Plain Batteries execution, with all cost and ghost data erased. -/
def plainStep {n : Nat} (s : SizedForest n) : Operation n → SizedForest n
  | .find x => s.find x
  | .union x y => s.union x y

/-- Execute one real Batteries operation while retaining its concrete cost and budget. -/
def step {n : Nat} (m : Machine n) : Operation n → StepResult n
  | .find x =>
      let xi := m.node x
      { state :=
          { forest := (m.forest.find xi).1
            size_eq := by simp [m.size_eq]
            budget := m.budget.afterFind xi }
        cost := findEdges m.forest xi + 1 }
  | .union x y =>
      let xi := m.node x
      let yi := m.node y
      { state :=
          { forest := m.forest.union xi yi
            size_eq := by simp [Forest.union_size, m.size_eq]
            budget := m.budget.afterUnion xi yi }
        cost := unionCost m.forest xi yi }

/-- Erasing a costed step gives exactly the corresponding Batteries operation. -/
theorem step_erase {n : Nat} (m : Machine n) (op : Operation n) :
    (step m op).state.erase = plainStep m.erase op := by
  cases op <;> rfl

/-- Every individual operation obeys a uniform logarithmic bound. -/
theorem step_cost_le {n : Nat} (m : Machine n) (op : Operation n) :
    (step m op).cost ≤ 2 * Nat.log2 n + 3 := by
  cases op with
  | find x =>
      have h := costedFind_cost_le_log2 m.budget (m.node x)
      simp only [step, costedFind_cost] at h ⊢
      rw [m.size_eq] at h
      omega
  | union x y =>
      have h := costedUnion_cost_le_log2 m.budget (m.node x) (m.node y)
      simpa [step, costedUnion_cost, m.size_eq] using h

/-- Result of a finite costed execution. -/
structure RunResult (n : Nat) where
  state : Machine n
  cost : Nat

/-- Execute a list of operations and accumulate their concrete costs. -/
def run {n : Nat} (m : Machine n) : List (Operation n) → RunResult n
  | [] => ⟨m, 0⟩
  | op :: ops =>
      let one := step m op
      let rest := run one.state ops
      ⟨rest.state, one.cost + rest.cost⟩

/-- Plain repeated Batteries execution. -/
def plainRun {n : Nat} (s : SizedForest n) : List (Operation n) → SizedForest n
  | [] => s
  | op :: ops => plainRun (plainStep s op) ops

/-- Erasing an entire costed run gives exactly repeated Batteries execution. -/
theorem run_erase {n : Nat} (m : Machine n) (ops : List (Operation n)) :
    (run m ops).state.erase = plainRun m.erase ops := by
  induction ops generalizing m with
  | nil => rfl
  | cons op ops ih =>
      simp only [run, plainRun]
      rw [ih]
      rw [step_erase]

/-- One plain executable step refines the corresponding abstract partition step. -/
theorem plainStep_refines {n : Nat} (s : SizedForest n) (P : Partition Nat)
    (hrep : ∀ a b, (Forest.partition s.forest).sameSet a b ↔ P.sameSet a b)
    (op : Operation n) (a b : Nat) :
    (Forest.partition (plainStep s op).forest).sameSet a b ↔
      (stepSpec P op.toSpec).sameSet a b := by
  cases op with
  | find x =>
      change
        (Forest.partition (s.forest.find (s.node x)).1).sameSet a b ↔
          P.sameSet a b
      rw [Forest.find_preserves_sameSet]
      exact hrep a b
  | union x y =>
      change
        (Forest.partition (s.forest.union (s.node x) (s.node y))).sameSet a b ↔
          (P.merge x y).sameSet a b
      rw [Forest.union_sameSet_iff, Partition.merge_sameSet_iff]
      simp only [SizedForest.node_val]
      rw [hrep a b, hrep a x, hrep y b, hrep a y, hrep x b]

/-- Repeated plain Batteries execution refines the complete abstract operation trace. -/
theorem plainRun_refines {n : Nat} (s : SizedForest n) (P : Partition Nat)
    (hrep : ∀ a b, (Forest.partition s.forest).sameSet a b ↔ P.sameSet a b)
    (ops : List (Operation n)) (a b : Nat) :
    (Forest.partition (plainRun s ops).forest).sameSet a b ↔
      (runSpec P (ops.map Operation.toSpec)).sameSet a b := by
  induction ops generalizing s P with
  | nil => simpa [plainRun, runSpec] using hrep a b
  | cons op ops ih =>
      simp only [plainRun, List.map_cons, runSpec]
      exact ih (plainStep s op) (stepSpec P op.toSpec)
        (plainStep_refines s P hrep op)

/-- The initialized costed run has exactly the abstract Section 21.1 semantics. -/
theorem run_refines_spec {n : Nat} (ops : List (Operation n)) (a b : Nat) :
    (Forest.partition (run (Machine.initial n) ops).state.forest).sameSet a b ↔
      (runSpec (Partition.discrete : Partition Nat)
        (ops.map Operation.toSpec)).sameSet a b := by
  have herase := run_erase (Machine.initial n) ops
  have hforest := congrArg SizedForest.forest herase
  have hforest' :
      (run (Machine.initial n) ops).state.forest =
        (plainRun (Machine.initial n).erase ops).forest := by
    simpa [Machine.erase] using hforest
  rw [hforest']
  apply plainRun_refines
  intro u v
  exact Forest.singletonForest_refines_discrete n u v

/-- Every state reachable by the operation machine retains the logarithmic rank bound. -/
theorem run_rank_le_log2 {n : Nat} (m : Machine n) (ops : List (Operation n))
    {x : Nat} (hx : x < (run m ops).state.forest.size) :
    (run m ops).state.forest.rank x ≤ Nat.log2 n := by
  have h := rank_le_log2 (run m ops).state.budget.toRankMassCertificate hx
  simpa [(run m ops).state.size_eq] using h

/-- A sequence of {lit}`m` real operations has the concrete {lit}`O(m log n)` bound. -/
theorem run_cost_le {n : Nat} (m : Machine n) (ops : List (Operation n)) :
    (run m ops).cost ≤ ops.length * (2 * Nat.log2 n + 3) := by
  induction ops generalizing m with
  | nil => simp [run]
  | cons op ops ih =>
      simp only [run, List.length_cons]
      have hone := step_cost_le m op
      have hrest := ih (step m op).state
      calc
        (step m op).cost + (run (step m op).state ops).cost ≤
            (2 * Nat.log2 n + 3) +
              ops.length * (2 * Nat.log2 n + 3) :=
          Nat.add_le_add hone hrest
        _ = (ops.length + 1) * (2 * Nat.log2 n + 3) := by
          rw [Nat.add_mul]
          simp [Nat.add_comm]

end Costed
end Analysis
end Chapter21
end CLRS

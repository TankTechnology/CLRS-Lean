import Mathlib

/-!
# CLRS Section 21.3+21.4 - Forest Representation of Disjoint Sets

Rooted-tree forest with union by rank and path compression.
-/

namespace CLRS
namespace Chapter21

structure DisjointSetForest (n : Nat) where
  parent : Fin n → Fin n
  rank : Fin n → Nat
  size : Fin n → Nat

namespace DisjointSetForest

variable {n : Nat}

def isRoot (f : DisjointSetForest n) (x : Fin n) : Prop := f.parent x = x

def findSetFuel (f : DisjointSetForest n) : Nat → Fin n → Fin n
  | 0, x => x
  | k+1, x =>
    let p := f.parent x
    if p = x then x else findSetFuel f k p

def findSet (f : DisjointSetForest n) (x : Fin n) : Fin n := findSetFuel f n x

theorem findSetFuel_root (f : DisjointSetForest n) (k : Nat) (x : Fin n)
    (hx : f.parent x = x) : findSetFuel f k x = x := by
  induction' k with k ih
  · rfl
  · unfold findSetFuel
    simpa [hx] using ih

theorem findSet_isRoot (f : DisjointSetForest n) (x : Fin n) (hx : f.isRoot x) :
    f.findSet x = x :=
  findSetFuel_root f n x hx

def makeSet (f : DisjointSetForest n) (x : Fin n) : DisjointSetForest n :=
  { parent := λ y => if y = x then x else f.parent y
    rank := λ y => if y = x then 0 else f.rank y
    size := λ y => if y = x then 1 else f.size y
  }

theorem makeSet_isRoot (f : DisjointSetForest n) (x : Fin n) :
    (f.makeSet x).isRoot x := by
  unfold makeSet isRoot; simp

theorem makeSet_size_ge_rank_pow (f : DisjointSetForest n) (x : Fin n) :
    (f.makeSet x).size x ≥ 2 ^ (f.makeSet x).rank x := by
  unfold makeSet; simp

def union (f : DisjointSetForest n) (x y : Fin n) : DisjointSetForest n :=
  let rx := f.findSet x
  let ry := f.findSet y
  if rx = ry then f
  else if f.rank rx < f.rank ry then
    { parent := λ z => if z = rx then ry else f.parent z
      rank := f.rank
      size := λ z =>
        if z = ry then f.size ry + f.size rx else if z = rx then 0 else f.size z }
  else if f.rank ry < f.rank rx then
    { parent := λ z => if z = ry then rx else f.parent z
      rank := f.rank
      size := λ z =>
        if z = rx then f.size rx + f.size ry else if z = ry then 0 else f.size z }
  else
    { parent := λ z => if z = rx then ry else f.parent z
      rank := λ z => if z = ry then f.rank ry + 1 else f.rank z
      size := λ z =>
        if z = ry then f.size ry + f.size rx else if z = rx then 0 else f.size z }

private lemma sum_ge_pow_succ (a b r : Nat) (ha : a ≥ 2 ^ r) (hb : b ≥ 2 ^ r) :
    a + b ≥ 2 ^ (r + 1) := by
  have h_double : 2 ^ r + 2 ^ r = 2 ^ (r + 1) := by ring
  omega

theorem union_preserves_rank_size (f : DisjointSetForest n) (x y : Fin n)
    (hx_root : f.isRoot x) (hy_root : f.isRoot y)
    (h_size_x : f.size x ≥ 2 ^ f.rank x)
    (h_size_y : f.size y ≥ 2 ^ f.rank y) (h_ne : x ≠ y) :
    let f' := f.union x y
    let new_root := if f.rank x < f.rank y then y
                    else if f.rank y < f.rank x then x
                    else y
    f'.size new_root ≥ 2 ^ f'.rank new_root := by
  have hx_fs : f.findSet x = x := findSet_isRoot f x hx_root
  have hy_fs : f.findSet y = y := findSet_isRoot f y hy_root
  intro f' new_root
  unfold f' union new_root
  simp [hx_fs, hy_fs, h_ne]
  by_cases hlt : f.rank x < f.rank y
  · simp [hlt]
    -- Goal: f.size y + f.size x ≥ 2 ^ f.rank y
    rw [Nat.add_comm (f.size y) (f.size x)]
    omega
  · simp [hlt]
    by_cases hgt : f.rank y < f.rank x
    · simp [hgt]
      -- Goal: f.size x + f.size y ≥ 2 ^ f.rank x
      omega
    · simp [hgt]
      have h_eq_rank : f.rank x = f.rank y := by omega
      -- Goal: f.size y + f.size x ≥ 2 ^ (f.rank y + 1)
      -- Using sum_ge_pow_succ with h_size_y and h_size_x
      have hx' : f.size x ≥ 2 ^ f.rank y := by rwa [← h_eq_rank]
      apply sum_ge_pow_succ (f.size y) (f.size x) (f.rank y) h_size_y hx'

theorem rank_log_bound_of_size_ge_pow (size_val rank_val : Nat)
    (h_size_ge : size_val ≥ 2 ^ rank_val) (h_size_le_n : size_val ≤ n) :
    rank_val ≤ Nat.log 2 n := by
  have h_pow_le_n : 2 ^ rank_val ≤ n := Nat.le_trans h_size_ge h_size_le_n
  by_cases hn0 : n = 0
  · subst n
    have hone : 1 ≤ 2 ^ rank_val := by
      calc
        1 = 2 ^ 0 := by norm_num
        _ ≤ 2 ^ rank_val := Nat.pow_le_pow_right (by norm_num) (Nat.zero_le _)
    omega
  · have hb : 1 < 2 := by norm_num
    exact Nat.le_log_of_pow_le hb h_pow_le_n

def findSetCompressFuel (f : DisjointSetForest n) : Nat → Fin n → (DisjointSetForest n × Fin n)
  | 0, x => (f, x)
  | k+1, x =>
    let p := f.parent x
    if _ : p = x then (f, x)
    else
      let (f', root) := findSetCompressFuel f k p
      ({ f' with parent := λ z => if z = x then root else f'.parent z }, root)

def findSetCompress (f : DisjointSetForest n) (x : Fin n) : DisjointSetForest n × Fin n :=
  findSetCompressFuel f n x

theorem findSetCompressFuel_root (f : DisjointSetForest n) (k : Nat) (x : Fin n)
    (h_root : f.parent x = x) : findSetCompressFuel f k x = (f, x) := by
  induction' k with k ih
  · rfl
  · unfold findSetCompressFuel
    simpa [h_root] using ih

theorem findSetCompressFuel_snd_eq_findSetFuel (f : DisjointSetForest n) (k : Nat) (x : Fin n) :
    (findSetCompressFuel f k x).2 = findSetFuel f k x := by
  induction' k with k ih generalizing x
  · rfl
  · unfold findSetCompressFuel findSetFuel
    by_cases hp : f.parent x = x
    · simp [hp]
    · simp [hp]
      -- The IH gives: (findSetCompressFuel f k (f.parent x)).2 = findSetFuel f k (f.parent x)
      -- We case-split to expose the .2
      have h_ih := ih (f.parent x)
      cases h_pair : findSetCompressFuel f k (f.parent x)
      · rename_i f' root
        -- h_pair: findSetCompressFuel f k (f.parent x) = (f', root)
        -- So h_ih becomes: root = findSetFuel f k (f.parent x)
        rw [h_pair] at h_ih
        simp at h_ih ⊢
        exact h_ih

end DisjointSetForest

end Chapter21
end CLRS

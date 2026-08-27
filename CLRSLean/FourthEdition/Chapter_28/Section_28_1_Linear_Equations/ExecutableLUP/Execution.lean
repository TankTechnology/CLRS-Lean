import CLRSLean.FourthEdition.Chapter_28.Section_28_1_Linear_Equations.ExecutableLUP.Elimination

/-!
# CLRS Section 28.1 - Recursive executable LUP decomposition

This file contains only data-producing definitions.  The recursive execution
uses the concrete pivot scan and direct elimination before assembling child
factors by block reindexing.  Permutations are direct index lookups, and the
counter includes the multiplier divisions performed during factor assembly.
-/

namespace CLRS
namespace Chapter28

open Matrix

variable {F : Type} [Field F] [DecidableEq F]

/-- Computable reindexing of `Fin (n + 1)` as the pivot coordinate followed by
the trailing `Fin n` coordinates. -/
def execFinOneSumFin (n : Nat) : Fin (n + 1) ≃ Fin 1 ⊕ Fin n where
  toFun i := if h : i = 0 then Sum.inl ⟨0, by omega⟩ else Sum.inr (i.pred h)
  invFun x := Sum.elim (fun _ => (0 : Fin (n + 1))) Fin.succ x
  left_inv := by
    intro i
    by_cases h : i = 0
    · simp [h]
    · simp [h]
  right_inv := by
    intro x
    cases x with
    | inl j =>
        have hj : (⟨0, by omega⟩ : Fin 1) = j := Subsingleton.elim _ _
        simp [hj]
    | inr i => simp

@[simp]
theorem execFinOneSumFin_symm_inl (n : Nat) (j : Fin 1) :
    (execFinOneSumFin n).symm (Sum.inl j) = (0 : Fin (n + 1)) := by
  rfl

@[simp]
theorem execFinOneSumFin_symm_inr (n : Nat) (i : Fin n) :
    (execFinOneSumFin n).symm (Sum.inr i) = Fin.succ i := by
  rfl

/-- Move pivot row `p` to row zero by direct row lookup. -/
def pivotedMatrix {n : Nat} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    (p : Fin (n + 1)) : Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
  fun i j => A (Equiv.swap 0 p i) j

/-- Lift a child permutation so it fixes the pivot coordinate. -/
def liftTrailingPerm {n : Nat} (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n + 1)) :=
  let re := execFinOneSumFin n
  (re.trans (Equiv.Perm.sumCongr (1 : Equiv.Perm (Fin 1)) σ)).trans re.symm

/-- Assemble the parent factors from a pivoted matrix, its eliminated value,
and a successful decomposition of the trailing block. -/
def assembleLUPFactors {n : Nat}
    (B D : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    (pivotPerm : Equiv.Perm (Fin (n + 1))) (child : LUPFactors n F) :
    LUPFactors (n + 1) F :=
  let re := execFinOneSumFin n
  let α : Matrix (Fin 1) (Fin 1) F := fun _ _ => D 0 0
  let v : Matrix (Fin 1) (Fin n) F := fun _ j => D 0 (Fin.succ j)
  let mult : Matrix (Fin n) (Fin 1) F := fun i _ => B (Fin.succ i) 0 / B 0 0
  -- Multiplication by a permutation matrix is implemented as direct row
  -- lookup, so factor assembly does not hide an `n × n` matrix product.
  let permutedMult : Matrix (Fin n) (Fin 1) F :=
    fun i j => mult (child.perm i) j
  let L : Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
    (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) F) 0 permutedMult child.lower).reindex
      re.symm re.symm
  let U : Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
    (Matrix.fromBlocks α v (0 : Matrix (Fin n) (Fin 1) F) child.upper).reindex
      re.symm re.symm
  ⟨pivotPerm * liftTrailingPerm child.perm, L, U⟩

/-- Total LUP execution.  Failure is data: no factor triple is returned, but
the comparisons and field operations already performed remain recorded.  A
successful size-`n+1` assembly charges the `n` multiplier divisions used in
the lower-left block. -/
def lupDecomposeWithCost : ∀ (n : Nat),
    Matrix (Fin n) (Fin n) F → LUPExecution n F
  | 0, _A =>
      ⟨some ⟨1, 1, 1⟩, 0⟩
  | n + 1, A =>
      let pivotRun := findPivotWithCost A
      match pivotRun.pivot with
      | none => ⟨none, pivotRun.comparisons⟩
      | some p =>
          let pivotPerm : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 p.1
          let B := pivotedMatrix A p.1
          have hp0 : A p.1 0 ≠ 0 := p.2
          have hB : B 0 0 ≠ 0 := by
            simpa [B, pivotedMatrix] using hp0
          let eliminated := eliminateWithCost B hB
          let M : Matrix (Fin n) (Fin n) F :=
            fun i j => eliminated.value (Fin.succ i) (Fin.succ j)
          let child := lupDecomposeWithCost n M
          match child.result with
          | none =>
              ⟨none, pivotRun.comparisons + eliminated.work + child.work⟩
          | some factors =>
              ⟨some (assembleLUPFactors B eliminated.value pivotPerm factors),
                pivotRun.comparisons + eliminated.work + child.work + n⟩

end Chapter28
end CLRS

import CLRSLean.FourthEdition.Chapter_12.Section_12_1_Binary_Search_Trees.RandomConstruction

/-!
# Section 12.4 - Expected height of a randomly built BST

The deterministic bridge in {lit}`RandomConstruction` transfers the existing
finite-permutation exponential-tail analysis to the binary search tree built by
uniformly random insertion order.  The resulting theorem concerns the maximum
root-to-leaf depth of the whole tree, rather than the expected depth of one
fixed key.
-/

namespace CLRS
namespace Chapter12
namespace BSTree

open CLRS.Probability

/-- Expected height of the BST obtained from a uniform random permutation of
{lit}`Fin n`. -/
noncomputable def expectedHeight (n : Nat) : Real :=
  fintypeExpect (fun π : Equiv.Perm (Fin n) => (height (buildFromPerm π) : Real))

/-- Reindexing insertion orders by reversed priorities identifies random-BST
expected height with the already established canonical treap expectation. -/
theorem expected_height_eq_treap (n : Nat) :
    expectedHeight n = Extensions.Treap.expectedTreapHeight (n := n) := by
  classical
  unfold expectedHeight Extensions.Treap.expectedTreapHeight
  calc
    fintypeExpect (fun π : Equiv.Perm (Fin n) =>
        (height (buildFromPerm π) : Real)) =
        fintypeExpect (fun σ : Extensions.Treap.PrioPerm n =>
          (height (buildFromPerm (Extensions.Treap.revBijection σ)) : Real)) := by
            symm
            exact fintypeExpect_equiv Extensions.Treap.revBijection
              (fun π : Equiv.Perm (Fin n) => (height (buildFromPerm π) : Real))
    _ = fintypeExpect (fun σ : Extensions.Treap.PrioPerm n =>
          (Extensions.Treap.treapHeight σ : Real)) := by
            congr 1
            funext σ
            congr 1
            simpa [priorityPermOfInsertion] using
              height_buildFromPerm_eq_treapHeight
                (π := Extensions.Treap.revBijection σ)

/-- **CLRS Theorem 12.4, explicit harmonic form.**  The expected height of a
randomly built BST on {lit}`n` keys is at most {lit}`30 Hₙ`. -/
theorem expected_height_le_thirty_harmonic (n : Nat) :
    expectedHeight n ≤ 30 * (harmonic n : Real) := by
  rw [expected_height_eq_treap]
  exact Extensions.Treap.expectedTreapHeight_le

/-- **CLRS Theorem 12.4.**  The expected height of a randomly built BST is
logarithmic: {lit}`E[height] ≤ 30(1 + log n)`. -/
theorem expected_height_le_O_log (n : Nat) :
    expectedHeight n ≤ 30 * (1 + Real.log (n : Real)) := by
  calc
    expectedHeight n ≤ 30 * (harmonic n : Real) :=
      expected_height_le_thirty_harmonic n
    _ ≤ 30 * (1 + Real.log (n : Real)) := by
      gcongr
      exact harmonic_le_one_add_log n

end BSTree
end Chapter12
end CLRS

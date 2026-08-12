import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.ParallelMerge.LowerBound.Correctness

/-!
# CLRS Chapter 26.3 — P-MERGE Split Data

P-MERGE always chooses the midpoint of the longer input and locates that pivot
in the shorter input by binary lower bound.  {lit}`MergeSplit` records this
normalization without a Boolean flag, together with the size and pivot facts
needed by the recursive correctness and cost proofs.
-/

namespace CLRS
namespace Chapter27

universe u

/-- A normalized, nonempty P-MERGE split.

{lit}`primary` is one of the original inputs and is at least as long as
{lit}`secondary`; {lit}`inputOrder` records whether normalization preserved or
exchanged the inputs.  The pivot is the midpoint element of {lit}`primary`, and
{lit}`search` is exactly binary lower bound on {lit}`secondary`.  The remaining
fields expose the input-size and search-index invariants used by later proof
modules.
-/
structure MergeSplit (α : Type u) [LinearOrder α] where
  xs : List α
  ys : List α
  primary : List α
  secondary : List α
  inputOrder :
    (primary = xs ∧ secondary = ys) ∨ (primary = ys ∧ secondary = xs)
  secondary_length_le_primary : secondary.length ≤ primary.length
  total_positive : 0 < xs.length + ys.length
  normalized_total : primary.length + secondary.length = xs.length + ys.length
  pivotIndex_lt : primary.length / 2 < primary.length
  pivot : α
  pivot_eq : primary.get ⟨primary.length / 2, pivotIndex_lt⟩ = pivot
  search : Costed ℕ
  search_eq : search = binaryLowerBound secondary pivot
  search_index_le : search.value ≤ secondary.length

namespace MergeSplit

variable [LinearOrder α]

/-- The midpoint chosen from the normalized primary input. -/
def pivotIndex (S : MergeSplit α) : ℕ := S.primary.length / 2

/-- The canonical partition index returned by lower-bound search. -/
def splitIndex (S : MergeSplit α) : ℕ := S.search.value

/-- The canonical lower-bound index lies within the secondary input. -/
theorem splitIndex_le_secondary (S : MergeSplit α) :
    S.splitIndex ≤ S.secondary.length := by
  simpa [splitIndex] using S.search_index_le

/-- The primary prefix sent to the lower recursive call. -/
def lowerPrimary (S : MergeSplit α) : List α := S.primary.take S.pivotIndex

/-- The secondary prefix sent to the lower recursive call. -/
def lowerSecondary (S : MergeSplit α) : List α := S.secondary.take S.splitIndex

/-- The primary suffix strictly after the pivot. -/
def upperPrimary (S : MergeSplit α) : List α := S.primary.drop (S.pivotIndex + 1)

/-- The secondary suffix beginning at the lower-bound index. -/
def upperSecondary (S : MergeSplit α) : List α := S.secondary.drop S.splitIndex

/-- Total input size of the lower recursive call. -/
def leftSize (S : MergeSplit α) : ℕ :=
  S.lowerPrimary.length + S.lowerSecondary.length

/-- Total input size of the upper recursive call. -/
def rightSize (S : MergeSplit α) : ℕ :=
  S.upperPrimary.length + S.upperSecondary.length

/-- Total size of the original two inputs. -/
def totalSize (S : MergeSplit α) : ℕ := S.xs.length + S.ys.length

/-- The two recursive inputs partition every element except the one primary
pivot.  This exact accounting uses both the lawful midpoint and the
lower-bound index bound. -/
theorem childSizes_add_one (S : MergeSplit α) :
    S.leftSize + S.rightSize + 1 = S.totalSize := by
  have hiLt : S.pivotIndex < S.primary.length := by
    simpa [pivotIndex] using S.pivotIndex_lt
  have hi : S.pivotIndex ≤ S.primary.length := Nat.le_of_lt hiLt
  have hj := S.splitIndex_le_secondary
  have hiSucc : S.pivotIndex + 1 ≤ S.primary.length := by omega
  have hprimarySub := Nat.sub_add_cancel hiSucc
  have hsecondarySub := Nat.sub_add_cancel hj
  simp only [leftSize, rightSize, lowerPrimary, lowerSecondary, upperPrimary,
    upperSecondary, List.length_take, List.length_drop]
  rw [Nat.min_eq_left hi, Nat.min_eq_left hj]
  simp only [totalSize]
  rw [← S.normalized_total]
  omega

/-- Removing the primary pivot makes the lower recursive problem strictly
smaller, independently of the search result. -/
theorem leftSize_lt (S : MergeSplit α) : S.leftSize < S.totalSize := by
  have h := S.childSizes_add_one
  omega

/-- Removing the primary pivot makes the upper recursive problem strictly
smaller, independently of the search result. -/
theorem rightSize_lt (S : MergeSplit α) : S.rightSize < S.totalSize := by
  have h := S.childSizes_add_one
  omega

end MergeSplit

/-- Normalize two nonempty-total inputs and build the midpoint/lower-bound data
for one P-MERGE recursive step. -/
def mergeSplit [LinearOrder α] (xs ys : List α)
    (htotal : 0 < xs.length + ys.length) : MergeSplit α := by
  by_cases hxy : xs.length < ys.length
  · have hypos : 0 < ys.length := by omega
    have hidx : ys.length / 2 < ys.length := Nat.div_lt_self hypos (by omega)
    let pivot := ys.get ⟨ys.length / 2, hidx⟩
    let search := binaryLowerBound xs pivot
    exact
      { xs := xs
        ys := ys
        primary := ys
        secondary := xs
        inputOrder := Or.inr ⟨rfl, rfl⟩
        secondary_length_le_primary := Nat.le_of_lt hxy
        total_positive := htotal
        normalized_total := by omega
        pivotIndex_lt := hidx
        pivot := pivot
        pivot_eq := rfl
        search := search
        search_eq := rfl
        search_index_le := by
          dsimp [search]
          exact binaryLowerBound_index_le_length xs pivot }
  · have hyx : ys.length ≤ xs.length := Nat.le_of_not_gt hxy
    have hxpos : 0 < xs.length := by omega
    have hidx : xs.length / 2 < xs.length := Nat.div_lt_self hxpos (by omega)
    let pivot := xs.get ⟨xs.length / 2, hidx⟩
    let search := binaryLowerBound ys pivot
    exact
      { xs := xs
        ys := ys
        primary := xs
        secondary := ys
        inputOrder := Or.inl ⟨rfl, rfl⟩
        secondary_length_le_primary := hyx
        total_positive := htotal
        normalized_total := rfl
        pivotIndex_lt := hidx
        pivot := pivot
        pivot_eq := rfl
        search := search
        search_eq := rfl
        search_index_le := by
          dsimp [search]
          exact binaryLowerBound_index_le_length ys pivot }

@[simp] theorem mergeSplit_xs [LinearOrder α] (xs ys : List α)
    (htotal : 0 < xs.length + ys.length) : (mergeSplit xs ys htotal).xs = xs := by
  unfold mergeSplit
  split <;> rfl

@[simp] theorem mergeSplit_ys [LinearOrder α] (xs ys : List α)
    (htotal : 0 < xs.length + ys.length) : (mergeSplit xs ys htotal).ys = ys := by
  unfold mergeSplit
  split <;> rfl

end Chapter27
end CLRS

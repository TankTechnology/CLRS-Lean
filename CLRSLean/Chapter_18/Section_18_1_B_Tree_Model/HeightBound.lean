import CLRSLean.Chapter_18.Section_18_1_B_Tree_Model

/-!
# CLRS Section 18.1 - B-tree key count and height bound

This module counts every key slot represented by a B-tree.  Its exact
accounting identity rewrites an internal node's augmented key count as the sum
of the augmented counts of its children.  That recurrence is the arithmetic
foundation for the structural minimum-key and logarithmic-height bounds.
-/

namespace CLRS
namespace Chapter18
namespace BTree

/-! ## Exact key accounting -/

/-- The number of key slots represented by a B-tree. -/
def totalKeys (tr : BTree) : Nat :=
  (keysOf tr).length

/-- A node's total key count is its local key count plus all child counts. -/
theorem totalKeys_node (ks : List Nat) (cs : List BTree) :
    totalKeys (node ks cs) =
      ks.length + (cs.map totalKeys).sum := by
  unfold totalKeys
  simp [keysOf, List.length_flatMap]

/--
For an internal node, adding one to the total key count exactly absorbs every
separator key into one augmented count per child.
-/
private lemma totalKeys_add_one_eq_sum_children
    {ks : List Nat} {c0 : BTree} {cs : List BTree}
    (hcb : ChildBounded (node ks (c0 :: cs))) :
    totalKeys (node ks (c0 :: cs)) + 1 =
      ((c0 :: cs).map (fun child => totalKeys child + 1)).sum := by
  have hlen : (c0 :: cs).length = ks.length + 1 := by
    unfold ChildBounded at hcb
    simpa using hcb.1
  rw [totalKeys_node, List.sum_map_add, List.map_const', List.sum_const_nat]
  simp only [Nat.mul_one]
  omega

/-- A pointwise lower bound lifts to the sum over all list positions. -/
private lemma length_mul_le_sum_map
    {α : Type} (xs : List α) (q : Nat) (f : α → Nat)
    (hpoint : ∀ x ∈ xs, q ≤ f x) :
    xs.length * q ≤ (xs.map f).sum := by
  have hsum : (xs.map (fun _ => q)).sum ≤ (xs.map f).sum :=
    List.sum_le_sum hpoint
  rw [List.map_const', List.sum_const_nat] at hsum
  exact hsum

/-! ## Internal-child projections -/

/-- Every child position of a child-bounded internal node is child-bounded. -/
private lemma childBounded_of_mem
    {ks : List Nat} {c0 child : BTree} {cs : List BTree}
    (hcb : ChildBounded (node ks (c0 :: cs)))
    (hc : child ∈ c0 :: cs) :
    ChildBounded child := by
  unfold ChildBounded at hcb
  exact hcb.2.2 child hc

/-- Every child position of an occupied node satisfies non-root occupancy. -/
private lemma occupancy_false_of_mem
    {t : Nat} {isRoot : Bool} {ks : List Nat} {c0 child : BTree}
    {cs : List BTree}
    (hocc : Occupancy t isRoot (node ks (c0 :: cs)))
    (hc : child ∈ c0 :: cs) :
    Occupancy t false child := by
  unfold Occupancy at hocc
  exact hocc.2.2.2 child hc

/-- Every child position of a same-depth internal node is itself same-depth. -/
private lemma sameDepth_of_mem
    {ks : List Nat} {c0 child : BTree} {cs : List BTree}
    (hsd : SameDepth (node ks (c0 :: cs)))
    (hc : child ∈ c0 :: cs) :
    SameDepth child := by
  rcases List.mem_cons.mp hc with rfl | hcTail
  · exact sameDepth_head_sd hsd
  · exact sameDepth_tail_sd hsd child hcTail

/-- Every child of a same-depth internal node has the head child's height. -/
private lemma heightOf_eq_head_of_mem
    {ks : List Nat} {c0 child : BTree} {cs : List BTree}
    (hsd : SameDepth (node ks (c0 :: cs)))
    (hc : child ∈ c0 :: cs) :
    heightOf child = heightOf c0 :=
  sameDepth_children_eq_height hsd child hc c0 (by simp)

/-! ## Non-root minimum-key bound -/

/--
Every non-root B-tree subtree contains enough key slots for its height.  The
augmented form avoids natural-number subtraction and is the induction theorem
used by the root-level CLRS bound.
-/
theorem nonRoot_totalKeys_add_one_lower_bound
    (t : Nat) (_ht : 2 ≤ t) {tr : BTree}
    (hcb : ChildBounded tr)
    (hocc : Occupancy t false tr)
    (hsd : SameDepth tr) :
    t ^ (heightOf tr + 1) ≤ totalKeys tr + 1 := by
  induction hsd with
  | leaf ks =>
      simp [Occupancy] at hocc
      simp [heightOf, totalKeys_node]
      omega
  | internal ks c0 cs hheights hsd0 hsdcs ih0 ihcs =>
      have hsdNode : SameDepth (node ks (c0 :: cs)) :=
        SameDepth.internal ks c0 cs hheights hsd0 hsdcs
      have hcount : t ≤ (c0 :: cs).length := by
        have hocc' := hocc
        simp [Occupancy] at hocc'
        exact hocc'.2.2.1.1
      let q := t ^ (heightOf c0 + 1)
      have hpoint :
          ∀ child ∈ c0 :: cs, q ≤ totalKeys child + 1 := by
        intro child hc
        rcases List.mem_cons.mp hc with rfl | hcTail
        · exact ih0
            (childBounded_of_mem hcb (by simp))
            (occupancy_false_of_mem hocc (by simp))
        · have hcMem : child ∈ c0 :: cs := by simp [hcTail]
          simpa [q, heightOf_eq_head_of_mem hsdNode hcMem] using
            (ihcs child hcTail
              (childBounded_of_mem hcb hcMem)
              (occupancy_false_of_mem hocc hcMem))
      have hsum :
          (c0 :: cs).length * q ≤
            ((c0 :: cs).map (fun child => totalKeys child + 1)).sum :=
        length_mul_le_sum_map (c0 :: cs) q
          (fun child => totalKeys child + 1) hpoint
      have hmul : t * q ≤ (c0 :: cs).length * q :=
        Nat.mul_le_mul_right q hcount
      rw [totalKeys_add_one_eq_sum_children hcb]
      calc
        t ^ (heightOf (node ks (c0 :: cs)) + 1) = t * q := by
          rw [heightOf_internal_of_sameDepth hsdNode]
          have hexponent :
              1 + heightOf c0 + 1 = (heightOf c0 + 1) + 1 := by
            omega
          rw [hexponent, Nat.pow_succ]
          exact Nat.mul_comm _ _
        _ ≤ (c0 :: cs).length * q := hmul
        _ ≤ ((c0 :: cs).map (fun child => totalKeys child + 1)).sum := hsum

end BTree
end Chapter18
end CLRS

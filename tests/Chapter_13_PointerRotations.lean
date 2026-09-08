import CLRSLean.FourthEdition.Chapter_13.Section_13_2_Rotations

open CLRS.Chapter13
open RBStore (nil)

#check StoreReprAt.unique
#check StoreRepr.tree_unique
#check Represents.tree_unique
#check rotateLeftP_refines_root
#check rotateRightP_refines_root
#check rotateLeftP_refines_context
#check rotateRightP_refines_context
#check RotationResult.lift_left
#check RotationResult.lift_right
#check RotationResult.lift_context

namespace PointerRotationTests

-- Every fixture has a non-NIL middle subtree and an unrelated allocated record.
def fixture (atRoot rightRotation onRight : Bool) : RBStore where
  root := if atRoot then 1 else 4
  node i := match i with
    | 1 => some ⟨10, .red, if rightRotation then 2 else 0,
        if rightRotation then 0 else 2, if atRoot then 0 else 4⟩
    | 2 => some ⟨20, .black, if rightRotation then 0 else 3,
        if rightRotation then 3 else 0, 1⟩
    | 3 => some ⟨15, .red, 0, 0, 2⟩
    | 4 => some ⟨40, .black, if onRight then 5 else 1,
        if onRight then 1 else 5, 0⟩
    | 5 => some ⟨50, .black, 0, 0, 4⟩
    | 9 => some ⟨90, .red, 91, 92, 99⟩
    | _ => none

def run (atRoot rightRotation onRight : Bool) : RBStore :=
  if rightRotation then (rotateRightP (fixture atRoot rightRotation onRight) 1).1
  else (rotateLeftP (fixture atRoot rightRotation onRight) 1).1

-- Both root rotations promote the child and reconnect the middle subtree.
example (rightRotation : Bool) :
    (run true rightRotation false).root = 2 ∧
    (run true rightRotation false).get 1 = some
      ⟨10, .red, if rightRotation then 3 else 0, if rightRotation then 0 else 3, 2⟩ ∧
    (run true rightRotation false).get 2 = some
      ⟨20, .black, if rightRotation then 0 else 1, if rightRotation then 1 else 0, 0⟩ := by
  cases rightRotation <;> decide

-- All four interior combinations: left/right rotation at a left/right child.
example (rightRotation onRight : Bool) :
    (run false rightRotation onRight).root = 4 ∧
    (run false rightRotation onRight).get 4 = some
      ⟨40, .black, if onRight then 5 else 2, if onRight then 2 else 5, 0⟩ ∧
    ((run false rightRotation onRight).get 2).map RBNode.parent = some 4 := by
  cases rightRotation <;> cases onRight <;> decide

-- Complete record checks frame all non-parent fields of beta, all sibling
-- fields, all unrelated fields, and the sentinel in every fixture.
example (atRoot rightRotation onRight : Bool) :
    (run atRoot rightRotation onRight).get 3 = some ⟨15, .red, 0, 0, 1⟩ ∧
    (run atRoot rightRotation onRight).get 5 = (fixture atRoot rightRotation onRight).get 5 ∧
    (run atRoot rightRotation onRight).get 9 = (fixture atRoot rightRotation onRight).get 9 ∧
    (run atRoot rightRotation onRight).get nil = none := by
  cases atRoot <;> cases rightRotation <;> cases onRight <;> decide

private def leaf (c : Color) (k : Nat) : RBTree := .node c .empty k .empty
private def beforeLeft : RBTree := .node .red .empty 10 (.node .black (leaf .red 15) 20 .empty)
private def afterLeft : RBTree := .node .black (.node .red .empty 10 (leaf .red 15)) 20 .empty

private theorem leaf_repr {s : RBStore} {p i k : Nat} {c : Color}
    (hi : i ≠ nil) (hp : p ≠ i) (hg : s.get i = some ⟨k, c, 0, 0, p⟩) :
    StoreReprAt s p i (leaf c k) {i} := by
  simpa [leaf] using StoreReprAt.node hi hg rfl (.empty i) (.empty i)
    (by simp) (by simp) (by simp) (by simpa using hp)

private theorem left_subtree_repr (atRoot onRight : Bool) :
    StoreReprAt (fixture atRoot false onRight) (if atRoot then 0 else 4) 1 beforeLeft {1, 2, 3} := by
  have hb : StoreReprAt (fixture atRoot false onRight) 2 3 (leaf .red 15) {3} :=
    leaf_repr (by decide) (by decide) rfl
  have hy : StoreReprAt (fixture atRoot false onRight) 1 2
      (.node .black (leaf .red 15) 20 .empty) {2, 3} := by
    simpa using StoreReprAt.node (n := ⟨20, .black, 3, 0, 1⟩)
      (by decide) (by rfl) rfl hb (.empty 2) (by decide) (by simp) (by simp) (by decide)
  simpa [beforeLeft] using StoreReprAt.node
    (n := ⟨10, .red, 0, 2, if atRoot then 0 else 4⟩)
    (by decide) (by rfl) rfl (.empty 1) hy (by simp) (by decide) (by simp)
    (by cases atRoot <;> decide)

private def beforeRight : RBTree := .node .red (.node .black .empty 20 (leaf .red 15)) 10 .empty
private def afterRight : RBTree := .node .black .empty 20 (.node .red (leaf .red 15) 10 .empty)

private theorem right_subtree_repr (atRoot onRight : Bool) :
    StoreReprAt (fixture atRoot true onRight) (if atRoot then 0 else 4) 1 beforeRight {1, 2, 3} := by
  have hb : StoreReprAt (fixture atRoot true onRight) 2 3 (leaf .red 15) {3} :=
    leaf_repr (by decide) (by decide) rfl
  have hy : StoreReprAt (fixture atRoot true onRight) 1 2
      (.node .black .empty 20 (leaf .red 15)) {2, 3} := by
    simpa using StoreReprAt.node (n := ⟨20, .black, 0, 3, 1⟩)
      (by decide) (by rfl) rfl (.empty 2) hb (by simp) (by decide) (by simp) (by decide)
  simpa [beforeRight] using StoreReprAt.node
    (n := ⟨10, .red, 2, 0, if atRoot then 0 else 4⟩)
    (by decide) (by rfl) rfl hy (.empty 1) (by decide) (by simp) (by simp)
    (by cases atRoot <;> decide)

-- Non-vacuous root refinement from a constructed, uniquely owned input.
example : Represents (rotateLeftP (fixture true false false) 1).1 afterLeft := by
  apply rotateLeftP_refines_root
  exact ⟨rfl, _, left_subtree_repr true false⟩

-- Non-vacuous interior refinements exercise both parent positions and prove
-- the complete enclosing output representation through the context theorem.
example : Represents (rotateLeftP (fixture false false false) 1).1
    (.node .black afterLeft 40 (leaf .black 50)) := by
  have hs := left_subtree_repr false false
  have hb : StoreReprAt (fixture false false false) 4 5 (leaf .black 50) {5} :=
    leaf_repr (by decide) (by decide) rfl
  have ctx : RotationContext (fixture false false false) 4 1 {1, 2, 3}
      0 4 {4, 1, 2, 3, 5} (fun t => .node .black t 40 (leaf .black 50)) := by
    simpa [Finset.union_assoc, Finset.insert_comm] using RotationContext.left
      (n := ⟨40, .black, 1, 5, 0⟩) (.hole 4 1 {1, 2, 3} (by simp [nil]))
      (by decide) (by rfl) rfl hs hb (by decide) (by decide) (by decide)
      (by decide) (fun _ => rfl)
  exact rotateLeftP_refines_context rfl hs ctx

example : Represents (rotateLeftP (fixture false false true) 1).1
    (.node .black (leaf .black 50) 40 afterLeft) := by
  have hs := left_subtree_repr false true
  have hb : StoreReprAt (fixture false false true) 4 5 (leaf .black 50) {5} :=
    leaf_repr (by decide) (by decide) rfl
  have ctx : RotationContext (fixture false false true) 4 1 {1, 2, 3}
      0 4 {4, 5, 1, 2, 3} (fun t => .node .black (leaf .black 50) 40 t) := by
    simpa [Finset.union_assoc, Finset.insert_comm] using RotationContext.right
      (n := ⟨40, .black, 5, 1, 0⟩) (.hole 4 1 {1, 2, 3} (by simp [nil]))
      (by decide) (by rfl) rfl hb hs (by decide) (by decide) (by decide) (by decide)
      (by decide) (fun _ => rfl)
  exact rotateLeftP_refines_context rfl hs ctx

-- Non-vacuous root refinement from a constructed, uniquely owned input.
example : Represents (rotateRightP (fixture true true false) 1).1 afterRight := by
  apply rotateRightP_refines_root
  exact ⟨rfl, _, right_subtree_repr true false⟩

-- Non-vacuous interior refinements exercise both parent positions and prove
-- the complete enclosing output representation through the context theorem.
example : Represents (rotateRightP (fixture false true false) 1).1
    (.node .black afterRight 40 (leaf .black 50)) := by
  have hs := right_subtree_repr false false
  have hb : StoreReprAt (fixture false true false) 4 5 (leaf .black 50) {5} :=
    leaf_repr (by decide) (by decide) rfl
  have ctx : RotationContext (fixture false true false) 4 1 {1, 2, 3}
      0 4 {4, 1, 2, 3, 5} (fun t => .node .black t 40 (leaf .black 50)) := by
    simpa [Finset.union_assoc, Finset.insert_comm] using RotationContext.left
      (n := ⟨40, .black, 1, 5, 0⟩) (.hole 4 1 {1, 2, 3} (by simp [nil]))
      (by decide) (by rfl) rfl hs hb (by decide) (by decide) (by decide)
      (by decide) (fun _ => rfl)
  exact rotateRightP_refines_context rfl hs ctx

example : Represents (rotateRightP (fixture false true true) 1).1
    (.node .black (leaf .black 50) 40 afterRight) := by
  have hs := right_subtree_repr false true
  have hb : StoreReprAt (fixture false true true) 4 5 (leaf .black 50) {5} :=
    leaf_repr (by decide) (by decide) rfl
  have ctx : RotationContext (fixture false true true) 4 1 {1, 2, 3}
      0 4 {4, 5, 1, 2, 3} (fun t => .node .black (leaf .black 50) 40 t) := by
    simpa [Finset.union_assoc, Finset.insert_comm] using RotationContext.right
      (n := ⟨40, .black, 5, 1, 0⟩) (.hole 4 1 {1, 2, 3} (by simp [nil]))
      (by decide) (by rfl) rfl hb hs (by decide) (by decide) (by decide) (by decide)
      (by decide) (fun _ => rfl)
  exact rotateRightP_refines_context rfl hs ctx

-- Successful rotations with NIL middle children leave NIL untouched too.
example (rightRotation : Bool) :
    let s := (fixture true rightRotation false).set 2 ⟨20, .black, 0, 0, 1⟩
    let result := if rightRotation then rotateRightP s 1 else rotateLeftP s 1
    result.1.root = 2 ∧ result.1.get nil = none ∧ result.2 = 6 := by
  cases rightRotation <;> decide

-- An allocated subtree with the wrong root parent is not a whole tree.
example (t : RBTree) : ¬ Represents { fixture false false false with root := 1 } t := by
  rintro ⟨_, F, h⟩
  cases h with
  | @node p i n l r L R hn hg hp hL hR hnL hnR hd hpo =>
    have he : n = ⟨10, .red, 0, 2, 4⟩ := Option.some.inj hg.symm
    cases he
    cases hp

-- Missing root and missing pivot child return exactly the original store.
example : rotateLeftP (fixture true false false) 99 = (fixture true false false, 0) :=
  rotateLeftP_missing _ _ rfl
example : rotateRightP (fixture true false false) 99 = (fixture true false false, 0) :=
  rotateRightP_missing _ _ rfl
example : rotateLeftP (fixture true false false) 3 = (fixture true false false, 0) :=
  rotateLeftP_missing_child _ _ ⟨15, .red, 0, 0, 2⟩ rfl rfl
example : rotateRightP (fixture true false false) 3 = (fixture true false false, 0) :=
  rotateRightP_missing_child _ _ ⟨15, .red, 0, 0, 2⟩ rfl rfl

-- NIL can never represent a nonempty tree, even with an allocated record.
example (s : RBStore) (c l k r) : ¬ StoreRepr s nil (.node c l k r) := by
  rintro ⟨_, p, F, h⟩
  cases h with
  | node hn => exact hn rfl

example (s : RBStore) (n : RBNode) (t : RBTree) : ¬ Represents (s.set nil n) t := by
  rintro ⟨h, _⟩
  simp at h

-- Self-cycles and shared non-NIL children are rejected, independent of keys.
def malformed (shared : Bool) : RBStore where
  root := 1
  node i := if i = 1 then some ⟨10, .black, if shared then 2 else 1, 2, 0⟩
    else if i = 2 then some ⟨20, .red, 0, 0, 1⟩ else none

example (t : RBTree) : ¬ Represents (malformed false) t := by
  rintro ⟨_, F, h⟩
  have hn := h.no_self_child (by decide) (n := ⟨10, .black, 1, 2, 0⟩) rfl
  exact hn.1 rfl

example (t : RBTree) : ¬ Represents (malformed true) t := by
  rintro ⟨_, F, h⟩
  have hn := h.children_distinct (by decide) (n := ⟨10, .black, 2, 2, 0⟩) rfl (by decide)
  exact hn rfl

#print axioms StoreReprAt.unique
#print axioms rotateLeftP_refines_context
#print axioms rotateRightP_refines_context

end PointerRotationTests

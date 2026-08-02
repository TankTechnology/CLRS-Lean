import CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model.S1_ExecutableFibHeap

/-!
# Chapter 19.1 S2: occurrence paths and cascading cuts

This module gives the persistent Fibonacci-heap model a duplicate-safe node
handle.  A path selects a concrete root-list occurrence and then concrete
child-list occurrences; keys are deliberately not used as identities.
-/

namespace CLRS
namespace Chapter19

/-- A duplicate-safe occurrence path: one root position followed by child
positions from the selected root. -/
structure FHPath where
  root : Nat
  children : List Nat
  deriving DecidableEq, Repr

/-- One zipper frame recording the parent of a focused child. -/
structure FHFrame where
  key : Int
  marked : Bool
  before : List FHNode
  after : List FHNode

namespace FHFrame

/-- Reinsert a focused child into one parent frame. -/
def close (frame : FHFrame) (child : FHNode) : FHNode :=
  FHNode.node frame.key frame.marked (frame.before ++ child :: frame.after)

/-- Remove the focused child from one parent frame. -/
def removeFocus (frame : FHFrame) : FHNode :=
  FHNode.node frame.key frame.marked (frame.before ++ frame.after)

/-- Close parent frames ordered from the nearest parent to the root. -/
def closeAll (focus : FHNode) (parents : List FHFrame) : FHNode :=
  parents.foldl (fun child frame => frame.close child) focus

/-- The focused child occurs at the split position of its frame. -/
theorem getElem?_close_children (frame : FHFrame) (child : FHNode) :
    (frame.before ++ child :: frame.after)[frame.before.length]? = some child := by
  simp

/-- Erasing the focused position leaves exactly the two stored sibling lists. -/
theorem eraseIdx_close_children (frame : FHFrame) (child : FHNode) :
    (frame.before ++ child :: frame.after).eraseIdx frame.before.length =
      frame.before ++ frame.after := by
  cases frame with
  | mk key marked before after =>
      induction before with
      | nil => rfl
      | cons sibling before ih =>
          change sibling ::
              ((before ++ child :: after).eraseIdx before.length) =
            sibling :: (before ++ after)
          rw [ih]

/-- Replacing the focused child is list replacement at the split position. -/
theorem set_close_children (frame : FHFrame) (old new : FHNode) :
    (frame.before ++ old :: frame.after).set frame.before.length new =
      frame.before ++ new :: frame.after := by
  cases frame with
  | mk key marked before after =>
      induction before with
      | nil => rfl
      | cons sibling before ih =>
          change sibling ::
              ((before ++ old :: after).set before.length new) =
            sibling :: (before ++ new :: after)
          rw [ih]

/-- Removing a focused child preserves heap order of the parent and projects
heap order to the removed subtree. -/
theorem close_heapOrdered_remove {frame : FHFrame} {child : FHNode}
    (hordered : (frame.close child).HeapOrdered) :
    child.HeapOrdered ∧ frame.removeFocus.HeapOrdered := by
  cases hordered with
  | node hle hall =>
      constructor
      · exact hall child (by simp [close])
      · refine FHNode.HeapOrdered.node ?_ ?_
        · intro current hcurrent
          exact hle current (by
            simp only [removeFocus, close, List.mem_append,
              List.mem_cons] at hcurrent ⊢
            tauto)
        · intro current hcurrent
          exact hall current (by
            simp only [removeFocus, close, List.mem_append,
              List.mem_cons] at hcurrent ⊢
            tauto)

/-- Replacing the focused subtree by a heap-ordered subtree with the same key
preserves heap order of that parent. -/
theorem close_heapOrdered_replace {frame : FHFrame} {old new : FHNode}
    (hordered : (frame.close old).HeapOrdered)
    (hnew : new.HeapOrdered) (hkey : new.key = old.key) :
    (frame.close new).HeapOrdered := by
  cases hordered with
  | node hle hall =>
      refine FHNode.HeapOrdered.node ?_ ?_
      · intro current hcurrent
        simp only [close, List.mem_append, List.mem_cons] at hcurrent ⊢
        rcases hcurrent with hbefore | rfl | hafter
        · exact hle current (by simp [hbefore])
        · have hold := hle old (by simp)
          rw [hkey]
          exact hold
        · exact hle current (by simp [hafter])
      · intro current hcurrent
        simp only [close, List.mem_append, List.mem_cons] at hcurrent ⊢
        rcases hcurrent with hbefore | rfl | hafter
        · exact hall current (by simp [hbefore])
        · exact hnew
        · exact hall current (by simp [hafter])

/-- Removing a focused child preserves the loss invariant of the parent and
projects it to the removed subtree. -/
theorem close_lossInvariant_remove {frame : FHFrame} {child : FHNode}
    (hloss : (frame.close child).LossInvariant) :
    child.LossInvariant ∧ frame.removeFocus.LossInvariant := by
  have hi : frame.before.length <
      (frame.before ++ child :: frame.after).length := by simp
  have hremove := FH.lossInvariant_remove_index hloss
    frame.before.length hi
  obtain ⟨_, hget⟩ := List.getElem?_eq_some_iff.mp
    (getElem?_close_children frame child)
  rw [hget] at hremove
  rw [eraseIdx_close_children] at hremove
  exact hremove

/-- Replacing the focused subtree by one with the same degree and mark
preserves the parent's mark-aware loss invariant. -/
theorem close_lossInvariant_replace {frame : FHFrame} {old new : FHNode}
    (hloss : (frame.close old).LossInvariant)
    (hnew : new.LossInvariant) (hdegree : new.degree = old.degree)
    (hmarked : new.marked = old.marked) :
    (frame.close new).LossInvariant := by
  cases hloss with
  | node hdeg hall =>
      refine FHNode.LossInvariant.node ?_ ?_
      · intro j hj
        have hjold : j < (frame.before ++ old :: frame.after).length := by
          simpa using hj
        have hset := set_close_children frame old new
        have hjset : j <
            ((frame.before ++ old :: frame.after).set
              frame.before.length new).length := by
          simpa [hset] using hj
        have hget := List.getElem_set
          (l := frame.before ++ old :: frame.after)
          (i := frame.before.length) (j := j) (a := new) hjset
        have hget' :
            (frame.before ++ new :: frame.after)[j] =
              if frame.before.length = j then new
              else (frame.before ++ old :: frame.after)[j] := by
          simpa only [hset] using hget
        by_cases hindex : frame.before.length = j
        · simp only [hindex, if_true] at hget'
          rw [hget']
          subst j
          have hold := hdeg frame.before.length (by simp)
          simpa [hdegree, hmarked] using hold
        · simp only [hindex, if_false] at hget'
          rw [hget']
          exact hdeg j hjold
      · intro child hchild
        simp only [close, List.mem_append, List.mem_cons] at hchild ⊢
        rcases hchild with hbefore | rfl | hafter
        · exact hall child (by simp [hbefore])
        · exact hnew
        · exact hall child (by simp [hafter])

/-- Replacing an unmarked child after its first child loss preserves the
parent's mark-aware loss invariant: the new mark accounts for exactly the one
unit decrease in degree. -/
theorem close_lossInvariant_firstLoss {frame : FHFrame} {old new : FHNode}
    (hloss : (frame.close old).LossInvariant)
    (hnew : new.LossInvariant) (hdegree : new.degree + 1 = old.degree)
    (holdMarked : old.marked = false) (hnewMarked : new.marked = true) :
    (frame.close new).LossInvariant := by
  cases hloss with
  | node hdeg hall =>
      refine FHNode.LossInvariant.node ?_ ?_
      · intro j hj
        have hjold : j < (frame.before ++ old :: frame.after).length := by
          simpa using hj
        have hset := set_close_children frame old new
        have hjset : j <
            ((frame.before ++ old :: frame.after).set
              frame.before.length new).length := by
          simpa [hset] using hj
        have hget := List.getElem_set
          (l := frame.before ++ old :: frame.after)
          (i := frame.before.length) (j := j) (a := new) hjset
        have hget' :
            (frame.before ++ new :: frame.after)[j] =
              if frame.before.length = j then new
              else (frame.before ++ old :: frame.after)[j] := by
          simpa only [hset] using hget
        by_cases hindex : frame.before.length = j
        · simp only [hindex, if_true] at hget'
          rw [hget']
          subst j
          have hold := hdeg frame.before.length (by simp)
          simp [holdMarked] at hold
          simp [hnewMarked]
          omega
        · simp only [hindex, if_false] at hget'
          rw [hget']
          exact hdeg j hjold
      · intro child hchild
        simp only [close, List.mem_append, List.mem_cons] at hchild ⊢
        rcases hchild with hbefore | rfl | hafter
        · exact hall child (by simp [hbefore])
        · exact hnew
        · exact hall child (by simp [hafter])

/-- Removing and promoting a focused child preserves the exact subtree-key
multiset balance. -/
theorem close_keyBag_balance (frame : FHFrame) (child : FHNode) :
    child.keyBag + frame.removeFocus.keyBag = (frame.close child).keyBag := by
  simp [close, removeFocus, FHNode.forestKeyBag_append]
  ac_rfl

/-- A frame contributes a fixed multiset around its focused child. -/
theorem close_keyBag_eq (frame : FHFrame) (child : FHNode) :
    (frame.close child).keyBag =
      child.keyBag +
        ({frame.key} + FHNode.forestKeyBag frame.before +
          FHNode.forestKeyBag frame.after) := by
  simp [close, FHNode.forestKeyBag_append]
  ac_rfl

/-- An exact one-occurrence multiset replacement is preserved by one zipper
frame, even when the erased key also occurs elsewhere in the context. -/
theorem close_keyBag_update {old new : FHNode} {erased inserted : Int}
    (frame : FHFrame) (hmem : erased ∈ old.keyBag)
    (hupdate : new.keyBag = old.keyBag.erase erased + {inserted}) :
    (frame.close new).keyBag =
      (frame.close old).keyBag.erase erased + {inserted} := by
  let context :=
    ({frame.key} + FHNode.forestKeyBag frame.before +
      FHNode.forestKeyBag frame.after : Multiset Int)
  rw [close_keyBag_eq, close_keyBag_eq, hupdate]
  change (old.keyBag.erase erased + {inserted}) + context =
    (old.keyBag + context).erase erased + {inserted}
  rw [Multiset.erase_add_left_pos context hmem]
  ac_rfl

/-- Exact one-occurrence multiset replacement is preserved through the full
zipper context. -/
theorem closeAll_keyBag_update {old new : FHNode} {erased inserted : Int}
    {parents : List FHFrame} (hmem : erased ∈ old.keyBag)
    (hupdate : new.keyBag = old.keyBag.erase erased + {inserted}) :
    (closeAll new parents).keyBag =
      (closeAll old parents).keyBag.erase erased + {inserted} := by
  induction parents generalizing old new with
  | nil => simpa [closeAll] using hupdate
  | cons frame parents ih =>
      have hstep := close_keyBag_update frame hmem hupdate
      have hmemParent : erased ∈ (frame.close old).keyBag := by
        rw [close_keyBag_eq]
        exact Multiset.mem_add.mpr (Or.inl hmem)
      simpa [closeAll] using ih hmemParent hstep

/-- A key occurrence in the focus remains present after closing every frame. -/
theorem closeAll_mem_keyBag {focus : FHNode} {key : Int}
    {parents : List FHFrame} (hmem : key ∈ focus.keyBag) :
    key ∈ (closeAll focus parents).keyBag := by
  induction parents generalizing focus with
  | nil => simpa [closeAll] using hmem
  | cons frame parents ih =>
      apply ih
      rw [close_keyBag_eq]
      exact Multiset.mem_add.mpr (Or.inl hmem)

/-- Removing and promoting a focused child preserves the exact node-count
balance. -/
theorem close_size_balance (frame : FHFrame) (child : FHNode) :
    child.size + frame.removeFocus.size = (frame.close child).size := by
  simp [close, removeFocus, FHNode.forestSize_append]
  omega

/-- Removing and promoting a focused child preserves all subtree marks; the
focused subtree and remaining parent partition the original mark count. -/
theorem close_marks_balance (frame : FHFrame) (child : FHNode) :
    child.marks + frame.removeFocus.marks = (frame.close child).marks := by
  simp [close, removeFocus, FHNode.marks, FHNode.forestMarks]
  omega

/-- One zipper frame transports the mark-count difference between two focused
subtrees unchanged. -/
theorem close_marks_exchange (frame : FHFrame) (old new : FHNode) :
    (frame.close new).marks + old.marks =
      (frame.close old).marks + new.marks := by
  simp only [close, FHNode.marks_node, List.map_append, List.map_cons,
    List.sum_append, List.sum_cons]
  omega

/-- Heap order of a fully closed context projects to its focused subtree. -/
theorem heapOrdered_focus_of_closeAll {focus : FHNode}
    {parents : List FHFrame}
    (hordered : (closeAll focus parents).HeapOrdered) :
    focus.HeapOrdered := by
  induction parents generalizing focus with
  | nil => simpa [closeAll] using hordered
  | cons frame parents ih =>
      have hparent : (frame.close focus).HeapOrdered := by
        apply ih
        simpa [closeAll] using hordered
      exact (close_heapOrdered_remove hparent).1

/-- The loss invariant of a fully closed context projects to its focused
subtree. -/
theorem lossInvariant_focus_of_closeAll {focus : FHNode}
    {parents : List FHFrame}
    (hloss : (closeAll focus parents).LossInvariant) :
    focus.LossInvariant := by
  induction parents generalizing focus with
  | nil => simpa [closeAll] using hloss
  | cons frame parents ih =>
      have hparent : (frame.close focus).LossInvariant := by
        apply ih
        simpa [closeAll] using hloss
      exact (close_lossInvariant_remove hparent).1

/-- Replacing the focused subtree by an ordered subtree with the same root key
preserves heap order through every enclosing zipper frame. -/
theorem closeAll_heapOrdered_replace {old new : FHNode}
    {parents : List FHFrame}
    (hordered : (closeAll old parents).HeapOrdered)
    (hnew : new.HeapOrdered) (hkey : new.key = old.key) :
    (closeAll new parents).HeapOrdered := by
  induction parents generalizing old new with
  | nil => simpa [closeAll] using hnew
  | cons frame parents ih =>
      have holdParent : (frame.close old).HeapOrdered := by
        apply heapOrdered_focus_of_closeAll
        simpa [closeAll] using hordered
      have hnewParent : (frame.close new).HeapOrdered :=
        close_heapOrdered_replace holdParent hnew hkey
      apply ih (old := frame.close old) (new := frame.close new)
      · simpa [closeAll] using hordered
      · exact hnewParent
      · rfl

/-- Replacing the focused subtree by one with the same degree and mark
preserves the loss invariant through every enclosing zipper frame. -/
theorem closeAll_lossInvariant_replace {old new : FHNode}
    {parents : List FHFrame}
    (hloss : (closeAll old parents).LossInvariant)
    (hnew : new.LossInvariant) (hdegree : new.degree = old.degree)
    (hmarked : new.marked = old.marked) :
    (closeAll new parents).LossInvariant := by
  induction parents generalizing old new with
  | nil => simpa [closeAll] using hnew
  | cons frame parents ih =>
      have holdParent : (frame.close old).LossInvariant := by
        apply lossInvariant_focus_of_closeAll
        simpa [closeAll] using hloss
      have hnewParent : (frame.close new).LossInvariant :=
        close_lossInvariant_replace holdParent hnew hdegree hmarked
      apply ih (old := frame.close old) (new := frame.close new)
      · simpa [closeAll] using hloss
      · exact hnewParent
      · simp [close, FHNode.degree]
      · rfl

/-- A replacement under at least one frame preserves the mark of the rebuilt
root, because every frame supplies that enclosing node's mark. -/
theorem closeAll_marked_eq_of_cons (old new : FHNode) (frame : FHFrame)
    (parents : List FHFrame) :
    (closeAll old (frame :: parents)).marked =
      (closeAll new (frame :: parents)).marked := by
  induction parents generalizing frame old new with
  | nil => rfl
  | cons next parents ih =>
      simpa [closeAll] using
        (ih (frame := next) (old := frame.close old) (new := frame.close new))

/-- Exact key-multiset balance is preserved by any enclosing zipper context. -/
theorem closeAll_keyBag_balance {cut remaining original : FHNode}
    {parents : List FHFrame}
    (hbalance : cut.keyBag + remaining.keyBag = original.keyBag) :
    cut.keyBag + (closeAll remaining parents).keyBag =
      (closeAll original parents).keyBag := by
  induction parents generalizing remaining original with
  | nil => simpa [closeAll] using hbalance
  | cons frame parents ih =>
      apply ih
      simp only [close, FHNode.keyBag_node, FHNode.forestKeyBag_append,
        FHNode.forestKeyBag_cons, FHNode.forestKeyBag_nil]
      rw [← hbalance]
      ac_rfl

/-- Exact subtree-size balance is preserved by any enclosing zipper context. -/
theorem closeAll_size_balance {cut remaining original : FHNode}
    {parents : List FHFrame}
    (hbalance : cut.size + remaining.size = original.size) :
    cut.size + (closeAll remaining parents).size =
      (closeAll original parents).size := by
  induction parents generalizing remaining original with
  | nil => simpa [closeAll] using hbalance
  | cons frame parents ih =>
      apply ih
      simp only [close, FHNode.size_node, List.map_append, List.map_cons,
        List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
      omega

/-- Exact mark-count balance is preserved by every enclosing zipper frame. -/
theorem closeAll_marks_balance {cut remaining original : FHNode}
    {parents : List FHFrame}
    (hbalance : cut.marks + remaining.marks = original.marks) :
    cut.marks + (closeAll remaining parents).marks =
      (closeAll original parents).marks := by
  induction parents generalizing remaining original with
  | nil => simpa [closeAll] using hbalance
  | cons frame parents ih =>
      apply ih
      simp only [close, FHNode.marks_node, List.map_append, List.map_cons,
        List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
      omega

/-- Replacing a focused subtree by one with the same mark count preserves the
mark count of the fully rebuilt root. -/
theorem closeAll_marks_congr {old new : FHNode} {parents : List FHFrame}
    (hmarks : new.marks = old.marks) :
    (closeAll new parents).marks = (closeAll old parents).marks := by
  induction parents generalizing old new with
  | nil => simpa [closeAll] using hmarks
  | cons frame parents ih =>
      apply ih
      simp only [close, FHNode.marks_node, List.map_append, List.map_cons,
        List.sum_append, List.sum_cons]
      omega

/-- The mark-count difference between two focused subtrees is transported
unchanged through every enclosing zipper frame. -/
theorem closeAll_marks_exchange (old new : FHNode)
    (parents : List FHFrame) :
    (closeAll new parents).marks + old.marks =
      (closeAll old parents).marks + new.marks := by
  induction parents generalizing old new with
  | nil => simp [closeAll, add_comm]
  | cons frame parents ih =>
      have houter := ih (frame.close old) (frame.close new)
      have hinner := close_marks_exchange frame old new
      change (closeAll (frame.close new) parents).marks + old.marks =
        (closeAll (frame.close old) parents).marks + new.marks
      omega

/-- Replacing a focused subtree by one of equal size preserves the size of the
fully rebuilt root. -/
theorem closeAll_size_congr {old new : FHNode} {parents : List FHFrame}
    (hsize : new.size = old.size) :
    (closeAll new parents).size = (closeAll old parents).size := by
  induction parents generalizing old new with
  | nil => simpa [closeAll] using hsize
  | cons frame parents ih =>
      apply ih
      simp only [close, FHNode.size_node, List.map_append, List.map_cons,
        List.sum_append, List.sum_cons]
      omega

end FHFrame

/-- A verified zipper focused on one concrete heap-node occurrence. -/
structure FHCursor where
  focus : FHNode
  parents : List FHFrame
  rootsBefore : List FHNode
  rootsAfter : List FHNode
  size : Nat
  minRoot : Option FHNode

namespace FHCursor

/-- Rebuild the selected root from the focused node. -/
def closeNode (cursor : FHCursor) : FHNode :=
  FHFrame.closeAll cursor.focus cursor.parents

/-- Rebuild the complete heap represented by a cursor. -/
def close (cursor : FHCursor) : FH :=
  { roots := cursor.rootsBefore ++ cursor.closeNode :: cursor.rootsAfter
  , size := cursor.size
  , minRoot := cursor.minRoot }

end FHCursor

/-- Split a list around a successful indexed lookup. -/
theorem List.take_append_getElem_drop_of_getElem?_eq_some
    {α : Type} {xs : List α} {i : Nat} {x : α}
    (hget : xs[i]? = some x) :
    xs.take i ++ x :: xs.drop (i + 1) = xs := by
  obtain ⟨hi, hix⟩ := List.getElem?_eq_some_iff.mp hget
  calc
    xs.take i ++ x :: xs.drop (i + 1) =
        xs.take i ++ xs.drop i := by
      rw [List.drop_eq_getElem_cons hi, hix]
    _ = xs := List.take_append_drop i xs

namespace FHNode

/-- Set a node's mark while leaving its key and children unchanged. -/
def markTrue : FHNode → FHNode
  | node key _ children => node key true children

@[simp] theorem markTrue_key (node : FHNode) : node.markTrue.key = node.key := by
  cases node <;> rfl

@[simp] theorem markTrue_marked (node : FHNode) : node.markTrue.marked = true := by
  cases node <;> rfl

@[simp] theorem markTrue_degree (node : FHNode) : node.markTrue.degree = node.degree := by
  cases node <;> rfl

@[simp] theorem markTrue_size (node : FHNode) : node.markTrue.size = node.size := by
  cases node <;> simp [markTrue, size]

/-- Marking an unmarked node adds exactly one marked node. -/
theorem markTrue_marks_of_unmarked {node : FHNode}
    (hmarked : node.marked = false) :
    node.markTrue.marks = node.marks + 1 := by
  cases node with
  | node key marked children =>
      cases marked <;> simp_all [markTrue] <;> omega

@[simp] theorem markTrue_keyBag (node : FHNode) : node.markTrue.keyBag = node.keyBag := by
  cases node <;> simp [markTrue, keyBag, keysList]

/-- Marking a node does not change heap order. -/
theorem markTrue_heapOrdered {node : FHNode} (hordered : node.HeapOrdered) :
    node.markTrue.HeapOrdered := by
  cases node with
  | node key marked children =>
      cases hordered with
      | node hle hall => exact HeapOrdered.node hle hall

/-- Marking a node does not change its own child-loss obligations. -/
theorem markTrue_lossInvariant {node : FHNode} (hloss : node.LossInvariant) :
    node.markTrue.LossInvariant := by
  cases node with
  | node key marked children =>
      cases hloss with
      | node hdeg hall => exact LossInvariant.node hdeg hall

/-- Add one structurally good root to a structurally good forest. -/
theorem forestGood_cons {root : FHNode} {roots : List FHNode}
    (hordered : root.HeapOrdered) (hwellformed : root.Wellformed)
    (hforest : ForestGood roots) : ForestGood (root :: roots) := by
  constructor <;> intro current hcurrent
  · rcases List.mem_cons.mp hcurrent with rfl | hcurrent
    · exact hordered
    · exact hforest.1 current hcurrent
  · rcases List.mem_cons.mp hcurrent with rfl | hcurrent
    · exact hwellformed
    · exact hforest.2 current hcurrent

/-- Add one loss-invariant root to a loss-invariant forest. -/
theorem forestLossInvariant_cons {root : FHNode} {roots : List FHNode}
    (hroot : root.LossInvariant) (hforest : ForestLossInvariant roots) :
    ForestLossInvariant (root :: roots) := by
  intro current hcurrent
  rcases List.mem_cons.mp hcurrent with rfl | hcurrent
  · exact hroot
  · exact hforest current hcurrent

/-- Add one unmarked root to an unmarked root forest. -/
theorem rootsUnmarked_cons {root : FHNode} {roots : List FHNode}
    (hroot : root.marked = false) (hforest : RootsUnmarked roots) :
    RootsUnmarked (root :: roots) := by
  intro current hcurrent
  rcases List.mem_cons.mp hcurrent with rfl | hcurrent
  · exact hroot
  · exact hforest current hcurrent

/-- Concatenate structurally good root forests. -/
theorem forestGood_append {left right : List FHNode}
    (hleft : ForestGood left) (hright : ForestGood right) :
    ForestGood (left ++ right) := by
  constructor <;> intro current hcurrent
  · rcases List.mem_append.mp hcurrent with hcurrent | hcurrent
    · exact hleft.1 current hcurrent
    · exact hright.1 current hcurrent
  · rcases List.mem_append.mp hcurrent with hcurrent | hcurrent
    · exact hleft.2 current hcurrent
    · exact hright.2 current hcurrent

/-- Concatenate loss-invariant root forests. -/
theorem forestLossInvariant_append {left right : List FHNode}
    (hleft : ForestLossInvariant left) (hright : ForestLossInvariant right) :
    ForestLossInvariant (left ++ right) := by
  intro current hcurrent
  rcases List.mem_append.mp hcurrent with hcurrent | hcurrent
  · exact hleft current hcurrent
  · exact hright current hcurrent

/-- Concatenate unmarked root forests. -/
theorem rootsUnmarked_append {left right : List FHNode}
    (hleft : RootsUnmarked left) (hright : RootsUnmarked right) :
    RootsUnmarked (left ++ right) := by
  intro current hcurrent
  rcases List.mem_append.mp hcurrent with hcurrent | hcurrent
  · exact hleft current hcurrent
  · exact hright current hcurrent

/-- Open a path below one root, returning the focus and nearest-first parent
frames. -/
def openChildren : FHNode → List Nat → Option (FHNode × List FHFrame)
  | node k marked children, [] => some (node k marked children, [])
  | node k marked children, i :: path =>
      match children[i]? with
      | none => none
      | some child =>
          match child.openChildren path with
          | none => none
          | some (focus, parents) =>
              some
                (focus,
                  parents ++
                    [{ key := k
                     , marked := marked
                     , before := children.take i
                     , after := children.drop (i + 1) }])

/-- Closing a successfully opened descendant zipper reconstructs the original
root exactly. -/
theorem openChildren_close {root focus : FHNode} {path : List Nat}
    {parents : List FHFrame}
    (hopen : root.openChildren path = some (focus, parents)) :
    FHFrame.closeAll focus parents = root := by
  induction path generalizing root focus parents with
  | nil =>
      cases root
      simp [openChildren] at hopen
      rcases hopen with ⟨rfl, rfl⟩
      rfl
  | cons i path ih =>
      cases root with
      | node k marked children =>
          simp only [openChildren] at hopen
          cases hchild : children[i]? with
          | none => simp [hchild] at hopen
          | some child =>
              cases hdesc : child.openChildren path with
              | none => simp [hchild, hdesc] at hopen
              | some result =>
                  rcases result with ⟨descendant, descendantParents⟩
                  simp [hchild, hdesc] at hopen
                  rcases hopen with ⟨rfl, rfl⟩
                  rw [FHFrame.closeAll, List.foldl_append]
                  simp only [List.foldl_cons, List.foldl_nil]
                  have hclosed := ih hdesc
                  unfold FHFrame.closeAll at hclosed
                  rw [hclosed]
                  simp only [FHFrame.close]
                  rw [List.take_append_getElem_drop_of_getElem?_eq_some hchild]

end FHNode

namespace FH

@[simp] theorem markFalse_marked (node : FHNode) :
    (markFalse node).marked = false := by
  cases node <;> rfl

/-- Open a duplicate-safe occurrence path in a heap. -/
def openPath (h : FH) (path : FHPath) : Option FHCursor :=
  match h.roots[path.root]? with
  | none => none
  | some root =>
      match root.openChildren path.children with
      | none => none
      | some (focus, parents) =>
          some
            { focus := focus
            , parents := parents
            , rootsBefore := h.roots.take path.root
            , rootsAfter := h.roots.drop (path.root + 1)
            , size := h.size
            , minRoot := h.minRoot }

/-- Closing a successfully opened heap path reconstructs the exact heap,
including the cached minimum root. -/
theorem openPath_close {h : FH} {path : FHPath} {cursor : FHCursor}
    (hopen : h.openPath path = some cursor) :
    cursor.close = h := by
  unfold openPath at hopen
  cases hroot : h.roots[path.root]? with
  | none => simp [hroot] at hopen
  | some root =>
      cases hchildren : root.openChildren path.children with
      | none => simp [hroot, hchildren] at hopen
      | some result =>
          rcases result with ⟨focus, parents⟩
          simp [hroot, hchildren] at hopen
          subst cursor
          cases h with
          | mk roots size minRoot =>
              simp only [FHCursor.close, FHCursor.closeNode]
              have hnode : FHFrame.closeAll focus parents = root :=
                FHNode.openChildren_close hchildren
              rw [hnode]
              have hroots :
                  roots.take path.root ++ root :: roots.drop (path.root + 1) = roots :=
                List.take_append_getElem_drop_of_getElem?_eq_some hroot
              rw [hroots]

/-! ## Arbitrary-node CUT and CASCADING-CUT -/

/-- The observable result of a cascading cut.  `cuts` counts promoted nodes;
`cost` counts only the additional cascade iterations after the mandatory
first cut, matching the constant-overhead cost convention used in S3. -/
structure FHCascadeResult where
  heap : FH
  cuts : Nat
  cost : Nat

/-- Internal tree-level result.  Keeping promoted roots separate from the one
rebuilt original root makes node-count and invariant preservation compositional
during a cascade; no recursively produced intermediate is mislabeled as a
complete heap. -/
structure FHCascadeTreeResult where
  promoted : List FHNode
  root : FHNode
  cuts : Nat
  cost : Nat

namespace FHCascadeTreeResult

/-- The root forest contributed by the edited original root occurrence. -/
def roots (result : FHCascadeTreeResult) : List FHNode :=
  result.promoted ++ [result.root]

end FHCascadeTreeResult

/-- Rebuild a heap with a supplied root forest and refresh its minimum cache. -/
def rebuildRoots (cursor : FHCursor) (roots : List FHNode) : FH :=
  { roots := roots
  , size := cursor.size
  , minRoot := computeMinRoot roots }

/-- Potential contribution of a root forest, factored out so zipper-local
potential changes can be proved compositionally. -/
def forestPotential (roots : List FHNode) : Int :=
  Int.ofNat roots.length + 2 * Int.ofNat (FHNode.forestMarks roots)

/-- Potential contribution of a single rooted tree occurrence. -/
def nodePotential (node : FHNode) : Int :=
  1 + 2 * Int.ofNat node.marks

@[simp] theorem forestPotential_nil : forestPotential [] = 0 := by
  simp [forestPotential]

@[simp] theorem forestPotential_cons (root : FHNode) (roots : List FHNode) :
    forestPotential (root :: roots) =
      nodePotential root + forestPotential roots := by
  simp [forestPotential, nodePotential]
  omega

@[simp] theorem forestPotential_append (left right : List FHNode) :
    forestPotential (left ++ right) =
      forestPotential left + forestPotential right := by
  simp [forestPotential]
  omega

/-- The heap potential is exactly the contribution of its root forest. -/
theorem potential_eq_forestPotential (h : FH) :
    h.potential = forestPotential h.roots := rfl

/-- The structural cascading-cut recursion over nearest-first parent frames.
It returns only the roots replacing the selected original root; the complete
heap is rebuilt once, after recursion has finished. -/
def cascadingCutTreeRawAux :
    FHNode → List FHFrame → Option FHCascadeTreeResult
  | _, [] => none
  | focus, [frame] =>
      let cut := markFalse focus
      let parent := frame.removeFocus
      some
        { promoted := [cut]
        , root := markFalse parent
        , cuts := 1
        , cost := 0 }
  | focus, frame :: next :: parents =>
      let cut := markFalse focus
      let parent := frame.removeFocus
      if frame.marked then
        match cascadingCutTreeRawAux parent (next :: parents) with
        | none => none
        | some result =>
            some
              { promoted := cut :: result.promoted
              , root := result.root
              , cuts := result.cuts + 1
              , cost := result.cost + 1 }
      else
        let markedParent := parent.markTrue
        let rebuiltRoot := FHFrame.closeAll markedParent (next :: parents)
        some
          { promoted := [cut]
          , root := rebuiltRoot
          , cuts := 1
          , cost := 0 }

/-- Direct, check-free postcondition for the tree-level cascade recursion. -/
def CascadeTreePost (focus : FHNode) (parents : List FHFrame)
    (result : FHCascadeTreeResult) : Prop :=
  FHNode.forestKeyBag result.roots =
      (FHFrame.closeAll focus parents).keyBag ∧
  FHNode.forestSize result.roots =
      (FHFrame.closeAll focus parents).size ∧
  FHNode.ForestGood result.roots ∧
  FHNode.ForestLossInvariant result.roots ∧
  FHNode.RootsUnmarked result.roots ∧
  result.cuts = result.promoted.length ∧
  result.cost + 1 = result.cuts

/-- The raw structural recursion itself preserves the exact occurrence bag,
node count, heap order, loss invariant, and root-mark rule.  `original` is the
pre-loss version of the current focus stored in the valid enclosing context;
the recursively carried `focus` may already have lost the child promoted by
the preceding cascade step. -/
theorem cascadingCutTreeRawAux_correct {focus original : FHNode}
    {parents : List FHFrame} {result : FHCascadeTreeResult}
    (hfocusOrdered : focus.HeapOrdered)
    (hfocusLoss : focus.LossInvariant)
    (horiginalOrdered :
      (FHFrame.closeAll original parents).HeapOrdered)
    (horiginalLoss :
      (FHFrame.closeAll original parents).LossInvariant)
    (horiginalRootUnmarked :
      (FHFrame.closeAll original parents).marked = false)
    (hraw : cascadingCutTreeRawAux focus parents = some result) :
    CascadeTreePost focus parents result := by
  induction parents generalizing focus original result with
  | nil => simp [cascadingCutTreeRawAux] at hraw
  | cons frame tail ih =>
      cases tail with
      | nil =>
          simp [cascadingCutTreeRawAux] at hraw
          subst result
          have horiginalParentOrdered :
              (frame.close original).HeapOrdered := by
            simpa [FHFrame.closeAll] using horiginalOrdered
          have horiginalParentLoss :
              (frame.close original).LossInvariant := by
            simpa [FHFrame.closeAll] using horiginalLoss
          have hparentOrdered :=
            (FHFrame.close_heapOrdered_remove horiginalParentOrdered).2
          have hparentLoss :=
            (FHFrame.close_lossInvariant_remove horiginalParentLoss).2
          have hcutOrdered := markFalse_heapOrdered focus hfocusOrdered
          have hcutLoss := markFalse_lossInvariant focus hfocusLoss
          have hrootOrdered := markFalse_heapOrdered frame.removeFocus hparentOrdered
          have hrootLoss := markFalse_lossInvariant frame.removeFocus hparentLoss
          have hforestGood : FHNode.ForestGood
              [markFalse focus, markFalse frame.removeFocus] :=
            FHNode.forestGood_cons hcutOrdered
              (FHNode.lossInvariant_wellformed _ hcutLoss)
              (FHNode.forestGood_cons hrootOrdered
                (FHNode.lossInvariant_wellformed _ hrootLoss)
                (by simp [FHNode.ForestGood]))
          have hforestLoss : FHNode.ForestLossInvariant
              [markFalse focus, markFalse frame.removeFocus] :=
            FHNode.forestLossInvariant_cons hcutLoss
              (FHNode.forestLossInvariant_cons hrootLoss
                (by simp [FHNode.ForestLossInvariant]))
          have hrootsUnmarked : FHNode.RootsUnmarked
              [markFalse focus, markFalse frame.removeFocus] :=
            FHNode.rootsUnmarked_cons (markFalse_marked focus)
              (FHNode.rootsUnmarked_cons (markFalse_marked frame.removeFocus)
                (by simp [FHNode.RootsUnmarked]))
          refine ⟨?_, ?_, hforestGood, hforestLoss, hrootsUnmarked, rfl, rfl⟩
          · simp only [FHCascadeTreeResult.roots, List.cons_append,
              List.nil_append, List.append_nil, FHNode.forestKeyBag_cons,
              FHNode.forestKeyBag_nil, FHFrame.closeAll, List.foldl_cons,
              List.foldl_nil]
            rw [markFalse_keyBag, markFalse_keyBag]
            simpa only [add_zero] using
              FHFrame.close_keyBag_balance frame focus
          · simp only [FHCascadeTreeResult.roots, List.cons_append,
              List.nil_append, List.append_nil, FHNode.forestSize_cons,
              FHNode.forestSize_nil, FHFrame.closeAll, List.foldl_cons,
              List.foldl_nil]
            rw [markFalse_size, markFalse_size]
            exact FHFrame.close_size_balance frame focus
      | cons next parents =>
          have horiginalParentOrdered :
              (frame.close original).HeapOrdered := by
            exact FHFrame.heapOrdered_focus_of_closeAll
              (focus := frame.close original) (parents := next :: parents)
              (by simpa [FHFrame.closeAll] using horiginalOrdered)
          have horiginalParentLoss :
              (frame.close original).LossInvariant := by
            exact FHFrame.lossInvariant_focus_of_closeAll
              (focus := frame.close original) (parents := next :: parents)
              (by simpa [FHFrame.closeAll] using horiginalLoss)
          have hparentOrdered :=
            (FHFrame.close_heapOrdered_remove horiginalParentOrdered).2
          have hparentLoss :=
            (FHFrame.close_lossInvariant_remove horiginalParentLoss).2
          have hcutOrdered := markFalse_heapOrdered focus hfocusOrdered
          have hcutLoss := markFalse_lossInvariant focus hfocusLoss
          by_cases hmarked : frame.marked = true
          · cases hrecursive : cascadingCutTreeRawAux frame.removeFocus
                (next :: parents) with
            | none =>
                simp [cascadingCutTreeRawAux, hmarked, hrecursive] at hraw
            | some recursive =>
                simp [cascadingCutTreeRawAux, hmarked, hrecursive] at hraw
                subst result
                have hrecursivePost := ih
                  (focus := frame.removeFocus)
                  (original := frame.close original)
                  (result := recursive)
                  hparentOrdered hparentLoss
                  (by simpa [FHFrame.closeAll] using horiginalOrdered)
                  (by simpa [FHFrame.closeAll] using horiginalLoss)
                  (by simpa [FHFrame.closeAll] using horiginalRootUnmarked)
                  hrecursive
                rcases hrecursivePost with
                  ⟨hbag, hsize, hgood, hloss, hunmarked, hcuts, hcost⟩
                have hnewGood : FHNode.ForestGood
                    (markFalse focus :: recursive.roots) :=
                  FHNode.forestGood_cons hcutOrdered
                    (FHNode.lossInvariant_wellformed _ hcutLoss) hgood
                have hnewLoss : FHNode.ForestLossInvariant
                    (markFalse focus :: recursive.roots) :=
                  FHNode.forestLossInvariant_cons hcutLoss hloss
                have hnewUnmarked : FHNode.RootsUnmarked
                    (markFalse focus :: recursive.roots) :=
                  FHNode.rootsUnmarked_cons (markFalse_marked focus) hunmarked
                refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                · simp only [FHCascadeTreeResult.roots, List.cons_append,
                    FHNode.forestKeyBag_cons, markFalse_keyBag]
                  unfold FHCascadeTreeResult.roots at hbag
                  rw [hbag]
                  simpa [FHFrame.closeAll] using
                    (FHFrame.closeAll_keyBag_balance
                      (parents := next :: parents)
                      (FHFrame.close_keyBag_balance frame focus))
                · simp only [FHCascadeTreeResult.roots, List.cons_append,
                    FHNode.forestSize_cons, markFalse_size]
                  unfold FHCascadeTreeResult.roots at hsize
                  rw [hsize]
                  simpa [FHFrame.closeAll] using
                    (FHFrame.closeAll_size_balance
                      (parents := next :: parents)
                      (FHFrame.close_size_balance frame focus))
                · simpa [FHCascadeTreeResult.roots] using hnewGood
                · simpa [FHCascadeTreeResult.roots] using hnewLoss
                · simpa [FHCascadeTreeResult.roots] using hnewUnmarked
                · simp [hcuts]
                · change recursive.cost + 1 + 1 = recursive.cuts + 1
                  omega
          · have hmarkedFalse : frame.marked = false := by
              cases h : frame.marked <;> simp_all
            simp [cascadingCutTreeRawAux, hmarkedFalse] at hraw
            subst result
            let markedParent := FHNode.markTrue frame.removeFocus
            have hmarkedParentOrdered : markedParent.HeapOrdered :=
              FHNode.markTrue_heapOrdered hparentOrdered
            have hmarkedParentLoss : markedParent.LossInvariant :=
              FHNode.markTrue_lossInvariant hparentLoss
            have holdChildMarked : (frame.close original).marked = false := by
              simpa [FHFrame.close] using hmarkedFalse
            have hdegreeLoss : markedParent.degree + 1 =
                (frame.close original).degree := by
              simp [markedParent, FHNode.markTrue, FHFrame.removeFocus,
                FHFrame.close, FHNode.degree]
              omega
            have hfirstLoss :
                (next.close markedParent).LossInvariant :=
              FHFrame.close_lossInvariant_firstLoss
                (old := frame.close original)
                (new := markedParent)
                (by
                  apply FHFrame.lossInvariant_focus_of_closeAll
                  simpa [FHFrame.closeAll] using horiginalLoss)
                hmarkedParentLoss hdegreeLoss holdChildMarked (by
                  simp [markedParent])
            have hrebuiltLoss :
                (FHFrame.closeAll markedParent (next :: parents)).LossInvariant := by
              apply FHFrame.closeAll_lossInvariant_replace
                (old := next.close (frame.close original))
                (new := next.close markedParent)
                (parents := parents)
              · simpa [FHFrame.closeAll] using horiginalLoss
              · exact hfirstLoss
              · simp [FHFrame.close, FHNode.degree]
              · rfl
            have hrebuiltOrdered :
                (FHFrame.closeAll markedParent (next :: parents)).HeapOrdered :=
              FHFrame.closeAll_heapOrdered_replace
                horiginalOrdered hmarkedParentOrdered (by rfl)
            have hrebuiltUnmarked :
                (FHFrame.closeAll markedParent (next :: parents)).marked = false := by
              rw [← FHFrame.closeAll_marked_eq_of_cons
                (frame.close original) markedParent next parents]
              simpa [FHFrame.closeAll] using horiginalRootUnmarked
            have hforestGood : FHNode.ForestGood
                [markFalse focus,
                  FHFrame.closeAll markedParent (next :: parents)] :=
              FHNode.forestGood_cons hcutOrdered
                (FHNode.lossInvariant_wellformed _ hcutLoss)
                (FHNode.forestGood_cons hrebuiltOrdered
                  (FHNode.lossInvariant_wellformed _ hrebuiltLoss)
                  (by simp [FHNode.ForestGood]))
            have hforestLoss : FHNode.ForestLossInvariant
                [markFalse focus,
                  FHFrame.closeAll markedParent (next :: parents)] :=
              FHNode.forestLossInvariant_cons hcutLoss
                (FHNode.forestLossInvariant_cons hrebuiltLoss
                  (by simp [FHNode.ForestLossInvariant]))
            have hrootsUnmarked : FHNode.RootsUnmarked
                [markFalse focus,
                  FHFrame.closeAll markedParent (next :: parents)] :=
              FHNode.rootsUnmarked_cons (markFalse_marked focus)
                (FHNode.rootsUnmarked_cons hrebuiltUnmarked
                  (by simp [FHNode.RootsUnmarked]))
            refine ⟨?_, ?_, hforestGood, hforestLoss, hrootsUnmarked, rfl, rfl⟩
            · simp only [FHCascadeTreeResult.roots, List.cons_append,
                List.nil_append, List.append_nil, FHNode.forestKeyBag_cons,
                FHNode.forestKeyBag_nil]
              have hlocal :
                  (markFalse focus).keyBag + markedParent.keyBag =
                    (frame.close focus).keyBag := by
                simpa [markedParent, FHNode.markTrue_keyBag,
                  markFalse_keyBag] using
                  FHFrame.close_keyBag_balance frame focus
              simpa only [add_zero, FHFrame.closeAll, List.foldl_cons] using
                (FHFrame.closeAll_keyBag_balance
                  (parents := next :: parents) hlocal)
            · simp only [FHCascadeTreeResult.roots, List.cons_append,
                List.nil_append, List.append_nil, FHNode.forestSize_cons,
                FHNode.forestSize_nil]
              have hlocal :
                  (markFalse focus).size + markedParent.size =
                    (frame.close focus).size := by
                simpa [markedParent, FHNode.markTrue_size,
                  markFalse_size] using FHFrame.close_size_balance frame focus
              change (markFalse focus).size +
                  (FHFrame.closeAll markedParent (next :: parents)).size =
                (FHFrame.closeAll (frame.close focus) (next :: parents)).size
              exact
                (FHFrame.closeAll_size_balance
                  (parents := next :: parents) hlocal)

/-- The cascade recursion pays for every additional cut from the standard
potential.  The stronger focus-mark term is what makes the marked recursive
case close with a constant bound. -/
theorem cascadingCutTreeRawAux_amortized {focus original : FHNode}
    {parents : List FHFrame} {result : FHCascadeTreeResult}
    (horiginalRootUnmarked :
      (FHFrame.closeAll original parents).marked = false)
    (hraw : cascadingCutTreeRawAux focus parents = some result) :
    Int.ofNat result.cost + forestPotential result.roots -
        nodePotential (FHFrame.closeAll focus parents) ≤
      3 - 2 * Int.ofNat (if focus.marked then 1 else 0) := by
  induction parents generalizing focus original result with
  | nil => simp [cascadingCutTreeRawAux] at hraw
  | cons frame tail ih =>
      cases tail with
      | nil =>
          simp [cascadingCutTreeRawAux] at hraw
          subst result
          have hframeUnmarked : frame.marked = false := by
            simpa [FHFrame.closeAll, FHFrame.close] using
              horiginalRootUnmarked
          have hbalance := FHFrame.close_marks_balance frame focus
          have hfocusClear := markFalse_marks_add focus
          have hparentClear := markFalse_marks_add frame.removeFocus
          simp only [FHCascadeTreeResult.cost, Int.ofNat_zero, zero_add,
            FHCascadeTreeResult.roots, List.cons_append, List.nil_append,
            List.append_nil, forestPotential_cons, forestPotential_nil,
            add_zero, FHFrame.closeAll, List.foldl_cons, List.foldl_nil]
          cases hfocusMarked : focus.marked <;>
            simp [nodePotential, hframeUnmarked, hfocusMarked,
              FHFrame.removeFocus] at hbalance hfocusClear hparentClear ⊢ <;>
            omega
      | cons next parents =>
          have hbalanceLocal := FHFrame.close_marks_balance frame focus
          have hbalanceAll := FHFrame.closeAll_marks_balance
            (parents := next :: parents) hbalanceLocal
          have hfocusClear := markFalse_marks_add focus
          by_cases hmarked : frame.marked = true
          · cases hrecursive : cascadingCutTreeRawAux frame.removeFocus
                (next :: parents) with
            | none =>
                simp [cascadingCutTreeRawAux, hmarked, hrecursive] at hraw
            | some recursive =>
                simp [cascadingCutTreeRawAux, hmarked, hrecursive] at hraw
                subst result
                have hrecursiveBound := ih
                  (focus := frame.removeFocus)
                  (original := frame.close original)
                  (result := recursive)
                  (by simpa [FHFrame.closeAll] using horiginalRootUnmarked)
                  hrecursive
                have hparentMarked : frame.removeFocus.marked = true := by
                  simp [FHFrame.removeFocus, hmarked]
                change Int.ofNat (recursive.cost + 1) +
                    forestPotential (markFalse focus :: recursive.roots) -
                    nodePotential
                      (FHFrame.closeAll (frame.close focus) (next :: parents)) ≤
                  3 - 2 * Int.ofNat (if focus.marked then 1 else 0)
                cases hfocusMarked : focus.marked <;>
                  simp [nodePotential, hfocusMarked, hparentMarked] at hrecursiveBound hfocusClear ⊢ <;>
                  omega
          · have hmarkedFalse : frame.marked = false := by
              cases h : frame.marked <;> simp_all
            simp [cascadingCutTreeRawAux, hmarkedFalse] at hraw
            subst result
            let parent := frame.removeFocus
            let markedParent := parent.markTrue
            have hparentUnmarked : parent.marked = false := by
              simp [parent, FHFrame.removeFocus, hmarkedFalse]
            have hmarkedParentMarks : markedParent.marks = parent.marks + 1 := by
              exact FHNode.markTrue_marks_of_unmarked hparentUnmarked
            have htransport := FHFrame.closeAll_marks_exchange parent
              markedParent (next :: parents)
            dsimp [parent, markedParent] at hmarkedParentMarks htransport
            simp only [FHCascadeTreeResult.cost, Int.ofNat_zero, zero_add,
              FHCascadeTreeResult.roots, List.cons_append, List.nil_append,
              List.append_nil, forestPotential_cons, forestPotential_nil,
              add_zero]
            norm_num
            rw [show FHFrame.closeAll focus (frame :: next :: parents) =
                FHFrame.closeAll (frame.close focus) (next :: parents) by rfl]
            cases hfocusMarked : focus.marked <;>
              simp [nodePotential, hfocusMarked] at hfocusClear ⊢ <;>
              omega

/-- The structural cascading-cut state machine on an already dereferenced
cursor.  The nearest parent is edited first.  An unmarked nonroot parent is
marked and stops the cascade; a marked parent is cut recursively. -/
def cascadingCutRaw (cursor : FHCursor) : Option FHCascadeResult :=
  match cascadingCutTreeRawAux cursor.focus cursor.parents with
  | none => none
  | some tree =>
      let roots :=
        cursor.rootsBefore ++ tree.promoted ++ tree.root :: cursor.rootsAfter
      some
        { heap := rebuildRoots cursor roots
        , cuts := tree.cuts
        , cost := tree.cost }

/-- The bundled postcondition certified at the boundary of cascading CUT. -/
def CascadePost (cursor : FHCursor) (result : FHCascadeResult) : Prop :=
  result.heap.keyBag = cursor.close.keyBag ∧
  result.heap.size = cursor.close.size ∧
  result.heap.Valid ∧
  1 ≤ result.cuts

/-- General raw-cascade correctness after the focused subtree has been edited.
`originalFocus` supplies the pre-edit valid enclosing context; the edited focus
itself supplies the subtree invariants and equal-size frame condition. -/
theorem cascadingCutRaw_correct_of_original {cursor : FHCursor}
    {originalFocus : FHNode} {result : FHCascadeResult}
    (hvalid : ({ cursor with focus := originalFocus } : FHCursor).close.Valid)
    (hfocusOrdered : cursor.focus.HeapOrdered)
    (hfocusLoss : cursor.focus.LossInvariant)
    (hfocusSize : cursor.focus.size = originalFocus.size)
    (hcut : cascadingCutRaw cursor = some result) :
    result.heap.keyBag = cursor.close.keyBag ∧
    result.heap.size = cursor.close.size ∧
    result.heap.Valid ∧
    1 ≤ result.cuts := by
  rcases hvalid with ⟨hgood, hloss, hunmarked, hstoredSize, hminimum⟩
  let originalRoot := FHFrame.closeAll originalFocus cursor.parents
  have hselectedMem : originalRoot ∈
      ({ cursor with focus := originalFocus } : FHCursor).close.roots := by
    simp [FHCursor.close, FHCursor.closeNode, originalRoot]
  have hselectedOrdered : originalRoot.HeapOrdered :=
    hgood.1 originalRoot hselectedMem
  have hselectedLoss : originalRoot.LossInvariant :=
    hloss originalRoot hselectedMem
  have hselectedUnmarked : originalRoot.marked = false :=
    hunmarked originalRoot hselectedMem
  cases htree : cascadingCutTreeRawAux cursor.focus cursor.parents with
  | none => simp [cascadingCutRaw, htree] at hcut
  | some tree =>
      simp [cascadingCutRaw, htree] at hcut
      subst result
      have htreePost := cascadingCutTreeRawAux_correct
        (focus := cursor.focus) (original := originalFocus)
        (parents := cursor.parents) (result := tree)
        hfocusOrdered hfocusLoss
        (by simpa [originalRoot] using hselectedOrdered)
        (by simpa [originalRoot] using hselectedLoss)
        (by simpa [originalRoot] using hselectedUnmarked)
        htree
      rcases htreePost with
        ⟨htreeBag, htreeSize, htreeGood, htreeLoss,
          htreeUnmarked, htreeCuts, htreeCost⟩
      have htreeBag' : FHNode.forestKeyBag tree.roots =
          cursor.closeNode.keyBag := by
        simpa [FHCursor.closeNode] using htreeBag
      have htreeSize' : FHNode.forestSize tree.roots =
          cursor.closeNode.size := by
        simpa [FHCursor.closeNode] using htreeSize
      let roots :=
        cursor.rootsBefore ++ tree.promoted ++ tree.root :: cursor.rootsAfter
      have hrootsEq :
          roots = cursor.rootsBefore ++ tree.roots ++ cursor.rootsAfter := by
        simp [roots, FHCascadeTreeResult.roots, List.append_assoc]
      have hbeforeGood : FHNode.ForestGood cursor.rootsBefore := by
        constructor <;> intro current hcurrent
        · exact hgood.1 current (by simp [FHCursor.close, hcurrent])
        · exact hgood.2 current (by simp [FHCursor.close, hcurrent])
      have hafterGood : FHNode.ForestGood cursor.rootsAfter := by
        constructor <;> intro current hcurrent
        · exact hgood.1 current (by simp [FHCursor.close, hcurrent])
        · exact hgood.2 current (by simp [FHCursor.close, hcurrent])
      have hbeforeLoss :
          FHNode.ForestLossInvariant cursor.rootsBefore := by
        intro current hcurrent
        exact hloss current (by simp [FHCursor.close, hcurrent])
      have hafterLoss :
          FHNode.ForestLossInvariant cursor.rootsAfter := by
        intro current hcurrent
        exact hloss current (by simp [FHCursor.close, hcurrent])
      have hbeforeUnmarked : FHNode.RootsUnmarked cursor.rootsBefore := by
        intro current hcurrent
        exact hunmarked current (by simp [FHCursor.close, hcurrent])
      have hafterUnmarked : FHNode.RootsUnmarked cursor.rootsAfter := by
        intro current hcurrent
        exact hunmarked current (by simp [FHCursor.close, hcurrent])
      have hrootsGood : FHNode.ForestGood roots := by
        rw [hrootsEq]
        exact FHNode.forestGood_append
          (FHNode.forestGood_append hbeforeGood htreeGood) hafterGood
      have hrootsLoss : FHNode.ForestLossInvariant roots := by
        rw [hrootsEq]
        exact FHNode.forestLossInvariant_append
          (FHNode.forestLossInvariant_append hbeforeLoss htreeLoss) hafterLoss
      have hrootsUnmarked : FHNode.RootsUnmarked roots := by
        rw [hrootsEq]
        exact FHNode.rootsUnmarked_append
          (FHNode.rootsUnmarked_append hbeforeUnmarked htreeUnmarked)
          hafterUnmarked
      have hrootsBag : FHNode.forestKeyBag roots =
          FHNode.forestKeyBag cursor.close.roots := by
        rw [hrootsEq]
        simp only [FHNode.forestKeyBag_append, htreeBag']
        simp only [FHCursor.close, FHNode.forestKeyBag_append,
          FHNode.forestKeyBag_cons]
        ac_rfl
      have hrootsSize : FHNode.forestSize roots =
          FHNode.forestSize cursor.close.roots := by
        rw [hrootsEq]
        simp only [FHNode.forestSize_append, htreeSize']
        simp only [FHCursor.close, FHNode.forestSize_append,
          FHNode.forestSize_cons]
        omega
      have hstoredSize' : cursor.size = FHNode.forestSize roots := by
        have horiginal : cursor.size =
            FHNode.forestSize
              ({ cursor with focus := originalFocus } : FHCursor).close.roots := by
          simpa [FHCursor.close] using hstoredSize
        have hcurrentSize : FHNode.forestSize cursor.close.roots =
            FHNode.forestSize
              ({ cursor with focus := originalFocus } : FHCursor).close.roots := by
          simp only [FHCursor.close, FHCursor.closeNode,
            FHNode.forestSize_append,
            FHNode.forestSize_cons]
          have hrootSize := FHFrame.closeAll_size_congr
            (parents := cursor.parents) hfocusSize
          omega
        rw [hrootsSize]
        rw [hcurrentSize]
        exact horiginal
      have hresultValid : (rebuildRoots cursor roots).Valid := by
        refine ⟨hrootsGood, hrootsLoss, hrootsUnmarked, hstoredSize', ?_⟩
        simpa [rebuildRoots] using
          computeMinRoot_valid roots cursor.size hrootsGood
      refine ⟨?_, rfl, ?_, ?_⟩
      · simpa [rebuildRoots, keyBag, roots, List.append_assoc] using hrootsBag
      · simpa [roots] using hresultValid
      · change 1 ≤ tree.cuts
        omega

/-- The executable raw cascade directly satisfies the complete heap-level
postcondition; no proposition-valued result filter is involved. -/
theorem cascadingCutRaw_correct {cursor : FHCursor} {result : FHCascadeResult}
    (hvalid : cursor.close.Valid)
    (hcut : cascadingCutRaw cursor = some result) :
    result.heap.keyBag = cursor.close.keyBag ∧
    result.heap.size = cursor.close.size ∧
    result.heap.Valid ∧
    1 ≤ result.cuts := by
  exact cascadingCutRaw_correct_of_original hvalid
    (FHFrame.heapOrdered_focus_of_closeAll
      (hvalid.1.1 cursor.closeNode (by simp [FHCursor.close])))
    (FHFrame.lossInvariant_focus_of_closeAll
      (hvalid.2.1 cursor.closeNode (by simp [FHCursor.close])))
    rfl hcut

/-- The actual additional cascade-iteration charge plus the potential change
is at most three.  A marked focus gives the stronger residual bound used by
the recursive proof. -/
theorem cascadingCutRaw_amortized {cursor : FHCursor}
    {result : FHCascadeResult}
    (hrootUnmarked : cursor.closeNode.marked = false)
    (hcut : cascadingCutRaw cursor = some result) :
    Int.ofNat result.cost + result.heap.potential - cursor.close.potential ≤
      3 - 2 * Int.ofNat (if cursor.focus.marked then 1 else 0) := by
  cases htree : cascadingCutTreeRawAux cursor.focus cursor.parents with
  | none => simp [cascadingCutRaw, htree] at hcut
  | some tree =>
      simp [cascadingCutRaw, htree] at hcut
      subst result
      have htreeBound := cascadingCutTreeRawAux_amortized
        (focus := cursor.focus) (original := cursor.focus)
        (parents := cursor.parents) (result := tree)
        (by simpa [FHCursor.closeNode] using hrootUnmarked) htree
      let roots :=
        cursor.rootsBefore ++
          (tree.promoted ++ tree.root :: cursor.rootsAfter)
      have hresultPotential :
          (rebuildRoots cursor roots).potential =
            forestPotential cursor.rootsBefore +
              forestPotential tree.roots +
              forestPotential cursor.rootsAfter := by
        simp [potential, forestPotential, rebuildRoots, roots,
          FHCascadeTreeResult.roots, List.append_assoc]
        omega
      have hsourcePotential :
          cursor.close.potential =
            forestPotential cursor.rootsBefore +
              nodePotential
                (FHFrame.closeAll cursor.focus cursor.parents) +
              forestPotential cursor.rootsAfter := by
        simp [potential, forestPotential, nodePotential, FHCursor.close,
          FHCursor.closeNode]
        omega
      change Int.ofNat tree.cost + (rebuildRoots cursor roots).potential -
          cursor.close.potential ≤
        3 - 2 * Int.ofNat (if cursor.focus.marked then 1 else 0)
      rw [hresultPotential, hsourcePotential]
      omega

/-- Public executable cascading cut. -/
def cascadingCut (cursor : FHCursor) : Option FHCascadeResult :=
  cascadingCutRaw cursor

/-- A successful cascading cut preserves the exact occurrence bag and node
count, produces a valid heap, and performs at least one CUT. -/
theorem cascadingCut_correct {cursor : FHCursor} {result : FHCascadeResult}
    (hvalid : cursor.close.Valid)
    (hcut : cascadingCut cursor = some result) :
    result.heap.keyBag = cursor.close.keyBag ∧
    result.heap.size = cursor.close.size ∧
    result.heap.Valid ∧
    1 ≤ result.cuts := by
  exact cascadingCutRaw_correct hvalid hcut

/-- Open an arbitrary occurrence path and perform raw CLRS cascading CUT from
its focus. -/
def cutAtPathRaw (h : FH) (path : FHPath) : Option FHCascadeResult :=
  h.openPath path >>= cascadingCutRaw

/-- Public executable arbitrary-occurrence CUT. -/
def cutAtPath (h : FH) (path : FHPath) : Option FHCascadeResult :=
  h.cutAtPathRaw path

/-- A successful arbitrary-path cut preserves the exact heap multiset and
stored size, reestablishes full validity, and performs at least one cut. -/
theorem cutAtPath_raw_correct {h : FH} {path : FHPath}
    {result : FHCascadeResult} (hvalid : h.Valid)
    (hcut : h.cutAtPathRaw path = some result) :
    result.heap.keyBag = h.keyBag ∧
    result.heap.size = h.size ∧
    result.heap.Valid ∧
    1 ≤ result.cuts := by
  unfold cutAtPathRaw at hcut
  cases hopen : h.openPath path with
  | none => simp [hopen] at hcut
  | some cursor =>
      simp only [hopen] at hcut
      have hclose := openPath_close hopen
      have hcursorValid : cursor.close.Valid := by simpa [hclose] using hvalid
      have hcorrect := cascadingCutRaw_correct hcursorValid hcut
      simpa [hclose] using hcorrect

/-- Public arbitrary-path CUT correctness is the raw executable theorem. -/
theorem cutAtPath_correct {h : FH} {path : FHPath}
    {result : FHCascadeResult} (hvalid : h.Valid)
    (hcut : h.cutAtPath path = some result) :
    result.heap.keyBag = h.keyBag ∧
    result.heap.size = h.size ∧
    result.heap.Valid ∧
    1 ≤ result.cuts := by
  exact cutAtPath_raw_correct hvalid hcut

/-! ## Decrease-key and deletion by occurrence handle -/

/-- Replace only a node's key, retaining its mark and child occurrences. -/
def setNodeKey (node : FHNode) (newKey : Int) : FHNode :=
  FHNode.node newKey node.marked node.children

@[simp] theorem setNodeKey_key (node : FHNode) (newKey : Int) :
    (setNodeKey node newKey).key = newKey := by
  cases node <;> rfl

@[simp] theorem setNodeKey_marked (node : FHNode) (newKey : Int) :
    (setNodeKey node newKey).marked = node.marked := by
  cases node <;> rfl

@[simp] theorem setNodeKey_degree (node : FHNode) (newKey : Int) :
    (setNodeKey node newKey).degree = node.degree := by
  cases node <;> rfl

@[simp] theorem setNodeKey_size (node : FHNode) (newKey : Int) :
    (setNodeKey node newKey).size = node.size := by
  cases node <;> simp [setNodeKey]

@[simp] theorem setNodeKey_marks (node : FHNode) (newKey : Int) :
    (setNodeKey node newKey).marks = node.marks := by
  cases node <;> simp [setNodeKey]

/-- Replacing a node key changes exactly its root occurrence in the subtree
multiset, including when the same key occurs elsewhere below it. -/
theorem setNodeKey_keyBag (node : FHNode) (newKey : Int) :
    (setNodeKey node newKey).keyBag =
      node.keyBag.erase node.key + {newKey} := by
  cases node with
  | node key marked children =>
      simp [setNodeKey, FHNode.keyBag_node, Multiset.erase_cons_head,
        Multiset.singleton_add, add_comm]

/-- Decreasing a node key preserves heap order within its own subtree. -/
theorem setNodeKey_heapOrdered {node : FHNode} {newKey : Int}
    (hordered : node.HeapOrdered) (hdecrease : newKey ≤ node.key) :
    (setNodeKey node newKey).HeapOrdered := by
  cases node with
  | node key marked children =>
      cases hordered with
      | node hle hall =>
          exact FHNode.HeapOrdered.node
            (fun child hchild => le_trans hdecrease (hle child hchild)) hall

/-- Key replacement does not affect mark-aware child-loss obligations. -/
theorem setNodeKey_lossInvariant {node : FHNode} {newKey : Int}
    (hloss : node.LossInvariant) :
    (setNodeKey node newKey).LossInvariant := by
  cases node with
  | node key marked children =>
      cases hloss with
      | node hdeg hall => exact FHNode.LossInvariant.node hdeg hall

/-- A decreased child whose new key still respects its parent edge can replace
the old child while preserving that parent's heap order. -/
theorem FHFrame.close_heapOrdered_decrease {frame : FHFrame}
    {old new : FHNode} (hordered : (frame.close old).HeapOrdered)
    (hnew : new.HeapOrdered) (hparent : frame.key ≤ new.key) :
    (frame.close new).HeapOrdered := by
  cases hordered with
  | node hle hall =>
      refine FHNode.HeapOrdered.node ?_ ?_
      · intro current hcurrent
        simp only [FHFrame.close, List.mem_append, List.mem_cons] at hcurrent ⊢
        rcases hcurrent with hbefore | rfl | hafter
        · exact hle current (by simp [hbefore])
        · exact hparent
        · exact hle current (by simp [hafter])
      · intro current hcurrent
        simp only [FHFrame.close, List.mem_append, List.mem_cons] at hcurrent ⊢
        rcases hcurrent with hbefore | rfl | hafter
        · exact hall current (by simp [hbefore])
        · exact hnew
        · exact hall current (by simp [hafter])

/-- A nonviolating decrease preserves heap order through the complete zipper
context. -/
theorem FHFrame.closeAll_heapOrdered_decrease {old new : FHNode}
    {frame : FHFrame} {parents : List FHFrame}
    (hordered : (FHFrame.closeAll old (frame :: parents)).HeapOrdered)
    (hnew : new.HeapOrdered) (hparent : frame.key ≤ new.key) :
    (FHFrame.closeAll new (frame :: parents)).HeapOrdered := by
  have holdParent : (frame.close old).HeapOrdered :=
    FHFrame.heapOrdered_focus_of_closeAll
      (by simpa [FHFrame.closeAll] using hordered)
  have hnewParent := FHFrame.close_heapOrdered_decrease
    holdParent hnew hparent
  exact FHFrame.closeAll_heapOrdered_replace
    (old := frame.close old) (new := frame.close new) (parents := parents)
    (by simpa [FHFrame.closeAll] using hordered) hnewParent rfl

/-- Refresh only the persistent minimum-root cache of a heap. -/
def refreshMinimum (h : FH) : FH :=
  { roots := h.roots
  , size := h.size
  , minRoot := computeMinRoot h.roots }

@[simp] theorem refreshMinimum_potential (h : FH) :
    (refreshMinimum h).potential = h.potential := rfl

/-- Replacing only the focused key leaves the complete heap potential
unchanged. -/
theorem close_setNodeKey_potential (cursor : FHCursor) (newKey : Int) :
    ({ cursor with focus := setNodeKey cursor.focus newKey } : FHCursor).close.potential =
      cursor.close.potential := by
  have hrootMarks := FHFrame.closeAll_marks_congr
    (parents := cursor.parents) (setNodeKey_marks cursor.focus newKey)
  unfold potential
  simp [FHCursor.close, FHCursor.closeNode, hrootMarks]

/-- The addressed root-key occurrence remains present in its subtree bag. -/
theorem focus_key_mem_keyBag (node : FHNode) : node.key ∈ node.keyBag := by
  cases node
  simp [FHNode.keyBag_node]

/-- Closing a cursor after replacing its focused node key performs exactly one
occurrence replacement in the complete heap multiset. -/
theorem close_setNodeKey_keyBag (cursor : FHCursor) (newKey : Int) :
    ({ cursor with focus := setNodeKey cursor.focus newKey } : FHCursor).close.keyBag =
      cursor.close.keyBag.erase cursor.focus.key + {newKey} := by
  let oldRoot := FHFrame.closeAll cursor.focus cursor.parents
  let newRoot :=
    FHFrame.closeAll (setNodeKey cursor.focus newKey) cursor.parents
  have hfocusMem := focus_key_mem_keyBag cursor.focus
  have hrootUpdate : newRoot.keyBag =
      oldRoot.keyBag.erase cursor.focus.key + {newKey} := by
    exact FHFrame.closeAll_keyBag_update hfocusMem
      (setNodeKey_keyBag cursor.focus newKey)
  have hrootMem : cursor.focus.key ∈ oldRoot.keyBag :=
    FHFrame.closeAll_mem_keyBag hfocusMem
  let context := FHNode.forestKeyBag cursor.rootsBefore +
    FHNode.forestKeyBag cursor.rootsAfter
  have holdForest : cursor.close.keyBag = oldRoot.keyBag + context := by
    simp only [FHCursor.close, keyBag, FHNode.forestKeyBag_append,
      FHNode.forestKeyBag_cons, oldRoot, context]
    ac_rfl
  have hnewForest :
      ({ cursor with focus := setNodeKey cursor.focus newKey } : FHCursor).close.keyBag =
        newRoot.keyBag + context := by
    simp only [FHCursor.close, FHCursor.closeNode, keyBag,
      FHNode.forestKeyBag_append, FHNode.forestKeyBag_cons, newRoot, context]
    ac_rfl
  rw [hnewForest, holdForest, hrootUpdate]
  rw [Multiset.erase_add_left_pos context hrootMem]
  ac_rfl

/-- Key replacement leaves the represented node count unchanged after closing
the cursor. -/
theorem close_setNodeKey_size (cursor : FHCursor) (newKey : Int) :
    ({ cursor with focus := setNodeKey cursor.focus newKey } : FHCursor).close.size =
      cursor.close.size := rfl

/-- If the rebuilt selected root is heap-ordered, refreshing the minimum cache
after a focused key replacement reestablishes full heap validity. -/
theorem refreshMinimum_setNodeKey_close_valid (cursor : FHCursor) (newKey : Int)
    (hvalid : cursor.close.Valid)
    (hnewRootOrdered :
      (FHFrame.closeAll (setNodeKey cursor.focus newKey)
        cursor.parents).HeapOrdered) :
    (refreshMinimum
      ({ cursor with focus := setNodeKey cursor.focus newKey } : FHCursor).close).Valid := by
  rcases hvalid with ⟨hgood, hloss, hunmarked, hstoredSize, hminimum⟩
  have holdRootMem : cursor.closeNode ∈ cursor.close.roots := by
    simp [FHCursor.close]
  have holdRootLoss : cursor.closeNode.LossInvariant :=
    hloss cursor.closeNode holdRootMem
  have holdRootUnmarked : cursor.closeNode.marked = false :=
    hunmarked cursor.closeNode holdRootMem
  have hfocusLoss : cursor.focus.LossInvariant :=
    FHFrame.lossInvariant_focus_of_closeAll
      (by simpa [FHCursor.closeNode] using holdRootLoss)
  have hnewFocusLoss : (setNodeKey cursor.focus newKey).LossInvariant :=
    setNodeKey_lossInvariant hfocusLoss
  have hnewRootLoss :
      (FHFrame.closeAll (setNodeKey cursor.focus newKey)
        cursor.parents).LossInvariant :=
    FHFrame.closeAll_lossInvariant_replace
      (by simpa [FHCursor.closeNode] using holdRootLoss)
      hnewFocusLoss (setNodeKey_degree cursor.focus newKey)
      (setNodeKey_marked cursor.focus newKey)
  have hnewRootUnmarked :
      (FHFrame.closeAll (setNodeKey cursor.focus newKey)
        cursor.parents).marked = false := by
    cases hparents : cursor.parents with
    | nil =>
        have hold : cursor.focus.marked = false := by
          simpa [FHCursor.closeNode, hparents, FHFrame.closeAll] using
            holdRootUnmarked
        simpa [hparents, FHFrame.closeAll] using hold
    | cons frame parents =>
        rw [← FHFrame.closeAll_marked_eq_of_cons cursor.focus
          (setNodeKey cursor.focus newKey) frame parents]
        simpa [FHCursor.closeNode, hparents] using holdRootUnmarked
  have hbeforeGood : FHNode.ForestGood cursor.rootsBefore := by
    constructor <;> intro current hcurrent
    · exact hgood.1 current (by simp [FHCursor.close, hcurrent])
    · exact hgood.2 current (by simp [FHCursor.close, hcurrent])
  have hafterGood : FHNode.ForestGood cursor.rootsAfter := by
    constructor <;> intro current hcurrent
    · exact hgood.1 current (by simp [FHCursor.close, hcurrent])
    · exact hgood.2 current (by simp [FHCursor.close, hcurrent])
  have hbeforeLoss : FHNode.ForestLossInvariant cursor.rootsBefore := by
    intro current hcurrent
    exact hloss current (by simp [FHCursor.close, hcurrent])
  have hafterLoss : FHNode.ForestLossInvariant cursor.rootsAfter := by
    intro current hcurrent
    exact hloss current (by simp [FHCursor.close, hcurrent])
  have hbeforeUnmarked : FHNode.RootsUnmarked cursor.rootsBefore := by
    intro current hcurrent
    exact hunmarked current (by simp [FHCursor.close, hcurrent])
  have hafterUnmarked : FHNode.RootsUnmarked cursor.rootsAfter := by
    intro current hcurrent
    exact hunmarked current (by simp [FHCursor.close, hcurrent])
  let newRoot :=
    FHFrame.closeAll (setNodeKey cursor.focus newKey) cursor.parents
  let roots := cursor.rootsBefore ++ newRoot :: cursor.rootsAfter
  have hrootsGood : FHNode.ForestGood roots := by
    constructor <;> intro current hcurrent
    · simp only [roots, List.mem_append, List.mem_cons] at hcurrent
      rcases hcurrent with hbefore | rfl | hafter
      · exact hbeforeGood.1 current hbefore
      · exact hnewRootOrdered
      · exact hafterGood.1 current hafter
    · simp only [roots, List.mem_append, List.mem_cons] at hcurrent
      rcases hcurrent with hbefore | rfl | hafter
      · exact hbeforeGood.2 current hbefore
      · exact FHNode.lossInvariant_wellformed _ hnewRootLoss
      · exact hafterGood.2 current hafter
  have hrootsLoss : FHNode.ForestLossInvariant roots := by
    intro current hcurrent
    simp only [roots, List.mem_append, List.mem_cons] at hcurrent
    rcases hcurrent with hbefore | rfl | hafter
    · exact hbeforeLoss current hbefore
    · exact hnewRootLoss
    · exact hafterLoss current hafter
  have hrootsUnmarked : FHNode.RootsUnmarked roots := by
    intro current hcurrent
    simp only [roots, List.mem_append, List.mem_cons] at hcurrent
    rcases hcurrent with hbefore | rfl | hafter
    · exact hbeforeUnmarked current hbefore
    · exact hnewRootUnmarked
    · exact hafterUnmarked current hafter
  have hnewRootSize : newRoot.size = cursor.closeNode.size := by
    exact FHFrame.closeAll_size_congr (setNodeKey_size cursor.focus newKey)
  have hrootsSize : cursor.size = FHNode.forestSize roots := by
    have holdSize : cursor.size = FHNode.forestSize cursor.close.roots := by
      simpa [FHCursor.close] using hstoredSize
    simp only [roots, FHCursor.close, FHNode.forestSize_append,
      FHNode.forestSize_cons] at holdSize ⊢
    omega
  change Valid (refreshMinimum
    ({ cursor with focus := setNodeKey cursor.focus newKey } : FHCursor).close)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [refreshMinimum, FHCursor.close, FHCursor.closeNode, roots, newRoot]
      using hrootsGood
  · simpa [refreshMinimum, FHCursor.close, FHCursor.closeNode, roots, newRoot]
      using hrootsLoss
  · simpa [refreshMinimum, FHCursor.close, FHCursor.closeNode, roots, newRoot]
      using hrootsUnmarked
  · simpa [refreshMinimum, FHCursor.close, FHCursor.closeNode, roots, newRoot]
      using hrootsSize
  · simpa [refreshMinimum, FHCursor.close, FHCursor.closeNode, roots, newRoot]
      using computeMinRoot_valid roots cursor.size hrootsGood

/-- Result of a handle-directed key update or deletion. -/
structure FHUpdateResult where
  oldKey : Int
  heap : FH
  cost : Nat

/-- Raw handle-directed decrease-key.  A root or a nonviolating edge closes
directly; a newly violating parent edge invokes the cascading-cut machine. -/
def decreaseKeyAtRaw (h : FH) (path : FHPath) (newKey : Int) :
    Option FHUpdateResult := do
    let cursor ← h.openPath path
    if newKey ≤ cursor.focus.key then
      let updatedCursor : FHCursor :=
        { cursor with focus := setNodeKey cursor.focus newKey }
      match updatedCursor.parents with
      | [] =>
          some
            { oldKey := cursor.focus.key
            , heap := refreshMinimum updatedCursor.close
            , cost := 0 }
      | parent :: _ =>
          if newKey < parent.key then
            let cut ← cascadingCutRaw updatedCursor
            some
              { oldKey := cursor.focus.key
              , heap := cut.heap
              , cost := cut.cost }
          else
            some
              { oldKey := cursor.focus.key
              , heap := refreshMinimum updatedCursor.close
              , cost := 0 }
    else none

/-- Exact occurrence-level postcondition for decrease-key. -/
def DecreasePost (h : FH) (newKey : Int) (result : FHUpdateResult) : Prop :=
  newKey ≤ result.oldKey ∧
  result.heap.keyBag = h.keyBag.erase result.oldKey + {newKey} ∧
  result.heap.size = h.size ∧
  result.heap.Valid

/-- The raw executable decrease-key directly replaces the addressed occurrence
and preserves full heap validity. -/
theorem decreaseKeyAtRaw_correct {h : FH} {path : FHPath} {newKey : Int}
    {result : FHUpdateResult} (hvalid : h.Valid)
    (hdec : h.decreaseKeyAtRaw path newKey = some result) :
    newKey ≤ result.oldKey ∧
    result.heap.keyBag = h.keyBag.erase result.oldKey + {newKey} ∧
    result.heap.size = h.size ∧
    result.heap.Valid := by
  unfold decreaseKeyAtRaw at hdec
  cases hopen : h.openPath path with
  | none => simp [hopen] at hdec
  | some cursor =>
      simp only [hopen, Option.bind_eq_bind, Option.bind_some] at hdec
      have hclose := openPath_close hopen
      have hcursorValid : cursor.close.Valid := by simpa [hclose] using hvalid
      have holdRootOrdered : cursor.closeNode.HeapOrdered :=
        hcursorValid.1.1 cursor.closeNode (by simp [FHCursor.close])
      have hfocusOrdered : cursor.focus.HeapOrdered :=
        FHFrame.heapOrdered_focus_of_closeAll
          (by simpa [FHCursor.closeNode] using holdRootOrdered)
      have holdRootLoss : cursor.closeNode.LossInvariant :=
        hcursorValid.2.1 cursor.closeNode (by simp [FHCursor.close])
      have hfocusLoss : cursor.focus.LossInvariant :=
        FHFrame.lossInvariant_focus_of_closeAll
          (by simpa [FHCursor.closeNode] using holdRootLoss)
      by_cases hdecrease : newKey ≤ cursor.focus.key
      · rw [if_pos hdecrease] at hdec
        let updated : FHCursor :=
          { cursor with focus := setNodeKey cursor.focus newKey }
        have hnewFocusOrdered : updated.focus.HeapOrdered := by
          exact setNodeKey_heapOrdered hfocusOrdered hdecrease
        have hnewFocusLoss : updated.focus.LossInvariant := by
          exact setNodeKey_lossInvariant hfocusLoss
        have hnewFocusSize : updated.focus.size = cursor.focus.size := by
          exact setNodeKey_size cursor.focus newKey
        have hupdatedBag : updated.close.keyBag =
            cursor.close.keyBag.erase cursor.focus.key + {newKey} := by
          simpa [updated] using close_setNodeKey_keyBag cursor newKey
        cases hparents : cursor.parents with
        | nil =>
            simp [updated, hparents] at hdec
            subst result
            have hnewRootOrdered :
                (FHFrame.closeAll (setNodeKey cursor.focus newKey) []).HeapOrdered := by
              simpa [FHFrame.closeAll] using hnewFocusOrdered
            have hresultValid := refreshMinimum_setNodeKey_close_valid
              cursor newKey hcursorValid
              (by simpa [hparents] using hnewRootOrdered)
            refine ⟨hdecrease, ?_, ?_, ?_⟩
            · simpa [updated, refreshMinimum, keyBag, hclose, hparents] using
                hupdatedBag
            · simpa [FHCursor.close, updated, refreshMinimum, hparents] using
                congrArg FH.size hclose
            · simpa [hparents] using hresultValid
        | cons parent parents =>
            by_cases hviolates : newKey < parent.key
            · simp only [hparents, hviolates, if_true] at hdec
              obtain ⟨cut, hcutExplicit, hresult⟩ :=
                Option.bind_eq_some_iff.mp hdec
              simp at hresult
              subst result
              have hcut : cascadingCutRaw updated = some cut := by
                simpa [updated, hparents] using hcutExplicit
              have hsourceValid :
                  ({ updated with focus := cursor.focus } : FHCursor).close.Valid := by
                simpa [updated] using hcursorValid
              have hcascade := cascadingCutRaw_correct_of_original
                (cursor := updated) (originalFocus := cursor.focus)
                (result := cut) hsourceValid hnewFocusOrdered hnewFocusLoss
                hnewFocusSize hcut
              refine ⟨hdecrease, ?_, ?_, hcascade.2.2.1⟩
              · rw [hcascade.1, hupdatedBag, hclose]
              · rw [hcascade.2.1]
                simpa [updated, FHCursor.close] using congrArg FH.size hclose
            · have hparent : parent.key ≤ newKey := le_of_not_gt hviolates
              have hnewRootOrdered :
                  (FHFrame.closeAll (setNodeKey cursor.focus newKey)
                    (parent :: parents)).HeapOrdered :=
                FHFrame.closeAll_heapOrdered_decrease
                  (by simpa [FHCursor.closeNode, hparents] using holdRootOrdered)
                  hnewFocusOrdered hparent
              simp [updated, hparents, hviolates] at hdec
              subst result
              have hresultValid := refreshMinimum_setNodeKey_close_valid
                cursor newKey hcursorValid
                (by simpa [hparents] using hnewRootOrdered)
              refine ⟨hdecrease, ?_, ?_, ?_⟩
              · simpa [updated, refreshMinimum, keyBag, hclose, hparents] using
                  hupdatedBag
              · simpa [FHCursor.close, updated, refreshMinimum, hparents] using
                  congrArg FH.size hclose
              · simpa [hparents] using hresultValid
      · rw [if_neg hdecrease] at hdec
        contradiction

/-- Raw handle-directed decrease-key has constant amortized cost under the
additional-cascade-iterations convention stored in `FHUpdateResult.cost`. -/
theorem decreaseKeyAtRaw_amortized {h : FH} {path : FHPath} {newKey : Int}
    {result : FHUpdateResult} (hvalid : h.Valid)
    (hdec : h.decreaseKeyAtRaw path newKey = some result) :
    Int.ofNat result.cost + result.heap.potential - h.potential ≤ 3 := by
  unfold decreaseKeyAtRaw at hdec
  cases hopen : h.openPath path with
  | none => simp [hopen] at hdec
  | some cursor =>
      simp only [hopen, Option.bind_eq_bind, Option.bind_some] at hdec
      have hclose := openPath_close hopen
      have hcursorValid : cursor.close.Valid := by simpa [hclose] using hvalid
      have hsourcePotential (key : Int) :
          ({ cursor with focus := setNodeKey cursor.focus key } : FHCursor).close.potential =
            h.potential := by
        rw [close_setNodeKey_potential, hclose]
      by_cases hdecrease : newKey ≤ cursor.focus.key
      · rw [if_pos hdecrease] at hdec
        let updated : FHCursor :=
          { cursor with focus := setNodeKey cursor.focus newKey }
        cases hparents : cursor.parents with
        | nil =>
            simp [updated, hparents] at hdec
            subst result
            simp only [FHUpdateResult.cost, Int.ofNat_zero, zero_add,
              FHUpdateResult.heap]
            rw [refreshMinimum_potential]
            have hpotential := hsourcePotential newKey
            simp [updated, hparents] at hpotential
            rw [hpotential]
            norm_num
        | cons parent parents =>
            by_cases hviolates : newKey < parent.key
            · simp only [hparents, hviolates, if_true] at hdec
              obtain ⟨cut, hcutExplicit, hresult⟩ :=
                Option.bind_eq_some_iff.mp hdec
              simp at hresult
              subst result
              have hcut : cascadingCutRaw updated = some cut := by
                simpa [updated, hparents] using hcutExplicit
              have holdRootUnmarked : cursor.closeNode.marked = false :=
                hcursorValid.2.2.1 cursor.closeNode (by simp [FHCursor.close])
              have hupdatedRootUnmarked : updated.closeNode.marked = false := by
                have hnew :
                    (FHFrame.closeAll (setNodeKey cursor.focus newKey)
                      (parent :: parents)).marked = false := by
                  rw [← FHFrame.closeAll_marked_eq_of_cons cursor.focus
                    (setNodeKey cursor.focus newKey) parent parents]
                  simpa [FHCursor.closeNode, hparents] using holdRootUnmarked
                simpa [updated, FHCursor.closeNode, hparents] using hnew
              have hbound := cascadingCutRaw_amortized
                hupdatedRootUnmarked hcut
              have hpotential : updated.close.potential = h.potential := by
                simpa [updated] using hsourcePotential newKey
              change Int.ofNat cut.cost + cut.heap.potential - h.potential ≤ 3
              rw [← hpotential]
              have hindicator :
                  0 ≤ Int.ofNat (if updated.focus.marked then 1 else 0) :=
                Int.natCast_nonneg (if updated.focus.marked then 1 else 0)
              omega
            · simp [updated, hparents, hviolates] at hdec
              subst result
              simp only [FHUpdateResult.cost, Int.ofNat_zero, zero_add,
                FHUpdateResult.heap]
              rw [refreshMinimum_potential]
              have hpotential := hsourcePotential newKey
              simp [updated, hparents] at hpotential
              rw [hpotential]
              norm_num
      · rw [if_neg hdecrease] at hdec
        contradiction

/-- The `oldKey` returned by raw decrease-key is the key of the occurrence
selected by the supplied path, rather than merely some equal heap key. -/
theorem decreaseKeyAtRaw_oldKey {h : FH} {path : FHPath} {newKey : Int}
    {result : FHUpdateResult}
    (hdec : h.decreaseKeyAtRaw path newKey = some result) :
    ∃ cursor, h.openPath path = some cursor ∧
      result.oldKey = cursor.focus.key := by
  unfold decreaseKeyAtRaw at hdec
  cases hopen : h.openPath path with
  | none => simp [hopen] at hdec
  | some cursor =>
      simp only [hopen, Option.bind_eq_bind, Option.bind_some] at hdec
      by_cases hdecrease : newKey ≤ cursor.focus.key
      · rw [if_pos hdecrease] at hdec
        let updated : FHCursor :=
          { cursor with focus := setNodeKey cursor.focus newKey }
        cases hparents : cursor.parents with
        | nil =>
            simp [updated, hparents] at hdec
            subst result
            exact ⟨cursor, rfl, rfl⟩
        | cons parent parents =>
            by_cases hviolates : newKey < parent.key
            · simp only [hparents, hviolates, if_true] at hdec
              obtain ⟨cut, hcut, hresult⟩ :=
                Option.bind_eq_some_iff.mp hdec
              simp at hresult
              subst result
              exact ⟨cursor, rfl, rfl⟩
            · simp [updated, hparents, hviolates] at hdec
              subst result
              exact ⟨cursor, rfl, rfl⟩
      · rw [if_neg hdecrease] at hdec
        contradiction

/-- Public executable occurrence-level decrease-key. -/
def decreaseKeyAt (h : FH) (path : FHPath) (newKey : Int) :
    Option FHUpdateResult :=
  h.decreaseKeyAtRaw path newKey

/-- Successful handle-directed decrease-key replaces exactly the addressed
occurrence, preserves node count, and preserves full heap validity. -/
theorem decreaseKeyAt_correct {h : FH} {path : FHPath} {newKey : Int}
    {result : FHUpdateResult} (hvalid : h.Valid)
    (hdec : h.decreaseKeyAt path newKey = some result) :
    newKey ≤ result.oldKey ∧
    result.heap.keyBag = h.keyBag.erase result.oldKey + {newKey} ∧
    result.heap.size = h.size ∧
    result.heap.Valid := by
  exact decreaseKeyAtRaw_correct hvalid hdec

/-- Raw CLRS deletion: decrease the addressed occurrence strictly below the
cached minimum and then extract that unique sentinel occurrence. -/
def deleteAtRaw (h : FH) (path : FHPath) : Option FHUpdateResult := do
    let cursor ← h.openPath path
    let minimum ← h.minimum
    let decreased ← h.decreaseKeyAtRaw path (minimum - 1)
    let (_, heap) ← decreased.heap.extractMin
    pure
      { oldKey := cursor.focus.key
      , heap := heap
      , cost := decreased.cost + 1 }

/-- Exact occurrence-level deletion postcondition. -/
def DeletePost (h : FH) (result : FHUpdateResult) : Prop :=
  result.heap.keyBag = h.keyBag.erase result.oldKey ∧
  result.heap.size + 1 = h.size ∧
  result.heap.Valid

/-- Raw deletion removes exactly the occurrence addressed by the path,
decreases the stored size by one, and preserves full heap validity. -/
theorem deleteAtRaw_correct {h : FH} {path : FHPath}
    {result : FHUpdateResult} (hvalid : h.Valid)
    (hdelete : h.deleteAtRaw path = some result) :
    result.heap.keyBag = h.keyBag.erase result.oldKey ∧
    result.heap.size + 1 = h.size ∧
    result.heap.Valid := by
  unfold deleteAtRaw at hdelete
  cases hopen : h.openPath path with
  | none => simp [hopen] at hdelete
  | some cursor =>
      simp only [hopen, Option.bind_eq_bind, Option.bind_some] at hdelete
      cases hmin : h.minimum with
      | none => simp [hmin] at hdelete
      | some minimum =>
          simp only [hmin, Option.bind_eq_bind, Option.bind_some] at hdelete
          cases hdec : h.decreaseKeyAtRaw path (minimum - 1) with
          | none => simp [hdec] at hdelete
          | some decreased =>
              simp only [hdec, Option.bind_eq_bind, Option.bind_some] at hdelete
              cases hextract : decreased.heap.extractMin with
              | none => simp [hextract] at hdelete
              | some pair =>
                  rcases pair with ⟨extracted, heap⟩
                  simp [hextract] at hdelete
                  subst result
                  have hdecreased := decreaseKeyAtRaw_correct hvalid hdec
                  have holdKeyPath := decreaseKeyAtRaw_oldKey hdec
                  obtain ⟨selected, hselected, holdKey⟩ := holdKeyPath
                  rw [hopen] at hselected
                  cases hselected
                  have hdecreasedBag :
                      decreased.heap.keyBag =
                        h.keyBag.erase cursor.focus.key + {minimum - 1} := by
                    simpa [holdKey] using hdecreased.2.1
                  have hdecreasedValid : decreased.heap.Valid :=
                    hdecreased.2.2.2
                  have hextractCorrect :=
                    extractMin_correct hdecreasedValid hextract
                  have hsentinelMem :
                      minimum - 1 ∈ decreased.heap.keyBag := by
                    rw [hdecreasedBag]
                    simp
                  have hextractedLe : extracted ≤ minimum - 1 :=
                    hextractCorrect.2.1 (minimum - 1) hsentinelMem
                  have hextractedEq : extracted = minimum - 1 := by
                    have hextractedMem := hextractCorrect.1
                    rw [hdecreasedBag, Multiset.mem_add] at hextractedMem
                    rcases hextractedMem with hremaining | hsentinel
                    · have horiginal : extracted ∈ h.keyBag :=
                        Multiset.mem_of_mem_erase hremaining
                      have hminimumLe : minimum ≤ extracted :=
                        minimum_le_keyBag hvalid.2.2.2.2 hmin horiginal
                      omega
                    · simpa using hsentinel
                  refine ⟨?_, ?_, hextractCorrect.2.2.2.1⟩
                  · rw [hextractCorrect.2.2.1, hextractedEq,
                      hdecreasedBag,
                      Multiset.erase_add_right_pos
                        (h.keyBag.erase cursor.focus.key) (by simp)]
                    simp
                  · have hextractSize :=
                      extractMin_size hdecreasedValid hextract
                    have hdecreasedSize : decreased.heap.size = h.size :=
                      hdecreased.2.2.1
                    change heap.size + 1 = h.size
                    omega

/-- Certified handle-directed deletion. -/
def deleteAt (h : FH) (path : FHPath) : Option FHUpdateResult :=
  h.deleteAtRaw path

/-- Successful handle-directed deletion removes exactly the addressed
occurrence, decreases node count by one, and preserves full validity. -/
theorem deleteAt_correct {h : FH} {path : FHPath} {result : FHUpdateResult}
    (hvalid : h.Valid) (hdelete : h.deleteAt path = some result) :
    result.heap.keyBag = h.keyBag.erase result.oldKey ∧
    result.heap.size + 1 = h.size ∧
    result.heap.Valid := by
  exact deleteAtRaw_correct hvalid hdelete

end FH

end Chapter19
end CLRS

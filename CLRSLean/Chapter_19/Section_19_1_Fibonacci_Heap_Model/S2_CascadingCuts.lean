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

/-- Removing and promoting a focused child preserves the exact node-count
balance. -/
theorem close_size_balance (frame : FHFrame) (child : FHNode) :
    child.size + frame.removeFocus.size = (frame.close child).size := by
  simp [close, removeFocus, FHNode.forestSize_append]
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

/-- The executable raw cascade directly satisfies the complete heap-level
postcondition; no proposition-valued result filter is involved. -/
theorem cascadingCutRaw_correct {cursor : FHCursor} {result : FHCascadeResult}
    (hvalid : cursor.close.Valid)
    (hcut : cascadingCutRaw cursor = some result) :
    result.heap.keyBag = cursor.close.keyBag ∧
    result.heap.size = cursor.close.size ∧
    result.heap.Valid ∧
    1 ≤ result.cuts := by
  rcases hvalid with ⟨hgood, hloss, hunmarked, hstoredSize, hminimum⟩
  have hselectedMem : cursor.closeNode ∈ cursor.close.roots := by
    simp [FHCursor.close]
  have hselectedOrdered : cursor.closeNode.HeapOrdered :=
    hgood.1 cursor.closeNode hselectedMem
  have hselectedLoss : cursor.closeNode.LossInvariant :=
    hloss cursor.closeNode hselectedMem
  have hselectedUnmarked : cursor.closeNode.marked = false :=
    hunmarked cursor.closeNode hselectedMem
  cases htree : cascadingCutTreeRawAux cursor.focus cursor.parents with
  | none => simp [cascadingCutRaw, htree] at hcut
  | some tree =>
      simp [cascadingCutRaw, htree] at hcut
      subst result
      have htreePost := cascadingCutTreeRawAux_correct
        (focus := cursor.focus) (original := cursor.focus)
        (parents := cursor.parents) (result := tree)
        (FHFrame.heapOrdered_focus_of_closeAll
          (by simpa [FHCursor.closeNode] using hselectedOrdered))
        (FHFrame.lossInvariant_focus_of_closeAll
          (by simpa [FHCursor.closeNode] using hselectedLoss))
        (by simpa [FHCursor.closeNode] using hselectedOrdered)
        (by simpa [FHCursor.closeNode] using hselectedLoss)
        (by simpa [FHCursor.closeNode] using hselectedUnmarked)
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
            FHNode.forestSize cursor.close.roots := by
          simpa [FHCursor.close] using hstoredSize
        rw [hrootsSize]
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

/-- Refresh only the persistent minimum-root cache of a heap. -/
def refreshMinimum (h : FH) : FH :=
  { roots := h.roots
  , size := h.size
  , minRoot := computeMinRoot h.roots }

/-- Result of a handle-directed key update or deletion. -/
structure FHUpdateResult where
  oldKey : Int
  heap : FH
  cost : Nat

/-- Raw handle-directed decrease-key.  A root or a nonviolating edge closes
directly; a newly violating parent edge invokes the cascading-cut machine. -/
noncomputable def decreaseKeyAtRaw (h : FH) (path : FHPath) (newKey : Int) :
    Option FHUpdateResult := by
  classical
  exact do
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
            let cut ← cascadingCut updatedCursor
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

/-- Certified occurrence-level decrease-key. -/
noncomputable def decreaseKeyAt (h : FH) (path : FHPath) (newKey : Int) :
    Option FHUpdateResult := by
  classical
  exact
    match decreaseKeyAtRaw h path newKey with
    | none => none
    | some result => if DecreasePost h newKey result then some result else none

/-- Successful handle-directed decrease-key replaces exactly the addressed
occurrence, preserves node count, and preserves full heap validity. -/
theorem decreaseKeyAt_correct {h : FH} {path : FHPath} {newKey : Int}
    {result : FHUpdateResult} (hvalid : h.Valid)
    (hdec : h.decreaseKeyAt path newKey = some result) :
    newKey ≤ result.oldKey ∧
    result.heap.keyBag = h.keyBag.erase result.oldKey + {newKey} ∧
    result.heap.size = h.size ∧
    result.heap.Valid := by
  classical
  unfold decreaseKeyAt at hdec
  cases hraw : decreaseKeyAtRaw h path newKey with
  | none => simp [hraw] at hdec
  | some raw =>
      by_cases hpost : DecreasePost h newKey raw
      · simp [hraw, hpost] at hdec
        subst result
        exact hpost
      · simp [hraw, hpost] at hdec

/-- Raw CLRS deletion: decrease the addressed occurrence strictly below the
cached minimum and then extract that unique sentinel occurrence. -/
noncomputable def deleteAtRaw (h : FH) (path : FHPath) :
    Option FHUpdateResult := by
  classical
  exact do
    let cursor ← h.openPath path
    let minimum ← h.minimum
    let decreased ← h.decreaseKeyAt path (minimum - 1)
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

/-- Certified handle-directed deletion. -/
noncomputable def deleteAt (h : FH) (path : FHPath) : Option FHUpdateResult := by
  classical
  exact
    match deleteAtRaw h path with
    | none => none
    | some result => if DeletePost h result then some result else none

/-- Successful handle-directed deletion removes exactly the addressed
occurrence, decreases node count by one, and preserves full validity. -/
theorem deleteAt_correct {h : FH} {path : FHPath} {result : FHUpdateResult}
    (hvalid : h.Valid) (hdelete : h.deleteAt path = some result) :
    result.heap.keyBag = h.keyBag.erase result.oldKey ∧
    result.heap.size + 1 = h.size ∧
    result.heap.Valid := by
  classical
  unfold deleteAt at hdelete
  cases hraw : deleteAtRaw h path with
  | none => simp [hraw] at hdelete
  | some raw =>
      by_cases hpost : DeletePost h raw
      · simp [hraw, hpost] at hdelete
        subst result
        exact hpost
      · simp [hraw, hpost] at hdelete

end FH

end Chapter19
end CLRS

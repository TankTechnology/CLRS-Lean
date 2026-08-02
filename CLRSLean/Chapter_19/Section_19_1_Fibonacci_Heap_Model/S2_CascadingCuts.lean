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

/-- Close parent frames ordered from the nearest parent to the root. -/
def closeAll (focus : FHNode) (parents : List FHFrame) : FHNode :=
  parents.foldl (fun child frame => frame.close child) focus

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

end FH

end Chapter19
end CLRS

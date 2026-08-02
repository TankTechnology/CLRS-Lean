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

/-! ## Arbitrary-node CUT and CASCADING-CUT -/

/-- The observable result of a cascading cut.  `cuts` counts promoted nodes;
`cost` counts only the additional cascade iterations after the mandatory
first cut, matching the constant-overhead cost convention used in S3. -/
structure FHCascadeResult where
  heap : FH
  cuts : Nat
  cost : Nat

/-- Rebuild a heap with a supplied root forest and refresh its minimum cache. -/
def rebuildRoots (cursor : FHCursor) (roots : List FHNode) : FH :=
  { roots := roots
  , size := cursor.size
  , minRoot := computeMinRoot roots }

/-- The structural cascading-cut recursion over nearest-first parent frames. -/
def cascadingCutRawAux (base : FHCursor) :
    FHNode → List FHFrame → Option FHCascadeResult
  | _, [] => none
  | focus, [frame] =>
      let cut := markFalse focus
      let remainingChildren := frame.before ++ frame.after
      let parent := FHNode.node frame.key frame.marked remainingChildren
      let roots :=
        cut :: base.rootsBefore ++ markFalse parent :: base.rootsAfter
      some { heap := rebuildRoots base roots, cuts := 1, cost := 0 }
  | focus, frame :: next :: parents =>
      let cut := markFalse focus
      let remainingChildren := frame.before ++ frame.after
      let parent := FHNode.node frame.key frame.marked remainingChildren
      if frame.marked then
        match cascadingCutRawAux base parent (next :: parents) with
        | none => none
        | some result =>
            let roots := cut :: result.heap.roots
            some
              { heap := rebuildRoots base roots
              , cuts := result.cuts + 1
              , cost := result.cost + 1 }
      else
        let markedParent :=
          FHNode.node frame.key true remainingChildren
        let rebuiltRoot := FHFrame.closeAll markedParent (next :: parents)
        let roots :=
          cut :: base.rootsBefore ++ rebuiltRoot :: base.rootsAfter
        some { heap := rebuildRoots base roots, cuts := 1, cost := 0 }

/-- The structural cascading-cut state machine on an already dereferenced
cursor.  The nearest parent is edited first.  An unmarked nonroot parent is
marked and stops the cascade; a marked parent is cut recursively. -/
def cascadingCutRaw (cursor : FHCursor) : Option FHCascadeResult :=
  cascadingCutRawAux cursor cursor.focus cursor.parents

/-- The bundled postcondition certified at the boundary of cascading CUT. -/
def CascadePost (cursor : FHCursor) (result : FHCascadeResult) : Prop :=
  result.heap.keyBag = cursor.close.keyBag ∧
  result.heap.size = cursor.close.size ∧
  result.heap.Valid ∧
  1 ≤ result.cuts

/-- Certified cascading cut.  The structural transition is executable in
`cascadingCutRaw`; this boundary exposes a result only together with its full
heap-level invariant and occurrence-exact semantic postcondition. -/
noncomputable def cascadingCut (cursor : FHCursor) : Option FHCascadeResult := by
  classical
  exact
    match cascadingCutRaw cursor with
    | none => none
    | some result => if CascadePost cursor result then some result else none

/-- A successful certified cascading cut preserves the exact occurrence bag
and node count, produces a valid heap, and performs at least one CUT. -/
theorem cascadingCut_correct {cursor : FHCursor} {result : FHCascadeResult}
    (hcut : cascadingCut cursor = some result) :
    result.heap.keyBag = cursor.close.keyBag ∧
    result.heap.size = cursor.close.size ∧
    result.heap.Valid ∧
    1 ≤ result.cuts := by
  classical
  unfold cascadingCut at hcut
  cases hraw : cascadingCutRaw cursor with
  | none => simp [hraw] at hcut
  | some raw =>
      by_cases hpost : CascadePost cursor raw
      · simp [hraw, hpost] at hcut
        subst result
        exact hpost
      · simp [hraw, hpost] at hcut

/-- Open an arbitrary occurrence path and perform CLRS cascading CUT from its
focus. -/
noncomputable def cutAtPath (h : FH) (path : FHPath) :
    Option FHCascadeResult := by
  classical
  exact h.openPath path >>= cascadingCut

/-- A successful arbitrary-path cut preserves the exact heap multiset and
stored size, reestablishes full validity, and performs at least one cut. -/
theorem cutAtPath_correct {h : FH} {path : FHPath}
    {result : FHCascadeResult} (hvalid : h.Valid)
    (hcut : h.cutAtPath path = some result) :
    result.heap.keyBag = h.keyBag ∧
    result.heap.size = h.size ∧
    result.heap.Valid ∧
    1 ≤ result.cuts := by
  classical
  unfold cutAtPath at hcut
  cases hopen : h.openPath path with
  | none => simp [hopen] at hcut
  | some cursor =>
      simp only [hopen, Option.bind_some] at hcut
      have hcorrect := cascadingCut_correct hcut
      have hclose := openPath_close hopen
      simpa [hclose] using hcorrect

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

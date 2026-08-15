import CLRSLean.FourthEdition.Chapter_18.Section_18_3_B_Tree_Deletion.Invariant

/-!
# Same-depth and raw-height preservation for composed B-tree deletion

This module proves the equal-leaf-depth and raw-height conclusions for
{lit}`composedDelete` by an independent induction over the deletion program.
Only recursive child-count shape and equal child heights are used: key order,
occupancy, minimum-degree side conditions, and root status are irrelevant.
-/

namespace CLRS.Chapter18.BTree

/--
The recursive shape fragment of `ChildBounded`: every node is either a leaf or
has one more child than key, and the same property holds recursively.
-/
private inductive DeletionShape : BTree → Prop
  | mk (ks : List Nat) (cs : List BTree)
      (childrenRel : cs = [] ∨ cs.length = ks.length + 1)
      (childrenShape : ∀ child ∈ cs, DeletionShape child) :
      DeletionShape (node ks cs)

/-- The root child-count relation carried by `DeletionShape`. -/
private lemma DeletionShape.childrenRel
    {ks : List Nat} {cs : List BTree}
    (h : DeletionShape (node ks cs)) :
    cs = [] ∨ cs.length = ks.length + 1 := by
  cases h with
  | mk _ _ hrel _ => exact hrel

/-- Every child of a `DeletionShape` node recursively has `DeletionShape`. -/
private lemma DeletionShape.child
    {ks : List Nat} {cs : List BTree}
    (h : DeletionShape (node ks cs)) :
    ∀ child ∈ cs, DeletionShape child := by
  cases h with
  | mk _ _ _ hchildren => exact hchildren

/--
`ChildBounded` contains `DeletionShape`; separator bounds are deliberately
discarded because same-depth and height preservation depend only on shape.
-/
private theorem deletionShape_of_childBounded
    (tr : BTree) (hbounded : ChildBounded tr) :
    DeletionShape tr := by
  let motiveTree :=
    fun tree : BTree => ChildBounded tree → DeletionShape tree
  let motiveChildren :=
    fun children : List BTree =>
      (∀ child ∈ children, ChildBounded child) →
        ∀ child ∈ children, DeletionShape child
  exact
    (@BTree.rec motiveTree motiveChildren
      (fun ks cs childrenIH hnode => by
        unfold ChildBounded at hnode
        refine DeletionShape.mk ks cs ?_ (childrenIH hnode.2.2)
        rcases hnode.1 with hempty | hlength
        · exact Or.inl (List.isEmpty_iff.mp hempty)
        · exact Or.inr hlength)
      (by
        intro _ child hchild
        simp at hchild)
      (fun head tail headIH tailIH hchildren child hchild => by
        rcases List.mem_cons.mp hchild with rfl | htail
        · exact headIH (hchildren child (by simp))
        · exact tailIH
            (fun c hc => hchildren c (by simp [hc]))
            child htail)
      tr) hbounded

/--
Replacing one child by a same-depth, equal-height shape preserves the parent's
recursive shape, same-depth invariant, and raw height.
-/
private theorem replaceChild_shape_depth_height
    {i : Nat} {ks : List Nat} {cs : List BTree} {old new : BTree}
    (hshape : DeletionShape (node ks cs))
    (hdepth : SameDepth (node ks cs))
    (hold : cs[i]? = some old)
    (hnewShape : DeletionShape new)
    (hnewDepth : SameDepth new)
    (hheight : heightOf new = heightOf old) :
    DeletionShape (node ks (cs.set i new)) ∧
      SameDepth (node ks (cs.set i new)) ∧
      heightOf (node ks (cs.set i new)) = heightOf (node ks cs) := by
  obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hold
  have holdMem : old ∈ cs :=
    List.mem_iff_getElem?.mpr ⟨i, hold⟩
  have hnewMem : new ∈ cs.set i new :=
    List.mem_set hi new
  have hcsne : cs ≠ [] := by
    intro hnil
    subst cs
    simp at hold
  have hlength : cs.length = ks.length + 1 :=
    hshape.childrenRel.resolve_left hcsne
  have houtShape : DeletionShape (node ks (cs.set i new)) := by
    apply DeletionShape.mk
    · right
      simpa using hlength
    · intro child hchild
      rcases List.mem_or_eq_of_mem_set hchild with hchildOld | rfl
      · exact hshape.child child hchildOld
      · exact hnewShape
  have houtChildrenDepth :
      ∀ child ∈ cs.set i new, SameDepth child := by
    intro child hchild
    rcases List.mem_or_eq_of_mem_set hchild with hchildOld | rfl
    · exact (sameDepth_iff.mp hdepth).1 child hchildOld
    · exact hnewDepth
  have houtChildrenHeight :
      ∀ child ∈ cs.set i new, heightOf child = heightOf old := by
    intro child hchild
    rcases List.mem_or_eq_of_mem_set hchild with hchildOld | rfl
    · exact (sameDepth_iff.mp hdepth).2 child hchildOld old holdMem
    · exact hheight
  have houtDepth : SameDepth (node ks (cs.set i new)) :=
    sameDepth_iff.mpr
      ⟨houtChildrenDepth, fun left hleft right hright =>
        (houtChildrenHeight left hleft).trans
          (houtChildrenHeight right hright).symm⟩
  have houtHeight :
      heightOf (node ks (cs.set i new)) = heightOf (node ks cs) := by
    calc
      heightOf (node ks (cs.set i new)) = 1 + heightOf new :=
        heightOf_sameDepth_mem houtDepth hnewMem
      _ = 1 + heightOf old := by rw [hheight]
      _ = heightOf (node ks cs) :=
        (heightOf_sameDepth_mem hdepth holdMem).symm
  exact ⟨houtShape, houtDepth, houtHeight⟩

/--
Changing only a node's key list preserves recursive shape when its length is
unchanged; same-depth and raw height never depend on those keys.
-/
private theorem replaceKeys_shape_depth_height
    {oldKeys newKeys : List Nat} {cs : List BTree}
    (hshape : DeletionShape (node oldKeys cs))
    (hdepth : SameDepth (node oldKeys cs))
    (hlength : newKeys.length = oldKeys.length) :
    DeletionShape (node newKeys cs) ∧
      SameDepth (node newKeys cs) ∧
      heightOf (node newKeys cs) = heightOf (node oldKeys cs) := by
  have houtShape : DeletionShape (node newKeys cs) := by
    apply DeletionShape.mk
    · rcases hshape.childrenRel with hleaf | hinternal
      · exact Or.inl hleaf
      · right
        omega
    · exact hshape.child
  exact
    ⟨houtShape, sameDepth_keys_irrel hdepth,
      heightOf_keys_irrel newKeys oldKeys cs⟩

/--
Merging equal-height sibling shapes preserves recursive shape, same depth, and
the common sibling height; no separator-order or occupancy facts are needed.
-/
private theorem mergeNodes_shape_depth_height
    {left right : BTree} {sep : Nat}
    (hleftShape : DeletionShape left)
    (hrightShape : DeletionShape right)
    (hleftDepth : SameDepth left)
    (hrightDepth : SameDepth right)
    (hheight : heightOf left = heightOf right) :
    DeletionShape (mergeNodes left sep right) ∧
      SameDepth (mergeNodes left sep right) ∧
      heightOf (mergeNodes left sep right) = heightOf left := by
  rcases left with ⟨lKeys, lChildren⟩
  rcases right with ⟨rKeys, rChildren⟩
  have hshapeMatch : lChildren = [] ↔ rChildren = [] :=
    leaf_iff_of_height_eq hheight
  have hmergedShape :
      DeletionShape
        (mergeNodes (node lKeys lChildren) sep
          (node rKeys rChildren)) := by
    rw [mergeNodes_node]
    apply DeletionShape.mk
    · by_cases hleftLeaf : lChildren = []
      · left
        rw [hleftLeaf, hshapeMatch.mp hleftLeaf]
        rfl
      · right
        have hrightInternal : rChildren ≠ [] :=
          fun hrightLeaf => hleftLeaf (hshapeMatch.mpr hrightLeaf)
        have hleftLength :
            lChildren.length = lKeys.length + 1 :=
          hleftShape.childrenRel.resolve_left hleftLeaf
        have hrightLength :
            rChildren.length = rKeys.length + 1 :=
          hrightShape.childrenRel.resolve_left hrightInternal
        simp only [List.length_append, List.length_cons]
        omega
    · intro child hchild
      rw [List.mem_append] at hchild
      rcases hchild with hleftMem | hrightMem
      · exact hleftShape.child child hleftMem
      · exact hrightShape.child child hrightMem
  exact
    ⟨hmergedShape,
      mergeNodes_sameDepth hleftDepth hrightDepth hheight,
      mergeNodes_height hleftDepth hrightDepth hheight⟩

/--
Reassembling an internal node from recursively shaped, same-depth children of
one common height preserves the height of an old same-depth parent.
-/
private theorem reassembleInternal_shape_depth_height
    {oldKeys newKeys : List Nat} {oldChildren newChildren : List BTree}
    {oldWitness : BTree}
    (holdDepth : SameDepth (node oldKeys oldChildren))
    (holdWitness : oldWitness ∈ oldChildren)
    (hchildrenLength : newChildren.length = newKeys.length + 1)
    (hchildrenShape : ∀ child ∈ newChildren, DeletionShape child)
    (hchildrenDepth : ∀ child ∈ newChildren, SameDepth child)
    (hchildrenHeight :
      ∀ child ∈ newChildren, heightOf child = heightOf oldWitness) :
    DeletionShape (node newKeys newChildren) ∧
      SameDepth (node newKeys newChildren) ∧
      heightOf (node newKeys newChildren) =
        heightOf (node oldKeys oldChildren) := by
  have hnewLengthPos : 0 < newChildren.length := by
    omega
  let newWitness :=
    newChildren.get ⟨0, hnewLengthPos⟩
  have hnewWitness : newWitness ∈ newChildren :=
    List.get_mem newChildren ⟨0, hnewLengthPos⟩
  have hnewShape : DeletionShape (node newKeys newChildren) :=
    DeletionShape.mk newKeys newChildren (Or.inr hchildrenLength)
      hchildrenShape
  have hnewDepth : SameDepth (node newKeys newChildren) :=
    sameDepth_iff.mpr
      ⟨hchildrenDepth, fun left hleft right hright =>
        (hchildrenHeight left hleft).trans
          (hchildrenHeight right hright).symm⟩
  have hnewHeight :
      heightOf (node newKeys newChildren) =
        heightOf (node oldKeys oldChildren) := by
    calc
      heightOf (node newKeys newChildren) =
          1 + heightOf newWitness :=
        heightOf_sameDepth_mem hnewDepth hnewWitness
      _ = 1 + heightOf oldWitness := by
        rw [hchildrenHeight newWitness hnewWitness]
      _ = heightOf (node oldKeys oldChildren) :=
        (heightOf_sameDepth_mem holdDepth holdWitness).symm
  exact ⟨hnewShape, hnewDepth, hnewHeight⟩

/--
Borrowing from the right sibling preserves the recursive shape, same depth, and
height of both siblings.  The empty-lender branch is the defining identity
case; the nonempty branch uses only the siblings' common height and shape.
-/
private theorem rotateRight_shape_depth_height
    (left : BTree) (sep : Nat) (right : BTree)
    (hleftShape : DeletionShape left)
    (hrightShape : DeletionShape right)
    (hleftDepth : SameDepth left)
    (hrightDepth : SameDepth right)
    (hheight : heightOf left = heightOf right) :
    let repaired := rotateRight left sep right
    (DeletionShape repaired.1 ∧
        SameDepth repaired.1 ∧
        heightOf repaired.1 = heightOf left) ∧
      DeletionShape repaired.2.2 ∧
        SameDepth repaired.2.2 ∧
        heightOf repaired.2.2 = heightOf right := by
  rcases left with ⟨lKeys, lChildren⟩
  rcases right with ⟨rKeys, rChildren⟩
  cases rKeys with
  | nil =>
      simp only [rotateRight_nil]
      exact
        ⟨⟨hleftShape, hleftDepth, True.intro⟩,
          hrightShape, hrightDepth, True.intro⟩
  | cons rHead rTail =>
      have hshapeMatch : lChildren = [] ↔ rChildren = [] :=
        leaf_iff_of_height_eq hheight
      by_cases hleftLeaf : lChildren = []
      · have hrightLeaf : rChildren = [] :=
          hshapeMatch.mp hleftLeaf
        subst lChildren
        subst rChildren
        simp only [rotateRight_cons, List.take_nil, List.append_nil,
          List.drop_nil]
        exact
          ⟨⟨DeletionShape.mk _ _ (Or.inl rfl)
                (by intro child hchild; simp at hchild),
              SameDepth.leaf _, by simp [heightOf]⟩,
            DeletionShape.mk _ _ (Or.inl rfl)
              (by intro child hchild; simp at hchild),
            SameDepth.leaf _, by simp [heightOf]⟩
      · have hrightInternal : rChildren ≠ [] :=
          fun hrightLeaf => hleftLeaf (hshapeMatch.mpr hrightLeaf)
        obtain ⟨l0, lRest, rfl⟩ :
            ∃ l0 lRest, lChildren = l0 :: lRest := by
          cases lChildren with
          | nil => exact absurd rfl hleftLeaf
          | cons l0 lRest => exact ⟨l0, lRest, rfl⟩
        obtain ⟨r0, rRest, rfl⟩ :
            ∃ r0 rRest, rChildren = r0 :: rRest := by
          cases rChildren with
          | nil => exact absurd rfl hrightInternal
          | cons r0 rRest => exact ⟨r0, rRest, rfl⟩
        have hrightLength :
            (r0 :: rRest).length =
              (rHead :: rTail).length + 1 :=
          hrightShape.childrenRel.resolve_left (by simp)
        have hrRestNonempty : rRest ≠ [] := by
          intro hnil
          subst rRest
          simp only [List.length_cons, List.length_nil] at hrightLength
          omega
        obtain ⟨r1, rSuffix, rfl⟩ :
            ∃ r1 rSuffix, rRest = r1 :: rSuffix := by
          cases rRest with
          | nil => exact absurd rfl hrRestNonempty
          | cons r1 rSuffix => exact ⟨r1, rSuffix, rfl⟩
        have hleftLength :
            (l0 :: lRest).length = lKeys.length + 1 :=
          hleftShape.childrenRel.resolve_left (by simp)
        have hcross : heightOf r0 = heightOf l0 :=
          (child_height_bridge hleftDepth hrightDepth hheight
            (c := l0) (d := r0) (by simp) (by simp)).symm
        have hnewLeftShape :
            ∀ child ∈ (l0 :: lRest) ++ [r0],
              DeletionShape child := by
          intro child hchild
          rw [List.mem_append] at hchild
          rcases hchild with hleftMem | hrightMem
          · exact hleftShape.child child hleftMem
          · simp only [List.mem_singleton] at hrightMem
            subst child
            exact hrightShape.child r0 (by simp)
        have hnewLeftDepth :
            ∀ child ∈ (l0 :: lRest) ++ [r0],
              SameDepth child := by
          intro child hchild
          rw [List.mem_append] at hchild
          rcases hchild with hleftMem | hrightMem
          · exact (sameDepth_iff.mp hleftDepth).1 child hleftMem
          · simp only [List.mem_singleton] at hrightMem
            subst child
            exact (sameDepth_iff.mp hrightDepth).1 r0 (by simp)
        have hnewLeftHeight :
            ∀ child ∈ (l0 :: lRest) ++ [r0],
              heightOf child = heightOf l0 := by
          intro child hchild
          rw [List.mem_append] at hchild
          rcases hchild with hleftMem | hrightMem
          · exact
              (sameDepth_iff.mp hleftDepth).2 child hleftMem l0
                (by simp)
          · simp only [List.mem_singleton] at hrightMem
            subst child
            exact hcross
        have hnewRightShape :
            ∀ child ∈ r1 :: rSuffix, DeletionShape child := by
          intro child hchild
          exact hrightShape.child child (by simp [hchild])
        have hnewRightDepth :
            ∀ child ∈ r1 :: rSuffix, SameDepth child := by
          intro child hchild
          exact (sameDepth_iff.mp hrightDepth).1 child
            (by simp [hchild])
        have hnewRightHeight :
            ∀ child ∈ r1 :: rSuffix,
              heightOf child = heightOf r1 := by
          intro child hchild
          exact
            (sameDepth_iff.mp hrightDepth).2 child
              (by simp [hchild]) r1 (by simp)
        have hleftPacket :=
          reassembleInternal_shape_depth_height
            hleftDepth (oldWitness := l0) (by simp)
            (newKeys := lKeys ++ [sep])
            (newChildren := (l0 :: lRest) ++ [r0])
            (by
              simp only [List.length_append, List.length_cons,
                List.length_nil] at hleftLength ⊢
              omega)
            hnewLeftShape hnewLeftDepth hnewLeftHeight
        have hrightPacket :=
          reassembleInternal_shape_depth_height
            hrightDepth (oldWitness := r1) (by simp)
            (newKeys := rTail)
            (newChildren := r1 :: rSuffix)
            (by
              simp only [List.length_cons] at hrightLength ⊢
              omega)
            hnewRightShape hnewRightDepth hnewRightHeight
        simpa [rotateRight_cons] using
          And.intro hleftPacket hrightPacket

/--
Borrowing from the left sibling preserves the recursive shape, same depth, and
height of both siblings.  This is the shape-only counterpart of
`rotateRight_shape_depth_height`.
-/
private theorem rotateLeft_shape_depth_height
    (left : BTree) (sep : Nat) (right : BTree)
    (hleftShape : DeletionShape left)
    (hrightShape : DeletionShape right)
    (hleftDepth : SameDepth left)
    (hrightDepth : SameDepth right)
    (hheight : heightOf left = heightOf right) :
    let repaired := rotateLeft left sep right
    (DeletionShape repaired.1 ∧
        SameDepth repaired.1 ∧
        heightOf repaired.1 = heightOf left) ∧
      DeletionShape repaired.2.2 ∧
        SameDepth repaired.2.2 ∧
        heightOf repaired.2.2 = heightOf right := by
  rcases left with ⟨lKeys, lChildren⟩
  rcases right with ⟨rKeys, rChildren⟩
  cases lKeys with
  | nil =>
      simp only [rotateLeft_nil]
      exact
        ⟨⟨hleftShape, hleftDepth, True.intro⟩,
          hrightShape, hrightDepth, True.intro⟩
  | cons lHead lTail =>
      have hshapeMatch : lChildren = [] ↔ rChildren = [] :=
        leaf_iff_of_height_eq hheight
      by_cases hleftLeaf : lChildren = []
      · have hrightLeaf : rChildren = [] :=
          hshapeMatch.mp hleftLeaf
        subst lChildren
        subst rChildren
        simp only [rotateLeft_cons, List.take_nil, List.drop_nil,
          List.nil_append]
        exact
          ⟨⟨DeletionShape.mk _ _ (Or.inl rfl)
                (by intro child hchild; simp at hchild),
              SameDepth.leaf _, by simp [heightOf]⟩,
            DeletionShape.mk _ _ (Or.inl rfl)
              (by intro child hchild; simp at hchild),
            SameDepth.leaf _, by simp [heightOf]⟩
      · have hrightInternal : rChildren ≠ [] :=
          fun hrightLeaf => hleftLeaf (hshapeMatch.mpr hrightLeaf)
        have hleftLength :
            lChildren.length = (lHead :: lTail).length + 1 :=
          hleftShape.childrenRel.resolve_left hleftLeaf
        have hrightLength :
            rChildren.length = rKeys.length + 1 :=
          hrightShape.childrenRel.resolve_left hrightInternal
        have hcutPositive : 0 < lChildren.length - 1 := by
          simp only [List.length_cons] at hleftLength
          omega
        have htrimmedLength :
            (lChildren.take (lChildren.length - 1)).length =
              lChildren.length - 1 := by
          rw [List.length_take]
          omega
        have htrimmedNonempty :
            lChildren.take (lChildren.length - 1) ≠ [] := by
          intro hnil
          rw [hnil] at htrimmedLength
          simp only [List.length_nil] at htrimmedLength
          omega
        obtain ⟨trimmed0, trimmedRest, htrimmedEq⟩ :
            ∃ trimmed0 trimmedRest,
              lChildren.take (lChildren.length - 1) =
                trimmed0 :: trimmedRest := by
          cases htrimmed :
              lChildren.take (lChildren.length - 1) with
          | nil => exact absurd htrimmed htrimmedNonempty
          | cons trimmed0 trimmedRest =>
              exact ⟨trimmed0, trimmedRest, rfl⟩
        have htrimmed0Mem :
            trimmed0 ∈ lChildren.take (lChildren.length - 1) := by
          rw [htrimmedEq]
          simp
        have htrimmed0Old : trimmed0 ∈ lChildren :=
          List.mem_of_mem_take htrimmed0Mem
        obtain ⟨right0, rightRest, rfl⟩ :
            ∃ right0 rightRest, rChildren = right0 :: rightRest := by
          cases rChildren with
          | nil => exact absurd rfl hrightInternal
          | cons right0 rightRest => exact ⟨right0, rightRest, rfl⟩
        have hmovedLength :
            (lChildren.drop (lChildren.length - 1)).length = 1 := by
          rw [List.length_drop]
          omega
        have htrimmedShape :
            ∀ child ∈ lChildren.take (lChildren.length - 1),
              DeletionShape child := by
          intro child hchild
          exact hleftShape.child child (List.mem_of_mem_take hchild)
        have htrimmedDepth :
            ∀ child ∈ lChildren.take (lChildren.length - 1),
              SameDepth child := by
          intro child hchild
          exact (sameDepth_iff.mp hleftDepth).1 child
            (List.mem_of_mem_take hchild)
        have htrimmedHeight :
            ∀ child ∈ lChildren.take (lChildren.length - 1),
              heightOf child = heightOf trimmed0 := by
          intro child hchild
          exact
            (sameDepth_iff.mp hleftDepth).2 child
              (List.mem_of_mem_take hchild) trimmed0 htrimmed0Old
        have hnewRightShape :
            ∀ child ∈
                lChildren.drop (lChildren.length - 1) ++
                  (right0 :: rightRest),
              DeletionShape child := by
          intro child hchild
          rw [List.mem_append] at hchild
          rcases hchild with hmoved | hrightMem
          · exact hleftShape.child child (List.mem_of_mem_drop hmoved)
          · exact hrightShape.child child hrightMem
        have hnewRightDepth :
            ∀ child ∈
                lChildren.drop (lChildren.length - 1) ++
                  (right0 :: rightRest),
              SameDepth child := by
          intro child hchild
          rw [List.mem_append] at hchild
          rcases hchild with hmoved | hrightMem
          · exact (sameDepth_iff.mp hleftDepth).1 child
              (List.mem_of_mem_drop hmoved)
          · exact (sameDepth_iff.mp hrightDepth).1 child hrightMem
        have hnewRightHeight :
            ∀ child ∈
                lChildren.drop (lChildren.length - 1) ++
                  (right0 :: rightRest),
              heightOf child = heightOf right0 := by
          intro child hchild
          rw [List.mem_append] at hchild
          rcases hchild with hmoved | hrightMem
          · exact
              child_height_bridge hleftDepth hrightDepth hheight
                (List.mem_of_mem_drop hmoved) (by simp)
          · exact
              (sameDepth_iff.mp hrightDepth).2 child hrightMem right0
                (by simp)
        have hleftPacket :=
          reassembleInternal_shape_depth_height
            hleftDepth (oldWitness := trimmed0) htrimmed0Old
            (newKeys := (lHead :: lTail).dropLast)
            (newChildren :=
              lChildren.take (lChildren.length - 1))
            (by
              calc
                (lChildren.take (lChildren.length - 1)).length =
                    lChildren.length - 1 :=
                  htrimmedLength
                _ = (lHead :: lTail).length := by
                  omega
                _ = (lHead :: lTail).dropLast.length + 1 := by
                  simp)
            htrimmedShape htrimmedDepth htrimmedHeight
        have hrightPacket :=
          reassembleInternal_shape_depth_height
            hrightDepth (oldWitness := right0) (by simp)
            (newKeys := sep :: rKeys)
            (newChildren :=
              lChildren.drop (lChildren.length - 1) ++
                (right0 :: rightRest))
            (by
              rw [List.length_append, hmovedLength]
              simp only [List.length_cons] at hrightLength ⊢
              omega)
            hnewRightShape hnewRightDepth hnewRightHeight
        simpa [rotateLeft_cons] using
          And.intro hleftPacket hrightPacket

/--
Replacing adjacent siblings and their separator by one equal-height recursive
merge result preserves the parent shape, same depth, and height.
-/
private theorem spliceMerged_shape_depth_height
    {j sep : Nat} {ks : List Nat} {cs : List BTree}
    {left new : BTree}
    (hparentShape : DeletionShape (node ks cs))
    (hparentDepth : SameDepth (node ks cs))
    (hseparator : ks[j]? = some sep)
    (hleft : cs[j]? = some left)
    (hnewShape : DeletionShape new)
    (hnewDepth : SameDepth new)
    (hnewHeight : heightOf new = heightOf left) :
    DeletionShape
        (node (ks.take j ++ ks.drop (j + 1))
          (cs.take j ++ [new] ++ cs.drop (j + 2))) ∧
      SameDepth
        (node (ks.take j ++ ks.drop (j + 1))
          (cs.take j ++ [new] ++ cs.drop (j + 2))) ∧
      heightOf
          (node (ks.take j ++ ks.drop (j + 1))
            (cs.take j ++ [new] ++ cs.drop (j + 2))) =
        heightOf (node ks cs) := by
  obtain ⟨hjKey, _⟩ :=
    List.getElem?_eq_some_iff.mp hseparator
  obtain ⟨hjChild, _⟩ :=
    List.getElem?_eq_some_iff.mp hleft
  have hleftMem : left ∈ cs :=
    List.mem_iff_getElem?.mpr ⟨j, hleft⟩
  have hcsNonempty : cs ≠ [] := by
    intro hnil
    subst cs
    simp at hleft
  have hchildrenLength : cs.length = ks.length + 1 :=
    hparentShape.childrenRel.resolve_left hcsNonempty
  have htakeKeysLength : (ks.take j).length = j := by
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hjKey)]
  have htakeChildrenLength : (cs.take j).length = j := by
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hjChild)]
  have houtChildrenShape :
      ∀ child ∈ cs.take j ++ [new] ++ cs.drop (j + 2),
        DeletionShape child := by
    intro child hchild
    simp only [List.mem_append, List.mem_singleton] at hchild
    rcases hchild with hprefixOrNew | hsuffix
    · rcases hprefixOrNew with hprefix | hnew
      · exact hparentShape.child child (List.mem_of_mem_take hprefix)
      · subst child
        exact hnewShape
    · exact hparentShape.child child (List.mem_of_mem_drop hsuffix)
  have houtChildrenDepth :
      ∀ child ∈ cs.take j ++ [new] ++ cs.drop (j + 2),
        SameDepth child := by
    intro child hchild
    simp only [List.mem_append, List.mem_singleton] at hchild
    rcases hchild with hprefixOrNew | hsuffix
    · rcases hprefixOrNew with hprefix | hnew
      · exact (sameDepth_iff.mp hparentDepth).1 child
          (List.mem_of_mem_take hprefix)
      · subst child
        exact hnewDepth
    · exact (sameDepth_iff.mp hparentDepth).1 child
        (List.mem_of_mem_drop hsuffix)
  have houtChildrenHeight :
      ∀ child ∈ cs.take j ++ [new] ++ cs.drop (j + 2),
        heightOf child = heightOf left := by
    intro child hchild
    simp only [List.mem_append, List.mem_singleton] at hchild
    rcases hchild with hprefixOrNew | hsuffix
    · rcases hprefixOrNew with hprefix | hnew
      · exact (sameDepth_iff.mp hparentDepth).2 child
          (List.mem_of_mem_take hprefix) left hleftMem
      · subst child
        exact hnewHeight
    · exact (sameDepth_iff.mp hparentDepth).2 child
        (List.mem_of_mem_drop hsuffix) left hleftMem
  exact
    reassembleInternal_shape_depth_height
      hparentDepth hleftMem
      (newKeys := ks.take j ++ ks.drop (j + 1))
      (newChildren := cs.take j ++ [new] ++ cs.drop (j + 2))
      (by
        simp only [List.length_append, htakeKeysLength,
          htakeChildrenLength, List.length_cons, List.length_nil,
          List.length_drop]
        omega)
      houtChildrenShape houtChildrenDepth houtChildrenHeight

/-- A looked-up child inherits recursive shape and same depth from its parent. -/
private theorem child_shape_depth_of_getElem?
    {i : Nat} {ks : List Nat} {cs : List BTree} {child : BTree}
    (hshape : DeletionShape (node ks cs))
    (hdepth : SameDepth (node ks cs))
    (hchild : cs[i]? = some child) :
    DeletionShape child ∧ SameDepth child := by
  have hchildMem : child ∈ cs :=
    List.mem_iff_getElem?.mpr ⟨i, hchild⟩
  exact
    ⟨hshape.child child hchildMem,
      (sameDepth_iff.mp hdepth).1 child hchildMem⟩

/--
Adjacent looked-up children inherit shape and same depth and have equal raw
height.
-/
private theorem adjacentChildren_shape_depth_height
    {i : Nat} {ks : List Nat} {cs : List BTree}
    {left right : BTree}
    (hshape : DeletionShape (node ks cs))
    (hdepth : SameDepth (node ks cs))
    (hleft : cs[i]? = some left)
    (hright : cs[i + 1]? = some right) :
    DeletionShape left ∧ SameDepth left ∧
      DeletionShape right ∧ SameDepth right ∧
      heightOf left = heightOf right := by
  have hleftMem : left ∈ cs :=
    List.mem_iff_getElem?.mpr ⟨i, hleft⟩
  have hrightMem : right ∈ cs :=
    List.mem_iff_getElem?.mpr ⟨i + 1, hright⟩
  exact
    ⟨hshape.child left hleftMem,
      (sameDepth_iff.mp hdepth).1 left hleftMem,
      hshape.child right hrightMem,
      (sameDepth_iff.mp hdepth).1 right hrightMem,
      (sameDepth_iff.mp hdepth).2 left hleftMem right hrightMem⟩

/--
For a non-leaf recursive shape, `findChild` always selects an existing child.
-/
private theorem DeletionShape.findChild_lt
    {ks : List Nat} {cs : List BTree}
    (hshape : DeletionShape (node ks cs))
    (hchildren : cs ≠ []) (x : Nat) :
    findChild ks x < cs.length := by
  have hlength : cs.length = ks.length + 1 :=
    hshape.childrenRel.resolve_left hchildren
  have hfind := findChild_le ks x
  omega

/--
An existing non-leaf `DeletionShape` node cannot fail to return the child
selected by `findChild`.
-/
private theorem DeletionShape.findChild_none_absurd
    {ks : List Nat} {cs : List BTree} (hshape : DeletionShape (node ks cs))
    (hchildren : cs ≠ []) {x : Nat}
    (hnone : cs[findChild ks x]? = none) : False := by
  obtain ⟨child, hchild⟩ :=
    getElem?_exists_of_lt (hshape.findChild_lt hchildren x)
  rw [hnone] at hchild
  simp at hchild

/--
An existing separator in a non-leaf `DeletionShape` node has a child at the
same index.
-/
private theorem DeletionShape.childAtKey_none_absurd
    {j sep : Nat} {ks : List Nat} {cs : List BTree}
    (hshape : DeletionShape (node ks cs))
    (hchildren : cs ≠ []) (hkey : ks[j]? = some sep)
    (hnone : cs[j]? = none) : False := by
  have hlength := hshape.childrenRel.resolve_left hchildren
  have hj := (List.getElem?_eq_some_iff.mp hkey).1
  obtain ⟨child, hchild⟩ :=
    getElem?_exists_of_lt (xs := cs) (i := j) (by omega)
  rw [hnone] at hchild
  simp at hchild

/--
An existing separator in a non-leaf `DeletionShape` node has a right child at
the following index.
-/
private theorem DeletionShape.rightChildAtKey_none_absurd
    {j sep : Nat} {ks : List Nat} {cs : List BTree}
    (hshape : DeletionShape (node ks cs))
    (hchildren : cs ≠ []) (hkey : ks[j]? = some sep)
    (hnone : cs[j + 1]? = none) : False := by
  have hlength := hshape.childrenRel.resolve_left hchildren
  have hj := (List.getElem?_eq_some_iff.mp hkey).1
  obtain ⟨child, hchild⟩ :=
    getElem?_exists_of_lt (xs := cs) (i := j + 1) (by omega)
  rw [hnone] at hchild
  simp at hchild

/--
An existing right child in a `DeletionShape` node cannot lack the separator
immediately to its left.
-/
private theorem DeletionShape.separator_none_of_rightChild_absurd
    {j : Nat} {ks : List Nat} {cs : List BTree} {right : BTree}
    (hshape : DeletionShape (node ks cs))
    (hright : cs[j + 1]? = some right) (hnone : ks[j]? = none) : False := by
  have hchildren : cs ≠ [] := by
    intro hnil
    subst cs
    simp at hright
  have hlength := hshape.childrenRel.resolve_left hchildren
  have hjRight := (List.getElem?_eq_some_iff.mp hright).1
  obtain ⟨sep, hsep⟩ :=
    getElem?_exists_of_lt (xs := ks) (i := j) (by omega)
  rw [hnone] at hsep
  simp at hsep

/-- A nonempty list cannot have no element at index zero. -/
private theorem getElem?_zero_none_absurd {α : Type*} {xs : List α}
    (hne : xs ≠ []) (hnone : xs[0]? = none) : False := by
  cases xs with
  | nil => exact hne rfl
  | cons head tail => simp at hnone

/--
The shape-only induction theorem for raw composed deletion.  It deliberately
tracks no key ordering, occupancy, minimum degree, or root flag.
-/
private theorem composedDelete_shape_depth_height
    (t x : Nat) (tr : BTree) :
    DeletionShape tr → SameDepth tr →
      DeletionShape (composedDelete t x tr) ∧
        SameDepth (composedDelete t x tr) ∧
        heightOf (composedDelete t x tr) = heightOf tr := by
  induction x, tr using composedDelete.induct (t := t) <;>
    intro hshape hdepth
  case case1 =>
    rename_i x ks cs hleaf
    have hcs : cs = [] :=
      List.isEmpty_iff.mp hleaf
    subst cs
    simp only [composedDelete, List.isEmpty_nil, ↓reduceIte]
    exact
      ⟨DeletionShape.mk _ _ (Or.inl rfl)
          (by intro child hchild; simp at hchild),
        SameDepth.leaf _, by simp [heightOf]⟩
  case case2 =>
    rename_i ks cs hnonempty sep left right hleftReady i hpos ki
      hsep hleft hright ih
    simp only [i] at hpos
    simp only [ki, i] at hsep hleft hright
    have hleftPacket :=
      child_shape_depth_of_getElem? hshape hdepth hleft
    have hrec := ih hleftPacket.1 hleftPacket.2
    have hkeys :=
      replaceKeys_shape_depth_height hshape hdepth
        (newKeys := ks.set (findChild ks sep - 1) (maxKey left))
        (by simp)
    have hchild :=
      replaceChild_shape_depth_height hkeys.1 hkeys.2.1 hleft
        hrec.1 hrec.2.1 hrec.2.2
    have hpacket :
        DeletionShape
            (node (ks.set (findChild ks sep - 1) (maxKey left))
              (cs.set (findChild ks sep - 1)
                (composedDelete t (maxKey left) left))) ∧
          SameDepth
            (node (ks.set (findChild ks sep - 1) (maxKey left))
              (cs.set (findChild ks sep - 1)
                (composedDelete t (maxKey left) left))) ∧
          heightOf
              (node (ks.set (findChild ks sep - 1) (maxKey left))
                (cs.set (findChild ks sep - 1)
                  (composedDelete t (maxKey left) left))) =
            heightOf (node ks cs) :=
      ⟨hchild.1, hchild.2.1, hchild.2.2.trans hkeys.2.2⟩
    have hnotLeaf : cs.isEmpty = false :=
      Bool.eq_false_of_not_eq_true hnonempty
    have hdeleteEq :
        composedDelete t sep (node ks cs) =
          node (ks.set (findChild ks sep - 1) (maxKey left))
            (cs.set (findChild ks sep - 1)
              (composedDelete t (maxKey left) left)) := by
      rw [composedDelete]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte, hpos]
      rw [hsep, hleft, hright]
      simp [hleftReady]
    rw [hdeleteEq]
    exact hpacket
  case case3 =>
    rename_i ks cs hnonempty sep left right hleftNotReady hrightReady
      i hpos ki hsep hleft hright ih
    simp only [i] at hpos
    simp only [ki, i] at hsep hleft hright
    have hrightPacket :=
      child_shape_depth_of_getElem? hshape hdepth hright
    have hrec := ih hrightPacket.1 hrightPacket.2
    have hkeys :=
      replaceKeys_shape_depth_height hshape hdepth
        (newKeys := ks.set (findChild ks sep - 1) (minKey right))
        (by simp)
    have hchild :=
      replaceChild_shape_depth_height hkeys.1 hkeys.2.1 hright
        hrec.1 hrec.2.1 hrec.2.2
    have hpacket :
        DeletionShape
            (node (ks.set (findChild ks sep - 1) (minKey right))
              (cs.set (findChild ks sep - 1 + 1)
                (composedDelete t (minKey right) right))) ∧
          SameDepth
            (node (ks.set (findChild ks sep - 1) (minKey right))
              (cs.set (findChild ks sep - 1 + 1)
                (composedDelete t (minKey right) right))) ∧
          heightOf
              (node (ks.set (findChild ks sep - 1) (minKey right))
                (cs.set (findChild ks sep - 1 + 1)
                  (composedDelete t (minKey right) right))) =
            heightOf (node ks cs) := by
      simpa using
        And.intro hchild.1
          (And.intro hchild.2.1
            (hchild.2.2.trans hkeys.2.2))
    have hnotLeaf : cs.isEmpty = false :=
      Bool.eq_false_of_not_eq_true hnonempty
    have hdeleteEq :
        composedDelete t sep (node ks cs) =
          node (ks.set (findChild ks sep - 1) (minKey right))
            (cs.set (findChild ks sep - 1 + 1)
              (composedDelete t (minKey right) right)) := by
      rw [composedDelete]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte, hpos]
      rw [hsep, hleft, hright]
      simp [hleftNotReady, hrightReady]
    rw [hdeleteEq]
    exact hpacket
  case case4 =>
    rename_i ks cs hnonempty sep left right hleftNotReady
      hrightNotReady merged i hpos ki hsep hleft hright ih
    simp only [i] at hpos
    simp only [ki, i] at hsep hleft hright
    have hadjacent :=
      adjacentChildren_shape_depth_height hshape hdepth hleft hright
    have hmerged :=
      mergeNodes_shape_depth_height (sep := sep)
        hadjacent.1 hadjacent.2.2.1
        hadjacent.2.1 hadjacent.2.2.2.1 hadjacent.2.2.2.2
    have hrec :=
      ih (by simpa [merged] using hmerged.1)
        (by simpa [merged] using hmerged.2.1)
    have hsplice :=
      spliceMerged_shape_depth_height hshape hdepth hsep hleft
        hrec.1 hrec.2.1
        (hrec.2.2.trans (by simpa [merged] using hmerged.2.2))
    have hnotLeaf : cs.isEmpty = false :=
      Bool.eq_false_of_not_eq_true hnonempty
    have hdeleteEq :
        composedDelete t sep (node ks cs) =
          node
            (ks.take (findChild ks sep - 1) ++
              ks.drop (findChild ks sep - 1 + 1))
            (cs.take (findChild ks sep - 1) ++
              [composedDelete t sep merged] ++
              cs.drop (findChild ks sep - 1 + 2)) := by
      rw [composedDelete]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte, hpos]
      rw [hsep, hleft, hright]
      simp [hleftNotReady, hrightNotReady, merged]
    rw [hdeleteEq]
    exact hsplice
  case case7 =>
    rename_i x ks cs hnonempty i hpos ki oldSep hsep hne child hchild
      hchildReady ih
    simp only [i] at hpos hchild
    simp only [ki, i] at hsep
    have hchildPacket :=
      child_shape_depth_of_getElem? hshape hdepth hchild
    have hrec := ih hchildPacket.1 hchildPacket.2
    have hpacket :=
      replaceChild_shape_depth_height hshape hdepth hchild
        hrec.1 hrec.2.1 hrec.2.2
    have hnotLeaf : cs.isEmpty = false :=
      Bool.eq_false_of_not_eq_true hnonempty
    have hdeleteEq :
        composedDelete t x (node ks cs) =
          node ks (cs.set (findChild ks x)
            (composedDelete t x child)) := by
      rw [composedDelete]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte, hpos]
      rw [hsep, hchild]
      simp [hchildReady]
      exact fun heq => (hne heq).elim
    rw [hdeleteEq]
    exact hpacket
  case case8 =>
    rename_i x ks cs hnonempty i hpos ki oldSep hsepOld hne child
      hchild hchildNotReady left hleft hleftReady sep hsep ih
    simp only [i] at hpos hchild hleft hsep
    simp only [ki, i] at hsepOld
    have holdSepEq : oldSep = sep :=
      Option.some.inj (hsepOld.symm.trans hsep)
    subst oldSep
    have hchildAt :
        cs[(findChild ks x - 1) + 1]? = some child := by
      simpa [show findChild ks x - 1 + 1 = findChild ks x by omega]
        using hchild
    have hadjacent :=
      adjacentChildren_shape_depth_height hshape hdepth hleft hchildAt
    have hrotated :=
      rotateLeft_shape_depth_height left sep child hadjacent.1
        hadjacent.2.2.1 hadjacent.2.1 hadjacent.2.2.2.1
        hadjacent.2.2.2.2
    dsimp only at hrotated
    have hrec := ih hrotated.2.1 hrotated.2.2.1
    have hkeys :=
      replaceKeys_shape_depth_height hshape hdepth
        (newKeys :=
          ks.set (findChild ks x - 1)
            (rotateLeft left sep child).2.1)
        (by simp)
    have hleftInstalled :=
      replaceChild_shape_depth_height hkeys.1 hkeys.2.1 hleft
        hrotated.1.1 hrotated.1.2.1 hrotated.1.2.2
    have hchildAfter :
        (cs.set (findChild ks x - 1)
          (rotateLeft left sep child).1)[findChild ks x]? =
            some child := by
      rw [List.getElem?_set_ne (by omega :
        findChild ks x - 1 ≠ findChild ks x)]
      exact hchild
    have hchildInstalled :=
      replaceChild_shape_depth_height hleftInstalled.1
        hleftInstalled.2.1 hchildAfter hrec.1 hrec.2.1
        (hrec.2.2.trans hrotated.2.2.2)
    have hpacket :
        DeletionShape
            (node
              (ks.set (findChild ks x - 1)
                (rotateLeft left sep child).2.1)
              ((cs.set (findChild ks x - 1)
                (rotateLeft left sep child).1).set
                (findChild ks x)
                (composedDelete t x
                  (rotateLeft left sep child).2.2))) ∧
          SameDepth
            (node
              (ks.set (findChild ks x - 1)
                (rotateLeft left sep child).2.1)
              ((cs.set (findChild ks x - 1)
                (rotateLeft left sep child).1).set
                (findChild ks x)
                (composedDelete t x
                  (rotateLeft left sep child).2.2))) ∧
          heightOf
              (node
                (ks.set (findChild ks x - 1)
                  (rotateLeft left sep child).2.1)
                ((cs.set (findChild ks x - 1)
                  (rotateLeft left sep child).1).set
                  (findChild ks x)
                  (composedDelete t x
                    (rotateLeft left sep child).2.2))) =
            heightOf (node ks cs) :=
      ⟨hchildInstalled.1, hchildInstalled.2.1,
        hchildInstalled.2.2.trans
          (hleftInstalled.2.2.trans hkeys.2.2)⟩
    have hnotLeaf : cs.isEmpty = false :=
      Bool.eq_false_of_not_eq_true hnonempty
    have hdeleteEq :
        composedDelete t x (node ks cs) =
          node
            (ks.set (findChild ks x - 1)
              (rotateLeft left sep child).2.1)
            ((cs.set (findChild ks x - 1)
              (rotateLeft left sep child).1).set
              (findChild ks x)
              (composedDelete t x
                (rotateLeft left sep child).2.2)) := by
      rw [composedDelete]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte, hpos]
      rw [hsepOld, hchild, hleft]
      simp [hne, hchildNotReady, hleftReady]
    rw [hdeleteEq]
    exact hpacket
  case case10 =>
    rename_i x ks cs hnonempty i hpos ki oldSep hsepOld hne child
      hchild hchildNotReady left hleft hleftNotReady right hright
      hrightReady sep hsep ih
    simp only [i] at hpos hchild hleft hright hsep
    simp only [ki, i] at hsepOld
    have hadjacent :=
      adjacentChildren_shape_depth_height hshape hdepth hchild hright
    have hrotated :=
      rotateRight_shape_depth_height child sep right hadjacent.1
        hadjacent.2.2.1 hadjacent.2.1 hadjacent.2.2.2.1
        hadjacent.2.2.2.2
    dsimp only at hrotated
    have hrec := ih hrotated.1.1 hrotated.1.2.1
    have hkeys :=
      replaceKeys_shape_depth_height hshape hdepth
        (newKeys :=
          ks.set (findChild ks x)
            (rotateRight child sep right).2.1)
        (by simp)
    have hchildInstalled :=
      replaceChild_shape_depth_height hkeys.1 hkeys.2.1 hchild
        hrec.1 hrec.2.1 (hrec.2.2.trans hrotated.1.2.2)
    have hrightAfter :
        (cs.set (findChild ks x)
          (composedDelete t x
            (rotateRight child sep right).1))[findChild ks x + 1]? =
              some right := by
      rw [List.getElem?_set_ne (by omega :
        findChild ks x ≠ findChild ks x + 1)]
      exact hright
    have hrightInstalled :=
      replaceChild_shape_depth_height hchildInstalled.1
        hchildInstalled.2.1 hrightAfter hrotated.2.1
        hrotated.2.2.1 hrotated.2.2.2
    have hpacket :=
      And.intro hrightInstalled.1
        (And.intro hrightInstalled.2.1
          (hrightInstalled.2.2.trans
            (hchildInstalled.2.2.trans hkeys.2.2)))
    have hnotLeaf : cs.isEmpty = false :=
      Bool.eq_false_of_not_eq_true hnonempty
    have hdeleteEq :
        composedDelete t x (node ks cs) =
          node
            (ks.set (findChild ks x)
              (rotateRight child sep right).2.1)
            ((cs.set (findChild ks x)
              (composedDelete t x
                (rotateRight child sep right).1)).set
              (findChild ks x + 1)
              (rotateRight child sep right).2.2) := by
      rw [composedDelete]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte, hpos]
      rw [hsepOld, hchild, hleft, hright, hsep]
      simp [hne, hchildNotReady, hleftNotReady, hrightReady]
    rw [hdeleteEq]
    exact hpacket
  case case12 =>
    rename_i x ks cs hnonempty i hpos ki oldSep hsepOld hne child
      hchild hchildNotReady left hleft hleftNotReady rightSib
      hrightSib hrightNotReady sep hsep ih
    simp only [i] at hpos hchild hleft hrightSib hsep
    simp only [ki, i] at hsepOld
    have holdSepEq : oldSep = sep :=
      Option.some.inj (hsepOld.symm.trans hsep)
    subst oldSep
    have hchildAt :
        cs[(findChild ks x - 1) + 1]? = some child := by
      simpa [show findChild ks x - 1 + 1 = findChild ks x by omega]
        using hchild
    have hadjacent :=
      adjacentChildren_shape_depth_height hshape hdepth hleft hchildAt
    have hmerged :=
      mergeNodes_shape_depth_height (sep := sep)
        hadjacent.1 hadjacent.2.2.1
        hadjacent.2.1 hadjacent.2.2.2.1 hadjacent.2.2.2.2
    have hrec := ih hmerged.1 hmerged.2.1
    have hsplice :=
      spliceMerged_shape_depth_height hshape hdepth hsep hleft
        hrec.1 hrec.2.1 (hrec.2.2.trans hmerged.2.2)
    have hpacket :
        DeletionShape
            (node
              (ks.take (findChild ks x - 1) ++
                ks.drop (findChild ks x))
              (cs.take (findChild ks x - 1) ++
                [composedDelete t x (mergeNodes left sep child)] ++
                cs.drop (findChild ks x + 1))) ∧
          SameDepth
            (node
              (ks.take (findChild ks x - 1) ++
                ks.drop (findChild ks x))
              (cs.take (findChild ks x - 1) ++
                [composedDelete t x (mergeNodes left sep child)] ++
                cs.drop (findChild ks x + 1))) ∧
          heightOf
              (node
                (ks.take (findChild ks x - 1) ++
                  ks.drop (findChild ks x))
                (cs.take (findChild ks x - 1) ++
                  [composedDelete t x (mergeNodes left sep child)] ++
                  cs.drop (findChild ks x + 1))) =
            heightOf (node ks cs) := by
      simpa [show findChild ks x - 1 + 1 = findChild ks x by omega,
        show findChild ks x - 1 + 2 = findChild ks x + 1 by omega]
        using hsplice
    have hnotLeaf : cs.isEmpty = false :=
      Bool.eq_false_of_not_eq_true hnonempty
    have hdeleteEq :
        composedDelete t x (node ks cs) =
          node
            (ks.take (findChild ks x - 1) ++ ks.drop (findChild ks x))
            (cs.take (findChild ks x - 1) ++
              [composedDelete t x (mergeNodes left sep child)] ++
              cs.drop (findChild ks x + 1)) := by
      rw [composedDelete]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte, hpos]
      rw [hsepOld, hchild, hleft, hrightSib]
      simp [hne, hchildNotReady, hleftNotReady, hrightNotReady]
    rw [hdeleteEq]
    exact hpacket
  case case14 =>
    rename_i x ks cs hnonempty i hpos ki oldSep hsepOld hne child
      hchild hchildNotReady left hleft hleftNotReady hrightNone
      sep hsep ih
    simp only [i] at hpos hchild hleft hrightNone hsep
    simp only [ki, i] at hsepOld
    have holdSepEq : oldSep = sep :=
      Option.some.inj (hsepOld.symm.trans hsep)
    subst oldSep
    have hchildAt :
        cs[(findChild ks x - 1) + 1]? = some child := by
      simpa [show findChild ks x - 1 + 1 = findChild ks x by omega]
        using hchild
    have hadjacent :=
      adjacentChildren_shape_depth_height hshape hdepth hleft hchildAt
    have hmerged :=
      mergeNodes_shape_depth_height (sep := sep)
        hadjacent.1 hadjacent.2.2.1
        hadjacent.2.1 hadjacent.2.2.2.1 hadjacent.2.2.2.2
    have hrec := ih hmerged.1 hmerged.2.1
    have hsplice :=
      spliceMerged_shape_depth_height hshape hdepth hsep hleft
        hrec.1 hrec.2.1 (hrec.2.2.trans hmerged.2.2)
    have hpacket :
        DeletionShape
            (node
              (ks.take (findChild ks x - 1) ++
                ks.drop (findChild ks x))
              (cs.take (findChild ks x - 1) ++
                [composedDelete t x (mergeNodes left sep child)] ++
                cs.drop (findChild ks x + 1))) ∧
          SameDepth
            (node
              (ks.take (findChild ks x - 1) ++
                ks.drop (findChild ks x))
              (cs.take (findChild ks x - 1) ++
                [composedDelete t x (mergeNodes left sep child)] ++
                cs.drop (findChild ks x + 1))) ∧
          heightOf
              (node
                (ks.take (findChild ks x - 1) ++
                  ks.drop (findChild ks x))
                (cs.take (findChild ks x - 1) ++
                  [composedDelete t x (mergeNodes left sep child)] ++
                  cs.drop (findChild ks x + 1))) =
            heightOf (node ks cs) := by
      simpa [show findChild ks x - 1 + 1 = findChild ks x by omega,
        show findChild ks x - 1 + 2 = findChild ks x + 1 by omega]
        using hsplice
    have hnotLeaf : cs.isEmpty = false :=
      Bool.eq_false_of_not_eq_true hnonempty
    have hdeleteEq :
        composedDelete t x (node ks cs) =
          node
            (ks.take (findChild ks x - 1) ++ ks.drop (findChild ks x))
            (cs.take (findChild ks x - 1) ++
              [composedDelete t x (mergeNodes left sep child)] ++
              cs.drop (findChild ks x + 1)) := by
      rw [composedDelete]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte, hpos]
      rw [hsepOld, hchild, hleft, hrightNone]
      simp [hne, hchildNotReady, hleftNotReady]
    rw [hdeleteEq]
    exact hpacket
  case case29 =>
    rename_i x ks cs hnonempty i hnotPos child hchild hchildReady ih
    simp only [i] at hnotPos hchild
    have hchildPacket :=
      child_shape_depth_of_getElem? hshape hdepth hchild
    have hrec := ih hchildPacket.1 hchildPacket.2
    have hpacket :=
      replaceChild_shape_depth_height hshape hdepth hchild
        hrec.1 hrec.2.1 hrec.2.2
    have hnotLeaf : cs.isEmpty = false :=
      Bool.eq_false_of_not_eq_true hnonempty
    have hdeleteEq :
        composedDelete t x (node ks cs) =
          node ks (cs.set 0 (composedDelete t x child)) := by
      rw [composedDelete]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte]
      rw [hchild]
      simp [hchildReady]
      exact fun hpos => (hnotPos hpos).elim
    rw [hdeleteEq]
    exact hpacket
  case case30 =>
    rename_i x ks cs hnonempty i hnotPos child hchild hchildNotReady
      right hright hrightReady sep hsep ih
    simp only [i] at hnotPos hchild hright hsep
    have hadjacent :=
      adjacentChildren_shape_depth_height hshape hdepth hchild hright
    have hrotated :=
      rotateRight_shape_depth_height child sep right hadjacent.1
        hadjacent.2.2.1 hadjacent.2.1 hadjacent.2.2.2.1
        hadjacent.2.2.2.2
    dsimp only at hrotated
    have hrec := ih hrotated.1.1 hrotated.1.2.1
    have hkeys :=
      replaceKeys_shape_depth_height hshape hdepth
        (newKeys := ks.set 0 (rotateRight child sep right).2.1)
        (by simp)
    have hchildInstalled :=
      replaceChild_shape_depth_height hkeys.1 hkeys.2.1 hchild
        hrec.1 hrec.2.1 (hrec.2.2.trans hrotated.1.2.2)
    have hrightAfter :
        (cs.set 0
          (composedDelete t x
            (rotateRight child sep right).1))[1]? = some right := by
      rw [List.getElem?_set_ne (by decide : 0 ≠ 1)]
      exact hright
    have hrightInstalled :=
      replaceChild_shape_depth_height hchildInstalled.1
        hchildInstalled.2.1 hrightAfter hrotated.2.1
        hrotated.2.2.1 hrotated.2.2.2
    have hpacket :=
      And.intro hrightInstalled.1
        (And.intro hrightInstalled.2.1
          (hrightInstalled.2.2.trans
            (hchildInstalled.2.2.trans hkeys.2.2)))
    have hnotLeaf : cs.isEmpty = false :=
      Bool.eq_false_of_not_eq_true hnonempty
    have hdeleteEq :
        composedDelete t x (node ks cs) =
          node (ks.set 0 (rotateRight child sep right).2.1)
            ((cs.set 0
              (composedDelete t x
                (rotateRight child sep right).1)).set 1
              (rotateRight child sep right).2.2) := by
      rw [composedDelete]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte]
      rw [dif_neg hnotPos]
      rw [hchild]
      simp only
      rw [dif_neg hchildNotReady]
      rw [hright]
      simp only
      rw [dif_pos hrightReady]
      rw [hsep]
    rw [hdeleteEq]
    exact hpacket
  case case32 =>
    rename_i x ks cs hnonempty i hnotPos child hchild hchildNotReady
      right hright hrightNotReady sep hsep ih
    simp only [i] at hnotPos hchild hright hsep
    have hadjacent :=
      adjacentChildren_shape_depth_height hshape hdepth hchild hright
    have hmerged :=
      mergeNodes_shape_depth_height (sep := sep)
        hadjacent.1 hadjacent.2.2.1
        hadjacent.2.1 hadjacent.2.2.2.1 hadjacent.2.2.2.2
    have hrec := ih hmerged.1 hmerged.2.1
    have hsplice :=
      spliceMerged_shape_depth_height hshape hdepth hsep hchild
        hrec.1 hrec.2.1 (hrec.2.2.trans hmerged.2.2)
    have hpacket :
        DeletionShape
            (node (ks.drop 1)
              ([composedDelete t x (mergeNodes child sep right)] ++
                cs.drop 2)) ∧
          SameDepth
            (node (ks.drop 1)
              ([composedDelete t x (mergeNodes child sep right)] ++
                cs.drop 2)) ∧
          heightOf
              (node (ks.drop 1)
                ([composedDelete t x (mergeNodes child sep right)] ++
                  cs.drop 2)) =
            heightOf (node ks cs) := by
      simpa using hsplice
    have hnotLeaf : cs.isEmpty = false :=
      Bool.eq_false_of_not_eq_true hnonempty
    have hdeleteEq :
        composedDelete t x (node ks cs) =
          node (ks.drop 1)
            ([composedDelete t x (mergeNodes child sep right)] ++
              cs.drop 2) := by
      rw [composedDelete]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte]
      rw [dif_neg hnotPos]
      rw [hchild]
      simp only
      rw [dif_neg hchildNotReady]
      rw [hright]
      simp only
      rw [dif_neg hrightNotReady]
      rw [hsep]
    rw [hdeleteEq]
    exact hpacket
  case case34 =>
    rename_i x ks cs hnonempty i hnotPos child hchild hchildNotReady
      hrightNone ih
    simp only [i] at hnotPos hchild hrightNone
    have hchildPacket :=
      child_shape_depth_of_getElem? hshape hdepth hchild
    have hrec := ih hchildPacket.1 hchildPacket.2
    have hpacket :=
      replaceChild_shape_depth_height hshape hdepth hchild
        hrec.1 hrec.2.1 hrec.2.2
    have hnotLeaf : cs.isEmpty = false :=
      Bool.eq_false_of_not_eq_true hnonempty
    have hdeleteEq :
        composedDelete t x (node ks cs) =
          node ks (cs.set 0 (composedDelete t x child)) := by
      rw [composedDelete]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte]
      rw [dif_neg hnotPos]
      rw [hchild]
      simp only
      rw [dif_neg hchildNotReady]
      rw [hrightNone]
    rw [hdeleteEq]
    exact hpacket
  all_goals
    exfalso
    try dsimp only at *
    first
      | apply findChild_predecessor_none_absurd <;> assumption
      | apply hshape.rightChildAtKey_none_absurd
        · intro hnil; subst_vars; simp_all
        · assumption
        · assumption
      | apply hshape.childAtKey_none_absurd
        · intro hnil; subst_vars; simp_all
        · assumption
        · assumption
      | apply hshape.separator_none_of_rightChild_absurd <;> assumption
      | apply hshape.findChild_none_absurd
        · intro hnil; subst_vars; simp_all
        · assumption
      | apply getElem?_zero_none_absurd
        · intro hnil; simp_all
        · assumption

/--
Raw composed deletion preserves equal leaf depth and height from recursive
child-count shape and the same-depth invariant alone.
-/
lemma composedDelete_sameDepth_height
    (t x : Nat) {tr : BTree}
    (hbounded : ChildBounded tr) (hdepth : SameDepth tr) :
    SameDepth (composedDelete t x tr) ∧
      heightOf (composedDelete t x tr) = heightOf tr := by
  have hresult :=
    composedDelete_shape_depth_height t x tr
      (deletionShape_of_childBounded tr hbounded) hdepth
  exact ⟨hresult.2.1, hresult.2.2⟩

end CLRS.Chapter18.BTree

import CLRSLean.FourthEdition.Chapter_13.Section_13_2_Rotations.Representation

namespace CLRS.Chapter13
open RBStore (nil)

namespace StoreReprAt

/-- Change only a represented root's parent; all its descendant records agree. -/
theorem reparent {s s' p q i t F} (h : StoreReprAt s p i t F) (hq : q ∉ F)
    (heq : ∀ j ∈ F, s'.get j =
      if j = i then (s.get j).map (fun n => { n with parent := q }) else s.get j) :
    StoreReprAt s' q i t F := by
  cases h with
  | empty => exact .empty _
  | @node p i n l r L R hn hg hp hL hR hnL hnR hd hpo =>
      apply StoreReprAt.node (n := { n with parent := q }) hn
      · simpa [hg] using heq i (by simp)
      · rfl
      · apply hL.of_agree
        intro j hj
        have hji : j ≠ i := by rintro rfl; exact hnL hj
        simpa [hji] using heq j (by simp [hj])
      · apply hR.of_agree
        intro j hj
        have hji : j ≠ i := by rintro rfl; exact hnR hj
        simpa [hji] using heq j (by simp [hj])
      · exact hnL
      · exact hnR
      · exact hd
      · exact hq

end StoreReprAt

/-- Complete subtree replacement contract, including the outside parent link.
Only the old parent's appropriate child field may change outside the footprint. -/
structure RotationResult (s s' : RBStore) (p oldRoot newRoot : Nat)
    (t : RBTree) (F : Finset Nat) : Prop where
  repr : StoreReprAt s' p newRoot t F
  root : s'.root = if p = nil then newRoot else s.root
  outside : ∀ j, j ∉ F → s'.get j =
    if j = p ∧ p ≠ nil then (s.get j).map (reconnectNode oldRoot newRoot) else s.get j

private theorem disjoint_parts {L R : Finset Nat} (h : Disjoint L R) :
    ∀ j, j ∈ L → j ∈ R → False := Finset.disjoint_left.mp h

/-- A successful left rotation refines the functional rotation at any subtree,
including its old parent's link; the footprint is preserved. -/
theorem rotateLeftP_refines_subtree {s p x c A k d B m C F}
    (h : StoreReprAt s p x (.node c A k (.node d B m C)) F) :
    ∃ y, RotationResult s (rotateLeftP s x).1 p x y
      (.node d (.node c A k B) m C) F := by
  cases h with
  | @node p x nx A right L R hx hg hp hA hR hxL hxR hLR hpF =>
    generalize hydef : nx.right = y at *
    cases hR with
    | @node _ _ ny B C M N hy hgy hpy hB hC hyM hyN hMN hxY =>
      have hxy : x ≠ y := by intro he; apply hxR; simp [he]
      have hxM : x ∉ M := by intro hm; apply hxR; simp [hm]
      have hxN : x ∉ N := by intro hn; apply hxR; simp [hn]
      have hyL : y ∉ L := by
        intro hl
        exact disjoint_parts hLR y hl (by simp)
      have hLM : Disjoint L M := by
        apply Finset.disjoint_left.mpr
        intro j hj hm
        exact disjoint_parts hLR j hj (by simp [hm])
      have hLN : Disjoint L N := by
        apply Finset.disjoint_left.mpr
        intro j hj hn
        exact disjoint_parts hLR j hj (by simp [hn])
      have hpx : p ≠ x := by intro he; apply hpF; simp [he]
      have hpy' : p ≠ y := by intro he; apply hpF; simp [he]
      have hpL : p ∉ L := by intro hj; apply hpF; simp [hj]
      have hpM : p ∉ M := by intro hj; apply hpF; simp [hj]
      have hpN : p ∉ N := by intro hj; apply hpF; simp [hj]
      have hbx : ny.left ≠ x := by
        intro he
        have hh := hB.root_mem (by simpa [he] using hx)
        rw [he] at hh
        exact hxM hh
      have hby : ny.left ≠ y := by
        intro he
        have hh := hB.root_mem (by simpa [he] using hy)
        rw [he] at hh
        exact hyM hh
      let s' := rotationPatch s x y ny.left p
        { nx with right := ny.left, parent := y } { ny with left := x, parent := p }
      have hex : (rotateLeftP s x).1 = s' := by
        simp [rotateLeftP, hg, hydef, hgy, hp, s']
      have hframe (j : Nat) (hjx : j ≠ x) (hjy : j ≠ y)
          (hjb : j ≠ ny.left) (hjp : j ≠ p) : s'.get j = s.get j := by
        simp [s', rotationPatch, RBStore.get, hjx, hjy, hjb, hjp]
      have hA' : StoreReprAt s' x nx.left A L := by
        apply hA.of_agree
        intro j hj
        apply hframe
        · rintro rfl; exact hxL hj
        · rintro rfl; exact hyL hj
        · intro he
          have hb0 : ny.left ≠ nil := by
            intro hb0
            rw [he, hb0] at hj
            exact hA.nil_not_mem hj
          exact disjoint_parts hLM j hj (he ▸ hB.root_mem hb0)
        · rintro rfl; exact hpL hj
      have hC' : StoreReprAt s' y ny.right C N := by
        apply hC.of_agree
        intro j hj
        apply hframe
        · rintro rfl; exact hxN hj
        · rintro rfl; exact hyN hj
        · intro he
          have hb0 : ny.left ≠ nil := by
            intro hb0
            rw [he, hb0] at hj
            exact hC.nil_not_mem hj
          exact disjoint_parts hMN j (he ▸ hB.root_mem hb0) hj
        · rintro rfl; exact hpN hj
      have hB' : StoreReprAt s' x ny.left B M := by
        apply hB.reparent hxM
        intro j hj
        have hjx : j ≠ x := by rintro rfl; exact hxM hj
        have hjy : j ≠ y := by rintro rfl; exact hyM hj
        have hjp : j ≠ p := by rintro rfl; exact hpM hj
        have hj0 : j ≠ nil := by rintro rfl; exact hB.nil_not_mem hj
        by_cases hjb : j = ny.left
        · have hb0 : ny.left ≠ nil := by simpa [← hjb] using hj0
          simp [s', rotationPatch, RBStore.get, hjb, hb0, hbx, hby]
        · simp [s', rotationPatch, RBStore.get, hjx, hjy, hjp, hjb]
      have hx' : s'.get x = some { nx with right := ny.left, parent := y } := by
        simp [s', rotationPatch, RBStore.get]
      have hy' : s'.get y = some { ny with left := x, parent := p } := by
        simp [s', rotationPatch, RBStore.get, Ne.symm hxy]
      have hnewX : StoreReprAt s' y x (.node nx.color A nx.key B) (insert x (L ∪ M)) := by
        apply StoreReprAt.node hx hx' rfl hA' hB' hxL hxM hLM
        simp [Ne.symm hxy, hyL, hyM]
      have hnewY : StoreReprAt s' p y
          (.node ny.color (.node nx.color A nx.key B) ny.key C)
          (insert y (insert x (L ∪ M) ∪ N)) := by
        apply StoreReprAt.node hy hy' rfl hnewX hC'
        · simp [Ne.symm hxy, hyL, hyM]
        · exact hyN
        · simp [Finset.disjoint_insert_left, hxN, Finset.disjoint_union_left, hLN, hMN]
        · simp [hpx, hpy', hpL, hpM, hpN]
      refine ⟨y, ?_⟩
      rw [hex]
      constructor
      · convert hnewY using 1
        ext j
        simp [or_left_comm]
      · simp [s', rotationPatch]
      · intro j hj
        have hjx : j ≠ x := by intro he; apply hj; simp [he]
        have hjy : j ≠ y := by intro he; apply hj; simp [he]
        have hjb : j ≠ ny.left ∨ ny.left = nil := by
          by_cases hb : ny.left = nil
          · exact Or.inr hb
          · left
            intro he
            apply hj
            have hh := hB.root_mem hb
            simp [he, hh]
        rcases hjb with hjb | hb
        · simp [s', rotationPatch, RBStore.get, hjx, hjy, hjb]
        · simp [s', rotationPatch, RBStore.get, hjx, hjy, hb]


/-- The symmetric right-rotation subtree refinement, including reconnection to
an external parent and preservation of all other external records. -/
theorem rotateRightP_refines_subtree {s p x c A k d B m C F}
    (h : StoreReprAt s p x (.node c (.node d A m B) k C) F) :
    ∃ y, RotationResult s (rotateRightP s x).1 p x y
      (.node d A m (.node c B k C)) F := by
  cases h with
  | @node p x nx left C R L hx hg hp hR hA hxR hxL hRL hpF =>
    have hLR := hRL.symm
    generalize hydef : nx.left = y at *
    cases hR with
    | @node _ _ ny A B N M hy hgy hpy hC hB hyN hyM hNM hxY =>
      have hMN := hNM.symm
      have hxy : x ≠ y := by intro he; apply hxR; simp [he]
      have hxM : x ∉ M := by intro hm; apply hxR; simp [hm]
      have hxN : x ∉ N := by intro hn; apply hxR; simp [hn]
      have hyL : y ∉ L := by
        intro hl
        exact disjoint_parts hLR y hl (by simp)
      have hLM : Disjoint L M := by
        apply Finset.disjoint_left.mpr
        intro j hj hm
        exact disjoint_parts hLR j hj (by simp [hm])
      have hLN : Disjoint L N := by
        apply Finset.disjoint_left.mpr
        intro j hj hn
        exact disjoint_parts hLR j hj (by simp [hn])
      have hpx : p ≠ x := by intro he; apply hpF; simp [he]
      have hpy' : p ≠ y := by intro he; apply hpF; simp [he]
      have hpL : p ∉ L := by intro hj; apply hpF; simp [hj]
      have hpM : p ∉ M := by intro hj; apply hpF; simp [hj]
      have hpN : p ∉ N := by intro hj; apply hpF; simp [hj]
      have hbx : ny.right ≠ x := by
        intro he
        have hh := hB.root_mem (by simpa [he] using hx)
        rw [he] at hh
        exact hxM hh
      have hby : ny.right ≠ y := by
        intro he
        have hh := hB.root_mem (by simpa [he] using hy)
        rw [he] at hh
        exact hyM hh
      let s' := rotationPatch s x y ny.right p
        { nx with left := ny.right, parent := y } { ny with right := x, parent := p }
      have hex : (rotateRightP s x).1 = s' := by
        simp [rotateRightP, hg, hydef, hgy, hp, s']
      have hframe (j : Nat) (hjx : j ≠ x) (hjy : j ≠ y)
          (hjb : j ≠ ny.right) (hjp : j ≠ p) : s'.get j = s.get j := by
        simp [s', rotationPatch, RBStore.get, hjx, hjy, hjb, hjp]
      have hA' : StoreReprAt s' x nx.right C L := by
        apply hA.of_agree
        intro j hj
        apply hframe
        · rintro rfl; exact hxL hj
        · rintro rfl; exact hyL hj
        · intro he
          have hb0 : ny.right ≠ nil := by
            intro hb0
            rw [he, hb0] at hj
            exact hA.nil_not_mem hj
          exact disjoint_parts hLM j hj (he ▸ hB.root_mem hb0)
        · rintro rfl; exact hpL hj
      have hC' : StoreReprAt s' y ny.left A N := by
        apply hC.of_agree
        intro j hj
        apply hframe
        · rintro rfl; exact hxN hj
        · rintro rfl; exact hyN hj
        · intro he
          have hb0 : ny.right ≠ nil := by
            intro hb0
            rw [he, hb0] at hj
            exact hC.nil_not_mem hj
          exact disjoint_parts hMN j (he ▸ hB.root_mem hb0) hj
        · rintro rfl; exact hpN hj
      have hB' : StoreReprAt s' x ny.right B M := by
        apply hB.reparent hxM
        intro j hj
        have hjx : j ≠ x := by rintro rfl; exact hxM hj
        have hjy : j ≠ y := by rintro rfl; exact hyM hj
        have hjp : j ≠ p := by rintro rfl; exact hpM hj
        have hj0 : j ≠ nil := by rintro rfl; exact hB.nil_not_mem hj
        by_cases hjb : j = ny.right
        · have hb0 : ny.right ≠ nil := by simpa [← hjb] using hj0
          simp [s', rotationPatch, RBStore.get, hjb, hb0, hbx, hby]
        · simp [s', rotationPatch, RBStore.get, hjx, hjy, hjp, hjb]
      have hx' : s'.get x = some { nx with left := ny.right, parent := y } := by
        simp [s', rotationPatch, RBStore.get]
      have hy' : s'.get y = some { ny with right := x, parent := p } := by
        simp [s', rotationPatch, RBStore.get, Ne.symm hxy]
      have hnewX : StoreReprAt s' y x (.node nx.color B nx.key C) (insert x (M ∪ L)) := by
        apply StoreReprAt.node hx hx' rfl hB' hA' hxM hxL hLM.symm
        simp [Ne.symm hxy, hyL, hyM]
      have hnewY : StoreReprAt s' p y
          (.node ny.color A ny.key (.node nx.color B nx.key C))
          (insert y (N ∪ insert x (M ∪ L))) := by
        apply StoreReprAt.node hy hy' rfl hC' hnewX
        · exact hyN
        · simp [Ne.symm hxy, hyL, hyM]
        · simp [Finset.disjoint_insert_right, hxN, Finset.disjoint_union_right, hLN.symm, hMN.symm]
        · simp [hpx, hpy', hpL, hpM, hpN]
      refine ⟨y, ?_⟩
      rw [hex]
      constructor
      · convert hnewY using 1
        ext j
        simp [or_left_comm, or_comm]
      · simp [s', rotationPatch]
      · intro j hj
        have hjx : j ≠ x := by intro he; apply hj; simp [he]
        have hjy : j ≠ y := by intro he; apply hj; simp [he]
        have hjb : j ≠ ny.right ∨ ny.right = nil := by
          by_cases hb : ny.right = nil
          · exact Or.inr hb
          · left
            intro he
            apply hj
            have hh := hB.root_mem hb
            simp [he, hh]
        rcases hjb with hjb | hb
        · simp [s', rotationPatch, RBStore.get, hjx, hjy, hjb]
        · simp [s', rotationPatch, RBStore.get, hjx, hjy, hb]


/-- A replacement never writes the sentinel record. -/
theorem RotationResult.sentinel {s s' p i j t F}
    (h : RotationResult s s' p i j t F) : s'.get nil = s.get nil := by
  have hf := h.outside nil h.repr.nil_not_mem
  have hn : ¬ (nil = p ∧ p ≠ nil) := by rintro ⟨rfl, hp⟩; exact hp rfl
  simpa [hn] using hf

/-- A replacement at root level is a whole-store representation refinement. -/
theorem RotationResult.represents {s s' i j t F}
    (h : RotationResult s s' nil i j t F) (hs : s.get nil = none) : Represents s' t := by
  refine ⟨h.sentinel.trans hs, F, ?_⟩
  have hr : s'.root = j := by simpa using h.root
  simpa [hr] using h.repr

/-- Actual left rotation at the store root refines the functional rotation. -/
theorem rotateLeftP_refines_root {s c A k d B m C}
    (h : Represents s (.node c A k (.node d B m C))) :
    Represents (rotateLeftP s s.root).1 (.node d (.node c A k B) m C) := by
  obtain ⟨hs, F, ht⟩ := h
  obtain ⟨y, hres⟩ := rotateLeftP_refines_subtree ht
  exact hres.represents hs

/-- Actual right rotation at the store root refines the functional rotation. -/
theorem rotateRightP_refines_root {s c A k d B m C}
    (h : Represents s (.node c (.node d A m B) k C)) :
    Represents (rotateRightP s s.root).1 (.node d A m (.node c B k C)) := by
  obtain ⟨hs, F, ht⟩ := h
  obtain ⟨y, hres⟩ := rotateRightP_refines_subtree ht
  exact hres.represents hs

@[simp] theorem reconnectNode_self (i : Nat) (n : RBNode) : reconnectNode i i n = n := by
  unfold reconnectNode
  split
  · rename_i h
    cases n
    simp_all
  · split
    · rename_i h
      cases n
      simp_all
    · rfl

@[simp] theorem reconnectNode_self_fun (i : Nat) : reconnectNode i i = id :=
  funext (reconnectNode_self i)

/-- Lift a subtree replacement through a left-child context. This theorem
checks the actual updated parent record and frames the sibling subtree. -/
theorem RotationResult.lift_left {s s' p i n l r L R j l'}
    (hi : i ≠ nil) (hg : s.get i = some n) (hp : n.parent = p)
    (hl : StoreReprAt s i n.left l L) (hr : StoreReprAt s i n.right r R)
    (hiL : i ∉ L) (hiR : i ∉ R) (hd : Disjoint L R)
    (hpF : p ∉ insert i (L ∪ R)) (hroot : p = nil → s.root = i)
    (h : RotationResult s s' i n.left j l' L) :
    RotationResult s s' p i i (.node n.color l' n.key r) (insert i (L ∪ R)) := by
  have hget : s'.get i = some { n with left := j } := by
    simpa [hi, hg, reconnectNode] using h.outside i hiL
  have hr' : StoreReprAt s' i n.right r R := by
    apply hr.of_agree
    intro k hk
    have hkL : k ∉ L := fun hkl => disjoint_parts hd k hkl hk
    have hki : k ≠ i := by rintro rfl; exact hiR hk
    simpa [hki] using h.outside k hkL
  constructor
  · exact StoreReprAt.node (n := { n with left := j }) hi hget hp h.repr hr' hiL hiR hd hpF
  · have hsroot : s'.root = s.root := by simpa [hi] using h.root
    rw [hsroot]
    split
    · exact hroot ‹p = nil›
    · rfl
  · intro k hk
    have hkL : k ∉ L := by intro hkl; apply hk; simp [hkl]
    have hki : k ≠ i := by intro he; apply hk; simp [he]
    simpa [hki, reconnectNode_self] using h.outside k hkL

/-- Lift a subtree replacement through a right-child context. The non-NIL
child condition covers every context on a path to a rotated node. -/
theorem RotationResult.lift_right {s s' p i n l r L R j r'}
    (hi : i ≠ nil) (hg : s.get i = some n) (hp : n.parent = p)
    (hl : StoreReprAt s i n.left l L) (hr : StoreReprAt s i n.right r R)
    (hr0 : n.right ≠ nil)
    (hiL : i ∉ L) (hiR : i ∉ R) (hd : Disjoint L R)
    (hpF : p ∉ insert i (L ∪ R)) (hroot : p = nil → s.root = i)
    (h : RotationResult s s' i n.right j r' R) :
    RotationResult s s' p i i (.node n.color l n.key r') (insert i (L ∪ R)) := by
  have hne : n.left ≠ n.right := by
    intro he
    have hmL := hl.root_mem (by simpa [he] using hr0)
    rw [he] at hmL
    exact disjoint_parts hd n.right hmL (hr.root_mem hr0)
  have hget : s'.get i = some { n with right := j } := by
    simpa [hi, hg, reconnectNode, hne] using h.outside i hiR
  have hl' : StoreReprAt s' i n.left l L := by
    apply hl.of_agree
    intro k hk
    have hkR : k ∉ R := fun hkr => disjoint_parts hd k hk hkr
    have hki : k ≠ i := by rintro rfl; exact hiL hk
    simpa [hki] using h.outside k hkR
  constructor
  · exact StoreReprAt.node (n := { n with right := j }) hi hget hp hl' h.repr hiL hiR hd hpF
  · have hsroot : s'.root = s.root := by simpa [hi] using h.root
    rw [hsroot]
    split
    · exact hroot ‹p = nil›
    · rfl
  · intro k hk
    have hkR : k ∉ R := by intro hkr; apply hk; simp [hkr]
    have hki : k ≠ i := by intro he; apply hk; simp [he]
    simpa [hki, reconnectNode_self] using h.outside k hkR

/-- A represented path from a subtree to its enclosing tree. Each frame owns
its sibling footprint and validates the actual parent record. -/
inductive RotationContext (s : RBStore) :
    Nat → Nat → Finset Nat → Nat → Nat → Finset Nat → (RBTree → RBTree) → Prop where
  | hole (p i : Nat) (F : Finset Nat) (hroot : p = nil → s.root = i) :
      RotationContext s p i F p i F id
  | left {p x F q i n l r L R plug}
      (inner : RotationContext s p x F i n.left L plug)
      (hi : i ≠ nil) (hg : s.get i = some n) (hp : n.parent = q)
      (hl : StoreReprAt s i n.left l L) (hr : StoreReprAt s i n.right r R)
      (hiL : i ∉ L) (hiR : i ∉ R) (hd : Disjoint L R)
      (hqF : q ∉ insert i (L ∪ R)) (hroot : q = nil → s.root = i) :
      RotationContext s p x F q i (insert i (L ∪ R))
        (fun t => .node n.color (plug t) n.key r)
  | right {p x F q i n l r L R plug}
      (inner : RotationContext s p x F i n.right R plug)
      (hi : i ≠ nil) (hg : s.get i = some n) (hp : n.parent = q)
      (hl : StoreReprAt s i n.left l L) (hr : StoreReprAt s i n.right r R)
      (hr0 : n.right ≠ nil)
      (hiL : i ∉ L) (hiR : i ∉ R) (hd : Disjoint L R)
      (hqF : q ∉ insert i (L ∪ R)) (hroot : q = nil → s.root = i) :
      RotationContext s p x F q i (insert i (L ∪ R))
        (fun t => .node n.color l n.key (plug t))

/-- Lift an actual rotation through any represented ancestor path. The result
retains the whole enclosing footprint and its outside-node frame contract. -/
theorem RotationResult.lift_context {s s' p x j t F q z G plug}
    (h : RotationResult s s' p x j t F)
    (ctx : RotationContext s p x F q z G plug) :
    ∃ z', RotationResult s s' q z z' (plug t) G := by
  induction ctx with
  | hole => exact ⟨j, h⟩
  | left inner hi hg hp hl hr hiL hiR hd hqF hroot ih =>
    obtain ⟨j', hj⟩ := ih
    exact ⟨_, hj.lift_left hi hg hp hl hr hiL hiR hd hqF hroot⟩
  | right inner hi hg hp hl hr hr0 hiL hiR hd hqF hroot ih =>
    obtain ⟨j', hj⟩ := ih
    exact ⟨_, hj.lift_right hi hg hp hl hr hr0 hiL hiR hd hqF hroot⟩

/-- Left rotation at an arbitrary represented interior position refines the
functional rotation plugged back through its enclosing path. -/
theorem rotateLeftP_refines_context {s p x F z G plug c A k d B m C}
    (hs : s.get nil = none)
    (h : StoreReprAt s p x (.node c A k (.node d B m C)) F)
    (ctx : RotationContext s p x F nil z G plug) :
    Represents (rotateLeftP s x).1 (plug (.node d (.node c A k B) m C)) := by
  obtain ⟨y, hy⟩ := rotateLeftP_refines_subtree h
  obtain ⟨z', hz⟩ := hy.lift_context ctx
  exact hz.represents hs

/-- Right rotation at an arbitrary represented interior position refines the
functional rotation plugged back through its enclosing path. -/
theorem rotateRightP_refines_context {s p x F z G plug c A k d B m C}
    (hs : s.get nil = none)
    (h : StoreReprAt s p x (.node c (.node d A m B) k C) F)
    (ctx : RotationContext s p x F nil z G plug) :
    Represents (rotateRightP s x).1 (plug (.node d A m (.node c B k C))) := by
  obtain ⟨y, hy⟩ := rotateRightP_refines_subtree h
  obtain ⟨z', hz⟩ := hy.lift_context ctx
  exact hz.represents hs

/-- Missing rotation roots leave the whole store unchanged. -/
theorem rotateLeftP_missing (s : RBStore) (i : Nat) (h : s.get i = none) :
    rotateLeftP s i = (s, 0) := by simp [rotateLeftP, h]

/-- Missing rotation roots leave the whole store unchanged. -/
theorem rotateRightP_missing (s : RBStore) (i : Nat) (h : s.get i = none) :
    rotateRightP s i = (s, 0) := by simp [rotateRightP, h]

/-- A missing right child makes left rotation a no-op. -/
theorem rotateLeftP_missing_child (s : RBStore) (i : Nat) (n : RBNode)
    (hi : s.get i = some n) (hc : s.get n.right = none) :
    rotateLeftP s i = (s, 0) := by simp [rotateLeftP, hi, hc]

/-- A missing left child makes right rotation a no-op. -/
theorem rotateRightP_missing_child (s : RBStore) (i : Nat) (n : RBNode)
    (hi : s.get i = some n) (hc : s.get n.left = none) :
    rotateRightP s i = (s, 0) := by simp [rotateRightP, hi, hc]

end CLRS.Chapter13

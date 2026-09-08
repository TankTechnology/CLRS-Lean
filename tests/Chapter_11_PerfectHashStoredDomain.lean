import CLRSLean.FourthEdition.Chapter_11.Section_11_5_Perfect_Hashing
open CLRS.Chapter11

-- A nonstored key may share both hashes with a stored key.
private def collidingNonmember : PerfectHashTable (Fin 2) 1 where
  keys := {0}
  prim := fun _ => 0
  sec := fun _ _ => 0
  table := fun _ s => if s = 0 then some 0 else none
  sec_inj := by
    intro j x y hx hy _ _ _
    simpa using (Finset.mem_singleton.mp hx).trans (Finset.mem_singleton.mp hy).symm
  table_stores_keys := by
    intro x hx
    have hx0 : x = 0 := Finset.mem_singleton.mp hx
    subst x
    simp
  table_only_keys := by
    intro j s x hx
    split at hx
    next hs =>
      have hx0 : x = 0 := (Option.some.inj hx).symm
      subst x
      exact ⟨by simp, Subsingleton.elim _ _, hs.symm⟩
    next => contradiction

example : perfectSearch collidingNonmember 0 := by
  rw [perfectSearch_iff_mem]
  simp [collidingNonmember]

example : ¬ perfectSearch collidingNonmember 1 := by
  rw [perfectSearch_iff_mem]
  simp [collidingNonmember]

example : collidingNonmember.sec 0 0 = collidingNonmember.sec 0 1 := rfl

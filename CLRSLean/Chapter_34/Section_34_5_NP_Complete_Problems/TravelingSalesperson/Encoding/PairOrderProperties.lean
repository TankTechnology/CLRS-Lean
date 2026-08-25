import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.Encoding.Basic
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.Complement

/-! # Structural properties of the canonical TSP matrix order -/

namespace CLRS.Chapter34

/-- The TSP matrix and graph-complement developments use the same canonical
strict-pair order. -/
theorem tspNormalizedPairs_eq_vertexCoverNormalizedPairs (n : Nat) :
    tspNormalizedPairs n = vertexCoverNormalizedPairs n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [tspNormalizedPairs, vertexCoverNormalizedPairs, ih]

theorem tspNormalizedPairs_nodup (n : Nat) :
    (tspNormalizedPairs n).Nodup := by
  induction n with
  | zero => simp [tspNormalizedPairs]
  | succ n ih =>
      rw [tspNormalizedPairs, List.nodup_append']
      refine ⟨ih, ?_, ?_⟩
      · exact (List.nodup_range.map fun left right heq => by
          simpa using congrArg Prod.fst heq)
      · rw [List.disjoint_left]
        intro pair hprior hnew
        have hpriorBounds := mem_tspNormalizedPairs_iff.mp hprior
        rcases List.mem_map.mp hnew with ⟨lower, hlower, heq⟩
        have hsecond := congrArg Prod.snd heq
        simp only at hsecond
        omega

theorem tspPairOrientations_nodup {pair : Nat × Nat}
    (hlt : pair.1 < pair.2) :
    (tspPairOrientations pair).Nodup := by
  rcases pair with ⟨u, v⟩
  simp [tspPairOrientations, Prod.ext_iff]
  omega

private theorem tspPairOrientations_disjoint
    {left right : Nat × Nat}
    (hleft : left.1 < left.2) (hright : right.1 < right.2)
    (hne : left ≠ right) :
    List.Disjoint (tspPairOrientations left) (tspPairOrientations right) := by
  rw [List.disjoint_left]
  intro pair hpairLeft hpairRight
  simp only [tspPairOrientations, List.mem_cons, List.not_mem_nil,
    or_false] at hpairLeft hpairRight
  rcases hpairLeft with hforward | hreverse <;>
    rcases hpairRight with hforward' | hreverse'
  · exact hne (hforward.symm.trans hforward')
  · have heq := hforward.symm.trans hreverse'
    have hfirst := congrArg Prod.fst heq
    have hsecond := congrArg Prod.snd heq
    simp only at hfirst hsecond
    omega
  · have heq := hreverse.symm.trans hforward'
    have hfirst := congrArg Prod.fst heq
    have hsecond := congrArg Prod.snd heq
    simp only at hfirst hsecond
    omega
  · have heq := hreverse.symm.trans hreverse'
    apply hne
    exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)

theorem tspOrientations_nodup (n : Nat) :
    ((tspNormalizedPairs n).flatMap tspPairOrientations).Nodup := by
  rw [List.nodup_flatMap]
  refine ⟨?_, ?_⟩
  · intro pair hpair
    exact tspPairOrientations_nodup
      (mem_tspNormalizedPairs_iff.mp hpair).1
  · exact (tspNormalizedPairs_nodup n).imp_of_mem (by
      intro left right hleft hright hne
      exact tspPairOrientations_disjoint
        (mem_tspNormalizedPairs_iff.mp hleft).1
        (mem_tspNormalizedPairs_iff.mp hright).1 hne)

/-- The physical complete-matrix order contains every directed pair exactly
once. -/
theorem tspPairOrder_nodup (n : Nat) : (tspPairOrder n).Nodup := by
  rw [tspPairOrder, List.nodup_append']
  refine ⟨?_, tspOrientations_nodup n, ?_⟩
  · exact (List.nodup_range.map fun left right heq => by
      simpa using congrArg Prod.fst heq)
  · rw [List.disjoint_left]
    intro pair hdiagonal horientation
    rcases List.mem_map.mp hdiagonal with ⟨vertex, hvertex, rfl⟩
    rcases List.mem_flatMap.mp horientation with
      ⟨normalized, hnormalized, horientation⟩
    have hlt := (mem_tspNormalizedPairs_iff.mp hnormalized).1
    rcases normalized with ⟨u, v⟩
    simp [tspPairOrientations, Prod.ext_iff] at horientation
    rcases horientation with heq | heq <;> omega

/-- Aligned lookup followed over the same duplicate-free key list recovers
the entire value stream. -/
theorem map_lookupTSPWeight_eq (pairs : List (Nat × Nat))
    (weights : List Nat) (hnodup : pairs.Nodup)
    (hlength : weights.length = pairs.length) :
    pairs.map (fun pair =>
      lookupTSPWeight pairs weights pair.1 pair.2) = weights := by
  induction pairs generalizing weights with
  | nil =>
      cases weights with
      | nil => rfl
      | cons weight weights => simp at hlength
  | cons pair pairs ih =>
      cases weights with
      | nil => simp at hlength
      | cons weight weights =>
          simp only [List.nodup_cons] at hnodup
          simp only [List.length_cons, Nat.succ.injEq] at hlength
          rw [List.map_cons]
          simp only [lookupTSPWeight, ↓reduceIte]
          apply congrArg (weight :: ·)
          calc
            pairs.map (fun next =>
                lookupTSPWeight (pair :: pairs) (weight :: weights)
                  next.1 next.2) =
                pairs.map (fun next =>
                  lookupTSPWeight pairs weights next.1 next.2) := by
              apply List.map_congr_left
              intro next hnext
              simp only [lookupTSPWeight]
              rw [if_neg]
              intro heq
              exact hnodup.1 (heq ▸ hnext)
            _ = weights := ih weights hnodup.2 hlength

/-- Every well-sized raw matrix is its canonical key order mapped through the
lookup operation used by `TSPData.toInstance`. -/
theorem tspWeights_eq_map_lookup (data : TSPData)
    (hshape : data.weights.length = data.vertexCount * data.vertexCount) :
    data.weights =
      (tspPairOrder data.vertexCount).map fun pair =>
        lookupTSPWeight (tspPairOrder data.vertexCount) data.weights
          pair.1 pair.2 := by
  symm
  apply map_lookupTSPWeight_eq
  · exact tspPairOrder_nodup _
  · simpa using hshape

end CLRS.Chapter34

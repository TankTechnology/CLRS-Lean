import CLRSLean.FourthEdition.Chapter_11

/-! # Chapter 11 public proof interface -/

#check CLRS.Chapter11.openSearch_openInsert
#check CLRS.Chapter11.linearProbe_bijective
#check CLRS.Chapter11.doubleHashProbe_bijective
#check CLRS.Chapter11.expectedUnsuccessfulProbes_le
#check CLRS.Chapter11.expectedSuccessfulProbes_le_ln

-- Explicit uniform-permutation provenance for the Section 11.4 probability model.
#check CLRS.Chapter11.firstProbesOccupied
#check CLRS.Chapter11.uniformProbeTailProbability
#check CLRS.Chapter11.uniformProbeTailProbability_eq_probeTail
#check CLRS.Chapter11.uniformUnsuccessfulProbeCount
#check CLRS.Chapter11.uniformUnsuccessfulExpectedProbes_eq
#check CLRS.Chapter11.uniformUnsuccessfulExpectedProbes_le
#check CLRS.Chapter11.uniformInsertionExpectedProbes_le
#check CLRS.Chapter11.uniformSuccessfulExpectedProbes_le_ln

-- Small finite cardinality regressions for the counting theorem.
example :
    (CLRS.Chapter11.occupiedPrefixPermutations
      (CLRS.Chapter11.canonicalOccupied 3 2) 1).card = 4 := by
  rw [CLRS.Chapter11.firstProbesOccupied_card _ (by decide)]
  decide

example :
    (CLRS.Chapter11.occupiedPrefixPermutations
      (CLRS.Chapter11.canonicalOccupied 4 3) 2).card = 12 := by
  rw [CLRS.Chapter11.firstProbesOccupied_card _ (by decide)]
  decide

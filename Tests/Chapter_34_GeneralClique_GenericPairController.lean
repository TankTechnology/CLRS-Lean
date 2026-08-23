import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesGenericRuntime

open CLRS.Chapter34
open CLRS.Chapter34.Turing
open CLRS.Chapter34.Turing.TMClique

private def sampleEntries : List (IndexedOccurrence × Nat) :=
  [({ clauseIndex := 0, positionIndex := 0, literal := .pos 0 }, 2),
   ({ clauseIndex := 1, positionIndex := 0, literal := .pos 0 }, 5)]

example :
    encodeCompatibleOccurrenceIterations sampleEntries.reverse =
      encodeCliqueEdge (2, 5) := by
  native_decide

example : compatibilityEdgesEntriesSteps [] = 3 := by
  native_decide

#check compatibilityEdges_entriesRun
#check compatibilityEdgesEntriesSteps_le_input
#check compatibilityEdgesEntries_computableInPolyTime

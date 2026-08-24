import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Public
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Reduction
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.SatTo3CNFMachine
import CLRSLean.Chapter_34.Section_34_3_NP_Completeness_And_Reducibility.Hardness

/-! # Textbook general CLIQUE is NP-complete -/

namespace CLRS.Chapter34

/-- 3-CNF-SAT is NP-hard through the concrete SAT-to-3-CNF machine. -/
theorem threeCNFSat_npHard : NPHard ThreeCNFSat :=
  NPHard.of_reducible SAT_npHard
    Turing.TM3CNF.sat_reducible_to_threeCNFSat

/-- The honest serialized graph-plus-`k` CLIQUE language is NP-hard. -/
theorem generalCLIQUE_npHard : NPHard GeneralCLIQUE :=
  NPHard.of_reducible threeCNFSat_npHard
    Turing.TMClique.threeCNFSat_reducible_to_generalCLIQUE

/-- The honest serialized graph-plus-`k` CLIQUE language is NP-complete. -/
theorem generalCLIQUE_npComplete : NPComplete GeneralCLIQUE :=
  ⟨generalCLIQUE_polyTimeVerifiable, generalCLIQUE_npHard⟩

/-- Public textbook spelling of the general CLIQUE NP-completeness theorem. -/
theorem CLIQUE_npComplete : NPComplete CLIQUE :=
  generalCLIQUE_npComplete

end CLRS.Chapter34

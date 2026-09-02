import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.NP
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.PolynomialRuntime

/-!
# Public textbook CLIQUE interface

The public `CLIQUE` name now denotes the honest serialized graph-plus-`k`
language.  The specialized occurrence-graph language remains available under
its explicit `ThreeCNFOccurrenceCLIQUE` name.
-/

namespace CLRS.Chapter34

/-- The textbook general graph-plus-`k` CLIQUE language. -/
abbrev CLIQUE : Language CliqueSym := GeneralCLIQUE

namespace Turing.TMClique

/-- The concrete polynomial-time reduction from 3-CNF-SAT to textbook
general CLIQUE. -/
theorem threeCNFSat_reducible_to_CLIQUE :
    PolyTimeReducible ThreeCNFSat CLIQUE :=
  threeCNFSat_reducible_to_generalCLIQUE

end Turing.TMClique
end CLRS.Chapter34

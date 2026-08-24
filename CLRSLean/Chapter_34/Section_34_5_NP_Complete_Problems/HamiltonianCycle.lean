import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Instance
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.CycleInterface
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Language
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Certificate
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.RawReduction
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.RawReductionLength

/-!
# HAM-CYCLE

Exports the honest shared graph encoding, ordered Hamiltonian-cycle semantics,
the total raw certificate checker, exact checker semantics, quadratic
certificate bound, and the total typed VERTEX-COVER reduction with a proved
semantic equivalence.  The typed construction is also lifted to a total raw
map with exact all-input language semantics and a cubic output-length bound.
Fixed reduction and verifier machines remain the next closure layers.
-/

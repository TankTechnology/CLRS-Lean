import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.BoundaryCircuits.Static
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.BoundaryCircuits.Initial
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.BoundaryCircuits.Accepting
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.BoundaryCircuits.Symbolic

/-!
# CLRS Section 34.4 - Exact tableau boundary constraints

This facade exports zero-gate pool-backed static rows, total concrete initial
and accepting constraints, and the symbolic-input initial form needed by the
whole-tableau verifier.  Both concrete constructors reject unencodable targets
with an actual constant-false circuit output.
-/

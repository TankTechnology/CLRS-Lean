import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Syntax
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Machine
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Macros
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Clock

/-!
# Verified bounded TM2 builders

This facade exposes the typed builder language, its independent semantics, the
concrete TM2 compiler, one-step agreement, exact bounded-run transport to TM2
output witnesses, and polynomial-time packaging.  The verified scan/copy,
symbol-local bounded-loop, and ordered-pair nested-loop macros are present with
canonical exact builder and compiled runs.  The nested loop computes row-major
pair output while clearing every scratch stack.  The clock layer repeatedly
composes that quadratic machine to supply concrete clocks of any required
fixed polynomial degree.
-/

import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.StatementCircuits.Core
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.StatementCircuits.Trace
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.StatementCircuits.Semantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.StatementCircuits.Bounds

/-!
# CLRS Section 34.4 - Recursive TM2 statement circuits

Reader-facing facade for recursive bundled-statement circuit compilation.
The implementation is split into a finite-control compiler core, exact decoded
structural gate traces, semantics, and emitted-gate bounds so each proof layer
can be checked narrowly.
-/

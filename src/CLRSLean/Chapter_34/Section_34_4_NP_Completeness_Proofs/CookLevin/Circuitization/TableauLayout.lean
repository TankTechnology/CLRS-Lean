import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.TableauLayout.Core
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.TableauLayout.Allocation
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.TableauLayout.Assignment

/-!
# Whole-tableau row layout

This facade exports consecutive row intervals, proof-carrying serial input-gate
allocation, and exact per-row assignment semantics.  It does not assemble
boundary or transition constraints.
-/

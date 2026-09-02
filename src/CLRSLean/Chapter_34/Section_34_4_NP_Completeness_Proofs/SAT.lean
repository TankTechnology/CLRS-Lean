import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.SAT.NPCompleteness

/-!
# Standalone SAT verification and NP-completeness

This facade exposes the canonical raw assignment format, total checker, exact
all-input acceptance semantics, and linear certificate bound for {lit}`SAT`.
It also exposes a fixed polynomial-time reduction-backed verifier and the
public {lit}`SAT_mem_ClassNP` and {lit}`SAT_npComplete` theorems.  Compiling the
smaller assignment checker itself to a fixed machine remains an optional
implementation refinement.
-/

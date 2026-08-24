import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.InternalEncoding.Basic
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.InternalEncoding.Parser
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.InternalEncoding.RoundTrip
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.InternalEncoding.Length

/-!
# Internal encoding for the concrete general-circuit-to-SAT machine

This facade exports the guarded finite alphabet, its complete parser, exact
round-trip theorems, and the quadratic size bounds used by the later TM2
controllers.
-/

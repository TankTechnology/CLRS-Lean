import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Syntax
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Machine
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Macros
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Clock
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactPolynomialClock
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryIndex
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.NatEncoding

/-!
# Verified bounded TM2 builders

This facade exposes the typed builder language, its independent semantics, the
concrete TM2 compiler, one-step agreement, exact bounded-run transport to TM2
output witnesses, and polynomial-time packaging.  The verified scan/copy,
symbol-local bounded-loop, and ordered-pair nested-loop macros are present with
canonical exact builder and compiled runs.  The nested loop computes row-major
pair output while clearing every scratch stack.  The clock layer repeatedly
composes that quadratic machine to supply concrete clocks of any required
fixed polynomial degree.  The exact-clock layer adds a sentinel-and-tuple
construction whose concrete TM2 output has length exactly `p.eval input.length`,
including empty inputs and constant terms.  The reversal layer provides an
exact linear-time finalization pass for prepend-based streaming encoders, and
the unary-index layer generates the complete wire-reference stream in
quadratic time.  The natural-number serializer connects those counters to the
actual finite `CircuitSym` encoding alphabet.
-/

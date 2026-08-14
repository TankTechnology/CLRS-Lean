import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Syntax
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Machine
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Macros
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Clock
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactPolynomialClock
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryIndex
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.NatEncoding
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.InputGate
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.CircuitPrefix
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.BoolPool
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.BoolEq

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
actual finite `CircuitSym` encoding alphabet.  The input-gate streamer emits
the exact serialized family `.input 0, ..., .input (n - 1)` with a concrete
quadratic-time machine.  The circuit-prefix layer parks and restores the clock
while combining its exact arity header with that input-gate stream in one
concrete quadratic-time run.  The Boolean-pool suffix layer then appends the
canonical false/true constant gates in linear time.
The exactly-one layer and its affine wrapper stream contextual row constraints;
the Boolean-equality layer reuses the same three-counter kernels to emit an
arbitrary five-gate XNOR trace with an exact linear runtime and cleared scratch.
-/

import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Syntax
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Machine
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Macros
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Clock
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactPolynomialClock
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactPolynomialUnaryFrame
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactPolynomialUnaryFrameFamily
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactPolynomialUnaryIndexFrames
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineUnaryProgression
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactPolynomialAffineUnaryProgression
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineUnaryTripleProgression
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactPolynomialAffineUnaryTripleProgression
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryIndex
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.NatEncoding
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.InputGate
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.CircuitPrefix
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.BoolPool
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.BoolEq
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.SuffixOr
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Not
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneOutputSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneOutputFamilySource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneRowFamilySource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOnePrefixSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneHeightSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneCellProgressionSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneStackSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneStackFamilySource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneStructuredRowSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneStructuredRowFamilySource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneSeedCarrierSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneMarkedRowInvocationSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneLeadingFixedCompactProjection
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneSeedCarrierNormalizeSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineValidityTailRowFamilySource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineValidityTailStackFamilySource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineStackOutputFamilySource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineValidityFinalConjunctionSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineValidityTailSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineUnaryTripleMapSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameDelimiterMap
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameFixedPrefixSplice
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryTripleRowMark
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowDuplicate
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameDuplicatedRowRoute
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneMarkedPrefixPayloadSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameLeadingSegmentFixedPrefixSplice

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
including empty inputs and constant terms.  The exact unary-frame layer then
compiles that value into the delimiter-bearing operand representation used by
the runtime controllers, and its family extension shares one tuple enumeration
while producing any fixed finite sequence of polynomial-valued operands.  The
reversal layer provides an
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
The affine suffix-OR layer uses a separate nested control phase to generate the
right-to-left active-cell mask with an exact contextual run and quadratic
counter bound.  The single-NOT layer closes the remaining primitive used at
the head of every six-gate stack-cell block.  The compact one-hot source layers
now compose the label/state prefix with every fixed stack block in one
continuous row controller, while keeping the tableau height and affine offsets
as runtime unary counters and proving the exact emitted frame sequence.  The
outer row-family source now iterates that controller over a runtime seed stream
with explicit counter clearing between rows and an exact clean-halt theorem.
The seed-carrier source preserves all three row parameters as two synthetic
compact frames, so the ordinary marked-row projector can consume those values
and the genuine one-hot row in one continuous stream.
The carrier normalizer then decodes those synthetic frames with one fixed
controller and emits a seed-first packet while preserving the genuine
invocation payload byte-for-byte, closing the next typed streaming boundary.
The affine-triple map source additionally turns a raw runtime
`(height, start, rowBase)` stream into any verifier-fixed finite table of
affine operands using one concrete quadratic-time TM2 controller.
The fixed delimiter-map layer then rewrites ordinary unary separators to any
verifier-fixed cyclic `separator`/`frameEnd` layout in exact linear time.
-/
